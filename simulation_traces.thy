theory Simulation_Traces imports Main begin

typedecl state
typedecl event
datatype xevent = Tau | Vis event
consts Mi :: "(state * xevent * state)set"

axiomatization
  Ms :: "(state * event * state)set"
where
  detMs: "ALL p e p1 p2. (p, e, p1) : Ms & (p, e, p2) : Ms --> p1=p2"

definition sim :: "(state * state)set => bool"
where
  "sim R =
    (ALL p q. (p, q) : R -->
      (ALL e p'. (p, Vis e, p') : Mi -->
          (EX q'. (q, e, q'): Ms & (p', q') : R))
    & (ALL p'. (p, Tau, p') : Mi --> (p', q) : R))"

inductive_set
  paths :: "('s * 'e * 's)set => 's => ('s * 'e * 's)list set"
  for M :: "('s * 'e * 's)set" and p :: 's
where
  base0 [intro]: "[] : paths M p" |
  base1: "(p, u, q) : M
            ==> [(p, u, q)] : paths M p" |
  step: "[| (q, u, q') : M; cs : paths M p; cs ~= [];
            snd (snd (hd cs)) = q |]
            ==> (q, u, q')#cs : paths M p"

fun path_to_trace_s :: "('s * event * 's)list => event list"
where
  "path_to_trace_s [] = []" |
  "path_to_trace_s ((p, e, q)#cs) = e#(path_to_trace_s cs)"

fun path_to_trace_i :: "('s * xevent * 's)list => event list"
where
  "path_to_trace_i [] = []" |
  "path_to_trace_i ((p, Tau, q)#cs) = path_to_trace_i cs" |
  "path_to_trace_i ((p, Vis e, q)#cs) = e#(path_to_trace_i cs)"

definition traces_s :: "state => event list set"
where
  "traces_s p = path_to_trace_s ` (paths Ms p)"

definition traces_i :: "state => event list set"
where
  "traces_i p = path_to_trace_i` (paths Mi p)"

lemma sim_D:
  "sim R ==>
    (ALL p q. (p, q) : R -->
              (ALL e p'. (p, Vis e, p') : Mi -->
                 (EX q'. (q, e, q'): Ms & (p', q') : R))
            & (ALL p'. (p, Tau, p') : Mi --> (p', q) : R))"
apply(unfold sim_def)
apply(auto)
done

lemma conjD1: "p & q ==> p"
by auto
lemma conjD2: "p & q ==> q"
by auto

lemma sim0:
  "[| (p, Vis e, p') : Mi; sim R; (p, q) : R |]
  ==> EX q'. (q, e, q') : Ms & (p', q') : R"
by (metis sim_D)

lemma sim1 [intro]:
  "[| (p, Vis e, p') : Mi; (q, e, q') : Ms; sim R; (p, q) : R |]
  ==> (p', q') : R"
by (metis detMs sim_D)

lemma sim2 [intro]:
  "[| (p, Tau, p') : Mi; sim R; (p, q) : R |]
  ==> (p', q) : R"
by (metis sim_D)

lemma path_prefix [rule_format]:
  "ps : paths m p ==>
  (ALL us vs. ps = us @ vs --> vs : paths m p)"
apply(erule paths.induct)
apply(auto)
apply(case_tac vs)
apply(clarsimp)
apply (metis paths.base0)
apply(case_tac vs)
apply(clarsimp)
apply (metis (erased, hide_lams) Cons_eq_append_conv Nil_is_append_conv paths.simps)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac us)
apply(clarsimp)
apply(drule_tac x="[]" in spec)
apply(drule_tac x="(a, aa, b) # list" in spec)
apply(drule mp)
apply(clarsimp)
apply(erule step)
apply(auto)
done

lemma path_prefix1:
  "(p1,u,p2)#ps : paths m p ==> ps : paths m p"
by (metis append.simps(1) append.simps(2) path_prefix)

lemma path1_event [simp]: "[(a, u, b)] : paths m p ==> a=p"
apply(erule paths.cases)
apply(auto)
done

lemma path1_step [simp]: "[(p, u, p')] : paths m p0 ==> (p, u, p') : m"
apply(erule paths.cases)
apply(auto)
done

lemma path2_event:
  "(b', u, c) # (a, w, b) # ps : paths m p ==> b'=b"
apply(erule paths.cases)
apply(auto)
done

lemma path2_step:
  "(p1, u, p2) # ps : paths m p ==> (p1, u, p2) : m"
apply(erule paths.cases)
apply(auto)
done

lemma path_spec_emp [simp, rule_format]:
"qs : paths Ms q ==>
  path_to_trace_s qs = [] --> qs = []"
apply(erule paths.induct)
apply(auto)
done

lemma path_tau [rule_format]: "path_to_trace_i ps = [] -->
  ps : paths Mi p -->
  sim R -->
  (p, q) : R -->
  ps ~= [] -->
  (snd (snd (hd ps)), q) : R"
apply(induct_tac ps)
apply(auto)
apply(case_tac aa)
apply(auto)
apply(case_tac aa)
apply(auto)
apply(drule path_prefix1)
apply(simp)
apply(subgoal_tac "a=p")
apply(drule path2_step)
apply (metis list.distinct(1) path_to_trace_i.simps(3) sim_D xevent.exhaust)
apply (metis path1_event)
apply(case_tac aa)
apply(auto)
apply(case_tac list)
apply(auto)
apply(subgoal_tac "a=p")
apply(clarsimp)
apply (metis path2_step sim_D)
apply (metis path1_event)
by (metis path2_event path2_step sim_D)

lemma sim_path [rule_format]:
  "ps : paths Mi p -->
  (ALL qs. qs : paths Ms q -->
  sim R -->
  (p, q) : R -->
  path_to_trace_s qs = path_to_trace_i ps -->
  ps ~= [] -->
  qs ~= [] -->
  (snd (snd (hd ps)), snd (snd (hd qs))) : R)"
apply(induct_tac ps)
apply(auto)
apply(drule_tac us="[(a, aa, b)]" and vs="list" in path_prefix)
apply(auto)
apply(case_tac list)
apply(auto)
apply(case_tac aa)
apply(auto)
apply(case_tac qs)
apply(auto)
apply(rule sim1)
apply(auto)
apply(frule path1_event)
apply(drule path1_step)
apply(simp)
apply (metis (full_types) list.distinct(1) path1_event path1_step path_to_trace_i.simps(1) path_to_trace_s.elims)
(**)
apply(case_tac aa)
apply(auto)
apply(drule_tac x="qs" in spec)
apply(auto)
apply (metis path2_event path2_step sim_D)
apply(case_tac qs)
apply(auto)
apply(drule_tac x="list" in spec)
apply(auto)
apply(drule_tac vs="list" in path_prefix)
apply(simp)
apply(clarsimp)
apply(case_tac ac)
apply(auto)
apply(frule path1_event)
apply(drule path1_step)
apply(clarsimp)
apply(case_tac lista)
apply(auto)
apply (metis path1_event path2_event path2_step path_prefix1 sim1 sim_D)
apply(case_tac ac)
apply(auto)
apply(subgoal_tac "path_to_trace_i ((ab, Tau, ba) # (aa, Tau, bc) # list) = []")
apply(drule path_tau)
apply(drule path_prefix1)
apply(assumption)
apply(assumption)
apply(assumption)
apply(simp)
apply(clarsimp)
apply(erule contrapos_np)
apply (metis path2_event path2_step sim1)
apply(simp)
apply(case_tac list)
apply(auto)
apply (metis list.distinct(1) list.sel(1) path1_event path2_event path2_step path_prefix1 path_tau sim1 snd_conv)
apply(frule path2_step)
apply(drule path2_event)
apply(clarsimp)
apply(frule path2_step)
apply(drule path2_event)
apply(clarsimp)
by (metis detMs sim_D)

lemma sim_tr0 [rule_format]:
  "ps : paths Mi p ==>
  sim R -->
  (p, q) : R -->
  (EX qs. qs : paths Ms q & path_to_trace_s qs = path_to_trace_i ps)"
apply(erule paths.induct)
apply(auto)
apply(case_tac u)
apply(auto)
apply(drule sim0)
apply(assumption)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="[(q, event, q')]" in exI)
apply(clarsimp)
apply (metis paths.base1)
(**)
apply(case_tac cs)
apply(auto)
apply(case_tac u)
apply(auto)
apply(case_tac qs)              (* to apply sim_path *)
apply(auto)
apply(subgoal_tac "(b, q) : R")
apply(drule sim0)
apply(auto)
apply(rule_tac x="[(q, event, q'a)]" in exI)
apply(clarsimp)
apply (metis paths.base1)
apply (metis list.distinct(1) list.sel(1) path_tau snd_conv)
apply(drule_tac ps="(a, aa, b) # list" and qs="(ab, ac, ba) # lista" in sim_path)
apply(auto)
apply(drule sim0)
apply(auto)
apply(rule_tac x="(ba, event, q'a)#(ab, ac, ba) # lista" in exI)
apply(auto)
by (metis list.distinct(1) list.sel(1) paths.step snd_conv)

lemma sim_tr:
  "[| ps : paths Mi p; sim R; (p, q) : R |]
  ==> EX qs. qs : paths Ms q & path_to_trace_s qs = path_to_trace_i ps"
apply(erule sim_tr0)
apply(auto)
done

theorem "EX R. sim R & (p, q) : R ==> traces_i p <= traces_s q"
apply(unfold traces_s_def traces_i_def)
apply(clarsimp)
apply(drule sim_tr)
apply(auto)
apply(rule_tac x="qs" in rev_image_eqI)
apply(auto)
done

end

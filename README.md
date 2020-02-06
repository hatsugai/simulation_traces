# simulation_traces

Formal proof by Isabelle/HOL 2014

Existence of asymmetric weak simulation between a deterministic transition system and a nondeterministic transition system implies the inclusion of traces.

∃R. R is a weak simulation and (p, q) ∈ R ==> traces(p) ⊆ traces(q)

where p is a state on a nondeterministic transition system
and q is a state on a deterministic transition system.

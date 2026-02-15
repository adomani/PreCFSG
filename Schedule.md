# Formalizing group theory

This is an intensive 1-week workshop for students interested in joining a collaborative effort to formalize the classification of finite simple groups in Lean.

We will meet every day for 2 hours, from Monday March 16th to Friday March 20th, 2026.

Each day, I will give a 30-45 minute presentation on group theory and formalization, followed by a hands-on session where you will work in small groups on various formalization targets.

The lectures will cover the mathematical ideas underlying the formalization targets, as well as ways of converting human-language proofs into Lean code.

I will also discuss best-practices for collaborative formalizations projects.

Sample formalization topics — these vary in length, some are open ended, some may be in reach within the week, others may involve much more work
* the Brauer-Fowler theorem (Aschbacher, Finite Simple Groups Theorem 45.5, page 244)
* the Thompson Odd-order formula (Aschbacher, Finite Simple Groups Theorem 45.6, page 245)
* defining semisimple groups and proving some of their basic properties (Isaacs, Finite Group Theory, page 274)
* minimal normal subgroups of finite groups are abelian or semisimple (Isaacs, Finite Group Theory, Lemma 9.6, page 275)
* basic structure of the layer (Isaacs, Finite Group Theory, Theorem 9.7, page 275)
* define extraspecial groups, classify them, study their characters
* construct one of the 26 sporadic simple groups, prove that it is simple, compute its size, find the conjugacy classes of its involutions

Every participant is expected to have access to a working copy of this repository.
In particular, this means having the Mathlib cache already available on your computer.
(E.g., running `lake exe cache get` should be virtually instantaneous.)

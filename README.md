## Workshop on Group theory and formalization in Lean

Lectures: Damiano Testa (University of Warwick)

Venue: Tsinghua University

Dates: March 16-20, 2026

### Format:

#### Mon-Fri 5-7pm

* 2 hours each day -- 30-45 minutes of lecture, followed by group work
* 1 hour lecture on "Overview of the Classification of Finite Simple Groups"

### Schedule (tentative)

#### Monday
* examples of informal vs formal definitions, with main focus on group theory
* presentation of group theory projects to work on during the week (you can also work on a project not among the ones that I suggest!)
* working on projects + Q&A

#### Tuesday
* maintaining formalisation libraries: [mathematics and infrastructure](Maintenance/Maintaining_1_Maths.pdf)
* working on projects + Q&A

#### Wednesday
* more group theory in Lean and design decisions
* working on projects + Q&A

#### Thursday
* maintaining formalisation libraries: [automation and AI](Maintenance/Maintaining_2_AI.pdf)
* working on projects + Q&A

#### Friday
* talk on the [classification of the finite simple groups](Overview_of_classification/Classification.pdf)
* working on projects and presentations

---

This is an intensive 1-week workshop for students interested in joining a collaborative effort to formalize the classification of finite simple groups in Lean.

We will meet every day for 2 hours, from Monday March 16th to Friday March 20th, 2026.

I will also give a presentation on the overall structure of finite simple groups.

Each day, I will give a 30-45 minute presentation on group theory, formalization and maintenance of large formalisation libraries.  After that, there will be hands-on sessions where the participants will work in small groups on various formalization targets.

The lectures will cover the mathematical ideas underlying the formalization targets, as well as ways of converting human-language proofs into Lean code.

I will also discuss best-practices for collaborative formalizations projects.

Sample formalization topics — these vary in length, some are open ended, some may be in reach within the week, others may involve much more work
* the Brauer-Fowler theorem (Aschbacher, Finite Simple Groups, Theorem 45.5, page 244)
* the Thompson Odd-order formula (Aschbacher, Finite Simple Groups, Theorem 45.6, page 245)
* defining semisimple groups and proving some of their basic properties (Isaacs, Finite Group Theory, page 274)
* minimal normal subgroups of finite groups are abelian or semisimple (Isaacs, Finite Group Theory, Lemma 9.6, page 275)
* basic structure of the layer (Isaacs, Finite Group Theory, Theorem 9.7, page 275)
* define extraspecial groups, classify them, study their characters
* construct one of the 26 sporadic simple groups, prove that it is simple, compute its size, find the conjugacy classes of its involutions

The actual topics may vary, this is just a sample.

Every participant is expected to have access to a working copy of this repository.
In particular, this means having the Mathlib cache already available on your computer.
(E.g., opening a file with `import Mathlib.Tactic` should *not* be building any file.)

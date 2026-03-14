## Workshop on Group theory and formalization in Lean

Lectures: Damiano Testa (University of Warwick)

Venue: Tsinghua University

Dates: March 16-20, 2026

### Format:

We will meet every day for 2 hours, from Monday March 16th to Friday March 20th, 2026.

Each day, I will give a 30-45 minute presentation on group theory, formalization and maintenance of large formalisation libraries.

After that, there will be hands-on sessions where the participants will work in small groups on various formalization targets.

#### Mon-Fri 5-7pm

* 2 hours each day -- 30-45 minutes of lecture, followed by group work
* 1 hour lecture on "Overview of the Classification of Finite Simple Groups"

### Schedule

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

### Description

This is an intensive 1-week workshop for students interested in joining a collaborative effort to formalize the classification of finite simple groups in Lean.

The lectures will cover
* mathematical ideas underlying the formalization targets
* ways of converting human-language proofs into Lean code
* best-practices for collaborative formalizations projects
* a presentation on the overall structure of finite simple groups

Here is a [list of formalisation ideas](formalisation_ideas.md).
These have different lengths and scopes: some are well-suited for being completed during the workshop, others are open-ended and long-term.

### Prerequisites

Every participant is expected to have access to a working copy of this repository.
In particular, this means having the Mathlib cache already available on your computer.
(E.g., opening a file with `import Mathlib.Tactic` should *not* be building any file.)

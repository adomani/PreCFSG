# Symptoms of AI Code

This file collects what I identify as symptoms of AI code.
What I point out here need not be undesirable code, but could be.

If carefully curated human code is the final goal of what AIs should write, then at least some of the items below need to be addressed!

## Walls of `have` and forward reasoning

* Disincentivize `have`
* Favor `refine`, `apply`, `exact`

The rationale is that `have`s bloat the context for little gain.
Tactics like `refine` and `apply` have the opposite effect:
* they usually create more subgoals,
* the subgoals are good candidates for API lemmas (possibly with a filter that they should be separate goals, only if they require fewer/different assumptions to be proved)
* create a tree-like structure for the proof, which allows for "recursive solving"

Using `refine` and `apply` often goes under the name of backward reasoning.

Possible reason for so many auto-generated walls of `have`:
informal mathematics proof often "arrive at the conclusion" starting from the hypotheses.

Imprecisely, if models could be trained by reading proofs from the end, they would likely begin with a `refine` or `apply` and generate as side-goals the latest `have`s.

Continuing in this manner has better chances of writing more idiomatic code.

It also highlights as possible API lemmas precisely the subgoals thus created.

## Nested tactic calls

`mathlib` has a loosely enforced principle that each line of a proof should contain at most one tactic.

AI-generated proofs, however, often like interlacing tactic-mode proofs and term-mode proofs, by nesting `exact` with `by exact`, possibly multiple times.

Disincentivising more than 1 tactic in each node of a sequence of tactics (a `tacticSeq`) seems more aligned with human code.

The result is often more readable and more maintainable code.

## Reduce lengths of proofs

After getting familiar with formalisation, it becomes apparent that what seems like a single reasoning step, really hides multiple more atomic connections.

AIs tend to take this to the extreme and produce individual proofs that are several hundreds or even thousands of lines long.

Penalising proofs proportionally to their length may have the effect of splitting out (useful? see the "Walls of `have`" section) lemmas, improving performance, reducing the overall complexity by focusing on simpler results.

## Reduce the number of `def`initions

While definitions are not intrinsically a symptom of bad code, many concepts do not actually need a separate definition.

More definitions means writing more API for each definition, which in turn bloats the code-base for potentially little benefit.

AI-generated proofs normally introduce multiple `def`initions for the most trivial of concepts.

I think that it is worthwhile to seriously consider whether so many definitions are useful or harmful -- my inclination is to think that they are harmful.

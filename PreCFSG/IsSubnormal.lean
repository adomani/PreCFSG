module

public import Mathlib.GroupTheory.IsSubnormal

/-!
# Subnormal subgroups

## Standard definition of subnormality

A subgroup `H ≤ G` is *subnormal* in `G` if there exists a **finite chain** of subgroups
`H = H₀ ⊴ H₁ ⊴ \cdots ⊴ Hₙ = G`

where each `Hᵢ` is **normal** in `Hᵢ₊₁`.

The emphasis in textbooks is:

* The chain is **finite**, in particular, `n` shows up.
* There is a **chain**, that is, you mention all subgroups in the statement.
* Each step involves highly dependent constraints
  ("dependent" in the "dependent type theory" sense).

-/

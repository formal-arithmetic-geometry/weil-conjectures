## Worker report

The module `Sheaf.AlgebraicGeometry.KoszulImmersionSmoothAmbientIndependence` states
`AlgebraicGeometry.isKoszulRegularImmersionNear_smoothAmbient_iff`, with its sole proof
`sorry`. The statement and proof plan follow Stacks, More on Morphisms, Tag 069E
(`lemma-koszul-independence-factorization`), read in `literature/stacks-project/`.
The comparison lemmas were also checked in Divisors, Tags 067S and 0693, and the
immersion definition in Tag 063J. No mathematical statement correction is needed.

Hypothesis and conclusion correspondence:

- The schemes S, T, P, P' are `{S T P P' : Scheme.{u}}`; `u` is explicitly declared.
  The two ambient structure maps are `(p : P ⟶ S)` and `(p' : P' ⟶ S)`.
- Smoothness is exactly `[Smooth p] [Smooth p']`, with no fixed relative dimension.
- The morphisms are `(i : T ⟶ P) (i' : T ⟶ P')`; the immersion hypotheses are
  `[IsImmersion i] [IsImmersion i']`, not closed-immersion hypotheses.
- Being over the same S is `(h : i ≫ p = i' ≫ p')`. Its common composite is the
  structure map T → S, so an additional choice of that map is unnecessary. Conversely,
  any pair of S-morphisms supplies this equality.
- Every source point is covered by `(t : T)` in the universally quantified theorem.
- The two sides of the iff are `IsKoszulRegularImmersionNear i t` and
  `IsKoszulRegularImmersionNear i' t`. Expanding this existing definition gives an
  open source neighbourhood V containing t, an open target U, and a closed immersion
  j : V → U satisfying `j ≫ U.ι = V.ι ≫ i`, together with
  `CotangentPresentation.IsKoszulImmersion j`. The latter quantifies over every
  point of V and supplies an affine target neighbourhood, r : ℕ, and a sequence
  `a : Fin r → Γ(U, W)` with `RingTheory.Sequence.IsKoszulRegular a` and
  `Ideal.span (Set.range a) = j.ker.ideal W`. Thus the locally generated ideal,
  finite Koszul-regular equations, varying lengths, and empty sequence are all
  rendered by the existing notion without adding an assumption.
- There are no Noetherian, flatness, separation or quasi-compactness binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`; its
  affine-local smooth-ring definition is the recorded equivalent of the infinitesimal
  definition (Stacks 02H6).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; the existing neighbourhood predicate uses it.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion`,
  `IsImmersion.isImmersion_iff_exists`, and the proof input `IsImmersion.of_comp`.
  This file is public through the neighbourhood-definition module.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, vanishing of nonzero Koszul homology.
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear`:
  `AlgebraicGeometry.IsKoszulRegularImmersionNear`. Its already landed definition node
  `def-sfb-koszul-regular-immersion-near` is added to stmt_deps under the rule allowing
  landed notions to be cited. There are no new nodes and no dependency repairs.
- `Sheaf.AlgebraicGeometry.LciCotangentPresentation`:
  `AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion`, read in full and used
  through the neighbourhood predicate, rather than defined again.
- Proof-only imports are `Mathlib.AlgebraicGeometry.Pullbacks` (the recorded
  `CategoryTheory.Limits.pullback` and its projections),
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (the recorded permanence leaves).
  Immersion cancellation is already available through the public imports. The two
  smooth lift/push nodes have no Lean record or Mathlib match and hence contribute no
  proof import at this stage. Their full five-step use remains in the theorem docstring.

Edge cases checked before writing: an empty source has no t to check; the scheme
universe is arbitrary. The zero-equation case is retained by r : ℕ in the existing
predicate (e.g. an identity/open immersion); the identity into T and a zero section
into affine one-space over T can have different equation lengths, which the statement
allows. No equality or positivity of codimensions is required. Arbitrary characteristics,
non-Noetherian bases and nonseparated ambient schemes remain allowed. For a nonregular
immersion the theorem asserts equivalence, not that either side always holds. The shared
base condition is substantive: smoothness alone does not identify the two composites.

Searches for existing statements and notions:

- `msearch.py`, leanfinder, query: “Koszul regularity of immersions into smooth schemes
  over the same base is independent of the smooth ambient scheme”. Eight hits, ordinary
  smoothness/formal unramifiedness only; no ambient-independence statement.
- `msearch.py`, loogle, query `"Koszul", "regular"`: zero hits.
- `msearch.py`, grep, query `Koszul|RegularImmersion|regular_immersion` in
  `AlgebraicGeometry`: zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for Koszul/regular immersions,
  then `IsKoszulImmersion|IsKoszulRegularImmersionNear|smooth_ambient|ambient_independence`:
  found the reusable closed-chart and near-point predicates, and the field-extension
  iff, which is a different statement. No existing smooth-ambient iff was found.
- Searched `lean/WeilConjectures` for the item's exact id, and the upstream-name index
  for `koszul-immersion-smooth`: no match. Searched both source trees for the chosen
  declaration name: no collision.
- Searched `dag/nodes` for the near-point predicate and read its existing definition
  node and closed-chart node, confirming that no new definition is needed.

Validation uses only the prescribed per-file server compiler and delivery wrapper.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

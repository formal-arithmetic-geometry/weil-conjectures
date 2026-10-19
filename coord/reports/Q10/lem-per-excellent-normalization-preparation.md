## Worker report

Q10 states `lem-per-excellent-normalization-preparation` in
`Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation`. The source is
`literature/stacks-project/morphisms.tex`, Tags 035S (Nagata normalization),
035Q (normality of normalization), and 0BAJ (finite birational isomorphism over
a dense open), with excellence from More on Algebra Tags 07QV and 07QU. The
statement is unchanged.

The theorem is
`AlgebraicGeometry.excellent_normalization_preparation`. Its input is a scheme
`X : Scheme.{u}` with `[IsReduced X]`, `[IsLocallyNoetherian X]`, and
`[CompactSpace X]`; these render reducedness and “Noetherian means locally
Noetherian and quasi-compact”. The explicit hypothesis
`hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U)` says that every affine
open coordinate ring is excellent, exactly the excellence convention in the
node. The componentwise normalization and its canonical map are the recorded
`X.reducedNormalization` and `X.fromReducedNormalization`.

Clause by clause, the conclusion is rendered as follows.

* `IsFinite X.fromReducedNormalization` and
  `Surjective X.fromReducedNormalization` state that the canonical map is finite
  and surjective, using Mathlib's scheme morphism predicates.
* `IsLocallyNoetherian X.reducedNormalization ∧
  CompactSpace X.reducedNormalization` states that the normalization is
  Noetherian under the node's locally-Noetherian plus quasi-compact convention.
* `∀ V : X.reducedNormalization.affineOpens,
  IsExcellent Γ(X.reducedNormalization, V)` states excellence of every affine
  coordinate ring of the normalization.
* `∀ x : X.reducedNormalization,
  IsDomain (X.reducedNormalization.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk x)` states that every
  local ring is an integrally closed domain. This is the recorded normal-ring
  interface (`IsDomain` together with Mathlib's `IsIntegrallyClosed`), applied
  to the scheme stalk.
* The final existential is an open subscheme `U : X.Opens`. Its three clauses
  are `Dense (U : Set X)`, containment of every generic point of each
  irreducible component (`∀ Z, ∀ x, IsGenericPoint x Z.1 → x ∈ U`), and
  `IsIso (X.fromReducedNormalization ∣_ U)`, the isomorphism of the restricted
  map from `ν⁻¹U` to `U`. The quantifiers allow the empty scheme and `U = ⊥`.

Dependency declarations used (their full signatures and docstrings were read):

* `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `AlgebraicGeometry.Scheme.reducedNormalization`,
  `AlgebraicGeometry.Scheme.fromReducedNormalization`, and
  `AlgebraicGeometry.Scheme.isIntegral_reducedNormalizationComponent`.
* `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (with its component
  definitions `IsQuasiExcellent` and `IsUniversallyCatenary`).
* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`:
  `AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.IsIntegralHom` (the
  finite predicate is the one used here).
* `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`:
  `IsDomain`, `IsIntegrallyClosed`, and `Localization.AtPrime` as the recorded
  normal-ring interface.
* `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (the restriction isomorphism is expressed
  by `IsIso` on the restricted morphism).
* `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`.
* `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
* `Mathlib.Topology.Sober`: `IsGenericPoint`.

Edge cases checked before writing: for `X = ∅`, the component index is empty,
`X.reducedNormalization` and `U` may both be empty, the finite and surjective
claims are vacuous in the corresponding scheme predicates, the local-ring
quantifier is empty, and the generic-point condition is vacuous. For a normal
integral affine scheme the normalization map can be the identity on all of `X`.
For a reducible reduced affine scheme such as `Spec (k[x,y]/(xy))`, generic
points are quantified componentwise, so the open only needs to contain those
points. No nonemptiness, separatedness, characteristic, or extra universe
assumption is introduced.

Searches for an existing exact declaration:

* `msearch.py ... leanfinder "finite normalization reduced Noetherian excellent
  scheme dense open generic points"`: returned Mathlib relative-normalization,
  reduced-normalization, and Noetherian declarations, but no theorem with the
  componentwise construction, excellence hypothesis, and dense-open conclusion.
* `msearch.py ... loogle "IsFinite Surjective IsIntegrallyClosed IsGenericPoint
  normalization"`: zero hits (the service also reported `IsFinite` as unknown).
* `msearch.py ... grep "excellent_normalization|componentwise
  normalization|fromReducedNormalization" WeilConjectures/Mathlib/AlgebraicGeometry
  WeilConjectures/`: no exact declaration.
* `rg -n "excellent_normalization_preparation|componentwise normalization|
  fromReducedNormalization"` over `WeilConjectures/` and shared `lean/Sheaf/`:
  found only componentwise-normalization constructions and theorems with
  different hypotheses/conclusions, including the field-change theorem; no exact
  statement. The existing field-change theorem does not assert excellence of the
  source or generic-point containment and therefore is not a match.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q10

I reread the node, its source clauses, and the module independently. The
reduced, locally-Noetherian, quasi-compact, and every-affine-excellent
hypotheses are all present. The finite and surjective map clauses use exactly
`fromReducedNormalization`; the source excellence and Noetherian clauses are
separate and both retained. The local-ring clause quantifies over every point of
the recorded normalization and uses the recorded integrally-closed-domain
encoding. The final open is an actual `X.Opens`, is dense, contains every
`IsGenericPoint` of every irreducible component, and uses the canonical
restriction `fromReducedNormalization ∣_ U` for the isomorphism. The empty case
remains admitted. No mismatch was found and no change was needed.

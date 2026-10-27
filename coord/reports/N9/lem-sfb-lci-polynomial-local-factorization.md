## Worker report

The module `Sheaf.AlgebraicGeometry.LciPolynomialLocalFactorization` states
`AlgebraicGeometry.exists_lci_polynomial_local_factorization`; its only proof is
`sorry`. No definitions or additional theorem statements are introduced. The node
is unchanged except for its Lean record and two added, already-landed definition
statement dependencies. No statement correction or disputed statement is needed.

Clause correspondence:

- Schemes and their morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Every source point has an open neighbourhood: `hf : ∀ x : X, ∃ U : X.Opens,
  x ∈ U ∧ ...`.
- The factorization into a closed immersion and smooth map is the existential
  `P`, `j : U.toScheme ⟶ P`, `p : P ⟶ Y`, with `IsClosedImmersion j`,
  `Smooth p`, and `j ≫ p = U.ι ≫ f`.
- Its ideal locally has finite Koszul-regular generators:
  `CotangentPresentation.IsKoszulImmersion j`. The recorded definition quantifies
  over each source point, an affine target neighbourhood, a finite length, and
  generators that span the actual kernel ideal and are Koszul-regular. It does
  not assert ordinary regularity or impose a constant length.
- The arbitrary chosen point and target open are `(x : X) (V : Y.Opens)` with
  exactly the required membership `hx : f x ∈ V`.
- The output source neighbourhood is `∃ U : X.Opens, x ∈ U ∧ U ≤ f ⁻¹ᵁ V`.
- The nonnegative integer is `n : ℕ`, including zero. The polynomial ambient
  scheme is Mathlib's `AffineSpace (ULift.{u} (Fin n)) V.toScheme`. The universe
  lift keeps its coordinate type in the scheme's universe without changing the
  number of coordinates.
- The map `a` has precisely that source and target, with `IsImmersion a`.
- Koszul regularity is `∀ z : U.toScheme, IsKoszulRegularImmersionNear a z`.
  Unfolding the recorded predicate gives a source neighbourhood of each `z`, an
  open target subscheme, and a closed immersion into it with locally finite
  Koszul-regular kernel generators. The global immersion condition is retained
  separately: local closed charts alone would not state global immersion.
- The composite is the equality
  `a ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) ≫ V.ι = U.ι ≫ f`.
  Thus `a` is over `V`: composing with the monomorphism `V.ι` agrees with the
  restriction to `V`, and cancellation identifies the two maps to `V`.
- No Noetherian, flatness, separation, quasi-compactness, nonemptiness, or field
  hypothesis occurs. No affine condition is imposed on the chosen target open.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; `Scheme.Opens` and the open subscheme inclusions.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; the immersion notion is
  `AlgebraicGeometry.IsImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, exported by the near-point module.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, using actual positive Koszul homology
  vanishing, with no nonzero-quotient condition.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and
  `AffineSpace.over`, the canonical projection used in the equality.
- `Sheaf.AlgebraicGeometry.LciCotangentPresentation`:
  `AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion` (lines 417--420).
  This is owned by already-landed `def-sfb-koszul-closed-immersion-chart`.
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear`:
  `AlgebraicGeometry.IsKoszulRegularImmersionNear`. This is owned by already-landed
  `def-sfb-koszul-regular-immersion-near`. Both definition nodes are added to
  `stmt_deps`; neither is copied or redefined.

Available proof-dependency modules are plain imports: finite presentation via
`Mathlib.RingTheory.FinitePresentation` (`Algebra.FinitePresentation`), the smooth
restriction instances in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, the affine
criterion `HasRingHomProperty.Spec_iff` in
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`, affine-space smoothness
`AffineSpace.smoothOfRelativeDimension_over` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`, and
`Algebra.Smooth.baseChange` / `Algebra.Smooth.comp` in
`Mathlib.RingTheory.Smooth.Basic`. The scheme, immersion, sequence and affine-space
proof dependencies are already public statement imports. The two proof-only nodes
`lem-sfb-koszul-immersion-smooth-lift` and
`lem-sfb-koszul-immersion-smooth-push` have no Lean record or Mathlib match in the
read clone, hence have no recorded module to import. They are named in the full
six-step proof docstring; the item does not need their statements for its signature.

Source checked: `literature/stacks-project/more-morphisms.tex`, the full
independence lemma 069E, the polynomial factorization remark preceding 069F, the
definition 069F, and the ensuing lemma 069G (lines 18055--18145). The assumption
uses the node's stronger closed-chart version of the local factorization; its
conclusion uses exactly the immersion version in the polynomial remark. No
source-driven correction is required.

Edge cases checked before writing: empty source gives a vacuous pointwise
conclusion; empty target open cannot contain `f x`; `n = 0` is permitted and uses
the canonical zero-space isomorphism; empty Koszul sequences and varying lengths
are permitted by both reused definitions; non-affine and non-quasi-compact `V`
are allowed. The nonflat regular immersion `Spec (ℤ/2) → Spec ℤ` is not excluded.
A length-one zero equation in a nonzero ring is not made regular by any arbitrary
regularity hypothesis; the reused predicate requires its actual Koszul homology
to vanish. All scheme and finite-coordinate universes are explicitly bound.

Searches made for an existing statement or notion:

- `msearch.py ... leanfinder`: "A scheme morphism locally factoring as a Koszul
  regular closed immersion followed by a smooth morphism locally embeds Koszul
  regularly into affine space over any target open" returned eight smooth-chart
  and related hits, none proving this statement.
- `msearch.py ... loogle`: `"IsKoszulRegular", "Smooth"` returned zero hits.
- `msearch.py ... grep`: `KoszulRegular|koszul.regular|IsLocalCompleteIntersection`
  returned only the regular-sequence Mathlib TODO.
- `msearch.py ... leansearch`: "Koszul regular immersion of schemes ideal locally
  generated by Koszul regular sequence" returned ordinary regular sequences and
  ordinary immersions, not this theorem or the missing local statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Koszul regularity and local
  complete intersections found the existing sequence and closed-chart definitions,
  and then the landed near-point definition. The upstream search for the exact
  item id and both trees for `PolynomialLocalFactorization`,
  `polynomial_local_factorization`, and `lci_polynomial` found no existing theorem.
- DAG search for Koszul regular immersions found the two landed definition nodes;
  `tools/blueprint_refs.py search 'Koszul-regular immersion'` returned zero blueprint
  nodes. The existing nodes' statements and full recorded definitions were read.

## Second reading by N9

I reread the node and the completed signature clause by clause using the mapping
above. This is a worker self-check; the dispatcher brief prohibits starting other
agents, and the maintainer supplies the independent delivery review. The essential
checks are that the hypothesis says closed immersion, the conclusion says global
immersion plus pointwise Koszul regularity, the arbitrary target open is retained,
and both equalities include the actual open inclusions and canonical projection.
No hypothesis, equation, or clause mismatch was found; no statement was corrected.

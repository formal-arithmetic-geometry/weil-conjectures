## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePseudoCoherenceAllAffineCharts` states
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_iff_all_affine_charts_and_exists_embedding`.
Its sole theorem has proof `sorry`; it introduces no definitions. The node changes only in
`lean`. No new nodes, dependency repairs, or statement corrections are needed.

Sources read: Stacks `more-morphisms.tex`, Tag 09UJ,
`lemma-relative-pseudo-coherence-characterize`, statement and proof; Tag 09VC,
`lemma-relatively-pseudo-coherent`, statement and proof; and the finite-generation/embedding
paragraph immediately before Tag 09UI. Also read the current blueprint's
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` file
`sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This is an auxiliary
Stacks lemma on the inherited prerequisite branch, not a change to the blueprint unit.

Hypotheses and clauses, in the node's order:

- Schemes and locally finite type morphism: `{X S : Scheme.{u}} (f : X ⟶ S)` and
  `[LocallyOfFiniteType f]`. There are no global affineness, separation, quasi-compactness,
  or Noetherian hypotheses.
- Derived object and arbitrary integer: `(E : schemeDerivedCategory X) (m : ℤ)`.
  No quasi-coherence or boundedness is assumed. The explicit
  `[∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u}
  (moduleRings Y.toRingedSpace))]` is the derived-localization size interface already
  required by the recorded relative pseudo-coherence definition; it supplies the source,
  all open subschemes, and all ambient affine spaces without identifying `u` and `w`.
- Relative degreewise pseudo-coherence: `IsMPseudoCoherentRelativeTo f m E`, precisely
  the dependency's affine-cover-and-embedding definition, not the all-integer predicate.
- “If and only if”: the first outer conjunct is an `↔`.
- Every compatible affine pair: `∀ (U : X.Opens) (V : S.Opens), IsAffineOpen U →
  IsAffineOpen V → ∀ (hUV : U ≤ f ⁻¹ᵁ V), ...`.
  The order inequality says exactly that `f(U) ⊆ V`.
- Every nonnegative integer and every closed immersion over the base:
  `∀ (n : ℕ) (j : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme),
  IsClosedImmersion j → j ≫ (AffineSpace ... V.toScheme ↘ V.toScheme) =
  f.resLE V U hUV → ...`.
  The equation is the over-`V` condition for the actual restriction of `f`.
- Absolute pseudo-coherence of the indicated derived direct image:
  `IsMPseudoCoherent (AffineSpace ...) m
  ((schemeDerivedDirectImage j).obj ((derivedPullback U.ι).obj E))`.
  Thus restrictions are the specified derived pullbacks, and absolute pseudo-coherence
  uses the recorded local strictly perfect approximation definition.
- Existence for each pair independently of `E`: the second outer conjunct repeats
  precisely the compatible affine-pair quantifiers and concludes
  `∃ n : ℕ, ∃ j : U.toScheme ⟶ AffineSpace ..., IsClosedImmersion j ∧
  j ≫ (AffineSpace ... ↘ V.toScheme) = f.resLE V U hUV`.
  The dimension is inside these quantifiers and can depend on the pair. This conjunct
  is not merely a consequence conditioned on relative pseudo-coherence.
- Relative affine space is Mathlib's `AffineSpace`, its fibre-product construction;
  `ULift.{u} (Fin n)` supplies the `n` variables in the scheme universe without changing
  the finite dimension. Closed immersion means Mathlib's `IsClosedImmersion`.

Dependency declarations used, with full signatures and docstrings read in their sources:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Opens` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (the morphism-convention node delegates to this).
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` (def-pc-derived-category).
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo`
  (def-sfb-relative-pseudo-coherent-complex).
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` (def-pc-derived-direct-image).
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent` (def-sfb-m-pseudo-coherent-complex).
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`
  (def-nagata-relative-affine-space).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- Restrictions use `AlgebraicGeometry.derivedPullback`, provided through the public
  imports of the recorded absolute pseudo-coherence module.

The relative-definition module publicly exposes its statement dependencies, so they are
available through that public import. The finite-type property has its own public import.
All stated proof dependencies are imported with plain imports: `Mathlib.AlgebraicGeometry.AffineScheme`
supplies `locallyOfFiniteType_iff`'s affine background, `exists_basicOpen_le_affine_inter`
and `Scheme.isBasis_affineOpens` (the finite-type equivalence itself is in the public
FiniteType module); `WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
supplies `schemeDerivedDirectImage_openRestriction`;
`Sheaf.AlgebraicGeometry.AffinePrincipalRelativePseudoCoherenceLocalization` supplies
`AlgebraicGeometry.affine_principal_relative_pseudoCoherence_localization`;
`Sheaf.AlgebraicGeometry.AffinePrincipalRelativePseudoCoherenceGluing` supplies
`AlgebraicGeometry.exists_affine_embedding_mPseudoCoherent_of_principal_cover`; and
`Sheaf.AlgebraicGeometry.AffinePolynomialEmbeddingPseudoCoherence` supplies
`AlgebraicGeometry.Scheme.isMPseudoCoherent_affine_polynomial_embedding_iff`.
The docstring records all six DAG proof steps and their prerequisites, including the
base-open restriction before principal localization.

Edge cases checked against the source and signatures: `n = 0` is included by `ℕ` and
`Fin 0`; no positivity is imposed on `m`; empty source, empty base, and empty affine
opens are allowed. The empty source admits a closed immersion into the zero-dimensional
affine space, and no nonempty cover or index family is assumed. For `E = 0`, both
pseudo-coherence conditions have zero strictly perfect approximations. Zero rings are
allowed as affine rings; choosing finite generators and a polynomial surjection works
without a nonzero-ring assumption. An arbitrary derived object, with potentially
non-quasi-coherent cohomology, remains admitted. No extra condition is attached to
the identity or to any particular embedding.

Searches executed through `msearch.py NY lem-sfb-relative-pseudocoherence-all-affine-charts`:

- LeanFinder: `Relative m pseudo coherence is equivalent to pseudo coherence of direct
  images for every affine polynomial embedding`. Eight hits, including
  `AffineTargetMorphismProperty.toProperty_apply`, `HasRingHomProperty.iff_appLE`, and
  `HasAffineProperty.iff_of_isAffine`; none states the derived-complex assertion.
- Loogle: `IsMPseudoCoherentRelativeTo, IsMPseudoCoherent`. Zero hits; unknown identifier
  `IsMPseudoCoherentRelativeTo` in the search service. This is not evidence of absence
  from the project, whose recorded definitions were read and reused.
- Mathlib grep: `[Pp]seudo.?[Cc]oher`. Zero hits.
- LeanSearch: `relative pseudo coherent complexes affine polynomial embeddings`.
  Eight hits; the relevant one is `AlgebraicGeometry.AffineSpace.SpecIso_inv_over`,
  describing the affine-space projection, not the theorem being stated. Other hits
  concern polynomial rings, spectra, and affine morphisms.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `IsMPseudoCoherentRelativeTo|relative.*[Pp]seudo|[Pp]seudo.*all.*affine` found the
  recorded scheme/ring definitions and the supporting localization, gluing, and
  invariance lemmas, but no existing all-affine-charts theorem. The ring-level
  `RelativeMPseudoCoherent` and `PolynomialPresentationPseudoCoherence` declarations
  concern algebraic complexes rather than arbitrary scheme-derived objects.
- Local `rg` for this item's exact id in `lean/WeilConjectures` returned no match.
  The item's citations in `lean/Sheaf` are proof-plan references in the downstream
  closed-support lemma, not declarations of this statement.

Validation: `scompile.py` successfully compiled the module in both sandbox and library
modes, each in 1.8 seconds, with no errors or unexpected warnings. All variables and
universes are bound explicitly; `autoImplicit false` is set. Only the one expected
stage-2 `sorry` remains. No statement faults or disputes were found.

## Second reading by NY

I reread the completed module with the node and Stacks statements open. This is an
author's second pass; the maintainer supplies the independent review.
The node's locally finite type map is exactly the `f` binder and typeclass; its arbitrary
derived object and arbitrary integer are the `E,m` binders. The left side is the
degreewise relative predicate with argument order `f m E`. The first conjunct's
right side quantifies over both opens, both affineness conditions, the image-inclusion
witness, every dimension, and every closed immersion with the correct base-projection
equation. Its output uses the same `m` and exactly the derived pushforward of the
derived open restriction of `E`. The second conjunct asserts an embedding for every
compatible pair without requiring the first conjunct's relative-pseudo-coherence
assumption; it permits the dimension and embedding to vary with that pair.
The absolute definition inspected really uses strictly perfect local approximations,
cohomology isomorphisms above `m`, and an epimorphism at `m`. The affine-space definition
inspected really is the fibre product over the terminal scheme. Neither the theorem
nor its imports introduces a replacement notion. I also checked that the six-step
docstring retains open restriction before localization, principal gluing before the
change-of-embedding argument, and affine-cover existence for the converse. No mismatch
was found and no signature or node-statement change was needed on this pass.

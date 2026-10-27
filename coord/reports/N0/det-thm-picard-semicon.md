## Worker report

The delivery states `det-thm-picard-semicon` in
`Sheaf.AlgebraicGeometry.PicardSemicontinuity`. There are two new theorems, each with proof
`by sorry`, and no new definition. The node's map clause is supplied by the existing public
`AlgebraicGeometry.Scheme.Modules.cechBaseChangeMap`, included in `lean.declarations` and
publicly imported from
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChangeMap`.
The full current blueprint statement and proof were read in
`literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-perfect/`.
The node's statement and dependency lists are unchanged.

Hypotheses and clauses:

- The objects are arbitrary `X T : Scheme.{u}` and `f : X ⟶ T`.
  `[IsProper f] [LocallyOfFinitePresentation f]` express proper and finite presentation:
  properness supplies quasi-compactness and separatedness, hence quasi-separatedness.
  No Noetherian or reduced assumption is imposed on semicontinuity.
- `F : X.Modules` is the structure-sheaf module, `[F.IsFinitePresentation]` is its finite
  presentation, and `hF : F.IsFlatOver f` is precisely the recorded affine-local flatness
  over the base. Finite presentation supplies quasi-coherence without another hypothesis.
- `q : ℤ` covers every integer. The displayed dimension function is
  `fun t : T ↦ if 0 ≤ q then F.hFiber f q.toNat t else 0`.
  The existing `hFiber` uses the scheme-theoretic fibre `f.fiber t`, pullback of `F` along
  `f.fiberι t`, and dimension over `T.residueField t`. For negative degrees the cohomology
  of a module placed in degree zero is zero; this is a conditional, not a truncation of
  negative degrees to degree zero. `UpperSemicontinuous` is the first conjunct.
- The canonical maps are the existing `cechBaseChangeMap`, not new existential maps.
  Its complete signature was read: for an affine-base pullback square `H`, a finite affine
  cover `U`, and an integer `q`, it is a linear map from
  `Γ(T', ⊤) ⊗[Γ(S, ⊤)] (cechModuleComplex f F U).homology q` to the homology of the
  pulled-back cover and sheaf. Its body is `homologyBaseChange` followed by the homology
  map of `cechModuleComplexBaseChangeIso`. Thus its element formula is exactly
  `b ⊗ [z] ↦ b • [p^*z]`, including zero and negative degrees. The tensor is written
  with the coefficient extension on the left, canonically equivalent to the displayed
  tensor in the node. No arbitrary linear map or Nonempty choice replaces this map.
- For the pointwise statement, `V : T.affineOpens` is any affine neighbourhood, and
  `t : V.1.toScheme` is its point. `Limits.pullback f V.1.ι` is its inverse image,
  `Limits.pullback.snd f V.1.ι` its structure morphism, and
  `(Scheme.Modules.pullback (Limits.pullback.fst f V.1.ι)).obj F` its restricted sheaf.
  The residue point is `V.1.toScheme.fromSpecResidueField t`. The algebra structure and
  `hg` explicitly specify scalar restriction along this morphism; they impose no extra
  geometric hypothesis, since the ring homomorphism's `toAlgebra` always supplies them.
  `U`, `hU`, and `hcover` quantify over every finite affine open cover of this inverse
  image. The intersection-affineness proof passed to the existing map is
  `isAffineOpen_iInf_of_isSeparated`. The Čech resolution identifies the source with the
  tensor of the higher direct image at the point and the target with fibre cohomology.
- The implication `IsReduced T → IsLocallyConstant (...) → ...` in
  `picard_semicontinuity` is exactly the conditional local-freeness clause.
  `SheafOfModules.IsFiniteLocallyFree.{u, u, u}` is the recorded variable-rank notion,
  applied to `(schemeModuleHigherDirectImage f q).obj F`. It does not assert one rank
  on the entire base. The following conjunct is its flatness over `𝟙 T`.
- `picard_cechBaseChange_bijective` adds `[IsReduced T] [IsLocallyNoetherian T]` and
  local constancy of the same global degree-q dimension function. Its conclusion is
  `Function.Bijective` of the very `cechBaseChangeMap` just described. For linear maps
  this is precisely being an isomorphism. Local Noetherianness is not assumed for the
  earlier conclusions, and no generization condition replaces local constancy.
- The explicitly bound `HasDerivedCategory.{w}` instances are infrastructure for the
  recorded integer-degree higher direct image, not assumptions of perfection, flatness
  of the morphism, or Noetherianness. Every type and universe is explicitly bound;
  `autoImplicit` is false. No file-local instance or notation is introduced.

Dependency declarations read and reused:

- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  `Scheme.Modules.moduleBaseChange` is tensor pullback along the canonical base-change
  map; its bundle records the fibre/projection conventions. Here the fibre products are
  Mathlib `Limits.pullback`, with `fst` and `snd` as that record specifies.
- The convention-only node `def-pc-morphism-conventions` has no declaration of its own.
  We use the specified Mathlib `IsProper`, `LocallyOfFinitePresentation`, pullbacks and
  affine opens. Their class signatures were opened in the pinned Mathlib source.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeModuleHigherDirectImage f q`, the recorded cohomology of `Rf_*` of `F[0]`, for
  integer q. This is used rather than defining a second higher-direct-image functor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation` (the node's recorded second declaration).
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver` and existing `Scheme.Modules.hFiber`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, whose rank may vary by covering member.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology`, the recorded O-module cohomology functor, is publicly
  imported. The already existing `hFiber` is used for fibre dimensions rather than
  copied: internally it uses abelian-sheaf `H`. Its identification with O-module
  cohomology is the usual injective-O-module acyclicity comparison (Stacks 01E3),
  not a claim that the two definitions are definitionally equal. This is the existing
  upstream dimension function used by the recorded semicontinuity theorem.
- The proof dependency `thm-pc-semicontinuity-base-change` is publicly reached through
  `BaseChangeMap`, which imports `Semicontinuity` through `BaseChange`. Its recorded
  `upperSemicontinuous_hFiber` and
  `exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant` were read
  with their full section variables and docstrings. They have natural-number degrees,
  whereas this item's statements retain all integer degrees and the recorded unbounded
  higher direct image.
- `Sheaf.AlgebraicGeometry.CechResolution` and
  `Sheaf.AlgebraicGeometry.BaseChangeMapCech` are proof-only imports for the two Čech
  proof dependencies. Their full signatures and docstrings were read. The latter's
  published signature has a documented defect: it does not assert the Čech term
  identifications or the comparison equation in its natural-language statement.
  This delivery does not use its unconstrained existential gamma as a substitute for
  the canonical map: the map is the concrete upstream `cechBaseChangeMap`. The future
  proof must use its actual tensor-comparison construction. The defective proof-only
  interface is reported here; it is not a statement dependency or a new definition.

Edge cases checked before and after elaboration:

- Negative q: the function is zero, integer-degree higher direct images vanish, and
  the existing Čech complex is extended by zero from natural degrees. No q>=0 binder.
- q=0 is retained, and is not replaced by a positive-degree assertion.
- Empty base and empty scheme: no point is required; local freeness of the zero sheaf
  is allowed. Neither theorem has a Nonempty hypothesis on the base or total space.
- Empty cover: `[Finite ι]` is used without `[Nonempty ι]`; a covering with empty index
  is permitted precisely for an empty inverse image, giving the zero-complex map.
- Disconnected reduced bases: local constancy and variable-rank local freeness allow
  different ranks on components. No global constant rank is asserted.
- Nonreduced bases: semicontinuity and the canonical map still exist. Local freeness
  and bijectivity keep reducedness; the blueprint's dual-number elliptic-curve line
  bundle example explains why it cannot be dropped.
- Arbitrary characteristics and arbitrary scheme universe u are allowed. Finite covers
  have index universe u, and the derived-category universe w is explicitly bound.

Searches made (results are also logged by msearch.py):

- LeanFinder, "Upper semicontinuity of fibre cohomology and Grauert base change for a
  finitely presented flat sheaf under a proper finitely presented morphism": eight hits,
  including `UniversallyOpen.of_flat`, `IsFinitePresentation` and `Flat`; none states
  the cohomological result.
- Loogle, `UpperSemicontinuous, AlgebraicGeometry.Scheme`: zero hits.
- Mathlib grep, `Grauert|[Ss]emicontinu|cechBaseChangeMap`, AlgebraicGeometry: zero hits.
- Project/source rg, the four blueprint Lean names and `semicontinuity_base_change`:
  found the actual upstream `Semicontinuity.lean` and `BaseChangeMap.lean`; their
  signatures and docstrings were read. The concrete map is reused. The nonnegative
  upstream theorems do not state the complete integer-degree item with its recorded
  derived-direct-image interface.
- Project/source rg, `det-thm-picard-semicon`: no declaration already assigned to this
  item. Searches over `lean/Sheaf` for semicontinuity, Grauert, and the displayed names
  found applications and unrelated rank/dimension results, not this combined statement.
- Full new declaration names were checked against source and Mathlib; no collisions.

Validation: the delivered module was compiled with scompile.py against the published live
build, separately as a sandbox and as its library module, with no errors or warnings.
No proofs were attempted, no live source was modified, and no global build was run.
No statement correction or new/dependency node is required. No STATEMENT-DISPUTED flag.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

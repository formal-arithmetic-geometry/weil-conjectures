## Worker report

The module `Sheaf.AlgebraicGeometry.PrescribedEnvelopeRelativeSheafDescente` states
`AlgebraicGeometry.prescribedEnvelope_relative_sheaf_descente`. Its only theorem has proof
`sorry`. All nine auxiliary definitions/structures have actual data or Prop-valued bodies;
there are no axioms, proof-valued placeholders inside definitions, or additional theorems.
All declarations are recorded in `lean.declarations`. They unpack this item's own geometric
and scalar-transpose data rather than introduce independent mathematical notions.

The mathematical statement is unchanged. `stmt_deps` gains the already-landed
`def-pc-derived-pullback-tensor-comparison`, whose K-flat characterization is used directly.
No dependency interface repair or new node is needed.

Clause-by-clause correspondence:

- The arbitrary commutative rings B and A are `B A : CommRingCat.{u}`. B is Noetherian by
  `[IsNoetherianRing B]`. The arbitrary map B -> A is `φ : B ⟶ A`.
- The prescribed envelope is `p : Y ⟶ Spec B`. `[IsSeparated p]`,
  `[LocallyOfFiniteType p]`, and `[QuasiCompact p]` express separated and finite type.
  These are the project's morphism conventions, not a projectivity assumption.
- Y_A is exactly `pullback p (Spec.map φ)`. The closed immersion is `j` with
  `[IsClosedImmersion j]`; its A-structure is `j ≫ pullback.snd p (Spec.map φ)`.
- E is `schemeDerivedCategory X`; `hE : schemeDerivedQCohProperty X E` expresses
  membership in D_QCoh. `hrel` uses the recorded `Scheme.IsPseudoCoherentRelativeTo`
  for precisely the above structure morphism. All localization choices have explicitly
  bound universes `u w` and a shared family of `HasDerivedCategory.{w}` instances.
- The integer bound is arbitrary `a : ℤ`.
- `PrescribedEnvelopeModel φ p j` packages B' (`ring`), maps `fromBase` and `toA`, and
  `factorization : fromBase ≫ toA = φ`. `finiteType` is
  `fromBase.hom.FiniteType`; `noetherian` is `IsNoetherianRing ring`.
- Its `Z` is a scheme, `k` maps into `pullback p (Spec.map fromBase)`, and `closed_k`
  states that k is a closed immersion. The definition `D.q` is k followed by the
  coefficient projection, so it is exactly the structure morphism q in the node.
- `j'` maps X into `pullback D.q (Spec.map D.toA)` and is closed by `closed_j'`.
  `comparison` is the base-changed k: `comparison_fst` and `comparison_snd` specify its
  two projections uniquely by the pullback universal property. `factor_j` says
  `j' ≫ comparison = j`, exactly k_A j' = j. This encoding avoids a separate choice
  of an iterated-pullback associativity isomorphism, and admits every geometric model
  in the node. `D.u` is j' followed by the projection to Z.
- The existential F lies in `schemeDerivedCategory D.Z`. `RingedSpace.IsCoherent` on
  every `DerivedCategory.homologyFunctor ... i` is coherent cohomology, including the
  finite-type-kernel condition in the recorded pqf definition. The two bounds `l r : ℤ`
  and `i < l ∨ r < i → IsZero ...` assert bounded cohomology.
- `γ : F ⟶ (schemeDerivedDirectImage D.u).obj E` is the required map into Ru_* E.
- `envelopeCoefficientSheaf D.toA` is literally Mathlib `tilde` on the restriction of
  the A-module A along B' -> A; `envelopeCoefficient` puts it in degree zero using
  `DerivedCategory.singleFunctor`. Thus it is the specified M, without any flatness.
- The source of `envelopeTheta` is exactly `(derivedPullback D.q).obj M ⊗ F`, using
  the global `schemeDerivedTensorMonoidal` instance.
- The ordinary evaluation `e` is not an arbitrary replacement for the scalar action.
  `EnvelopeEvaluationIsScalar` fixes its adjoint on EVERY coefficient section a of A:
  the associated-sheaf section `tilde.toOpen ... ⊤ a` maps to the image of a under the
  actual structure map X -> Spec A, using `Scheme.ΓSpecIso` and `s.appTop`.
  The composite tensor pullback adjunction is the already-pinned module adjunction.
  The global coefficient sections locally generate tilde A (localizations on basic
  opens); their images therefore determine the sheaf morphism uniquely. This is a
  characterization of the canonical evaluation, not a new assumption on the inputs.
- `envelopeSinglePullbackMap` is the shared left-derived counit on a single complex,
  transported by `quotientCompQhIso` and `singleMapHomologicalComplex`.
  `envelopeScalarAction` first uses this counit for q, pulls it back along u, uses
  the counit for u, then applies e in degree zero. Under canonical pullback composition
  this is exactly L(q o u)^* tilde A -> O_X. Crucially these counits are not inverted:
  neither A nor its maps are assumed flat.
- The existential tensor family τ is constrained by the existing
  `IsCanonicalPullbackTensorComparison D.u τ`, including its degreewise normalization
  on every pair of K-flat representatives and naturality. An unconstrained isomorphism
  or arbitrarily chosen monoidal structure would not suffice. This predicate uniquely
  determines τ; existence introduces no additional hypothesis on the theorem's inputs.
- `envelopeTheta` applies τ, tensors the scalar action with the derived-adjoint
  transpose of γ, then applies `(λ_ E).hom`; finally it applies the derived adjunction
  `homEquiv`. This is exactly the node's specified transpose and theta.
- The objects C, v and w form `Triangle.mk (envelopeTheta ...) v w ∈ distTriang ...`:
  C is a cone of this particular theta. `schemeDerivedQCohProperty D.Z C` states
  quasi-coherent cohomology; `∀ i : ℤ, a ≤ i → IsZero ...` is the requested vanishing,
  with the weak inequality including i = a. Cone uniqueness up to isomorphism makes
  this equivalent to the node's statement about the cone. No global sections occur.
- There is no Flat hypothesis on either coefficient map, no isomorphism requirement
  on j', and no altered envelope or replacement of derived tensor by ordinary tensor.

Recorded dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Scheme.ΓSpecIso`.
- Morphism convention: Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`;
  the convention node explicitly delegates to these declarations.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its two
  projections and their universal property.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `Scheme.IsPseudoCoherentRelativeTo` (full current signature and docstring read).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  `WeilConjectures.AlgebraicGeometry.Coherent` / `RingedSpace.IsCoherent`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `schemeDerivedTensorMonoidal`, the one global K-flat derived tensor instance.
- `WeilConjectures.AlgebraicGeometry.DerivedAdjoint`:
  `nonempty_derivedPullbackAdjunction`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `distTriang`, with
  `CategoryTheory.Pretriangulated.Triangle.mk` from `Triangulated.Basic`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde` and `tilde.toOpen`.
- `WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison`:
  `IsCanonicalPullbackTensorComparison`; this publicly exposes the shared
  `SingleComplexBaseChange.counit` and module pullback additivity.

Every proof dependency with a recorded Lean module is imported (plain imports except
modules already publicly imported for the statement). Unrecorded proof-only prerequisites
are not duplicated or assumed. The theorem docstring reproduces all eight proof steps.

Source reading: `literature/stacks-project/perfect.tex`, the paragraph following
`lemma-flat-proper-pseudo-coherent-direct-image-general` (Tag 0CSD). It only refers to
Kiehl for the general relative assertion, and does not state this approximation lemma.
The module and node explicitly retain its agent-formulated status and Kiehl WANTED.
The latest blueprint unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read; this prerequisite is not the unit's own six-functors statement. No source-based
correction, STATEMENT-DISPUTED flag, or mathematical weakening is made.

Edge cases checked: B = 0 and hence A = 0; empty X or Y; E = 0; identity B -> A;
B = Z and A = F_p (counits are not inverted, so the extra Tor terms survive);
A an infinite polynomial algebra (no finite-type condition on B -> A);
negative a and i = a; bounded interval possibly empty; proper closed j' rather than an
isomorphism. The comparison equations imply that the output A-structure equals the
input A-structure: compose `factor_j` with the A-projection and use `comparison_snd`.
No nonzero-ring, nonempty-scheme, projectivity, flatness or uniform rank condition appears.

Searches performed with the prescribed real msearch wrapper:

- LeanFinder: "A relatively pseudo coherent complex on a closed subscheme of a prescribed
  Noetherian scheme admits finite window approximation by derived scalar extension of a
  bounded coherent complex". Eight hits concern affine transition limits, finite-type
  module sheaves, and local cohomology; none is this derived approximation.
- Loogle: `"PseudoCoherent"`. Zero hits.
- Mathlib grep: `descente|coefficientWindow`, subdirectory `AlgebraicGeometry`. Zero hits.
- LeanSearch: "Relative pseudo coherent sheaf complex descente on a prescribed Noetherian
  finite type envelope with bounded coherent approximation and cone vanishing in large
  degrees". Eight hits concern quasi-coherent presentations and finite-type sheaves;
  none provides the approximation theorem.
- Project/source ripgrep: the item id, `prescribedEnvelope`, prescribed envelope,
  relative descente, and `CoefficientWindow`/`coefficientWindow` in `lean/Sheaf` and
  `lean/WeilConjectures`: no existing declaration of this statement. Searches of
  pullback/tensor/scalar APIs found the canonical tensor-comparison predicate and shared
  left-derived counit, which were reused rather than redefined.

Validation: scompile.py compiles this module cleanly in module mode, both as a sandbox
probe and under its intended library name. No warning remains other than the permitted
sorry warning. The full theorem was compiled with all available proof imports.

## Second reading by Q112

Self-review, not a second agent: the dispatcher expressly prohibits starting other agents;
the maintainer provides the independent review. Reopened the node and final module and
checked each item in the correspondence above. In particular checked the orientation of
both adjunctions (gamma uses inverse homEquiv; theta uses forward homEquiv), the exact
inequality i >= a, all three closed immersions, and the factorization through the prescribed
Y. Checked that the scalar section formula fixes the actual A-action, that the canonical
comparison predicate cannot be satisfied by an arbitrary map, and that the sequential
counits are retained in the nonflat case. The initial compiler probe exposed X.Modules
category-instance inference; the final helper explicitly names the shared sheaf-of-modules
category for Q. Removed all temporary #check/example probes. No statement discrepancy
remains; no node statement was changed.

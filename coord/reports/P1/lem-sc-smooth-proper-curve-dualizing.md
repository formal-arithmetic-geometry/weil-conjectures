## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing` states
`AlgebraicGeometry.smoothProperCurve_dualizing`, with proof `sorry`. No definition or proof
is added. The node's statement is unchanged. The already landed `def-pc-derived-category`
is added to `stmt_deps` to record the use of its full quasi-coherent subcategory.

The source was opened at https://stacks.math.columbia.edu/tag/0BRT, Lemma 48.15.7.
Its adjoint is on D_QCoh and its conclusion is an isomorphism in D(O_X); its dimension-one
specialization is exactly this node. The local literature copy of duality.tex is absent.

Each hypothesis and clause is represented as follows:

- A field k: `(k : Type u) [Field k]`, with no characteristic or perfection restriction.
- The morphism g:C→Spec k: `(C : Scheme.{u}) (g : C ⟶ Spec (.of k))`.
- Smooth and pure relative dimension one: `[SmoothOfRelativeDimension 1 g]`. Mathlib's
  charts are standard smooth of relative dimension one, at every point; this also implies
  `Smooth g`, so no redundant smoothness binder is included.
- Proper: `[IsProper g]`, the dependency's separated, universally closed, locally finite
  type class; universally closed supplies quasi-compactness and hence finite type.
- The derived categories: the shared `HasDerivedCategory` instances on
  `SheafOfModules.{u} (moduleRings ...)`, with independent explicit morphism universes
  `wC` and `wk`. This uses the same carrier and category instances as the recorded derived
  direct image, rather than introducing D(X.Modules) a second time.
- Rg_* on quasi-coherent complexes: the functor `R` between `schemeDerivedQCohCategory`
  objects, together with `comparison`, a natural isomorphism
  `R ⋙ ι_k ≅ ι_C ⋙ schemeDerivedDirectImage g`. Thus R is constrained to be the restriction
  of the recorded functor on every object and morphism, not an arbitrary replacement.
  This is the data needed to express the node's already assumed restriction; existence
  of such a restriction is not an additional geometric hypothesis.
- g^! as its right adjoint: `a` with `(adj : R ⊣ a)`. The node assumes the right adjoint;
  this theorem does not assert a separate existence result.
- O_Spec k in that subcategory: `O` and the isomorphism `hO` from its underlying object
  to `singleFunctor ... 0` of `SheafOfModules.unit`. This is a representative of the
  specified structure sheaf, not an arbitrary test complex. Quantification over all
  such representatives gives exactly the same statement, since functors preserve
  isomorphisms; the structure sheaf is quasi-coherent and has its canonical representative.
- Ω¹_C/k: `g.relativeDifferentials`, exactly the declaration recorded by
  `def-sc-kahler-differentials`. `singleFunctor ... 0` puts this sheaf in degree zero.
- [1]: the cohomological shift `⟦(1 : ℤ)⟧`, rather than a homological shift or twist.
- There is an isomorphism in D(O_C): `Nonempty ((a.obj O).obj ≅ ...⟦1⟧)`;
  `.obj` applies the full-subcategory inclusion on objects. No pairing, trace or chosen
  canonical isomorphism beyond the node's existential conclusion is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.SmoothOfRelativeDimension` (imported through Differentials).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohCategory` and `schemeDerivedQCohProperty` (imported through the
  direct-image module). Their full signatures and docstrings were read.

Edge cases checked before writing: no connectedness, geometric integrality, nonemptiness,
projectivity, algebraic closure or perfect-field hypothesis is imposed. Empty C is allowed
(the smooth relative dimension condition is vacuous, and the target category is zero).
Disjoint unions of smooth proper curves are allowed. Spec k itself is excluded by relative
dimension one when nonempty. The formula on P¹_k is O(-2)[1], in agreement with Serre
 duality; an elliptic curve gives O_C[1]. Positive and zero characteristic are both included.
The use of arbitrary naturally isomorphic restrictions/right adjoints and representatives
of O_k does not affect the conclusion, by uniqueness of right adjoints and preservation
of isomorphisms. No hollow definition is used or introduced.

Searches for an existing statement:

- msearch.py leanfinder: "The dualizing complex of a smooth proper curve is the sheaf of
  differentials shifted by one". Eight hits, mostly presheaf differential constructions
  and the smooth locus; no coherent derived-duality statement.
- msearch.py loogle: "AlgebraicGeometry.IsSmoothOfRelativeDimension". No hits; the old
  identifier is unknown on the service. Local source inspection found the current
  `SmoothOfRelativeDimension`, which is used.
- msearch.py grep: "dualizing|upperShriek", AlgebraicGeometry. No Mathlib hits.
- msearch.py leansearch: "smooth proper curve dualizing complex right adjoint derived
  pushforward". Service unavailable (Internal Server Error), recorded by the search tool.
- rg on WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry and Paper:
  "smooth.proper|dualizing|upperShriek|rightAdjoint|quasiCoherentDerived|IsSmoothOfRelativeDimension".
  Source has Serre duality and differential calculations, and étale dualizing complexes;
  none states this coherent dualizing-complex isomorphism. Sheaf has derived categories,
  direct images and diagonal conormal differential comparisons, reused here.
- rg for the exact node id in WeilConjectures: no hits.
- rg in dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf for
  "smoothProperCurve_dualizing|smooth.*proper.*dualiz|dualiz.*curve": no existing name
  or statement found.

Validation: remote compile and deliver2.py --no-push both failed before elaboration while loading
`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: its object file is absent from the
server's P1 last-green build. The source exists locally; no duplicate module was written.

Read-only inspection confirmed that the latest published global build was green at
2026-10-11T15:35:13Z, commit 0d4222897ffb6667cb888e7f85e6acab146213e2, but neither
lean/.lake/build/lib/lean nor local/build/P1 contains the needed object file. This is a
server dependency-build failure; the theorem has not yet been checked by Lean, and the
dry run has not printed OK. No delivery was pushed.

## Second reading by P1

Independent reading of the node, the 59-line module, all five statement-dependency
records, and their declaration sources. Verdict: the Lean says exactly what the node
says; no mathematical mismatch was found, and the Lean and node are unchanged.

Source read: Stacks `duality.tex`, `lemma-smooth-proper` (Tag 0BRT), lines
3661–3721, and the introduction of `section-examples`, lines 3279–3292.
The local literature file is absent, so the upstream TeX was downloaded to the
sandbox scratchpad from https://raw.githubusercontent.com/stacks/stacks-project/master/duality.tex.
The source assumes a Noetherian base, smooth proper relative dimension d, and a
right adjoint on D_QCoh; it concludes an isomorphism in D(O_X). For Spec k the
Noetherian assumption follows from Field k. The section introduction makes no
additional geometric hypotheses and promises no compatibility with base change
or composition. Inverting the source's isomorphism and setting d = 1 gives precisely
the node's conclusion. No statement_change, new definition node, or dependency
module occurs in this delivery, so H12/H13 and corrected-citer review do not apply.

Item-by-item list of objects, hypotheses and conclusion:

1. A field k: `(k : Type u) [Field k]`. Exact; no closure, perfection, characteristic,
   or finiteness assumption.
2. A scheme C and named structure morphism g: `(C : Scheme.{u})
   (g : C ⟶ Spec (.of k))`. Exact. Explicit g is permitted because the node names g.
3. Smoothness and pure relative dimension one: `[SmoothOfRelativeDimension 1 g]`.
   Exact: Mathlib Smooth.lean:135–147 supplies standard-smooth charts of that
   relative dimension at every point and derives Smooth g. The dependency
   def-sbc-smooth-morphisms records this very class; no extra Smooth binder needed.
4. Properness: `[IsProper g]`. Exact: Proper.lean:42 extends separated,
   universally closed and locally finite type. UniversallyClosed implies
   QuasiCompact, hence finite type, as the recorded dependency explains.
5. D(O_C), D(O_k), and their quasi-coherent full subcategories: the two
   `HasDerivedCategory` binders and `schemeDerivedQCohCategory`.
   Exact: DerivedCategory.lean:43–68 uses the existing abelian category of
   module sheaves and requires quasi-coherence of every integer cohomology sheaf.
   The binders select localization models, not additional geometric assumptions;
   independent `wC` and `wk` allow all available model universes.
6. Rg_* restricted to quasi-coherent complexes: `R` and
   `comparison : R ⋙ ι_k ≅ ι_C ⋙ schemeDerivedDirectImage g`.
   Exact, on both objects and morphisms. SchemeDerivedDirectImage.lean:40
   specializes `RingedSpace.derivedModuleDirectImage` to the underlying morphism.
   The latter is the actual unbounded rightDerivedFunctor of module direct image,
   computed by K-injective resolutions, not an unconstrained functor or private copy.
   For proper g over a field, preservation of quasi-coherence ensures such R exists.
7. The right adjoint g^!: `a` and `adj : R ⊣ a`. Exact. Both the node and source
   introduce the right adjoint as given; the statement correctly does not append
   a separate existence conclusion. Different choices are naturally isomorphic.
8. The structure sheaf O_k: `O : schemeDerivedQCohCategory (Spec (.of k))`
   and `hO : O.obj ≅ (DerivedCategory.singleFunctor ... 0).obj
   (SheafOfModules.unit ...)`. Exact: hO forces the underlying object to be
   precisely the structure sheaf in degree zero up to isomorphism. The structure
   sheaf is quasi-coherent, so this representation does not exclude the intended case.
9. The differential sheaf Ω¹_C/k: `g.relativeDifferentials` in the conclusion.
   Exact: source Differentials.lean:93 is the sheafified universal differential
   construction for arbitrary scheme morphisms. def-sc-kahler-differentials
   records this declaration and the shared diagonal-conormal comparison, so
   the node's diagonal definition is not replaced by a different notion.
10. The cohomological shift [1]: the differential sheaf is placed in degree zero
    by `DerivedCategory.singleFunctor ... 0` then shifted by `⟦(1 : ℤ)⟧`.
    Exact; this is the derived category's cohomological shift, not a tensor twist.
11. Existence of an isomorphism in D(O_C):
    `Nonempty ((a.obj O).obj ≅ ...⟦(1 : ℤ)⟧)`. Exact; `.obj` is the underlying
    object of the full subcategory. No extra trace, pairing, specified map or
    compatibility is asserted. Quantifier order is field, curve/morphism,
    geometric properties, category models, restricted pushforward, its adjoint,
    representative of O_k, then the isomorphism conclusion. Representation
    choices with comparison and hO merely transport the node's objects.

Edge cases: the empty scheme is admitted (pointwise smoothness vacuous, proper
empty morphism); its derived category has only zero objects up to isomorphism,
so both sides are zero. Disconnected smooth proper curves are admitted without
connectedness, integrality, projectivity or rational points. Zero complexes are
not incorrectly quantified as replacements for O_k: hO fixes that input; on an
empty curve the output can be zero. There is no index set or free integer n in
this node: dimension is fixed at one, so the dimension-zero nonempty scheme
Spec k is correctly outside the hypotheses. All characteristics, including
imperfect positive-characteristic fields, are admitted. P¹_k gives O(-2)[1],
and an elliptic curve gives O_C[1]. Arbitrary u and independent derived model
universes are bound explicitly. A scheme and a field initially in different
universes can be placed in a common larger universe; no countability or
small-index restriction occurs.

Independent H4 searches, using different language from the first reader:

- msearch.py leanfinder: "Serre duality identifies the right adjoint applied to
  the structure sheaf with differential forms shifted by relative dimension".
  Eight hits: ordinary module pullback/pushforward and restriction adjunctions;
  their displayed signatures are underived, not the right adjoint of Rg_*.
- msearch.py loogle: `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.
  No hits (service reports unknown identifier). Local source inspection found
  and checked the recorded declaration in Differentials.lean, rather than
  treating the service's index as evidence that the notion is absent.
- msearch.py grep: `canonical|dualizing|Serre`. Its 25 reported hits concern
  unrelated canonical maps and Serre modular-form results; none is this statement.
- Direct rg of Mathlib/AlgebraicGeometry: `dualizing|relative.*duality`.
  No hits. Direct rg of source WeilConjectures/AlgebraicGeometry and the project's
  lean/Sheaf/AlgebraicGeometry: `dualizing complex|smooth.*proper|canonical.*complex|shriek`.
  Hits are curve geometry and etale shriek material, not coherent derived duality.
  The project's existing shared DerivedCategory and SchemeDerivedDirectImage
  modules are correctly reused. Existing Serre-duality and finite-trace statements
  do not state this unbounded derived-category isomorphism.

H5/H6/H8/H9 checks: no new definitions, no hidden data holes, no private notions,
file-local notation or local instances. The sole proof is `sorry`. Both docstrings
carry the source and blueprint id; the theorem docstring carries both node proof
steps (general relative duality specialized to Spec k/d=1, then wedge¹ and shift
identifications). All imports are used, and no line exceeds 100 characters.
All variables and universes are bound; the node's lean.statement equals the
file signature verbatim.

Changes by this second reading: this independent review section and validation
record only. The first reader's missing-dependency build failure has resolved:
scompile.py compiled the unchanged module successfully in 2.6 seconds, exit 0,
with no errors or warnings. No duplicate dependency was added to bypass it.

Delivery validation: deliver2.py --no-push prints OK; commit e999a8384 passes
preflight and compiles. The exact-signature and 100-character line checks pass.

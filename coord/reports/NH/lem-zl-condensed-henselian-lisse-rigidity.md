## Worker report

Item: `lem-zl-condensed-henselian-lisse-rigidity`, stage 2, group NH, 2026-10-18.

The delivery is `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity`. Its primary
statement is
`AlgebraicGeometry.ProEtale.CondensedRing.henselian_lisse_rigidity`, with one `sorry`.
The same node owns the coefficient/pullback comparison constructions listed in
`lean.declarations`. Scalar realization is imported from the landed definition node
`def-zl-condensed-scalar-realization`; its construction is not repeated here. The
remaining data are existing functors and canonical natural isomorphisms.

I read the node, its statement dependencies and their recorded interfaces, the stage-2
brief and H-rules, the example CompactObject module/record, and the pro-etale framework
note. I checked Hemo--Richarz--Scholbach, *Constructible sheaves on schemes*, Section 3,
Proposition 4.3 and Corollary 4.4(1)--(2), from the repository PDF with pdftotext. The six
DAG proof steps are included in full in the theorem's docstring. The prior worker's
message confused the stage-1 split review with a stage-2 Lean binding: the shared node
has a split review but no `lean` field. This delivery supplies that missing binding.
No statement correction is necessary, and there is no STATEMENT-DISPUTED flag.

Hypothesis and clause correspondence:

1. Arbitrary commutative condensed ring: the variable
   `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with `[MonObj Λ]` and
   `[IsCommMonObj Λ]`, is the existing internal ring encoding. There is no assumption
   that Λ comes from a topological ring, is discrete, is solid, or is adically complete.
   This is the general ring-object presentation in the coefficient dependency's
   published ModuleObject.Basic framework, not a copy of the continuous-ring construction.
2. Small pro-etale site and pulled-back ring: every scheme category is
   `Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}` and its ring is the recorded
   `condensedRingObj Λ X = (upperStarFromPoint X).obj Λ`.
3. Ordinary unbounded derived module category: the expressions are exactly
   `DerivedCategory (Mod (Sheaf ...) (condensedRingObj Λ X))` from the published
   module-object framework. The recorded `sectionModuleEquivalence` identifies these
   internal modules with `ringedSiteModules` over the reconstructed commutative ring
   sheaf, preserving the underlying sheaves and section groups. The scalar construction
   explicitly uses this existing equivalence in the other direction. This is the
   standard module-sheaf encoding, with no replacement abelian structure, restricted
   subcategory, completion, or boundedness hypothesis.
4. Ordinary derived tensor and unit: the module imports the framework's Derived.Tensor;
   the ambient monoidal instance is `Mod.derivedMonoidalCategory`, the K-flat-derived
   relative tensor with the regular coefficient module in degree zero as its unit.
   `condensedDerivedBraiding` is a direct application of the existing
   `DerivedMonoidal.braiding` to `DerivedCategory.Qh` and quasi-isomorphisms. It uses the
   same tensor as the dualizable predicate, not a separately chosen monoidal category.
5. Lisse objects: `ObjectProperty.FullSubcategory (IsDualizable (C := ...))`.
   The published `IsDualizable` is nonempty right-dual data with evaluation,
   coevaluation and both triangle identities. In the symmetric derived category this
   is the node's dualizability. No perfect/local-system/heart condition replaces it.
   The node's analogous profinite-site notation explains its proof; there is no
   additional conclusion or hypothesis about an independent profinite set to quantify
   in this affine henselian-rigidity statement.
6. Ring and henselian ideal: `(A : Type u) [CommRing A] (I : Ideal A)
   [HenselianRing A I]`. This is the henselian-pair declaration listed in the dependency,
   including `I ≤ Jacobson(0)`; no local, nonzero, noetherian or characteristic hypothesis
   is added. Its root-lifting formulation is equivalent to the dependency's idempotent
   formulation, as the dependency record documents.
7. The affine pair and its canonical closed immersion: `Spec (.of A)`,
   `Spec (.of (A ⧸ I))`, and
   `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`. No arbitrary scheme map or
   alternative quotient identification is supplied by a hypothesis.
8. Component homeomorphism: the first conjunct is
   `IsHomeomorph (PrimeSpectrum.continuous_comap
   (Ideal.Quotient.mk I)).connectedComponentsMap`.
   This is precisely the component map of that immersion with the quotient topologies;
   the assertion is unconditional on w-contractibility.
9. W-contractibility: the second conjunct is
   `IsWContractibleRing A ↔ IsWContractibleRing (A ⧸ I)`, using the exact recorded class.
   Its inherited w-strict-locality and extremal disconnectedness are not replaced by
   affine acyclicity or a strictly local hypothesis.
10. Under these equivalent conditions: the last conjunct has antecedent
    `IsWContractibleRing A`. The preceding iff supplies the equivalent condition for A/I.
11. Exactness: the actual coefficient pullback's `.mapDerivedCategory.IsTriangulated`
    is stated. The functor is levelwise derivation of the existing exact module inverse
    image `upperStar Λ i`; its existing shift structure is used.
12. Symmetric monoidality: there exists `m` of type
    `(upperStar Λ i).mapDerivedCategory.Monoidal`, with the displayed braiding square
    for every ambient pair K,L. This includes invertible unit/tensor comparisons and
    their coherence laws through `Functor.Monoidal`. The square uses the fixed
    derived Koszul braidings in source and target, explicitly, with `m.toLaxMonoidal`.
    The underlying functor and the coefficient map are fixed beforehand, not existential
    functor parameters.
13. The lisse equivalence: `∃ e : FullSubcategory IsDualizable ≌
    FullSubcategory IsDualizable`, with
    `Nonempty (e.functor ⋙ ObjectProperty.ι _ ≅
    ObjectProperty.ι _ ⋙ (upperStar Λ i).mapDerivedCategory)`.
    Thus it is the specified inverse image on underlying objects AND morphisms.
    The isomorphism to a functor landing in the target full subcategory also asserts
    preservation of dualizability; IsDualizable is invariant under isomorphism.
14. Full faithfulness on morphisms between dualizables is included by this formulation:
    both inclusions are fully faithful, e is an equivalence, and the displayed natural
    isomorphism identifies the actual inverse-image maps with conjugates of e's maps.
    Consequently each such Hom map is bijective. This clause requires no extra choice
    of a restriction functor or independent assertion about unrelated morphisms.
15. Canonical coefficient identification: `upperStar Λ i` is, by its published
    definition, `mapMod(i*)` followed by `Mod.extendScalars (condensedPullbackHom Λ i)`.
    That coefficient morphism is the component at Λ of `upperStarFromPointComp i`.
    `fromCondensedPullbackIso` explicitly uses precisely this natural transformation,
    `mapModCompIso`, `extendScalarsIsoComapInv`, and the unit of the corresponding
    restriction-of-scalars equivalence. Its derived counterpart is obtained with
    `mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`. No coefficient
    identification or comparison is supplied as an arbitrary hypothesis.
16. Scalar extension of constant discrete complexes uses the landed
    `AlgebraicGeometry.ProEtale.condensedScalarRealization` from
    `Sheaf.AlgebraicGeometry.CondensedScalarRealization`. Its scalar ring is
    `condensedScalarRing Λ = Γ(*,Λ)` and its coefficient map is the canonical
    `condensedScalarMap Λ`, the constant-sheaf adjunction counit. The definition
    already composes the constant realization, universal derived scalar extension,
    section-module inverse equivalence and point pullback; none is copied here.
    `discreteScalarExtensionPullbackIso Λ f` has precisely the signature
    `condensedScalarRealization Λ Y ⋙ (upperStar Λ f).mapDerivedCategory ≅
    condensedScalarRealization Λ X`. Its data are three associators and nested
    `Functor.isoWhiskerLeft` of `derivedFromCondensedPullbackIso Λ f`, exposing the
    final point-pullback factor of the existing composite. Specializing to i gives
    the final clause for every unbounded discrete scalar complex, including
    identities and zero coefficients, with no flatness or finiteness assumption.
    This helper has only universe u and no auxiliary localization hypotheses.

Dependency declarations read and used:

- `sk-def-sfb-condensed-ring`: `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`
  and its public imports provide the project's coherent-Profinite/Ab coefficient
  encoding. The theorem uses arbitrary internal commutative ring objects, not its
  continuous coefficient specialization.
- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-weil-pbc-proetale-site`: Mathlib `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`,
  `condensedRingObj`, `upperStarFromPoint`, `upperStarFromPointComp`.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: Mathlib `DerivedCategory` and Q/Qh.
- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian`, reexporting `HenselianRing`.
- `sk-def-pe-wlocal`: `WeilConjectures.RingTheory.ProEtale.WContractible`,
  `IsWContractibleRing` and its inherited w-local hierarchy.
- `lem-pe-spectral-components-profinite`:
  `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`,
  `spectralSpace_connectedComponents_profinite` (also a proof dependency).
- `def-sfb-site-derived-constant-module-functor`:
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`,
  `realizationRing`, `realizationModules`,
  `commutativeSiteDerivedConstantModuleFunctor`.
- Added, already landed `def-weil-pbc-internal-abelian-sheaf-module-equivalence`:
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `InternalAbelianSheafModule.sectionRingSheaf` and `sectionModuleEquivalence`.
- Added, already landed `def-zl-condensed-scalar-realization`:
  `Sheaf.AlgebraicGeometry.CondensedScalarRealization`,
  `AlgebraicGeometry.ProEtale.condensedScalarRing`, `condensedScalarMap`,
  `condensedScalarRealization`. Its universal derived model is owned by that node;
  this item no longer has `lem-pur-derived-change-of-rings` as a statement dependency.
- The point exactness instances unfold `upperStarFromPoint` and `pointUpperStar`.
  Finite-limit preservation follows by instance inference. Finite-colimit
  preservation uses `pointUpperStarLowerStarAdjunction.isLeftAdjoint` and instance
  inference. No conjunct of `profinite_point_pullback` is used, so that theorem
  is also removed from the statement dependencies and imports.

Additional proof imports use the recorded spectral component result and
`WeilConjectures.Topology.SpectralSpace.ConnectedComponent`. The Mathlib affine
clopen/idempotent leaf is in the imported algebraic-geometry hierarchy. The three
not-yet-stated proof-only nodes (henselian w-strict-local invariance, w-contractible
lisse evaluation, and lisse pro-etale locality) have no Lean modules to import;
none is needed to type the theorem. Their precise role remains in its docstring.
No prerequisite is replaced by a stronger assumption.

Edge cases checked against the source and signatures:

- I = 0: i is the canonical identity up to the quotient identification; the component
  map is a homeomorphism and the induced lisse equivalence is the ordinary identity
  pullback. The scalar construction retains the canonical identity comparison.
- A = 0: both spectra and component spaces are empty. The module/sheaf categories
  over the empty site have only the zero object, and the lisse equivalence remains
  valid; no nontriviality or inhabitedness was introduced.
- I = A: the henselian Jacobson condition forces A = 0, reducing to that case.
- A henselian local ring with separably closed residue field, including k[[t]] with
  I = (t), gives the usual strictly henselian situation; arbitrary characteristic
  is allowed. A henselian pair such as (Z_p,(p)) need not be w-contractible: its
  first two conclusions remain unconditional, and the lisse-equivalence clause
  has precisely the stated w-contractibility antecedent.
- Zero Λ is allowed. Dualizability includes the zero object, evaluation and
  coevaluation obey both triangles, and no finite/nonzero-rank hypothesis appears.
- Arbitrarily unbounded complexes and arbitrary discrete R-modules are allowed.
  The site has object universe u+1, arrow universe u, and abelian coefficients u+1;
  no accidental equality with a scalar-derived localization universe is imposed.

Searches made (besides reading all recorded dependencies):

- `msearch.py NH <item> leanfinder` with
  "Inverse image for henselian closed immersions of weakly contractible affine schemes
  is an equivalence on dualizable derived condensed module sheaves": eight general
  LightCondensed/Condensed discrete-module hits; none concerns henselian pullback.
- `msearch.py ... loogle "IsWContractibleRing, HenselianRing"`: zero hits; the first
  identifier is project-specific and not in the Mathlib index. Repeated with the
  valid query `HenselianRing`: six hits, the class, its constructor/root-lifting and
  Jacobson fields, the maximal-ideal instance and the adic-completeness instance;
  no rigidity theorem.
- `msearch.py ... grep
  "(henselian|Henselian).*(dualizab|lisse)|(dualizab|lisse).*(henselian|Henselian)"`:
  zero Mathlib hits.
- `rg` of the same semantic patterns in the named upstream and side-project Lean
  trees found no theorem matching this one. The exact item id had no upstream match.
- Exact declaration-name searches for `henselian_lisse_rigidity`,
  `derivedFromCondensed`, `fromCondensedPullbackIso`, `condensedDerivedBraiding`
  and the point mapMod pattern in Mathlib/upstream names and the side project found
  no collision or existing general comparison. Existing specialized uses of
  `(upperStarFromPoint X).mapMod Λ` in finite-constant-model and Nakayama modules
  were inspected; they are not this theorem or a competing scalar construction.
- Current server source was read with `scompile.py --source` for side-only/stale
  interfaces, especially InternalAbelianSheafModuleEquivalence; local absence
  was not treated as a missing dependency.

The item's `lean` field and `stmt_deps` are updated as explicitly requested by the
return: drop `lem-pur-derived-change-of-rings` and
`lem-weil-pbc-profinite-point-pullback`; gain the already landed
`def-zl-condensed-scalar-realization`. There are no new nodes, dependency modules,
statement corrections or changes to the statement, proof or proof dependencies.
All nine remaining declarations are listed in the node's `lean.declarations`.

## Repair of H4 return

The saved packet was inspected first and its initial `deliver2.py --no-push` passed
mechanical preflight and compilation (dry-run commit 20fae97f2c). The substantive H4
self-check still found the duplicates identified in the immutable-head review.

1. Deleted `condensedDiscreteScalarRing`, `condensedDiscreteScalarMap`,
   `discreteScalarExtensionAtPoint`, `discreteScalarExtension`,
   `condensedSectionModules` and `condensedSectionModuleInverse_additive`.
   The landed scalar-definition module was opened in full and is now imported.
2. Replaced the two point exactness proofs with inference from the framework
   definitions and the point adjunction. Removed the two theorem imports and
   statement dependencies specified by the return.
3. Restated `discreteScalarExtensionPullbackIso` using exactly the existing
   `condensedScalarRealization` at Y and X. The comparison is the nested whiskering
   of `derivedFromCondensedPullbackIso`, with reassociation of the three preceding
   factors. No arbitrary isomorphism or replacement scalar realization is introduced.
4. Added `def-zl-condensed-scalar-realization` to `stmt_deps`, pruned the six deleted
   declarations from `lean.declarations`, and updated the clause correspondence and
   dependencies above. The main theorem signature and its six-step proof docstring
   are unchanged from the reviewed delivery.

## Second reading by NH

Repair self-check with the saved node, current shared node, landed scalar module
and revised Lean file open: the only saved/base differences before repair were
`lean` and `stmt_deps`; no unrelated stale fields needed rebasing. I rechecked the
actual signature's arbitrary commutative Λ and henselian pair binders; the direction
of the connected-component map; the unconditional w-contractibility iff; the
w-contractibility antecedent on the triangulated, symmetric monoidal functor and
lisse equivalence; and the natural isomorphism tying the equivalence to upperStar.
They are unchanged. The scalar clause now refers to the landed construction and
retains the same canonical coefficient map, arbitrary f and all discrete complexes.
The first repaired compile identified the composite's right association and a
letI style warning; nested associators and `let` corrected those diagnostics.
No independent reader is claimed here; the maintainer supplies the independent review.

Validation: repaired scompile.py passed both the sandbox and installed-path checks
(29.3 and 33.4 seconds), without errors or warnings. The final deliver2.py --no-push
dry run passed server preflight and compilation (dry-run commit 77b4c66734).

## Maintainer review fix (cc reviewer, 2026-10-18)

The delivered module stated the symmetric-monoidal clause as `∃ m : F.Monoidal` with a hand-written
braiding square over `condensedDerivedBraiding := DerivedMonoidal.braiding Qh quasiIso`. Elaborating
`DerivedMonoidal` at the concrete module category makes the kernel compare two elaborations of the
derived monoidal structure. That cost 19.5 s for the braiding definition and 38 s of elaboration plus
58 s of kernel time for the square, and the file timed out at 60 s in landing twice (heads 0bb989266f2f
and 86ed03158fe3). The fix states the clause as
`Nonempty (@Functor.Braided _ _ _ (DerivedCategory.braidedCategory _) _ _ _ (DerivedCategory.braidedCategory _) F)`,
using the published general braiding `DerivedCategory.braidedCategory` (whose `braiding` field is
`DerivedMonoidal.braiding Qh quasiIso`). It drops `condensedDerivedBraiding`. `Functor.Braided` is
exactly a `Functor.Monoidal` structure satisfying the same square. In Lean, `condensedDerivedBraiding Λ X K L = β_ K L` holds by `rfl`. The delivered and the fixed theorem statements were proved equivalent in a scratch file
(`braided_iff`, `stmt_iff`). No other clause, hypothesis, docstring proof step or dependency changed.
Item 12 of the worker report above therefore describes the earlier, equivalent formulation.
Compile: nt_compile.py 21.0 s at load 127, rc 0, no messages.


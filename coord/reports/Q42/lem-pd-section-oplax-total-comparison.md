## Worker report

The module `Sheaf.Paper.SectionOplaxTotalComparison` states the actual internal total
oplax comparison under the fixed section equivalence. Its only postponed proof is
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_oplax_total_comparison`.
The helper data are in `Sheaf.Paper.SectionTotalOplaxComparisonData`, applications
of existing constructions with no new choices.

Hypotheses and objects:
- Arbitrary commutative condensed coefficients are the explicit `Λ : Sheaf
  (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]`.
  This is the unbundled form of `Profinite.CondensedRing`.
- `X Y : Scheme.{u}` and `f : X ⟶ Y` are unrestricted. `modules`, `internalModules`,
  `ring`, `equivalence`, `pullback`, and `pullComparison` are the existing aliases
  from `Sheaf.Paper.SectionModuleOperationsData`. They use the small pro-etale site
  with object universe u+1, Hom universe u and module universe u+1.
- `HasDerivedCategory.{u+1} (modules Λ X)` fixes the localization size, as allowed
  by def-weil-abstract-derived-category. No equality between site universes is added.
- Every complex binder is `CochainComplex ... ℤ`, with no flatness or boundedness.
  The flat-term K-flat subcategories introduced in the node are contextual, not
  hypotheses on these complexes. Their existing definitions are publicly imported.

Clause correspondence (conjunct order in `SectionTotalNormalization`):
1. The hom of `conjugatedInternalTotalIso` equals the hom of `sectionTotalIso`.
   The former is explicitly the image of the actual internal arrow, conjugated
   by `totalComparison`, `termwisePullComparison` and their inverses on both sides.
2. Their inverse chain maps agree under the identical comparisons.
3. On each p+q=n summand, the section total restricts to the specified ordinary
   `normalizationSectionTensor`, followed by the target injection.
4. The inverse restricts to the inverse ordinary map followed by the image of
   the source injection. This is exactly the `tensorPullbackTotal` construction
   used by `CategoryTheory.CochainPullback.comparison` in the recorded cochain node.
5. On the actual total summand p+q=n, the image under internal pullback of the
   source injection followed by `(actualInternalTotalIso Λ f P Q).hom.f n`
   sends the scalar generator to the target injection of the pure tensor with
   scalars s and 1.
6. The target injection followed by the actual inverse total component sends
   the two scalar generators with s,t to the image of the source injection
   applied to the scalar generator with s*t. Both quantify over all source-site
   inverse-image sections, all p,q,n and every h:p+q=n.
7. The conjugated internal total unit equals the total ringed scalar unit.
8. Its degree-zero formula is s * alpha(r); all other degrees are those of the
   actual single complex and hence zero maps by construction.
9. The section comparison is natural in both arbitrary complex arguments.
10. The associator diagram is the usual signed-cochain associator diagram.
11–12. Both usual cochain unitor diagrams commute with the specified total unit.

`TotalMapAgreement` spells out equality as chain maps and equality of the images
under `HomotopyCategory.quotient` and `DerivedCategory.Q`. Thus tensor, inverse,
unit, naturality and constraints are also the specified localized equalities.
Both inverse equations are retained by the actual `Iso` values, not new assumptions:
`hom_inv_id` and `inv_hom_id` hold as chain-map equations and localize functorially.
The localized isomorphism is exactly `DerivedCategory.Q.mapIso (sectionTotalIso ...)`.
The differential is the existing signed total `P ⊗ Q`, equivalently
`CochainComplex.mapBifunctor P Q (curriedTensor _)`; the existing theorem
`CochainComplex.ιTensorObj_d` gives d_P tensor 1 + (-1)^p 1 tensor d_Q.
No bounded tensor or product total is used.

Dependency declarations read and reused:
- `Sheaf.Paper.ProEtaleSectionModuleFunctors`: `ordinaryTensorComparison`,
  `totalComparison`, `ordinaryUnitComparison`, `pullOplax`, `pullMonoidal`, and
  its additive/colimit instances. These are uniquely normalized existing maps.
- `Sheaf.Paper.SectionOrdinaryOplaxNormalization`: `normalizationInternalTensor`,
  `normalizationInternalTensorInv`, `normalizationInternalUnit`,
  `normalizationSectionTensor`, `normalizationSectionUnit`,
  `normalizationInverseImage`, `normalizationScalarTensor`,
  `normalizationInverseImageTensor`. The new definition node
  `def-pd-ordinary-pullback-balanced-generators` owns these eight plain
  definitions by an existing:true binding. The ordinary normalization theorem
  is a proof dependency only. The internal monoidal structure and section
  `pullOplax` are used through `def-pd-proetale-section-module-functors`.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`, with its
  `comparison` defined as the inverse of the normalized inverse total map.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionModuleEquivalence`; this is used through the recorded operation aliases.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `condensedPullbackHom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; `FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`; these remain context and do not restrict inputs.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedHom` and its relative derived tensor context.
- `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`:
  `Functor.mapCochainComplexμIso`, whose inverse is the actual summed oplax arrow.
  Its underlying `mapBifunctorComparisonX` is `Cofan.IsColimit.desc` on the
  preserved original coproduct, so the left-adjoint comparison is canonical.
- `Mathlib.Algebra.Homology.Additive`: `NatIso.mapHomologicalComplex`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory.Q`, `Qh`.
- `Mathlib.CategoryTheory.Adjunction.Limits`:
  `Adjunction.leftAdjoint_preservesColimits`, equivalence preservation declarations.

Edge cases checked: the identity morphism, zero coefficients, zero complexes,
complexes concentrated in degree zero, negative degrees and nonzero terms in all
integer degrees. All injections range over the entire p+q=n index with no finite
support hypothesis on the complexes. Empty schemes are allowed; no geometric
nonemptiness, quasi-compactness or finite-type hypotheses were added.

Searches (all via the prescribed msearch wrapper, plus source rg):
- LeanFinder: “Identify the actual internal module pullback oplax tensor arrow on
  signed unbounded total complexes under the section module equivalence”. Eight
  hits, including `HomologicalComplex.ιTensorObj`, `tensorHom`, `tensorObj` and
  `HasTensor`; no statement identifying the specified internal/section arrows.
- Loogle: `HomologicalComplex.mapBifunctor, Functor.OplaxMonoidal`: no hits
  (the service reports the abbreviated OplaxMonoidal name unknown).
- Mathlib grep `mapBifunctorComparison|mapCochainComplex_δ|oplaxMonoidal` in
  Algebra/Homology: no hits. Source rg found the upstream total-comparison API
  under WeilConjectures/Mathlib/Algebra/Homology and the existing cochain monoidal
  functor in WeilConjectures/Algebra/Homology/Monoidal/MapHomologicalComplex.
- LeanSearch: “An additive monoidal left adjoint on cochain complexes preserves
  the signed direct sum tensor comparison and its inverse”: eight generic hits,
  including left-adjoint additivity and the formula for the unit inverse.
- rg of WeilConjectures and Sheaf for the item id and the proposed comparison
  names: no existing statement. The downstream SectionDerivedTensorNormalization
  docstring describes this proof step but does not state this chain-map result.

Sources opened: sites-cohomology.tex lemma-pullback-tensor-product (07A4), its
full proof and displayed total arrow; sites-modules.tex lemma-tensor-product-pullback
(03EL), full statement and proof. No statement dispute or correction is required.

## Second reading by Q42

Self-review only: the dispatch explicitly forbids starting other agents. The
maintainer supplies the independent reading after delivery. Read the node and file
clause by clause. Replaced implicit cochain unit objects with explicit categories;
retained arbitrary source-site inverse-image sections; fixed missing scoped ring
object instances. The inverse and both units use existing canonical constructions.
The return identified that the plain generator definitions needed definition-node
ownership. The new definition node supplies that ownership without moving or
copying any landed declaration. No dependency module is changed.


## New nodes

`def-pd-section-total-oplax-comparison-data` owns the termwise functors,
canonical internal and section total comparison isomorphisms, the fixed tensor
conjugation, and degree-zero units and their fixed conjugation. Its module is
`Sheaf.Paper.SectionTotalOplaxComparisonData`. These are full definitions using
existing `mapBifunctorComparison`, the fixed `totalComparison`, and single-complex
functors. The explicit tensor-structure aliases retain the existing structures.
Source: Stacks 07A4, displayed total comparison, with constituents from 03EL.
The LeanSearch and LeanFinder query “canonical signed direct sum total oplax
tensor comparison for pullback of sheaf modules and its section equivalence
conjugation” returned generic sheaf pullback and direct-sum declarations; Mathlib
grep `mapCochainComplexμIso|conjugatedInternalTotalIso|sectionTotalIso` returned
zero. Source rg of Sheaf and WeilConjectures and DAG search found no specialized
comparison declaration or owner. Blueprint search “total oplax comparison” found
zero nodes. No postponed theorem is introduced in this definition module.

`def-pd-ordinary-pullback-balanced-generators` defines the actual inverse-image
module, its balanced tensor generator, the scalar-extension generator, and names
the specified internal tensor/inverse/unit and section tensor/unit maps. It uses
`existing: true` with the eight plain defs/abbrevs already in
`Sheaf.Paper.SectionOrdinaryOplaxNormalization`. It asserts no equations and uses
no theorem choice. Source: Modules on Sites 03D7, 03EK, 03EL; the displayed total
of Cohomology on Sites 07A4 uses these ordinary constituents. The definition nodes
`def-pd-section-module-operations-data` and
`def-pd-proetale-section-module-functors` supply its operations and structures.

Searches run for this ownership node on 2026-10-23:
- LeanSearch: "local balanced generators for inverse image and scalar extension
  of modules on a ringed site" returned eight results: LocalGeneratorsData and
  PresheafOfModules.pullback, not these specialized pure-tensor operations.
- LeanFinder: "inverse image of modules followed by extension of scalars local
  balanced pure tensor generator" returned eight algebraic localization and
  scalar-extension results, without this pro-etale construction.
- Mathlib grep: `normalizationInverseImage|normalizationScalarTensor|extendπ`
  returned zero hits. Source rg of WeilConjectures found no matching specialized
  names; source rg of Sheaf found the exact plain definitions in the landed
  ordinary normalization module, which are reused rather than copied.
- DAG rg for the generator names found only the ordinary theorem node, not a
  definition node. `blueprint_refs.py search 'balanced generators'` found
  def-wf-tensor-product, whose statement uses tensor and does not define this
  inverse-image/scalar-extension interface. The item's blueprint ancestor is
  None, so the new node retains that null ancestor and the full seeded via path.

## Repair of returned head 2edcd24ad58c

H2: replaced the added theorem statement dependency
`lem-pd-section-ordinary-oplax-normalization` with the new definition node above.
The ordinary theorem remains in the unchanged proof/proof_deps. The eight data
are ordinary defs/abbrevs, not objects extracted from the theorem. Its landed
module is public-imported for those existing definitions, with no source move.
The existing definition dependencies supply both `pullOplax` and the internal
`CondensedRing.monoidal_upperStar` structure.

Advisory: conjuncts 5 and 6 now state the forward and inverse local formulas
on the actual total summand, explicitly including the source and target coproduct
injections and `(actualInternalTotalIso Λ f P Q).hom.f n` / `.inv.f n`.
Conjunct 8 applies `(actualInternalTotalUnit Λ f).f 0` to the scalar unit generator.
Thus all three clauses refer to total components.

The section comparison b is represented by `asIso (mapBifunctorComparison ...)`
for the specified section pullback, the same isomorphism as
`mapCochainComplexμIso.symm`. This is the same construction as the RingedPullback
comparison: its forward map is the canonical preserved-coproduct comparison
followed by the specified ordinary oplax map on each summand; its inverse is
the sum of the ordinary lax inverse maps. The upstream
`ιTensorObj_mapCochainComplexμIso_hom_f` gives that inverse restriction, while
`CochainPullback.comparison` is defined as the inverse of `tensorPullbackTotal`
with those same constituents. Coproduct uniqueness and uniqueness of inverses
identify them. Thus this representation neither chooses a new comparison nor
assumes a new coherence property.

Self-check of the repair: read the new node against all eight existing
signatures and definitions; its scalar generator is literally `Mod.extendπ`
applied after the ambient pure tensor. The item keeps every original hypothesis,
its statement, source and split proof; only its allowed Lean record and added
definition statement dependency change. The total-summand and local formulas still
allow identity maps, empty schemes, zero coefficients, and arbitrary integer
p,q,n with p+q=n, including infinite degreewise sums.


## Compile repair and total comparison definition owner

The saved one-file packet timed out in the required first dry run. The canonical
comparison data are now in `Sheaf.Paper.SectionTotalOplaxComparisonData`, owned by
`def-pd-section-total-oplax-comparison-data`; the item imports that module. This
separates data elaboration from the proposition without changing the maps or
hypotheses. The compact ordinary, graded and cochain instance aliases reuse the original
instances. Tests with altered reducibility were discarded after typeclass failures.
The internal and section isomorphisms use `mapBifunctorComparison` directly, which
is the forward arrow of the previously used `mapCochainComplexμIso.symm`. Thus the
comparison is still the canonical preserved-coproduct comparison.

Under **New nodes**, this additional definition node owns the existing termwise
functors, fixed operation comparison, actual internal and section total isomorphisms,
their fixed tensor conjugation, and the degree-zero units and unit conjugation. Its
source is the displayed total of Stacks 07A4 with constituents from 03EL. Searches
via msearch LeanSearch, LeanFinder and Mathlib grep for the canonical total and
conjugation found generic pullback/direct-sum declarations but no specialized owner.
Source rg in Sheaf and WeilConjectures and DAG search found no existing specialized
comparison declaration or node. Blueprint search `total oplax comparison` gave zero
nodes. The three actual service search records are in its mathlib_searches.

Self-review: the new node supplies data only, with no new postponed theorem. Its
conjugation lists the same five tensor transports and four unit transports as the
item. Both comparisons retain the full signed coproduct and arbitrary unbounded
complex arguments. The generator-owner repair remains unchanged.

The final local formulas address the advisory directly. The tensor-data aliases
`totalInternalMonoidalStruct` and `totalSectionMonoidalStruct` are exactly the
parent fields of the existing cochain monoidal instances, with priority 3000.
They add no structure or hypothesis. The statement and its source remain unchanged.

Final second reading: the generator node owns exactly the eight existing ordinary
definitions; the added total-data node owns the termwise functors and specified
comparisons, with no theorem choices. The item cites both definition nodes and
uses ordinary normalization only through proof_deps. Conjuncts 5 and 6 are now
formulas on the actual total hom/inverse restricted by the appropriate injection.
Conjunct 8 is the actual total unit in degree zero. The fixed conjugations, both
Iso inverses, signed totals, unrestricted complexes and HasDerivedCategory size
are retained. No statement correction or additional mathematical hypothesis is used.


## Repair of returned head bea2e48ea8ad

The required initial dry run of the retained packet passed at 74c85f1653d, but
the independently reported name collision was still present. Read the current
server source with `scompile.py --source Sheaf.Paper.SectionDerivedRealization`
and compared its full declaration and body with the saved helper. These are
different constructions, so the return's explicit exception for different
declarations applies:

- The existing `AlgebraicGeometry.ProEtale.ModuleRingedComparison.totalPullComparison`
  takes two section complexes P,Q and is a chain map
  F_s(Tot(P tensor Q)) -> Tot(F_s(P) tensor F_s(Q)). Its body uses
  `HomologicalComplex.mapBifunctorComparison`, surrounded by `totalTensor_obj`
  transports. It remains the sole declaration with that name.
- The packet's helper takes one internal complex P and is an isomorphism
  E_X(F_i(P)) ≅ F_s(E_Y(P)). Its body is precisely
  `(NatIso.mapHomologicalComplex (pullComparison Λ f) (.up ℤ)).app P`.
  It is now named `termwisePullComparison`, describing the termwise lift of the
  fixed ordinary operation comparison, rather than the tensor comparison.

Renamed this distinct helper and all four uses in the fixed tensor/unit
conjugations; updated its owning node's declaration list. There is no new
theorem, assumption, alternate map or statement change. The comparison of two
tensor totals cannot replace an operation comparison on a single internal
complex: their source/target categories, numbers of complex arguments, and
constructions differ. Importing the existing tensor-comparison declaration
would not supply the required operation isomorphism.

Self-review: the tensor conjugation still uses a_(P tensor Q)^(-1), followed
by E_X(A), the fixed tensor transport, and a_P tensor a_Q. The unit conjugation
still uses a_(R_Y[0])^(-1). Thus every component of the original proposition
and all edge cases in the Worker report are retained. Searches with rg across
Sheaf and WeilConjectures for termwisePullComparison and the termwise lift of
pullComparison found no existing specialized operation-comparison declaration.
The definition's source, parameters, type and body are unchanged except for its
name, and its existing source docstring is retained.


Repair validation (2026-10-23 UTC): scompile.py compiled both delivered Lean
modules cleanly. A separate scratch module importing both
`Sheaf.Paper.SectionOplaxTotalComparison` and
`Sheaf.Paper.SectionDerivedRealization` also compiled cleanly on the server
(17.7 seconds for its sandbox check). Its two #check commands confirmed the
different signatures quoted above and simultaneous availability of both names.
The scratch probe is not delivered. JSON layout, recorded signatures, permitted
node-field changes, and all delivered Lean line lengths passed local read-only
self-checks. A focused source scan found no further declaration collisions
with existing Paper/Section modules.

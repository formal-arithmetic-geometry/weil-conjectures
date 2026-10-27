## Worker report

The module `Sheaf.Paper.FiniteFreeDualChainComparison` states the signed finite-free
scalar-chart comparison in the native internal module category. Definitions have
explicit data. The additivity assertion and main theorem have `sorry` proofs only.
No statement correction or dependency-interface repair is needed. The repair adds an
existing-definition ownership node for the five already published evaluation helpers.

Hypotheses and conclusions are rendered as follows.

- `universe u`, `X : Scheme.{u}`, and `Scheme.ProEt.topology X` retain site object
  universe u+1 and morphism universe u. Coefficients and scalar modules live in u+1.
- `Λ` is an abelian condensed sheaf with `[MonObj Λ] [IsCommMonObj Λ]`, the unbundled
  form of the recorded commutative condensed ring. `Internal Λ X` uses exactly
  `condensedRingObj Λ X = p_X^* Λ`; `ring Λ X` is its section-ring sheaf.
- `[CommRing A]` and `α : constantSheaf ... A ⟶ ring Λ X` express the scalar map.
  There is no flatness assumption. `realization` is existing ordinary constant
  scalar extension followed by reconstruction through the section equivalence.
  `chart` applies it termwise, including the differential.
- `P`, `hfinite`, `hfree`, and `l h hbounded` mean a bounded cochain complex with
  finite free terms. There is no chosen basis in the hypotheses.
- `scalarDual A P` uses the existing `ScalarPerfectDual.dual`, the ordinary
  Hom complex into A[0]. Its `coordinates` are Hom_A(P^(-b),A), and the recorded
  `dual_coordinates` supplies the stated (-1)^(b+1) differential.
- `κ` identifies the scalar extended signed dual with the ordinary ringed Hom
  dual. Its displayed equation evaluates r tensor φ on r' tensor x as
  r*r'*α(φ(x)); these balanced generators determine the identification.
- `ε` is an isomorphism of actual cochain complexes for every unrestricted `F`.
  It uses `internalTotalTensor`, the native direct-sum totalization, and the
  recorded `homComplex`, including its product terms and signed differential.
- `RingedOrdinaryEvaluationFormula` specifies every pure tensor and Hom
  projection: support only where i=-b, with value φ(x) • y. The factorization
  of `ε.hom` through `totalComparison`, `κ`, and `aEF` fixes the requested map.
- The equation with `tensorTargetMap` expresses naturality for every map F→G.
- The inverse formula quantifies over every finite basis in every degree.
  `Basis.coord` is the dual basis functional; the finite outer sum runs from
  -h to -l, and the inner sum is f(e_j) tensor e_j*. Thus basis independence
  is asserted for the same ε, rather than by choosing a basis-dependent map.
- The formulas quantify over all local objects U, and the maps are sheaf-module
  morphisms. The Hom values evaluate the actual localized Hom families.
  Consequently they specify the same formulas after slice restriction; no
  global-sections replacement is made.
- The acyclic-test clause states native K-flatness of D_T with the same actual
  tensor and the test factor on the left. The next clause quantifies over
  every K-injective augmentation η, and asserts its image by Hom(T,-) is a
  quasi-isomorphism, with no bound on F or on its K-injective replacement.
- `evaluationTranspose` is defined from the native tensor-Hom adjunction's
  `homEquiv`, actual counit, associator, braiding and right unitor.
- `S`, `M`, `t`, `θ` carry the recorded normalized native/section comparison;
  the displayed counit equality fixes θ by evaluation, not by arbitrary choice.
  `δ` identifies the localized D_T with native RHom(T,1). The localization
  tensor map and evaluation transpose are invertible. The final equality
  says the localized displayed chain map is exactly that native transpose
  after δ, through the section/localization comparisons.

The auxiliary `sectionDerivedCategory` is the existing Grothendieck localization,
with its type made explicit to avoid ambiguous instance search; it introduces no
new category or mathematical assumption. `sectionChartIso` is the equivalence
counit, and `scalarSection` and `scalar` are the existing balanced/constant
sheafification generators transported by that counit.

Edge cases checked mathematically: P=0; rank zero terms and empty bases; l>h
(the whole complex is zero); a one-term complex; adjacent nonzero terms (the
sign is -(-1)^b); arbitrary unbounded F; empty scheme/site; a nonflat scalar
map such as Z→Z/2. Finite support is in the source degrees only. In particular
no product/direct-sum exchange for an unbounded source is claimed.

Searches for an existing complete statement: msearch LeanFinder with the signed
finite-free scalar-extension tensor/Hom comparison query returned general
LightCondensed and free-module facts only; LeanSearch with bounded finite-free
signed dual tensor/internal Hom returned `dualTensorHomEquiv` and
`dualTensorHomEquivOfBasis`, which are underived module statements. Loogle
`"CochainComplex", "dual"` returned no hits. msearch grep
`dualTensorHom|finiteFreeDual|finite_free_dual` in Algebra/Homology returned no
complete match. Searches in WeilConjectures and Sheaf for this item and signed
finite-free comparison found the affine finite-free comparison, which concerns
affine O-modules, not this arbitrary condensed scalar chart and its native
closed-adjunction normalization. Detailed query output is saved in searches.jsonl.

Dependency declarations read and used (recorded interfaces):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: `None`, `universe convention`.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
- `sk-def-sfb-derived-tensor-hom`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- `def-sfb-modobj-relative-tensor`: `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`, `CategoryTheory.Mod.monoidalCategory`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`.
- `def-pur-hom-complex`: `WeilConjectures.Algebra.Homology.HomComplex`, `CategoryTheory.homComplex`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `lem-pe-internal-section-tensor-comparison`: `Sheaf.CategoryTheory.InternalSectionTensorComparison`, `CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`.
- `lem-sfb-internal-section-scalar-adjunction`: `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`, `CategoryTheory.InternalAbelianSheafModule.internal_section_scalar_adjunction`.
- `lem-sfb-scalar-perfect-dual-realization`: `Sheaf.Paper.ScalarPerfectDualRealization`, `CategoryTheory.ScalarPerfectDual.scalarPerfectDualRealization`.
- `lem-sfb-constant-finite-free-presentation-extension`: `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension`, `CategoryTheory.ConstantFiniteFreePresentationExtension.constantFiniteFreePresentationExtension`.
- `def-weil-presheaf-modules-sheafification`: `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, `PresheafOfModules.sheafification`.
- `def-pur-sheaf-hom`: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, `SheafOfModules.homObj`.
- `lem-sfb-ringed-site-bounded-evaluation-assembly`: `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly`, `CategoryTheory.RingedSiteBoundedEvaluation.assembly`.
- `lem-sfb-independent-bounded-exact-term-hom`: `Sheaf.Algebra.Homology.IndependentBoundedExactTermHom`, `CategoryTheory.SplitPerfectHom.quasiIso_homComplex_map_of_bounded_exact_terms`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`, `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `lem-pc-kflat-resolution`: `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- Statement interface: `def-sfb-ringed-ordinary-evaluation-models`, module
  `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization`, declarations
  `CategoryTheory.ringedOrdinaryHomValue`, `CategoryTheory.ringedOrdinaryDualValue`,
  `CategoryTheory.RingedOrdinaryEvaluationFormula`,
  `CategoryTheory.ringedHomAugmentationMap`, and
  `CategoryTheory.ringedOrdinaryHomComparison`. The localization theorem
  `lem-sfb-ringed-ordinary-evaluation-localization` is retained in proof_deps only.
- `lem-weil-pbc-site-derived-tensor-descent`: `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, `SheafOfModules.site_derived_tensor_descent_independentCoefficients`.
- Statement interface: `def-sfb-native-derived-koszul-braiding`, module
  `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`, declaration
  `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internalBraiding`.
  The theorem `lem-sfb-module-object-ringed-site-derived-comparison` is retained
  in proof_deps only; the signature uses its already owned braiding definition.

Additional landed statement interfaces used directly are
`StrictPerfectCoefficientPackageOfUniverses` (`scalarPerfectFunctor`,
`scalarPerfectConstantSection`), `InternalSectionTotalComparison` (`Internal`,
`Modules`, `complexForward`, `localizationIso`, `internalTotalTensor`,
`localizationTensorMap`), `InternalSectionDerivedTensorComparison`
(`totalComparison`, `TensorComparison`), and `CoefficientRingedTensorHomModel`
(`CoefficientClosedStructure`, `CoefficientTensorModels`,
`coefficientTotalTensor`, `coefficientTensorGenerator`). Their nodes are added
to stmt_deps, together with the already landed scalar-dual and evaluation
normalization nodes used in the signature.

## Second reading by Q80

This dispatcher assignment forbids starting another agent. No independent
second reading is claimed here; the maintainer's independent review reads the
delivery. The worker checked the clause mapping above against the node and the
Stacks 08JH/08JJ proof, including the zero and nonflat cases.


## New nodes

`def-sfb-ringed-ordinary-evaluation-models` is an `existing: true` definition
ownership node for precisely the five helper definitions listed above. Its source
is Stacks Section 0A8X and Tags 08JE/08J9, as used by the strictly perfect evaluation
in Tags 08JH/08JJ. It defines evaluation of an actual Hom projection, extraction
of the degree-zero coefficient from the dual, the unsigned generator formula,
Hom applied to the fixed augmentation, and the corresponding localized Hom
comparison. The new node records the existing definitions in
`Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization`; it adds no Lean
module and changes no dependency node.

Searches on 2026-10-23: LeanSearch for "Ordinary evaluation formula from tensor
with the Hom dual on a ringed site and canonical K injective Hom augmentation
comparison" returned eight general evaluation facts (`exp.ev`, `ihom.ev`,
`FGModuleCatEvaluation`, `Module.Dual.eval_apply`, and related results), with no
such cochain model. Loogle for `ringedOrdinaryHomValue,
RingedOrdinaryEvaluationFormula, ringedOrdinaryHomComparison` returned zero hits
and unknown identifier `ringedOrdinaryHomValue`. Mathlib grep in Algebra/Homology
for these names returned zero hits. Source-tree rg in WeilConjectures returned
zero hits; rg in Sheaf found exactly these existing definitions in the localization
module and their uses. DAG rg found their names in the theorem node's declarations
list only, with no definition-node owner. `tools/blueprint_refs.py search
ordinary-evaluation` returned zero blueprint-node matches. The complete raw search
outputs are stored in the new node's mathlib_searches; wrapper results are also
in searches.jsonl. Existing ownership is therefore recorded without duplicating
any construction.

The new node's clauses match the five bodies: `ringedOrdinaryHomValue` composes
`coefficientHomComponent` and `coefficientHomSectionApply`;
`ringedOrdinaryDualValue` composes that with `singleObjXSelf`;
`RingedOrdinaryEvaluationFormula` quantifies over all integer degrees, local
objects, pure tensors and both supported/unsupported cases; the supported case
uses `eqToHom` for the equal-degree transport. `ringedHomAugmentationMap` maps the
fixed `coefficientHomAugmentation` by `homComplexFunctor`;
`ringedOrdinaryHomComparison` composes its localization with
`coefficientHomResolutionIso.inv`. The ambient sheafification assumptions and
independent c/v/u/w universes are stated explicitly. Edge cases include a+q≠0,
zero modules/sections, arbitrary unbounded complexes, and an empty site. None
needs a flatness, freeness, K-flatness or K-injectivity hypothesis.

## Returned delivery repair

The retained packet is the one recorded in delivery.log at returned immutable
head `a52699e2833`. The initial saved-packet dry run passed as `22cb32742d7`.
Comparison with current main found changes only in lean and the previously added
statement dependencies. This repair addresses the returned H2 findings:

1. Replace `lem-sfb-ringed-ordinary-evaluation-localization` in stmt_deps with
   the new existing-definition node `def-sfb-ringed-ordinary-evaluation-models`.
   Keep the theorem in proof_deps. The five cited definitions now have a definition
   node owner; their statements and data are unchanged.
2. Replace `lem-sfb-module-object-ringed-site-derived-comparison` in stmt_deps
   with the already published `def-sfb-native-derived-koszul-braiding`. Keep the
   theorem in proof_deps. Its only signature use here is `internalBraiding`.

`lem-sfb-scalar-perfect-dual-realization` stays in stmt_deps: `coordinates`
uses `dual_coordinates.choose`, so this is a genuine theorem dependency.
No theorem, definition body, hypothesis, conclusion or proof dependency changed.
The original duplicate derived-category instance and the two unused definition
citations were advisories; preserving them retains the independently checked
Lean statement. The second-reading section explicitly claims no independent
reading, as required by the dispatcher prohibition on starting agents.

Self-check: reread the full node and module, including kappa on balanced generators,
epsilon's evaluation factorization, naturality, inverse for every finite basis,
the native acyclic tensor test, every K-injective augmentation, delta and the
native evaluation-transpose equality. The existing clause mapping above still
applies verbatim. Both replaced theorem dependencies remain in proof_deps; only
the newly added dependency entries are replaced. The original base stmt_deps,
source statement, proof and proof_deps are preserved. No dependency node file is
delivered. New-node signature is copied verbatim, preserving source whitespace, from the
published definition. Every delivered module is compiled with scompile.py and
then checked again by the prescribed dry run before pushing.

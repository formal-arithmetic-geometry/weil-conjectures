## Worker report

The delivery states `AlgebraicGeometry.ProEtale.ModuleRingedComparison.internal_oplax_resolving_components`
in `Sheaf.Paper.InternalOplaxResolvingComponents`. The only postponed proof is that theorem.
All seven helper definitions have actual bodies and belong to this same component assertion.
No mathematical statement, accepted proof split, source, or proof dependency is changed.
The item additionally cites the already landed definition node
`def-pd-section-total-oplax-comparison-data`, which owns the actual total unit used in the equation.
There are no new nodes and no dependency repairs.

Clause-by-clause translation (abbreviate the namespace
`AlgebraicGeometry.ProEtale.ModuleRingedComparison` by MRC in this report only):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary commutative condensed ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]`. This is the unbundled form of the recorded `Profinite.CondensedRing`; it does not assume topological coefficients. |
| Small pro-etale site and pulled-back coefficient ring | `internalModules Λ T` and `modules Λ T` are the recorded SectionModuleOperationsData aliases, over `Scheme.ProEt.topology T` and `condensedRingObj Λ T`; the latter is `p_T^* Λ`. The ringed category uses the reconstructed `ring Λ T`. |
| Exact section equivalence, ordinary operations, and their universes | All aliases and the fixed equivalence are the imported ones. The site is `Type (u+1)` with Hom in `Type u`, and module sections are in `Type (u+1)`. The `HasDerivedCategory.{u+1}` family is the existing localization-size convention, as in the dependency interfaces; it imposes no geometric condition. |
| q internal and section; K-flat flat-term resolving classes | `DerivedCategory.Qh` is the homotopy localization and `DerivedCategory.Q` its cochain form. `KFlatSectionComparison.internalResolving Λ T` is used unchanged: the acyclic signed-total test plus exactness of tensoring with every term. Its imported comparison theorem identifies it with the section predicate. No resolving predicate is redefined. |
| Signed unbounded direct-sum totals and relative derived tensors | `⊗` on homotopy and derived categories is the existing relative module tensor and its K-flat derivation. The homotopy tensor is the quotient of the signed direct-sum cochain tensor. All indices are integers without support restrictions. |
| Arbitrary scheme morphism f and the specified pullbacks | `{X Y : Scheme.{u}} (f : X ⟶ Y)`; `F = CondensedRing.upperStar Λ f` in the generic predicate is the full internal pullback composite. Its `leftDerivedFunctor` and `leftDerivedFunctorCounit` are the recorded total derived pullback and eta. The section derived realization and resolution-compatible gamma, theta, e are retained through the imported normalization interfaces; they are fixed constructions used in the proof, not new variable choices. |
| Pullbacks of A and B resolve | First conjunct of `Functor.ResolvingOplaxComponents`: every resolving homotopy object has resolving image under `F.mapHomotopyCategory (.up ℤ)`. Specializing to A and B gives exactly the two claims. |
| Eta_A, eta_B, eta_total are invertible | The first conjunct asserts `IsIso (F.leftDerivedFunctorCounit.app A)` on all resolving A. The second separately asserts it at `A ⊗ B` for resolving pairs. |
| a = eta_total after L(r inverse) | `resolvingComparisonA F` is the uncurrying of the existing `F.leftDerivedDerivedTensorCounit`. Its source formula, read in LeftDerivedFunctor/Monoidal.lean, is literally `F.leftDerivedFunctor.map (LaxMonoidal.μ Qh A B) ≫ eta_(A⊗B)`. The fixed lax map μ is the inverse orientation of the node's representative isomorphism r. |
| c = r inverse after eta_A tensor eta_B | `resolvingComparisonC F` uncurries the existing `F.derivedTensorLeftDerivedCounit`. Its component is `(eta_A ⊗ₘ eta_B) ≫ LaxMonoidal.μ Qh (F_h A) (F_h B)`. |
| a and c invertible | The two explicit `IsIso` clauses at `(A,B)` in `ResolvingOplaxComponents`. |
| Delta is the actual specified localized map | The final specialization supplies `internalDelta Λ f`, which the recorded SectionDerivedRealization defines as the actual `leftDerivedTensorComparison` of the internal pullback. The generic predicate takes that specific map, not an arbitrary map or an existentially chosen isomorphism. |
| c delta = q(b) a | The component equality in `ResolvingOplaxComponents`, in Lean composition order: `resolvingDelta ... ≫ resolvingComparisonC ... = resolvingComparisonA ... ≫ resolvingTotalArrow ...`. `resolvingTotalArrow` uses the existing `OplaxMonoidal.mapHomotopyCategoryδNatTrans` followed by Qh, whose quotient components are the actual signed-total `mapBifunctorComparison`. This is exactly the forward map of `actualInternalTotalIso`; no alternative total arrow is selected. |
| v = q(u) eta_unit | Final equality directly compares `(CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom` with `leftDerivedFunctorCounit.app (quotient.obj regularComplex) ≫ DerivedCategory.Q.map (actualInternalTotalUnit Λ f)`. These are the already constructed derived unit and actual ordinary unit. |
| Regular degree-zero unit resolves | Explicit middle conjunct with `𝟙_ (CochainComplex (internalModules Λ Y) ℤ)`, the existing regular module in degree zero. Its eta invertibility follows by the first conjunct applied to this resolving object. |
| Naturality in both homotopy variables | All four component families are natural transformations on the product homotopy category, obtained by uncurrying actual natural transformations. The component equality is therefore an equality between natural composites on resolving pairs; naturality is retained in the types rather than replaced by a pointwise arbitrary family. |
| Valid after inversion of quasi-isomorphisms | Four `ResolvingInverseSquares` clauses. The property `resolvingPairArrows` requires all four source/target components resolving and both maps quasi-isomorphisms. Each clause supplies isomorphisms whose forward maps equal the corresponding functor images, and asserts `i.inv ≫ tau.app source = tau.app target ≫ j.inv`. Inverting one variable uses the identity in the other; compositional inversion follows by composing these exact squares. |
| No coefficient-flatness or boundedness assumption | Neither appears anywhere in the theorem, the resolving predicate, or its generic package. Generic structural instances are the existing ones for the actual internal module category and pullback. |

Dependencies read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, the recorded arbitrary condensed-ring encoding.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, its category, and `ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`, `condensedRingObj`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, specialized by the recorded operations-data aliases.
- `Sheaf.Paper.SectionModuleOperationsData`: `ring`, `modules`, `internalModules`, `equivalence`, `pullback`, and `pullComparison`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the signed direct-sum total underlying the existing tensor notation.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: `CondensedRing.derivedTensor` and its relative module derived monoidal structure, publicly exported by this recorded dependency module.
- `Sheaf.Paper.SectionDerivedRealization`: `internalDelta`, `derivedPullComparison`, `qTensor` and the fixed section derived operations.
- `Sheaf.Paper.SectionDerivedPushpullNormalization`: `sectionDerivedPushpullNormalization`, especially its explicit resolution-transformation compatibility equation.
- `Sheaf.Paper.SectionKFlatTensorComparison`: `KFlatSectionComparison.internalResolving`, `sectionResolving`, `section_kflat_tensor_comparison`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: the canonical module-object derived functors and the publicly exported `leftDerivedFunctorCounit` interface.
- `Sheaf.Paper.ProEtaleSectionModuleFunctors`: the actual strong oplax pullback and its flatness preservation; these are imported by the total comparison owner.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`, used by the imported section resolving interface.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite` and `exactFunctor`, used by those same imported resolving predicates.
- `Sheaf.Paper.SectionTotalOplaxComparisonData`: `actualInternalTotalUnit` and `actualInternalTotalIso`; the owner is added to statement dependencies.
- The existing `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal` definitions `leftDerivedDerivedTensorCounit`, `derivedTensorLeftDerivedCounit`, `leftDerivedTensorComparison`, and the corresponding component formulas were read in full. Its `mapHomotopyCategoryδNatTrans` is the localization of the actual total oplax chain arrow.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`: `leftDerivedUpperStarUnitIso`, including its actual counit/single-complex/coefficient-unit composite. Only this existing map is used; no strong-monoidality theorem replaces the component assertion.
- All stated proof dependencies are imported: RingedTopoiCanonicalTensorPullbackOfUniverses, InternalModuleOperationsTransport, KFlatTotalTensorModel, DerivedPullbackRepresentativeComputation, SectionDerivedPushpullNormalization, SectionOplaxTotalComparison, SectionKFlatTensorComparison, and the Mathlib localization universal-property interface.

Edge cases checked before finalizing:

1. Zero complexes are admitted by the unbounded cochain and homotopy categories; no nonzero condition occurs. Empty degreewise summands remain the existing zero coproducts.
2. The regular unit is the actual single complex in degree zero; it remains admitted even for the zero coefficient ring. It is explicitly resolving and its counit is covered by the all-resolving-objects clause.
3. Identity scheme morphisms and identity quasi-isomorphisms remain allowed, including inversion in just one variable. No nonidentity condition is hidden in `resolvingPairArrows`.
4. All complexes may be unbounded in both directions; the internal tensor is the actual signed coproduct total, never a product total or truncated tensor.
5. The site object and morphism universes remain different (`u+1` and `u`). The generic category object universes are separate from their Hom universe, so instantiation does not identify those sizes.
6. No flatness of a structural coefficient map is assumed; only the two resolving inputs have flat terms. A nonflat scalar map such as Z to Z/2 is therefore not excluded by a new hypothesis. The claim is resolving pullback preservation, not arbitrary preservation of quasi-isomorphisms by scalar extension.

Searches for an existing whole statement:

- `msearch.py ... leanfinder "The actual localized internal derived pullback oplax tensor map has its K-flat representative component computed by the resolution counit and tensor localization map"`: eight generic hits, including localization monoidal tensor comparisons; none includes the specialized resolving preservation and actual unit assertion.
- `msearch.py ... loogle "CategoryTheory.Functor.leftDerivedTensorComparison, CategoryTheory.Functor.leftDerivedUnitComparison"`: zero hits; the service indexes Mathlib, not the project-specific generic derived comparison. The actual upstream declaration was then read directly and reused.
- `msearch.py ... grep "leftDerivedTensorComparison|leftDerivedUnitComparison|lift₂NatTrans_app_app" CategoryTheory`: one Mathlib hit, `CategoryTheory.Localization.lift₂NatTrans_app_app`; it is the generic localization component formula, not this item.
- `msearch.py ... leansearch "The localized tensor comparison for pullback on K flat complexes satisfies its resolution counit component equation"`: eight hits including `CategoryTheory.Functor.totalLeftDerivedCounit`; none states the specialized whole assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `internal.oplax|internal_oplax|resolving.components|leftDerivedTensorComparison|leftDerivedUnitComparison`: found the exact general comparison machinery and other users, but no theorem of this node. `grep -rn` of this item id in `lean/WeilConjectures` found none.
- Searched the final helper names against the project sources; no collision. Existing general tensor counits and their ordinary total-arrow machinery were reused rather than reconstructed.

Source check: opened Stacks `sites-cohomology.tex`, `lemma-pullback-K-flat` (Tag 0G7E) and `lemma-pullback-tensor-product` (Tag 07A4), including the K-flat-flat-term representative argument and the explicit signed-total construction. Also read the current blueprint unit under `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/`. The specialized component equations are correctly identified as agent calculations, not verbatim Stacks assertions.

Validation: prescribed `scompile.py NA lem-pd-internal-oplax-resolving-components ...` passed cleanly for both the sandbox module and its final library module. The final library compilation reported 43.5 seconds. No errors or warnings remain; only the named theorem is postponed. Earlier direct-specialization timeouts were repaired by packaging the same natural transformations in generic predicates, without splitting the file, raising the time limit, or weakening the assertion.

No STATEMENT-DISPUTED issue was found. No statement correction is made.

## Second reading by NA

A separate self-review pass reopened the item statement and final module, comparing every clause using the table above. No second agent was started, as required by the dispatch brief; the maintainer's independent review remains the independent reading. Checked especially that the generic predicate receives `internalDelta Λ f` itself, that the ordinary tensor arrow is the quotient of the existing signed-total oplax comparison, that a and c are the actual two counit composites rather than unconstrained maps, and that the unit equation uses both fixed constructions. The inverse-square assertions retain the exact forward functor images and thus fix the inverted arrows. The sole graph addition cites the already landed owner of `actualInternalTotalUnit`; no accepted proof text changes. All helper data are constructed, all variables and universes are explicit, and the only theorem proof is `sorry` with the complete six-step proof docstring.

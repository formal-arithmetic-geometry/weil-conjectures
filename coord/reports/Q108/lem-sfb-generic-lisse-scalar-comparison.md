## Worker report

The module `Sheaf.Paper.GenericLisseScalarComparison` states the local-chart and
actual-generic-section comparison for ordinary internal extension of the full
continuous norm-topology coefficient ring. All theorems have `sorry` proofs;
all maps, functors and scalar data are constructed explicitly. No mathematical statement
correction is made. The H2 repair replaces the theorem dependency by its
definition owner, as detailed below.

Hypotheses and clauses of the node are rendered as follows.

- `X : Scheme.{u}` and `[IsIntegral X]` provide a nonempty integral scheme.
  `[IsLocallyNoetherian X]` is the stated local Noetherian hypothesis, and
  `_hnormal : ∀ x, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)` is precisely normality of its local rings.
- The field is `X.functionField`, the stalk at `genericPoint X`;
  `NormalGenericLisse.genericMap X` is its actual spectrum map to X.
  `Ω : Type u`, `[Field Ω]`, `[Algebra X.functionField Ω]` and
  `[IsSepClosure X.functionField Ω]` fix the arbitrary separable closure.
  The Galois group is `Ω ≃ₐ[X.functionField] Ω`, with its existing Krull topology.
- `[NormedField A]`, `[NormedField B]`, `_hA` and `_hB` render the two
  nonarchimedean normed fields. `[Algebra A B]` and
  `hφ : Continuous (algebraMap A B)` render an arbitrary continuous field
  homomorphism: a unital homomorphism from a field is injective, and conversely
  every such homomorphism supplies this algebra structure. No completeness,
  valuation nontriviality, local compactness or algebraic closure is assumed.
- `normContinuousRing`, `normContinuousCoefficientMap` and
  `normContinuousExtension` use the landed continuous-map ring, its actual
  postcomposition map followed by p_X^*, and `Mod.extendScalars`.
  `NormContinuousLisse A X` uses the recorded `IsLisseCoefficientModule` on the
  small site `X.ProEt`. Thus every coefficient function is continuous for the norm
  topology; there is no finite-subextension-valued restriction.
- `extension_lisse` says the actual extended module is lisse. `extension` is the
  restriction of the actual extension functor to those objects, using that theorem
  only for its property field. `charts`, `IsExtendedCoefficientChart` and `ChartAssertions` retain every local
  rank r and normalize the new chart on every basis inclusion. Their entry square
  says the coefficient map carries each transition or rectangular morphism entry
  to the corresponding extended entry; transitions are the identity morphism in
  two charts on an overlap. These assertions are formulated through arbitrary
  condensed coefficients to prevent elaboration from expanding concrete ring
  structures; `charts` specializes them to the stated continuous field map.
- `NormalGenericLisse.geometricSections` is evaluation of the actual generic
  restricted module on `FieldSeparableCech.closureObject`. By site localization
  these are exactly the displayed Gamma after restriction to Spec Ω.
  `scalar` evaluates the existing constant internal scalar operation.
  `scalar_laws` supplies only its six module laws; `fiberModule` has that explicit
  scalar operation as its data. There is no arbitrary vector-space realization.
- `baseUnit`, `pullUnderlying`, `chartUnit`, `coefficientUnitArrow`, `unitArrow`
  and `unit` use the actual internal extension unit and the published canonical
  forgetful/pullback comparisons. `unitSource_eq` identifies its source with the given section object;
  `unitTarget_eq` identifies its target after forgetting the lisse-property
  wrapper on the ordinary extension. `unit` transports
  along this equality with `eqToHom`; its data are the actual evaluated unit,
  with no arbitrary choice. This isolates expensive definitional conversions.
  The first clause of `comparison` specifies `e L (b ⊗ₜ[A] v) = scalar ... b (unit ... v)`.
  This normalization on spanning pure tensors determines the comparison uniquely.
- `map` evaluates the actual generic pullback of a sheaf morphism. The second
  clause of `comparison` is its naturality square on every pure tensor.
  The fourth clause, with arbitrary finite bases c,d and indices i,j, is the
  entrywise formula for every rectangular generic matrix.
- `action` is restriction along the actual `NormalGenericLisse.automorphism`,
  induced by Spec(g). The third clause is precisely the intertwining equation
  with g acting trivially on b; the fifth is entrywise application of the field
  map to every Galois matrix. The convention is the recorded field-Cech convention
  c(gh)=c(g)c(h), rather than a newly chosen action.
- `etaleFiber` is the existing finite-etale geometric fibre functor at the generic
  separable closure, and `quotient` is the published `FiniteEtale.galoisToAut`
  homomorphism. In the final clause `_hqc : CompactSpace X` is quasi-compactness,
  `_hq` is surjectivity of this canonical q, and the two displayed factorization
  equations specify the factored actions. They are thereby determined by the
  actual generic actions. The two final equations give quotient equivariance and
  equivariance after precomposition by `a.symm`, for one arbitrary fixed
  topological group isomorphism to `Aut (Scheme.flcFiber x)`.
- All ranks and matrix dimensions are unrestricted natural numbers. `Fin 0`, the
  empty biproduct and the empty tensor basis cover rank zero and empty rectangular
  matrices. No positive-rank hypothesis appears.

Dependency declarations used (with their owning modules):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`;
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`: the `IsSepClosure` interface.
- `Sheaf.Topology.ContinuousMapCondensedRing`: the universe-polymorphic
  continuous-map ring and its actual monoid structure;
  `Sheaf.Topology.ContinuousMapCondensedRingMap`: its postcomposition map and
  `Profinite.isMonHom_continuousMapRingObjMapOfUniverse`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, the canonical coefficient comparisons;
  `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, regular modules and module maps;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`;
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.finiteFree`;
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars` and `Mod.extendUnitHom`;
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed`:
  `CondensedRing.upperStarObjXIso`.
- `Sheaf.Paper.NormContinuousMonodromyData`: `NormContinuousLisse`,
  `normContinuousRing`, `normContinuousCoefficientMap`, `normContinuousExtension`
  and `normContinuousScalar`.
- `Sheaf.Paper.NormalGenericLisseCocycle`: `genericMap`, `genericModule`,
  `geometricSections`, `automorphism`. The new definition node
  `def-sfb-normal-generic-lisse-sections` owns these five declarations (including
  `automorphism_over`, used only as a proof field). The generic-cocycle theorem
  is not a statement dependency: none of these definitions chooses its conclusion.
- `Sheaf.Paper.FieldSeparableCechCoordinates`: `closureObject` (owned by the directly cited
  `def-sfb-field-separable-cech-nerve`) and the recorded coordinate/action convention; `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`:
  `Scheme.flcFiber`; `WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction`:
  `FiniteEtale.pointOfAlgebra`, `fiber` and `galoisToAut`.
- Proof imports retain `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`,
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`,
  and `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`. The free-matrix
  scalar-extension and Galois-section-naturality proof nodes currently have no Lean
  record, so there is no module for those two nodes to import.

Source checked: Bhatt--Scholze, Lemma 7.4.7 and Remark 7.4.8 on p. 70 and
Lemma 7.4.10 on p. 71, together with the six explicit agent-written proof steps
of this node. The module does not attribute the arbitrary normed-field statement
to the paper's local-field classification.

Edge cases checked: φ=id; a proper continuous field inclusion; finite and
infinite extensions; trivial absolute value; rank zero; a zero morphism; n=0 or
m=0 in every rectangular identity; trivial Galois action; identity basepoint
transport; and arbitrary lifts in the final surjective-quotient identity.
The empty scheme is excluded exactly by the given integral/nonempty hypothesis.
No nonempty chart or positive dimension is added.

Searches (the original exact queries and responses are in the sandbox search log):

- LeanFinder: “Generic fibre extension of scalars lisse pro etale modules continuous
  coefficient fields Galois representation natural tensor comparison”: 8 results,
  concerning Kahler differentials and formally etale base change, no match.
- LeanSearch: “Extension of scalars for generic sections of locally free sheaves
  commutes with Galois monodromy”: 8 results including `IsGaloisGroup.commutes`,
  `ModuleCat.ExtendScalars.obj'`, localization scalar extension and
  `SheafOfModules.restrictScalars`; none states this comparison.
- Loogle: `TensorProduct.map, ModuleCat.extendScalars, SheafOfModules.pullback`
  initially reported service load; the later query `"extendScalars", "Mod"`
  returned general ModuleCat change-of-scalars declarations, no complete match.
- msearch grep: `(generic|Generic).*(scalar|Scalar)` and
  `(generic|Generic).*(scalar|Scalar)|(lisse|Lisse).*(scalar|Scalar)`: no match.
- Direct rg of WeilConjectures and Sheaf for generic/scalar and the node id found
  unrelated generic-fibre, trace and derived scalar statements, and no duplicate.
  Existing general internal tensor, actual normed coefficient data and generic
  section interfaces were reused throughout.

No known statement dispute. The endpoint obligations
`unitSource_eq` and `unitTarget_eq` equate the two presentations of the original
and extended section objects, covered by the node's ordinary-extension and unit
clause (steps 1 and 3). Their complete unfolding proofs are in their docstrings. Equality
transport is unique by proof irrelevance and does not choose any module data.
Compilation and delivery validation are recorded below.


Validation: the complete module compiled cleanly with `scompile.py`, both as the
sandbox module (22.0 seconds) and at its delivered module path (9.0 seconds).
No errors or unexpected warnings were reported. Six named theorem obligations
remain, each with the source and full natural-language proof in its docstring:
`extension_lisse`, `charts`, `scalar_laws`, `unitSource_eq`, `unitTarget_eq`,
and `comparison`. All definitions have constructed data.


## Repair of fac0019fb315

The saved packet initially passed deliver2.py --no-push at 3a3b5e8142d, but
retained the independent review's H2 defect. The repair now removes the added
`lem-sfb-normal-generic-lisse-cocycle` statement dependency, adds the definition
owner below, and directly cites the already-landed
`def-sfb-field-separable-cech-nerve` for `FieldSeparableCech.closureObject`.
The original statement, proof, proof_deps and complete Lean module are retained.
Only stmt_deps and lean metadata change on the item. Its other added dependency,
`def-sfb-norm-continuous-monodromy-data`, is an existing definition node supplying
the actual coefficient and lisse constructions.

The definition owner binds existing data in the same imported module; the import
of that module does not mean its full-faithfulness/cocycle theorem is required to
state the comparison. The only proof field used is `automorphism_over`; it verifies
that the explicitly constructed Spec(g) arrow lies over Spec(k).

For the review's advisories: `etaleFiber` uses `FiniteEtale.fiber` at the separably
closed generic point. Finite étale covers and finite locally constant étale sheaves
are canonically equivalent (Stacks 0BND), so its automorphism group is the stated
étale fundamental group, also modeled at the other point by `Scheme.flcFiber`.
`_hq : Function.Surjective (quotient X Ω)` explicitly retains the node's stipulated
surjection as a hypothesis. Its truth for the canonical generic map is the standard
normal-integral generic-point assertion (Stacks 0BQM); this comparison theorem
only uses it to choose a lift of a quotient element, as in node proof step 6.
The final basepoint equation is precisely the quotient equation evaluated at
`a.symm δ`; it is simultaneous transport by the one fixed topological isomorphism.

## New nodes

`def-sfb-normal-generic-lisse-sections` is an existing:true definition node on
`Sheaf.Paper.NormalGenericLisseCocycle`, owning `genericMap`, `genericModule`,
`geometricSections`, `automorphism_over` and `automorphism` in the
`AlgebraicGeometry.ProEtale.NormalGenericLisse` namespace. It introduces the actual
stalk map j, ordinary generic module pullback, evaluation on the separable-closure
object and Spec(g) site endomorphism. The common universe, integral X, arbitrary
normed field A, lisse L and arbitrary separable closure are exactly their existing
binders. Normality and Noetherian hypotheses are unnecessary to define these data.
The source is the same explicit generic restriction in Bhatt–Scholze 7.4.7 and
7.4.10 and the item's proof steps 3 and 5. No theorem conclusion is chosen.

Searches for this owner: `blueprint_refs.py search 'generic sections'` returned
zero blueprint nodes, and the DAG definition-node grep found no existing owner.
LeanSearch with the query recorded verbatim in mathlib_searches returned eight
general field-closure/fibre-evaluation hits, and LeanFinder returned eight
integral-closure/Galois restriction hits; none defines this specialization.
msearch grep `genericModule|geometricSections|NormalGenericLisse` returned zero
Mathlib hits. Project grep found the five exact declarations already in
NormalGenericLisseCocycle. The other `CondensedGalois.geometricSections` is a
functor to condensed action modules on a base-changed scheme, not this generic
small-site evaluation. Exact search outputs are preserved in mathlib_searches.
The new node cites the existing integral scheme, norm-continuous monodromy data,
separable closure, internal pullback and separable Čech-nerve definition nodes.
It creates no new Lean module or declaration and no additional sorry.

## Second reading by Q108

This dispatched worker does the repair self-check; the independent reading is the
maintainer's delivery review, as specified in the brief. I re-opened the item and
complete Lean file and checked the accepted hypothesis/clause mapping above.
Integral and locally Noetherian X and normal stalks remain explicit; arbitrary
nonarchimedean normed fields and the continuous algebraMap remain unrestricted.
`extension_lisse` plus the normalized charts retain each local rank and all
transition entries. The comparison is fixed on pure tensors by the actual unit,
and its naturality, Galois action, rectangular-matrix and Galois-matrix clauses
are intact. The final clause retains quasi-compactness, the canonical surjective
quotient, both factorizations, and arbitrary fixed basepoint transport. Rank zero,
empty matrices, identity scalar maps and identity basepoint transport are included.
The new node's five bindings were checked against their source signatures and
bodies: fromSpecStalk, upperStar, actual closureObject evaluation, the over-k
identity, and Over.homMk of Spec(g). The direct closureObject owner was also read.
The defect found is precisely the theorem/definition stmt_dep classification;
this repair changes ownership and dependency records without a mathematical
statement change or private copy of the existing definitions.

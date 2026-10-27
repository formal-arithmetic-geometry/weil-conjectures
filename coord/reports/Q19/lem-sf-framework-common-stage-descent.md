## Worker report

This delivery states the framework common-stage descent lemma on the recorded intrinsic
raw rationalized categories, with five named postponed theorems and real helper definitions.
It uses the existing StageSystem quotient functor and natural-transformation constructions.
No proof is supplied. All theorem proofs are `sorry`; the definitions contain real data.

The original statement is unchanged. Its hypotheses and clauses are rendered as follows.

* The global datum and distinct prime are `_D : FiniteFieldDatum` and `_hl : l ≠ _D.p`
  in `sfFrameworkCommonStageDescent`; primality is `[Fact l.Prime]`. The closure has
  `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`. The intrinsic constructions,
  as their owning modules explain, do not use the global datum's geometric field.
* T, S and the third scheme V have independent universe variables. No Noetherian,
  finite-dimensional, coefficient-invertibility or finite-type hypothesis is imposed.
* E ranges over `Padic.FiniteCoefficientFields l Ω`, exactly the finite intermediate
  fields. `GeneralAlgebraicallyClosedCoefficients.Stage` is the published raw
  `sfRationalConstructibleCategory` with its canonical small coefficient model.
* The systems are precisely `GeneralAlgebraicallyClosedCoefficients.stageSystem`.
  Their transitions are the specified completed integral extension followed by raw
  rationalization, with the actual `sfRationalScalarComp` associators and multiplication
  units. No Karoubi envelope or PBC stage category substitutes for a framework category.
* `SfFrameworkFamily.system.Φ` and `.β` are the given functors and natural isomorphisms;
  `.system.coh` is exactly the displayed tower square, in Lean's diagrammatic order.
  `.shift`, `.additive`, `.linear`, `.exact` give the specified shift comparison,
  additivity, E-linearity and preservation of distinguished triangles.
* `.scalar_shift` is `NatTrans.CommShift` for β with the composite shift comparisons.
  `.unit`, via `sfFrameworkUnitCompatible`, says β at E/E is the source multiplication
  unit followed by Φ applied to the inverse target multiplication unit. This is
  equivalent to the node's unit square. HEq accommodates the published equality of
  stageSystem transitions with the actual tensor transitions; it is an equality of
  actual arrows, with no arbitrary comparison supplied as an additional hypothesis.
* `sfFrameworkCommonStageDescent` states additivity, Ω-linearity and exactness of the
  existing `system.functor`, its pair object formula, its precise conjugated arrow
  formula and commutation with associator-conjugated transport. Since this is a
  functor on the existing quotient, it gives independence of all representatives;
  the last clause also explicitly records independence under extension of stage.
* `sfFrameworkCommonStageShift_existsUnique` fixes the descended shift on every pair
  to the inclusion of the given finite comparison. Inclusion already uses the unit
  identifications; its published shift comparison has identity components. The
  subsequent instance chooses from this unique, fully normalized specification.
* A second family G and a compatible `StageSystem.Morphism.Hom` are exactly the second
  paragraph's Ψ, γ and τ with their displayed scalar square. The transformation is the
  actual `descNatTrans`. `sfFrameworkCommonStageTransformations` states its component
  formula and preservation of invertibility, shifts, identities, vertical composition
  and any componentwise equality. A third parallel family H permits vertical composition.
* For a third scheme V, `sfFrameworkComposite_compatible` states that composition still
  satisfies the unit and scalar-shift squares. `SfFrameworkFamily.comp` retains the
  actual `StageSystem.Morphism.comp`, whose coherence is the composite tower square.
  `sfFrameworkCommonStageComposition` gives the two whiskered β factors, the canonical
  `functorCompIso`, compatibility with the specified shifts, its identity components,
  and equality of the maps with the composite of descended maps. Thus comparisons of
  compatible transformations identify as their finite-stage classes as well.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* The scheme-properties dependency is a convention node with no declaration;
  schemes use Mathlib `AlgebraicGeometry.Scheme`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its reexported coefficient constructions.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, its inherited
  shift and triangulation and `sfRationalScalarExtension`.
* `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`,
  the published independent-universe integral construction, retained by import.
* `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp`, `sfRationalScalarUnit`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageSystem`, `Pair`,
  `unitor`, `inclusion`, `stageTransitionCommShift`, `hasShift`, `inclusionCommShift`,
  `pretriangulated`, `isTriangulated`, and `generalAlgebraicallyClosedConstructibleCategory`.
* Mathlib `CategoryTheory.Pretriangulated`, `Functor.CommShift`, `Functor.IsTriangulated`
  and `NatTrans.CommShift` implement the exactness and shift notions of the convention node.
* The already landed `def-weil-pbc-qbar-category` is added to stmt_deps solely to cite
  `Sheaf.Paper.IntrinsicQbarCategory`'s `intrinsicQbarStageLinear` and `intrinsicQbarLinear`.
  These are the existing linear structures on the exact same intrinsic framework stages
  and pairs and do not require that node's PBC domain hypotheses. Its restricted alias
  `intrinsicPbcQbarCategory` is not used. No definition node is duplicated or rewritten.
* `WeilConjectures.CategoryTheory.StageSystem.Functor`: `Morphism`, `Morphism.Hom`,
  `Morphism.functor`, `mapAt`, `descNatTrans`, `Hom.id`, `Hom.comp`, `Morphism.comp`,
  `functorCompIso`. Their full signatures and docstrings were read before use.

Edge cases checked: identity inclusions E=L and repeated fields in towers retain actual
units and associators; no strict normalization is assumed. Zero objects and zero arrows
are included by the same formulas. Empty schemes have no extra geometric restrictions.
The identity family satisfies the normalized unit square. Shifts cover every integer,
including zero and negative shifts. Invertibility is required only in the corresponding
conditional conclusion; arbitrary compatible transformations are allowed. Scalars outside
a representative's field are handled by the published finite-compositum action. The
scheme, closure and global-datum universes remain independent.

Searches for existing notions and statements:

* msearch LeanFinder, query “Coherent finite coefficient stage functors descend to an
  exact functor with compatible natural transformations”: eight generic exact-functor
  hits (ExactFunctor.of, RightExactFunctor.ofExact, etc.); no exact framework statement.
* msearch LeanSearch, query “Descent of compatible exact functors between filtered
  common-stage coefficient categories”: eight generic exact-functor, descent-data and
  filtered-colimit hits; none states this framework result.
* msearch Loogle, `CategoryTheory.Functor.IsTriangulated, CategoryTheory.NatTrans`:
  zero hits.
* msearch grep, `descNatTrans|Morphism.functor|CoherentPairFunctor` in CategoryTheory:
  zero hits; and `Morphism|descNatTrans` in CategoryTheory/StageSystem: zero hits.
  Direct source reads nevertheless located the project's StageSystem constructions.
* rg over the source library and Sheaf for common-stage/descent/FrameworkFamily and
  the item id found generic StageSystem APIs, CoherentPairFunctorDescent (requires
  literally normalized identity transitions), and FdCommonStageComparisonDescent
  (equivalences to PBC categories with geometric restrictions). None is this lemma.
  The exact canonical quotient constructions are reused; only their framework
  specializations and the remaining exact-linear/normalization assertions are stated.

Source checked: main-20261015 prop-sf-open-closed-triangle-all-stages.proof.md, the
algebraically closed coefficient and Weil-structures paragraphs, and all eleven steps
of the extracted node proof. There is no statement correction or disputed statement.

The unit square is a named predicate so generating its structure projection does not
repeatedly unfold the large coefficient model. This does not alter its content.
The two composite-shift instances expose the ordinary finite composite comparison and
the uniquely normalized pair comparison. The composition formula and map comparison
use HEq only for their explicitly identified object endpoints; no information about
the arrows is discarded.

Validation: scompile.py compiled the full delivered module, both the sandbox name and
its real library name, with exit 0 and no warnings (13.2 s and 21.5 s respectively).
No diagnostic commands or scratch modules remain in the delivery. The dry run and
push are the prescribed deliver2.py operations.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

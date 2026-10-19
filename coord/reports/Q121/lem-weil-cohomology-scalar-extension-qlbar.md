## Worker report

Repair of returned immutable head bf8ec2fc4edd, points H3/H5+H4 and both H13 findings.
The module states `WeilConjectures.ordinaryCohomology_scalarExtension_qlbar`.
Only the item's Lean record and module are delivered. The mathematical node text,
statement dependencies, proof and proof dependencies are unchanged.

The repaired target `ordinaryConstantQbarSpace` is exactly
`globalGeometricFrobeniusQbarCohomology D l hl X₀ Ω c₀
(constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω) false i |>.a`.
Its endomorphism is the recorded `globalGeometricFrobeniusQbarOnCohomology`
on that same object, with compact=false. Neither the target cohomology nor its
operator is defined by locally extending the rational cohomology or operator.

`ordinaryConstantQbarComparison` is constructed, not postulated. It first applies
homology to `eqToIso (frobeniusCohomologyQbarSourceEq ...)`, the live functor's
object clause. Then `ordinaryCoefficientHomologyIso` commutes homology with the
actual exact coefficient-transport functor. Finally `ordinaryCoefficientLiftIso`
removes its ULifts using `TensorProduct.AlgebraTensorModule.uliftEquiv` and
`ULift.moduleEquiv`. The canonical map is `baseStageScalarComparison` followed
by the inverse of this composite. Its tensor normalization is a tensor h mapping
to a tensor h, then to the class of that tensor. No arbitrary map or Nonempty
isomorphism is chosen. A complex representative is obtained from the localization's
essential surjectivity only to compute the existing normalized homology comparison;
its homology and exactness comparisons supply the actual isomorphism.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- `D : FiniteFieldDatum.{u}` supplies p, a>0, q=p^a, k₀ and its chosen closure k.
- `l`, `[Fact l.Prime]`, `hl : l ≠ D.p` supply the coefficient prime and inequality.
- `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`
  supply an arbitrary specified algebraic closure; u and v are independent.
- `X₀ : Over (Spec (.of D.k₀))`, `[IsProper X₀.hom]`,
  `[GeometricallyConnected X₀.hom]`, `d : ℕ`, and
  `hsmooth : D.IsSmoothOfPureDimension X₀ d` give exactly the geometric assumptions.
  Properness supplies separatedness and finite type. The recorded constructions
  internally use `D.geometricFiber X₀` for X.
- `c₀ : Compactification X₀.hom` retains the recorded Frobenius presentation.
  It imposes no extra restriction: proper X₀ admits its identity compactification;
  every use here selects the ordinary false branch.
- `rationalFamilyCoefficient` is the canonical small model of the least finite
  field, Q_l. `rationalFamilyStageSpace` computes ordinary rational cohomology
  of `constantWeilRationalComplex`; `rationalFamilyStageMap` applies homology to
  point/exchange transport followed by the functor applied to its theta.
  `rationalFamilySpace` and `rationalFamilyMap` restrict this degree-one field
  model back to Q_l, giving H^i(X,Q_l) and F_l. These are helpers owned by this
  item, not replacements for the smooth-proper-family dependency's record.
- `ordinaryConstantTensorSpace` is Ω tensor_Ql H^i(X,Q_l), in scalar-first order;
  the source's reversed order is canonically identified by the tensor commutor.
  Its map is `LinearMap.baseChange Ω` of the rational Frobenius.
- The first `∀ i : ℤ` asserts bijectivity of the constructed canonical map and
  its commuting square with the live global Qbar Frobenius. It includes negative
  degrees and all degrees outside the cohomological range.
- In `0 ≤ i ≤ 2*d`, `∃ e` states conjugacy by an Ω-linear isomorphism whose
  forward map equals the canonical comparison. `e.inv ≫ F_tensor ≫ e.hom = F_Qbar`
  is the conjugacy equation.
- For every `α : Ω`, `Module.End.HasEigenvalue` agrees in both directions and
  the characteristic polynomials' `Polynomial.rootMultiplicity α` agree. Thus
  algebraic multiplicities are asserted, including nonsemisimple operators.
- The final equality maps `rationalFamilyPolynomial`, det(1-T F_l), along
  `algebraMap ℚ_[l] Ω`, and equals det(1-T F_Qbar) on actual live cohomology.

The only postponed theorem is the item's main theorem, with its six-step DAG
proof in its docstring. All definitions have real data. Finite-dimensional
instances are constructed by the existing finite coefficient cohomology theorem,
restriction along a finite extension, tensor extension, and the constructed
comparison isomorphism. No new finiteness hypothesis is assumed.

Dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, its `CoefficientDatum` and
  `geometricFiber`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the general common-stage
  category and `AlgebraicallyClosedCoefficients.Coefficient`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, `pointQbarFibre`.
- `Sheaf.Paper.GeometricHypotheses`: `FiniteFieldDatum.IsSmoothOfPureDimension`.
- `Sheaf.Paper.GlobalGeometricFrobenius`: all five recorded declarations retained;
  in particular `globalGeometricFrobeniusQbarCohomology` and
  `globalGeometricFrobeniusQbarOnCohomology` supply the target and actual action.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`, publicly retaining
  `OrdinaryCompactCohomology`: rational, Qbar, and independently sized adic
  ordinary-cohomology conventions.
- `Sheaf.Paper.CoefficientCohomologyModules`: `coefficientFdCohomology` and
  `coefficientFdCohomology_finite`; its Qbar object/map clauses were also read.
- `Sheaf.Paper.ConstantWeilStructure`: `constantWeilRationalComplex` and
  `constantWeilAlgebraicallyClosedComplex`, including their exact carrier data.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` through the global module:
  `frobeniusCohomologyStageEmbedding`, `frobeniusCohomologyQbarSourceEq`,
  `frobeniusCoefficientModules`, and the rational and Qbar functors.
- `Sheaf.Paper.FieldCohomologyScalarExtension`: `fieldDerivedHomologyIso` read;
  its same-universe signature requires the equivalent exact-functor comparison
  here, using the actual independent-universe coefficient transport.
- `WeilConjectures.ZetaFunction.CohomologicalFamily`:
  `AlgebraicGeometry.Scheme.frobeniusCharpolyRev`, read with `scompile.py --source`.
  Its published Qbar family and every existing consumer's binding remain intact.
  Rational helpers requested by the return reside in this item's module.
- Mathlib `ModuleCat.extendScalars`, `restrictScalars`, `LinearMap.baseChange`,
  `TensorProduct`, `ShortComplex.homologyFunctorIso`,
  `DerivedCategory.homologyFunctorFactors`, `Functor.mapDerivedCategoryFactors`,
  `Module.Finite.base_change`, `Module.Finite.trans`, `Module.Finite.equiv`,
  `LinearMap.charpoly`, `Polynomial.rootMultiplicity`, and `LinearMap.det`;
  upstream `LinearMap.charpolyRev` is used for reverse characteristic polynomials.

Edge cases: i<0 and i>2d are included; d=0 has the single range degree 0.
Zero cohomology gives determinant polynomial 1 and no eigenvalues. Empty schemes
are excluded by geometric connectedness, not by an extra assumption. A Jordan
block is covered by algebraic root multiplicity, not eigenspace dimension.
Independent u/v and arbitrary chosen algebraic closures are retained. No
STATEMENT-DISPUTED issue and no statement correction.

Searches (the earlier tool results remain in searches.jsonl):

- msearch LeanSearch, scalar extension of rational ell-adic cohomology compatible
  with Frobenius: only generic field/Frobenius and p-adic scalar tower hits.
- msearch LeanFinder, ordinary ell-adic cohomology with algebraically closed
  coefficients as scalar extension: p-adic/Witt/isocrystal hits, no exact theorem.
- msearch Loogle, `LinearMap.charpoly_baseChange`: generic polynomial identity,
  only the linear-algebra tail. The initial `LinearMap.charpolyRev` query was
  unknown to the Mathlib search index; its recorded upstream source is used.
- msearch grep, `cohomology.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*cohomology|frobenius.*[Ss]calar`:
  no Mathlib comparison theorem.
- rg of the item id and scalar-extension cohomology names in upstream
  WeilConjectures and shared lean/Sheaf: ArithmeticRoots citation, no exact item.
- Repair search, rg in Mathlib DerivedCategory/ExactFunctor and ShortComplex/
  PreservesHomology: found the canonical exact-functor comparison used here.
- Repair msearch Loogle, `TensorProduct.AlgebraTensorModule.uliftEquiv`: exact
  tensor/ULift equivalence and pure-tensor equations, used for size transport.

## Returned points repaired

H3/H5+H4: Qbar target and Frobenius now use the live recorded global package on
the constant algebraically closed complex at compact=false. The comparison is
explicit and canonical, through the live object clause and exact homology
comparison. Frobenius compatibility is a theorem, not built into a local target.

H13 global Frobenius: no dependency module or node edit remains. In particular no
GlobalGeometricFrobeniusStage module is delivered, and NZ+Q127's live five-declaration
GlobalGeometricFrobenius interface is imported unchanged.

H13 smooth-proper family: no dependency module or node edit remains. The existing
frobeniusCharpolyRev record is retained; the rational space/map/polynomial helpers
are in the item's module, as the return requested. ArithmeticRoots and
WeightPurityRoots keep their existing dependency binding.

The initial saved-packet dry run rejected an unowned TestNew.lean scratch file.
That scratch file was removed after its canonical-comparison experiment was
incorporated into the owning item. No scratch module is delivered.

## Second reading by Q121

The dispatcher forbids other agents, so this is a second reading by the same
worker, not an independent review. I opened the node and final module together.
I checked every hypothesis, both ordinary actions, the live target, canonical
comparison direction, all integer degrees, range bounds, canonical normalization
of e, both eigenvalue directions, root multiplicities, and mapped determinant
polynomial. The return's two dependency rebindings are absent. I repaired the
saved packet's missing .carrier projections, explicitly bound all universes,
and used the same HasDerivedCategory instances as the live functors. The
canonical comparison now elaborates with independent u/v and no assumed map.
The maintainer's independent review remains the acceptance check.

## Resumed packet check by Q121

The required initial dry run of this retained packet found only H9: the target
cohomology docstring at line 237 exceeded 100 characters. I wrapped that docstring;
no declaration signature or construction changed. A fresh comparison with the
shared node confirms that only `lean` differs, and `lean.statement` matches the
main theorem signature verbatim. The packet contains one delivered module, one
item node, no dependency-node replacement, and exactly one `sorry`, in the main
theorem. The live GlobalGeometricFrobenius module retains all five declarations;
the target uses its Qbar cohomology and operator on the canonical constant object.
The common-stage object clause and exact-functor homology construction were read
again together with the source scalar-extension display. The two H13 rebindings
remain absent, and the rational helpers stay in the owning item module.

## Worker report

Module: `Sheaf.Paper.FrobeniusFixesUnitSection`. Main declaration:
`WeilConjectures.frobenius_fixes_unit_section`. This states F(1_E)=1_E for the
canonical constant Weil complex, using the recorded geometric Frobenius operator and
the actual unit of `ConnectedConstantH0.oneRational`. The node changes only in `lean`.

Hypothesis and conclusion correspondence:

- The entire global datum p,a,q,k_0,k is `D : FiniteFieldDatum.{u}`. Its fields include
  p prime, positive a, q=p^a, the prescribed finite cardinality, and the chosen closure.
- The prime ell, ell distinct from p, and its chosen algebraic closure are
  `c : D.CoefficientDatum`: `c.l`, `c.prime`, `c.different`, and `c.Qbar`.
- The finite extension E/Q_ell inside that closure is
  `E : Padic.FiniteCoefficientFields c.l c.Qbar`; its field is `E.val`.
- The k_0-scheme is `Y₀ : Over (Spec (.of D.k₀))`. Finite type is precisely
  `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`, and separatedness is
  `[IsSeparated Y₀.hom]`.
- The specified geometric base change is `(D.geometricFiber Y₀).left`; its projection
  is `(D.geometricFiber Y₀).hom`. No different scheme or field extension is used.
- Nonempty connectedness is `[ConnectedSpace (D.geometricFiber Y₀).left]`.
  Mathlib's ConnectedSpace explicitly includes Nonempty.
- The pair (E_Y,theta_E) is exactly
  `constantWeilRationalComplex c.l E.val D c.different Y₀`, constructed in the
  dependency from its normalized integral comparison and raw rationalization.
- The ordinary geometric Frobenius F in degree zero is the first component of
  `globalGeometricFrobeniusOnCohomology D c E Y₀ c₀ (...) 0`.
- The distinguished unit is `oneRational D c.l c.different E.val (...)`, transported
  to F's cohomology presentation by `frobeniusUnitH0Comparison`. The latter is
  uniquely fixed by coefficient projection maps, as detailed below.
- The sole conclusion applies that endomorphism to this unit and equates the result
  to the same unit. It does not replace F by an arbitrary automorphism or identify
  the unit with an arbitrary nonzero vector.

The `c₀ : Compactification Y₀.hom` argument is the retained presentation required by
GlobalGeometricFrobenius's joint ordinary/compact API. The ordinary component selects
`false`, hence its construction is independent of c₀. The theorem holds for every
such presentation; separated finite-type models admit one. Properness and smoothness
are not hypotheses.

Presentation identification supplied in the same module:

The recorded ordinary H0 unit uses the chosen `SfIntegralDirectImage` Roos object,
whereas the global operator uses the simultaneous-system direct-image realization.
They are not definitionally equal; a direct application of F to `oneRational` failed
with exactly that type mismatch. The delivery adds helpers for the presentation of
this same unit, as authorized by the brief's missing-canonical-comparison rule:

1. `frobeniusUnitIntegralImage` is the already constructed whole-system direct image
   of the actual completed regular coefficient object. It supplies the canonical
   over-base structures and the existing base-change finite-type proofs locally
   inside its definition; these are not added assumptions.
2. `frobeniusUnitFiniteComparison` is an explicit composite of existing maps:
   inverse reduction evaluation, the actual reconstruction counit, the
   section-normalized system-direct-image evaluation mate, and input reduction
   evaluation. Thus it specifies the actual map to every positive finite reduction.
3. `FrobeniusUnitH0ComparisonSpec` says that the H0 isomorphism is induced by an
   integral morphism beta intertwining these fixed maps with
   `sfDirectImageReductionComparison` of `connectedIntegralImage`. It then requires
   literal equality with H0 of beta after the recorded rationalization and point
   fibre. It neither leaves the target projection maps free nor assumes that finite
   evaluations determine an arbitrary derived morphism.
4. `frobeniusUnitH0Comparison_existsUnique` postpones the existence and uniqueness
   proof of this H0 presentation identification. Its full proof is in the docstring:
   compare the two Roos triangles with their specified projections; negative finite
   cohomology vanishes; the degree-zero Milnor sequence makes the finite projections
   jointly injective; exact scalar localization gives uniqueness on rational H0.
5. `frobeniusUnitH0Comparison` chooses only this uniquely specified isomorphism.
   No data is chosen from a bare Nonempty or an unnormalized existence assertion.

These helpers identify the two presentations of the unit already named by the item;
they do not introduce an independent mathematical notion requiring a new node. All
six declarations are recorded in `lean.declarations`. The two postponed theorems are
`frobeniusUnitH0Comparison_existsUnique` and `frobenius_fixes_unit_section`; both have
source/blueprint docstrings and complete natural-language proofs. Every definition has
real data. The main docstring gives all six steps of the DAG's finite-to-integral-to-
rational argument, and explicitly names every proof dependency.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `FiniteFieldDatum.CoefficientDatum`,
  and `FiniteFieldDatum.geometricFiber`.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with null
  module/declaration. It directs consumers to Mathlib `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated`; their full definitions were read in
  `Mathlib/AlgebraicGeometry/Morphisms/{FiniteType,QuasiCompact,Separated}.lean`.
- `def-weil-connected-scheme` is a Mathlib leaf with `ConnectedSpace`, read in
  `Mathlib/Topology/Connected/Basic.lean:705`.
- `Sheaf.Paper.ConstantWeilStructure`: `constantWeilRationalComplex`,
  `constantWeilRationalTheta`, `constantWeilIntegralObject`, and the normalized
  coefficient comparison definitions. The recorded main declaration concerns the
  algebraically closed stage; its recorded declarations also supply the finite E
  stage used here, so no dependency repair is required.
- `Sheaf.Paper.GlobalGeometricFrobenius`: `globalGeometricFrobenius` and
  `globalGeometricFrobeniusOnCohomology`, with `false` ordinary transport.
- `Sheaf.Paper.ConnectedConstantH0`: `oneRational`, `oneIntegral`,
  `connectedIntegralImage`, `connected_constant_h0`, and its actual projection and
  tensor maps.
- Helpers reuse `FrobeniusExchange.directImageFunctor`, `operationReduction`,
  `systemDirectEvaluation`, `models`, and their reduction-evaluation interfaces
  from `Sheaf.Paper.SystemOperationExchangeRealization`; plus
  `rationalOrdinaryCohomology`, `integralImage`, and the recorded
  `sfDirectImageReductionComparison`, localization and point fibre.
- All published proof-dependency modules are imported without `public`:
  `ConstantCoefficientScalarNormalization`, `FrobeniusCohomologyTransport`,
  `FrobeniusGeometricExchange`, `FrobeniusPointTransport`,
  `FrobeniusExchangeDegreeZero`, `PointProEtaleSectionsExact`,
  `SfIntegralDirectImageConstructible`, `IntegralPointTransportTowerRealization`,
  `CanonicalCoefficientPullbackReduction`, and `BasicOperationsCoefficientReduction`.

Edge cases checked before writing: empty Y is excluded exactly by ConnectedSpace;
disconnected Y is likewise excluded. Y=Spec k is included, with Frobenius acting on
the scheme while the constant coefficient 1 stays fixed. E=Q_ell is allowed. Every
prime ell different from p is allowed, including ell=2 when p differs. No assumption
ell divides q or arbitrary Tate twist is introduced. The helper index n=0 means
coefficient exponent 1, not the zero coefficient ring. Positive-dimensional,
nonproper and singular connected schemes are included. The universe is the existing
finite-field/coefficient interface's u, and neither site morphism nor object
universes are identified beyond those recorded interfaces.

Searches made in this session (the msearch wrapper also stores exact output metadata
in sandbox `searches.jsonl`):

- LeanFinder: `geometric Frobenius fixes the unit class in degree zero cohomology of
  the constant Weil sheaf`. Eight hits: arithmetic Frobenius at ideals, Witt-vector
  Frobenius/isocrystals and Hilbert 90; no pro-etale constant Weil cohomology statement.
- Loogle: `frobenius_one, globalGeometricFrobeniusOnCohomology, oneRational`.
  Zero hits; unknown identifier `frobenius_one` in that service.
- Mathlib grep through msearch, subdirectory AlgebraicGeometry:
  `frobenius.*unit|unit.*frobenius|Frobenius.*[Hh]0`. Zero hits.
- LeanSearch: `Geometric Frobenius fixes the unit class of the constant Weil sheaf
  in degree zero cohomology`. Eight hits, mainly ring-theoretic Frobenius identities,
  plus `CompHausLike.LocallyConstant.unitIso`; none match the specified operator.
- rg over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and project `lean/Sheaf`
  for `frobenius.*[Uu]nit|[Uu]nit.*[Ff]robenius|oneRational|globalGeometricFrobeniusOnCohomology`.
  Read the relevant upstream `Etale.frobeniusOperator_unit_smul_id` and
  `Etale.frobeniusOperator_unit_eq_self` in `SixFunctors/Etale/Derived/WeilFrobenius.lean`:
  they concern finite etale coefficients and Hom from that tensor unit, not this
  rational pro-etale operator defined through the specified point/exchange maps.
  Adic WeilSheaf variants also use another coefficient/cohomology construction.
- grep of the item's blueprint id in the upstream WeilConjectures tree: no hits.
- rg for the proposed main declaration name in Mathlib/upstream names/project:
  no existing declaration.

Source read: current blueprint
`main-20261015/blueprint/sec-poincare-duality/sk-lem-finite/prop-cohomological-finiteness.proof.md`,
Step 7, especially its final paragraph. The protected historical source field cites
Weil I (1.11)-(1.12); the node's reviewed note already identifies that citation as
historically inaccurate for this pro-etale computation. The proof and declaration
cite the current blueprint and use the corrected DAG proof route. No mathematical
statement correction or STATEMENT-DISPUTED flag is needed.

Validation: file-only `scompile.py` compilation in both the private sandbox and library
module positions; no errors or warnings. Auto-implicit binding is explicitly disabled.
The required deliver2.py --no-push dry run passed preflight and per-file compilation
(commit 3a05464bb7). Two pre-existing scratch modules were archived as .lean.txt files
outside the delivery Lean tree; only this module, the node record and this report are staged.

## Second reading by Q116

Author's separate second pass, not an independent review; the dispatcher explicitly
forbids sub-agents and the maintainer provides the independent reading.

Reopened the DAG statement, six proof steps, actual dependency modules and the final
module. Checked every correspondence above. The main equation uses the canonical
constant rational Weil complex, ordinary component, degree 0, and exactly the
recorded `oneRational` through a normalized H0 isomorphism. In particular connectedness
includes nonemptiness, E lies in the chosen closure, and finite type includes both
local finite type and quasi-compactness. Compactification is only a presentation
parameter of the existing operator, not a properness assumption on Y₀.

The substantive issue found was the two distinct direct-image presentations. It was
repaired with explicit finite comparison maps and a uniquely specified H0 comparison.
During the second pass I also checked that the comparison condition fixes the target's
actual finite maps: allowing an arbitrary Roos projection on the target would admit
scalar rescaling and destroy uniqueness. The final predicate uses the reconstruction
counit and normalized evaluation maps themselves, and leaves no projection free.
The postponed comparison theorem proves uniqueness only after H0 and scalar extension,
where negative finite cohomology vanishes. It makes no false assertion that reductions
detect equality of all derived morphisms. No statement, dependency record or source
file outside this sandbox was changed. Definitions are constructed; all theorem
proofs remain `sorry`.

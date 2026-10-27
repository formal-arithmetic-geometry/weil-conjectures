## Worker report

This delivery states `WeilConjectures.CoefProjectionEvaluation.projectionEvaluation`.
The conclusion supplies simultaneous, normalized module-derived adjunction and tensor
models, rather than taking their existence as a hypothesis. The maps are actual
composites in the ordinary unbounded derived categories of the prescribed sequence
sites. All theorem proofs are postponed with natural-language proofs; definition
data are real constructions or records of the stated universal properties.

Clause-by-clause correspondence:

- The coefficient binders `l`, `[Fact l.Prime]`, `E`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the prime and finite
  extension. The imported coefficient constructors give its integer ring and actual
  quotients. Index `n : ℕ` denotes exponent `n+1`, so only positive levels occur.
- `Scheme.{u}`, `ProEt.topology`, `coefficientSequenceTopology`,
  `coefficientSequenceCommRingSheaf`, `coefficientSequenceModules`, and
  `coefficientSequenceDerived` retain the existing small pro-etale presentation,
  with object universe u+1, Hom universe u and module universe u+1. The derived
  category is the standard ordinary unbounded localization, in universe u+2.
- Completed coefficients, their constant sequence and the map to the quotient
  sequence are `coefHomConstantRing`, `coefHomDerivedConstant`, and
  `coefHomScalarMap`. Scalar restriction and quotient point sections are exactly
  `coefHomPointRestriction`, `coefHomPointDerivedRestriction`,
  `coefHomQuotientSections`, `coefHomQuotientDerivedSections`. No limit is applied.
- The quotient point topos is the existing `coefHomQuotientPointModules` category.
  `pointRing` gives its commutative presentation. `pointRing_forget` identifies the
  exact quotient transition homomorphisms, and `ringMonoidal` transports the
  Mathlib pointwise module tensor through that equality. No new module category
  or independently chosen ring tower is introduced.
- The field k and its scheme structures are `[X.Over (Spec (.of k))]` and the
  analogous Y instance. Finite type is `LocallyOfFiniteType` plus `QuasiCompact`
  on both structure morphisms and on a; `a.IsOver` gives compatibility.
  `IsSeparated a`, `_hl : IsUnit (l : k)` and `c : Compactification a` are
  precisely the remaining geometric hypotheses. The compactification supplies
  the open immersion, proper map and their equality; it is fixed throughout.
- `Model.support` is the existing `CoefSupportOpenTensor.operation`, exact native
  varying-ring J followed by separately right-derived P. The fixed-ring finite
  operation is the imported `sfIntrinsicCompactSupport`.
- For arbitrary U,N, `Model.hom`, `Model.h`, `m.gy.left.obj (h U N)` and
  `Model.b` are respectively D, h, L and b. No restrictions on U,N are imposed.
- `SectionsComposition.sections` fixes ordinary composition on terminal-object
  base-change sections and `.normalization` fixes the derived composition by its
  universal units. `Model.sectionsPullback` is its adjunction conjugate.
  `Model.t` is that pullback comparison followed by the X-sections counit.
- `Model.v` tensors t by U, applies the signed derived symmetry, then the recorded
  closed evaluation. `SystemTensor.signed` uses the imported full Koszul symmetry
  predicate. `CoefficientTensorModels` retains actual Hom evaluation on K-flat /
  K-injective representatives. `PointSymmetry.signed` specifies (-1)^(pq) on each
  point-tower total summand.
- `AdjointLocalization` fixes left localization, ordinary adjunction and the
  simultaneous derived transpose equation. `TensorAdjunction.ordinary_unit`
  characterizes the ordinary comparison as the transpose of actual local pure
  tensors; `.representative` fixes the derived comparison on signed total tensor.
  `SectionsTensor`, `PushTensor` and `RestrictionTensor` fix those ordinary maps
  on every pure section and every horizontal transition. `projection` is exactly
  the existing `derivedProjectionFormulaMate`, hence the counit-defined mate.
- `Model.Pi` is the proper mate, right-derived image of the existing
  `systemGamma`, and the actual varying-ring pullback composition for c. The
  proper comparison is transported by the unique adjoint-compatible isomorphism
  to the existing native pullback, never chosen independently.
- `Model.q` is the Y-sections projection mate followed by sections applied to
  Pi and compact support of v, in the displayed order.
- `Model.balance` is the scalar restriction projection mate followed by exact
  restriction of identity tensor the scalar-extension counit.
- `Model.beta` is balance followed by restriction of the signed point symmetry
  and q. It has source restriction(h) tensor_R restriction(b_U) and target
  restriction(b_N). All these maps live on whole derived system categories;
  localization universal properties and the representative equations specify
  their descent. No finite-Tor condition or invertibility of a mate is assumed.
- `ScalarSpecialization.reduced` is Lrho_X*(const K). Its `reductionEvaluation`
  and `reductionModel` retain actual finite reductions and all quotient maps.
  Its Hom `comparison` is the existing `coefHomTower` to `coefHomScalarTower`
  comparison with the identical prescribed inverse formula from
  `coefHomTowerScalarModel`, using the normalized scalar internal-Hom adjunction.
  `supportTower` is B_K. `SupportSections` retains the actual identity on sections
  and derived-unit normalization; `supportComparison` composes it with the
  recorded compact-support point-square comparison. `transported` is beta
  preceded by that Hom comparison tensor identity, for arbitrary K and N.

Dependency declarations used: `Padic.coefficientExtensionIntegers`,
`coefficientExtensionRing`, `coefficientExtensionTransition`
(`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and public coefficient
imports); `Scheme.ProEt` (`Mathlib.AlgebraicGeometry.Sites.Proetale`);
`integralConstantToCompletionOfUniverses`
(`Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`);
`CategoryTheory.ringedSiteModules` (`Sheaf.CategoryTheory.RingedSiteModules`);
`DerivedCategory`, `HasDerivedCategory` (Mathlib derived category Basic);
`coefficientSequenceCommRingSheaf`, modules/derived/internalHom/evaluation/restriction
(`Sheaf.Paper.CoefficientRingedSequenceSite`);
`derivedInternalHomOfUniverses`
(`Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`);
`CoefficientClosedStructure`, `CoefficientTensorModels`
(`Sheaf.Paper.CoefficientRingedTensorHomModel`);
`Compactification` (`WeilConjectures.Compactification.RefinementCategory`);
`sfIntrinsicCompactSupport` (`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`);
`scalarReductionDerivedExtension`
(`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`);
`SheafOfModules.derivedProjectionFormulaMate`
(`Sheaf.Paper.ProjectionFormulaArrows`, publicly reexported by ProjectionMateExact);
`CoefSupportOpenTensor.operation`, `systemGamma`, `SectionsModel`
(`Sheaf.Paper.CoefSupportOpenTensorModel`);
`coefHomTower`, `coefHomScalarTower`, actual point restrictions and sections,
`coefHomDerivedFactorization`, `coefHomTowerScalarModel`
(`Sheaf.SixFunctors.CoefHomTowerScalarModel`). The size and scheme-property
nodes are recorded conventions and require no new declaration.

Interface diagnosis: ProjectionMateExact's RingedTensorCorner packages equal site
object/Hom universes, whereas the pro-etale site retains u+1/u. Its underlying
existing `derivedProjectionFormulaMate` is category-generic; this delivery uses it
with independently typed module categories and records the actual simultaneous
adjunction, pure-tensor and signed representative equations in the new generic module
and the item’s site-specific records.
The existing open and Hom interfaces are reused directly. No dependency statement
is weakened and no mathematical hypothesis is added to force universe equalities.

Edge cases checked: zero U or N; identity morphisms and identity compactification;
all unbounded K,U,N and arbitrary L; the n=0 index is A_1; equal-level transitions
are identities; nonflat successive quotient maps are retained as semilinear
restrictions, without exact scalar extension assumptions; scalar restriction is
exact, but tensor balancing is its counit composite and not an asserted tensor
identification; signed symmetry appears in both prescribed positions. There is
no inverse limit and no attempt to infer whole-system equality from finite values.
No statement dispute or source correction.

Searches: msearch LeanFinder for derived coefficient-system pairing by projection
mates, internal-Hom evaluation and scalar balancing; no exact match. Loogle for
`CategoryTheory.Adjunction.counit, CategoryTheory.ihom.ev` returned the generic
internal-Hom adjunction counit, not this system composite. LeanSearch for a derived
compact-support internal-Hom evaluation pairing returned generic adjunction/evaluation
declarations, not this statement. msearch grep for
`projectionEvaluation|projection_evaluation|systemProjection` found no Mathlib match.
Project rg searches over WeilConjectures and Sheaf found component mate, scalar and
open comparison interfaces, and the recorded Hom/support comparison modules, but
no theorem or construction equal to this entire word. The exact item-id search
found no prior implementation. The current blueprint paragraph 2 is the retained
mapping-complex argument before limits; supporting Stacks module adjunction,
pullback tensor, internal Hom and projection equations match the seven node steps.

## Second reading by Q19

No second worker was started, as required by the dispatcher brief. The maintainer's
independent review is the delivery review. A self rereading checked the full node
against all map sources, targets, factor orders, signs, tower scalars, reduction
transitions, and ordinary/derived normalizations; this is not represented as an
independent review. The reading checked that `Model.v` applies symmetry before
closed evaluation, `Model.Pi` applies proper projection before open gamma,
`Model.q` has b_U before h, and `Model.beta` balances h before b_U before swapping
them. It checked the scalar specialization for arbitrary ambient K and N, including
the normalized inverse Hom comparison and all reduction transitions. No mathematical
statement changes were needed. Compile repairs made only functor arguments,
additivity witnesses, scalar-model universes, and the compactification comparison’s
implicit parameters explicit.

## New nodes

`def-sf-coefficient-projection-adjunction-data` defines universal tensor localization,
ordinary and derived adjunction compatibility, the pure-tensor-normalized strong
comparison and signed-total representative square, the extracted existing projection
mate, and the derived composition unit square. Source: Stacks 06YN, 07A4, 07A6,
0B56 and 0D6E, in the stated blueprint mapping-complex construction. This general
package has independent category universes and no existence claim. LeanFinder and
LeanSearch returned generic localization/adjunction constructions; Mathlib grep and
project/DAG searches found no complete package with these equations. The new module
contains actual data declarations and functorial constructions only. All original
site-specific maps remain in the item's module.

`def-sf-coefficient-projection-point-data` packages the actual quotient point tensor,
pure-section lax maps, signed symmetry and normalized sections composition used by
the item. It uses the existing point modules and sections, never another carrier.
Source: Stacks 03EK, 06YN, 07A6, 0D6D, 0941. The recorded searches found the
component functors but no such normalized point package. Its separation keeps each
compile within the prescribed per-file limit.

Validation: all three delivered modules compiled successfully through scompile.py.
The server confirmation compiled them separately in 11.5, 40.1 and 53.4 seconds,
respectively, within the 60-second limit; no errors or unexpected warnings.

## Repair of returned delivery a18b1cbb42ad

The immutable-head review accepted the mathematics and returned H2/H12 dependency
ownership omissions. All three Lean modules and the item's mathematical statement
are unchanged. The delivery wrapper rebases this repaired packet on current main.

1. The item's stmt_deps now directly cites all seven requested landed owners:
   def-sp-varying-ring-operations (VaryingRing.push/P/G/J/adj/gComp),
   def-weil-compact-support-native-system-evaluation (compactSupportSystemLevel/Quotient),
   def-coef-native-open-tensor-evaluation-data (SystemOpenModel/systemGamma),
   def-coef-support-point-sections-data (SectionsModel and point-sections functors),
   def-zl-ringed-derived-closed-symmetric-monoidal-data (RingedDerivedTensorSymmetryModel),
   def-sfb-scalar-hom-comparison-data (ScalarHomModels, tensor comparison, Hom adjunction),
   and def-coef-derived-system-calculus-data (system tensors and reduction models).
2. def-sf-coefficient-projection-point-data now cites the five requested owners:
   def-sp-varying-ring-operations, def-weil-compact-support-native-system-evaluation,
   def-coef-semilinear-system-models, def-weil-proetale-inverse-image, and
   def-pur-sheaf-tensor-product. Its description includes each citation at the
   corresponding operation or tensor notion.
3. def-sf-coefficient-projection-adjunction-data now cites
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback, the owner identified by the
   source docstring of CategoryTheory.tensorPullbackTotal in
   Sheaf.Paper.RingedTopoiCanonicalTensorPullback. Its description explicitly names
   this existing signed-total construction in the representative square.

The newly cited modules were read against the owning node records. These are
ownership corrections, with no new hypothesis, definition, theorem or proof.
The item keeps its original statement; no statement_change is needed.

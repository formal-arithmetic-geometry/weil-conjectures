## Worker report

The delivery states `WeilConjectures.constantExtensionReturnLocalOperators` in
`Sheaf.Paper.ConstantExtensionReturnLocalOperators`, with all theorem proofs postponed.
Its auxiliary definitions have actual data. The canonical stalk isomorphism is selected
from an existence-and-uniqueness statement fixing its complete arrow formula, never from
an unqualified existence of an isomorphism. All new declarations belong to this node.

Hypotheses and clauses, matched against the node:

- The global datum is `D : FiniteFieldDatum.{u}`. It includes primality of p, a positive
  exponent, q=p^a, cardinality q, and the fixed algebraic closure. The coefficient
  hypotheses are `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`, and the field/algebra/algebraic-
  closure instances on `Ω : Type v`. Scheme and coefficient universes are independent.
- The separated finite-type model is `X₀ : Over (Spec (.of D.k₀))`, with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map.
  Positive m is `m` and `hm : 1 ≤ m`.
- The existing `constantExtensionDatum D m hm` is the datum over the actual subfield
  `D.extensionSubfield m hm`. `constantExtensionModel` is X_(0,m) over k_m;
  `constantExtensionOriginalModel` is precisely that same scheme regarded over k_0.
  Its geometric fibre is Y. `constantExtensionSheet` uses the k_m geometric fibre,
  canonically identified with X by `constantExtensionFiberIso`. Thus the domain is
  the actual iterated fibre product, rather than an unspecified isomorphic scheme.
- `ConstantExtensionSheetSpec ... R` fixes the functor on underlying carriers and
  morphisms by a natural isomorphism with distinguished-sheet pullback. Its displayed
  structure equation fixes phi as the m-fold `constantExtensionWeilIterate` composed
  with `constantExtensionReturnComparison`. Both use `zlPullComp`, whose components
  are characterized by integral representatives and their finite reductions. This
  uses the exact existing declarations now owned by
  `def-zl-constant-extension-sheet-pullback-data`; it does not use the equivalence theorem.
- The closed-point conjunct quantifies over every closed z of the actual extension
  model. It states `localClosedPointDegree D original z = m * localClosedPointDegree
  extended model z` and `Nat.card κ(z) = D.q ^ (m * ... )`. Since the extended datum
  has q-component q^m, these give both absolute residue sizes q^(mr).
- `SheetReturn.blocks` concatenates positive blocks by the ordered recursion:
  previous block composite, transport on the pulled-back input, then inverse of the
  specified compositor. The index r means r+1 blocks; no positive return is excluded.
  `SheetReturn.TransportLaws` states that this is the mr transport at every finite
  coefficient level and in the category of whole derived coefficient towers. Its
  third clause is the actual `moduleLimit`, `zeta`, `iota`, `nu` realization equation
  with only bounded constructibility of the realized input. Equality of reductions
  alone is not used. `finiteComp` uses the existing unit-normalized finite compositor;
  `towerComp` uses the strict whole-system compositor before realization.
- At an arbitrary finite rational field E, `SheetReturnRationalSpec` specifies the
  same carrier/Weil-map formula. `sheetReturnStalkIso_existsUnique` specifies the
  canonical comparison as point sections applied to pullback of alpha followed by
  the inverse prescribed compositor. It includes the equality of point-fibre
  functors for the two finite bases, `sheetReturnPointFibre_eq`. These are necessary
  presentation interfaces and contain their complete natural-language proof plans.
- `SheetReturnRationalOperators` compares the original `localFrobeniusOperator`
  recipes for the return exponent r+1 and the original exponent m*(r+1), on every
  pair of constructible finite-stage Weil sheaves identified by that specification.
  The geometric point x is on the distinguished sheet; the original point is
  literally `x ≫ constantExtensionSheet`. Both actual semilinear return equalities
  are retained. The displayed identity is c F_N = F_R c in Lean's composition order.
- `SheetReturnStalkNaturality` is the commuting square for arbitrary Weil morphisms
  f,g whose carrier maps correspond under alpha. The actual stalk arrows are
  pullbacks of `f.hom.f` and `g.hom.f` followed by the point-fibre functors.
- `SheetReturnScalarCompatibility` quantifies over every finite field extension
  `ι : E →ₐ[Padic l] L`, including the identity. `sheetReturnScalarStalk` uses the
  specified `pointRationalFibreScalarIso` and `rationalPullbackScalarComparison`.
  The carrier square relates alpha and alpha' using the same scalar/pullback map;
  the conclusion is the square for the canonical sheet stalk comparison itself.
  In particular it does not replace that comparison by an existential conjugacy.
- At common-stage Ω coefficients the closed-point operator assertion is the existing
  `ConstantExtensionLocalConjugacy ... N (R.obj N) z z 1`. It quantifies over all
  common finite Weil presentations and both residue embeddings; its actual operators
  are `localClosedFrobeniusCohomology` extended to Ω. Together with the preceding
  canonical finite-stage identities and scalar square this retains the common-stage
  construction without imposing a single coefficient field for every object.
- The isomorphism to C is `iota : Ω ≃+* ℂ`. Every w is a real number. The purity
  conjunct is the equivalence of `SfIsPunctuallyPureOfWeight` for N and its return;
  this uses the original actual local spectra and Nat.card residue-size convention.
- `PreservesFiniteLimits R` and `PreservesFiniteColimits R` express exactness on
  the existing abelian Weil hearts. `SheetReturnFiltrations` gives a subobject order
  isomorphism e with `e U = Subobject.mk (R.map U.arrow)`. It states the adjacent
  quotient isomorphism using actual cokernels of `Subobject.ofLE`, and equivalence
  of purity for every specified real weight on each quotient. For every t its eF
  is an equivalence on `Fin (t+1)`-indexed monotone subobject chains, componentwise e,
  preserving precisely the zero and total endpoints. Its inverse gives existence
  and uniqueness of the inverse filtration as subobjects. This is not uniqueness
  of arbitrarily chosen representatives of monomorphisms.
- The separate `SfIsMixedOfWeightsAtMost` equivalence retains every arbitrary upper
  weight bound. There are no lissity, semisimplicity, or Tor-amplitude assumptions.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `extensionSubfield`,
  `extensionEmbedding`, `geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, its finite stages and inclusions.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeartProperty`,
  `sfCommonStageHeartProperty`, their full heart subcategories.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilSheaf`,
  `sfCommonStageWeilSheaf`, the actual finite/common-stage Frobenius pullbacks.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlPullComp` and its integral-representative
  normalization, `zlWeilHeartAbelian`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localWeilIterate`, `localPointComplex`,
  `localFrobeniusOperator`, `localPullbackComposition`, `localClosedPointDegree`.
- `Sheaf.Paper.AdicPunctualWeights`: `SfIsPunctuallyPureOfWeight`,
  `SfIsMixedOfWeightsAtMost` and their eigenvalue/cokernel definitions.
- Definition owners for the shared constant-extension source module are now explicit:
  `def-dl-a1-constant-extension-data`,
  `def-zl-constant-extension-sheet-pullback-data` (including Spec and sheet return),
  and `def-zl-constant-extension-restriction-local-data`.
- Finite and integral power transports are owned by the two new definition records
  listed below; their source declarations and canonical normalization are unchanged.
  `pointPowerPullbackModel` is owned by the cited
  `def-trf-finite-pullback-presentation-comparison`. `finiteComp` now writes out its
  unit-normalized four-factor compositor; `finiteFibre` writes out the actual
  `SheafOfModules` coefficient category. Neither uses the returned theorem-owned alias.

Proof imports retain the recorded usable interfaces: closed-point fields, scalar
localization, finite pullback composition, whole-system powers, integral pullback
realization, iterated-return scalar calculus, local conjugacy and cyclic-return
exact equivalence. `lem-zl-constant-extension-sheet-heart-coordinates` currently has
no Lean record; it is a proof dependency only. Its result is part of the future proof
plan in the theorem docstring, with no invented replacement axiom/interface.

Edge cases checked before writing: m=1 has one block and the original one-step map;
the finite coefficient level is n+1, so n=0 means the first nonzero level; every return
exponent is r+1, including one. A zero stalk has no eigenvalue and purity is vacuous.
Repeated filtration terms have zero quotient. For t=0 the endpoint equations force
the zero object, exactly the length-zero filtration convention. The empty scheme has
no closed points. Subobject equivalences retain all repeated chains and specified real
weights, positive or negative. Scalar extension includes identity field maps. All
variables and universes are explicitly bound, with autoImplicit disabled.

Searches: msearch leanfinder queried local Frobenius/weights under constant field
extension (8 hits about arithmetic Frobenius and Witt vectors, none this statement);
msearch loogle `CategoryTheory.Subobject, CategoryTheory.Equivalence` (7 generic
subobject equivalence hits, reused subobject API); msearch grep
`sheetReturn|returnLocal|constant.extension.*[Ww]eil` (0 Mathlib hits); msearch
leansearch queried preservation of local Frobenius and pure weight filtrations
(8 finite-field algebra hits, no match). Project searches with rg for
`sheetReturn|returnLocal|constantExtensionDatum|constantExtensionModel|sheetZero` and
for the node id found the existing parent construction and related geometric modules,
not this stronger ordered-block/local-filtration statement. Upstream's
`RealSheaves/ConstantExtension.lean` is about Weil groups/representations; it is not
this result on all constructible sheaves. Searches are logged in searches.jsonl.

Source read: Deligne Weil II, printed pp. 151--154 (pdftotext), especially the paragraph
on p.152 identifying Weil-sheaf categories under change of the finite base, the local
operator definitions (1.1.7)--(1.1.10), and the weight convention. The current blueprint
unit `literature/blueprint/latest/.../sk-i-dl-general-real/_section.md` was also read.
The repair adds definition ownership records and a dependency-record repair as detailed
below. There is no mathematical statement correction or STATEMENT-DISPUTED finding.

Validation: the prescribed scompile.py checks both sandbox and final module separately
against the live server library; the latest completed check is clean. Early failures
were repaired by binding the actual derived presentation of finite point sections and
specifying canonical comparisons for the different inherited invertibility witnesses.
The definition did not need a longer compile limit or a universe equality.

## Second reading by NI

A second clause-by-clause self-reading was performed with the node and final module
open. This is not represented as an independent agent review: the dispatcher explicitly
forbids starting another agent, and the maintainer performs the independent review.
The reading caught two concrete omissions in the initial draft: a mere common-stage
conjugacy did not specify the canonical comparison, and abstract exactness alone did
not state the inverse finite filtration. The final module adds the normalized
finite-stage comparison and its actual intertwining/naturality/scalar squares, the
finite/whole-system block identities with the actual realization maps, and the
subobject order and finite-chain equivalences with quotient weights and endpoints.
Independent coefficient universes were retained by expressing Ω-local operators on
finite presentations, as the existing weight definition does. There are no hidden
finite-stage-only sheaf assumptions, and no claim of unique monomorphism representatives.
The remaining proof is deliberately sorry, as required in stage 2.

Repair validation: scompile.py compiled the repaired module in both sandbox and library
presentations with no error or warning. The final theorem signature matches the record
verbatim and the maximum Lean line width is 99. The delivery dry run also checks every
existing declaration attached by the new or repaired ownership records.


## Dependency modules

`def-zl-constant-extension-sheet-pullback-data`: §1(B), existing declaration repair.
The old lean record omitted `WeilConjectures.ConstantExtensionSheetSpec` and
`WeilConjectures.constantExtensionSheet_return`, leaving their definition ownership
with the parent equivalence theorem and hence creating the returned hidden cycle.
The repaired existing record includes precisely these canonical supporting interfaces
in `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`. Spec pins the carrier functor,
all arrows and the ordered Weil return; the equality pins the geometric map comparison.
No Lean source is copied or modified. The parent equivalence assertion remains solely
a downstream theorem. Because these definitions share its existing source module,
the reverse proof import into that source module must be omitted under the explicit
cycle exception of stages/2-statements §3.7. Definition ownership follows DAG nodes,
not the theorem named by a shared source filename. This is the ownership-record option
explicitly requested by the return.

## New nodes

`def-zl-finite-point-power-transport-data` records the already existing
`pointPowerTransportFiniteComplex` and `pointPowerTransportFinite` in
`Sheaf.TraceFormula.PointTransportComposition`, with `existing: true`.
The source is Deligne (1.1.7)–(1.1.10), interpreted through the recorded finite-coefficient
restriction and tensor-unit construction. It defines Gamma(kappa) after sigma and
its localization conjugation for every power and every positive quotient level.
The theorem stating the composition law is not a statement dependency.

`def-zl-integral-point-tower-transport-data` records the already existing construction
in `Sheaf.Paper.IntegralPointTransportTowerPowers`, with `existing: true`.
It owns whole-system pullback and sections, the section-normalized transformation,
the specified limit-cone mates zeta and nu, and integral sigma/iota, with the supporting
uniqueness/exactness interfaces needed to define those maps. It asserts none of the
power or realization laws: those remain the original theorem's proof work.
The source is the same point-transport recipe and its whole-system integral enhancement
specified by the existing tower-powers node. In particular it retains arbitrary systems,
bounded constructibility only for the realized object in nu, the entire limit counit,
and r=0; it never reconstructs a map from individual derived evaluations.

Searches for both ownership nodes: LeanSearch and LeanFinder returned eight unrelated
Frobenius/Witt/arithmetic-restriction results each; Loogle found no named declaration;
Mathlib grep had zero hits. The raw launcher results are copied to each new node.
Project grep found exactly the existing constructors now recorded, with no upstream
WeilConjectures match. DAG grep found the theorem owners, the distinct integral power
compositor, and unrelated section/return models. blueprint_refs name searches for
point-power-transport and integral-point-transport found no blueprint definition node.
Thus these nodes record existing project data, without a duplicate Lean definition.

## Returned H2 repair and second reading

Compared the retained 2b7bbcb19c20 packet with current main: the accepted mathematical
node statement and its original dependency list are unchanged on main; the packet is
rebased by preserving all current non-Lean fields. Added the six returned definition
owners directly to stmt_deps, plus the finite presentation and inverse-image comparison
owners and the two new ownership nodes. Repaired the sheet definition record as above.
Inlined `IteratedReturnTransport.finiteComposition` and
`integralOperationsFiniteModules` at their two uses, preserving their exact data.
The finite/whole tower block laws, realization, operators, canonical stalk formula,
naturality, scalar square, all real weights, degree/cardinality equations and filtration
endpoints are identical. No universe equality or hypothesis was introduced.
The original edge-case review remains applicable: m=1, r=0, n=0, zero stalks, t=0,
empty schemes, identity coefficient embeddings, and independent u/v are retained.

The final theorem signature remains verbatim in lean.statement. New definitions use
existing declarations only; the only Lean edits expand two reducible constructions
and make their presentation import explicit. The dependency graph has no edge from
this item or its new definition owners to the parent equivalence node. The shared
source import constraint is documented above rather than silently asking stage 3 to
insert a reverse import.

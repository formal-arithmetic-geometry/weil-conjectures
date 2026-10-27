## Worker report

Item: thm-pur-weil-equivariance-of-purity-and-trace. Group NC, stage 2.
The delivery states the theorem in Sheaf.Paper.WeilEquivarianceOfPurityAndTrace,
namespace WeilConjectures.PurityWeil. Its only postponed proof is the main theorem.
The helper definitions contain actual compositions, canonical comparison maps and
full-subcategory restrictions. They are coordinate helpers for this node, not
additional axioms, compatibility hypotheses, or independent replacement notions.

Source read: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
thm-pur-weil-equivariance-of-purity-and-trace.md and its proof. Also read the expanded
DAG statement and all six proof steps, the dependency node statements and recorded
interfaces, and the stage-1 resolved repair note. The node statement is unchanged.

Hypotheses and coefficient domains:

- P : PurityFiniteSetting bundles k0 finite, k its chosen algebraic closure, the
  prime ell different from the characteristic, the fixed coefficient closure,
  finite E inside it and the positive exponent n. P is arbitrary, so the finite
  clause includes every positive coefficient level and every finite E.
- X0,Y0 : Over (Spec k0), LocallyOfFiniteType, QuasiCompact and IsSeparated on their
  structure maps render separated finite-type models. f0 has exactly the separated
  finite-type morphism classes. The fibres and P.frobeniusMap are the recorded
  geometric base changes. SmoothOfRelativeDimension d with d : Nat renders pure
  relative dimension d >= 0, including d = 0.
- P.frobeniusGaloisMap and sfWeilFrobeniusPullback/common-stage counterparts are
  geometric Frobenius on the underlying schemes. No IsOver k hypothesis is imposed
  on these semilinear endomorphisms. Every inverse-image comparison uses their
  actual commuting square.
- FiniteClause quantifies over the fixed-scalar derived category with hK equal to
  finiteTorConstructible after the published intrinsic realization equivalence.
  This is exactly the existing D^b_ctf domain in equivalent coordinates, not all
  unbounded objects and not merely sheaves in degree zero.
- IntegralClause quantifies over finiteTorConstructibleIntegralCategory: modules
  over the completed integral coefficient sheaf, with the existing derived-complete,
  bounded-constructible and uniform finite-Tor predicates. integralPull uses
  integral_residue_tor only to restrict the existing pullback to this domain.
- RationalClause uses the actual localized sfRationalConstructibleCategory.
  CommonClause uses generalAlgebraicallyClosedConstructibleCategory, including all
  common-stage morphism classes. As in the recorded field-purity interface, these
  are the field coefficient ctf categories; no integral lattice carrying phi is
  assumed. Each clause quantifies over every iso phi : P K ≅ K.
- c0 and S present the compactification and coefficient-normalized adjunctions
  already used by the dependency declarations. They are universally quantified
  choices of the prescribed constructions, not assumptions of equivariance.
  integralLeft/rationalLeft and commonComparison retain their normalization.

Every definition and conclusion of the node:

- H = Lf*(-)(d)[2d] is the existing finite compositionTwistShift after pullback;
  integralH is the full-subcategory lift with exactly integralSource's object and
  arrow formula; the field clauses use RationalWeilPurity.H/CommonWeilPurity.H.
  The integral and field coordinates place the even shift on the coefficient line,
  with the canonical tensor symmetry and shift identification of the usual H.
- Gamma is geometricPurityIso at finite level, integralGamma (integralIso of the
  canonical integral trace-transpose realization), and rationalWeilPurityGamma/
  commonWeilPurityGamma. The tower-trace comparison identifies integralIso with
  normalized tower purity under the unique counit-preserving adjoint comparison.
  Thus integralGamma is the specified map, not an arbitrary lift of finite maps.
- b is geometricPuritySource at finite level; integralB uses the canonical completed
  tensor/pullback comparison, integralShiftedLine and the published normalized
  integral pullback compositors; field b is RationalWeilPurity.b/CommonWeilPurity.b.
  integralShiftedLine is completedToOrdinary, the ordinary derived shift constraint,
  then the actual ordinaryDerivedLineMap on the root line. No Gamma is used to
  define any b, and no trivialization replaces the root-tower Tate map.
- exceptionalStructure is literally inverse Q(Gamma), then b, then Gamma at PK,
  then G(phi). This is the node's E followed by G(phi), hence phi!. Its source
  structure is b followed by H(phi), hence phiPur.
- The first conjunct of ThreeSquares is Q.map Gamma.hom followed by phi! = phiPur
  followed by Gamma.hom. This is exactly the purity square, in Lean's diagrammatic
  composition convention.
- epsilon is geometricPurityCounit at finite level and the actual adjunction.counit
  of S at integral and field stages. No abstract choice of epsilon is quantified.
- BH and BG are geometricPurityB, integralBeta, or the published rational/common
  beta components, at HK and GK respectively. integralBeta conjugates the actual
  integral proper/open exchange through S.ring.integralLeft, then lifts through the
  full finite-Tor inclusion. Each compact-support structure is therefore precisely
  B_M followed by F(phi_M), as required by def-pur-compact-support-transport.
- The second conjunct is P.map epsilon followed by phi = the transported structure
  on FGK followed by epsilon. This states the exceptional-counit equivariance.
- The trace is written out as F.map Gamma.hom followed by epsilon, exactly the
  coefficient-valued normalized smooth trace. The third conjunct is its equivariance
  with the transported structure at FHK. It contains neither an extra scalar trace
  normalization nor any replacement trace map.
- The main theorem conjoins FiniteClause, IntegralClause, RationalClause and
  CommonClause. Thus every coefficient case has all three squares.

Dependency declarations used (module : names):

- Sheaf.Paper.PurityFiniteSetting : WeilConjectures.PurityFiniteSetting and its
  Ring/Coefficient fields, field/extension/level data.
- Sheaf.SixFunctors.SchemeGeometricFrobenius : frobeniusFiber, frobeniusMap,
  frobeniusGaloisMap and the canonical first square; the fixed-pair field pullbacks
  are those of Sheaf.Paper.SfWeilSheafComplex.
- Sheaf.Paper.PurityTateDatum : UniformPurityTateDatum, phiPur/phi! formulas (named
  φpur and φ! there), and the uniform strict-datum domains. The main theorem writes
  these formulas directly in their equivalent coefficient presentations.
- Sheaf.Paper.SmoothPurityMap : smoothPurityMap, its canonical tensor orientation;
  Sheaf.Paper.FiniteGeometricPurityMate : geometricPurityF, geometricPurityCounit,
  geometricPurityIso, geometricPuritySource, geometricPurityInput, geometricPurityB.
  These include the intrinsic-realization units of the recorded finite Gamma.
  Their definition owner is now def-pur-finite-geometric-comparison-data.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients :
  ConstructibleExceptionalCoefficients.System, operation, adjunction, integralLeft,
  rationalLeft, commonComparison. S's actual adjunction supplies F,G,epsilon.
- Sheaf.Paper.FiniteSmoothPullbackExchange : finiteReductionSmoothExchange and its
  inverse-purity formula; exceptionalStructure expands precisely this typed formula.
- Sheaf.Paper.FrobeniusCoefficientTwistsCanonical : completedToOrdinary,
  ordinaryDerivedLineMap, plus the root-normalized field b factors. These retain
  coefficient restriction, the roots-of-unity map and the signed shift convention.
- Sheaf.Paper.PurityCompactSupportTransport : the B followed by F(phi) definition;
  Sheaf.Paper.SmoothTrace : the F(Gamma) followed by counit trace definition.
- Sheaf.Paper.RationalSmoothPurityCanonical : integralSource_mem, pullFiniteTor,
  integralIso, rationalIso, commonIso and its shifted completed twist.
- Sheaf.Paper.RationalWeilPurityNaturalityMate : rationalWeilPurityGamma,
  commonWeilPurityGamma, RationalWeilPurity.H/b/beta/integralFrobenius/
  integralExchange and CommonWeilPurity.H/b/beta. Their definition owner is now
  def-pur-field-geometric-comparison-data. The mate theorem itself is not used
  to type the statement and is not added to stmt_deps.
- Sheaf.Paper.IntegralResidueTor : integral_residue_tor;
  Sheaf.Paper.IntegralPullbackComposition : integralPullbackComposition;
  Sheaf.Paper.CompletedPullbackTensorComparison : canonicalIntegralPullbackTensor.
  Their landed nodes are added to stmt_deps. The full-subcategory helpers only
  restrict these existing operations, without defining a second tensor or pullback.
- Mathlib AlgebraicGeometry.Morphisms.FiniteType/Proper : LocallyOfFiniteType,
  QuasiCompact and IsSeparated; Mathlib category-theory composition, mapIso and
  ObjectProperty lifts/isoMk supply the coordinate packaging.

Proof plan imports include SmoothPurityTowerGamma, IntegralAdjunctionBijection,
TowerGeometricPurityMate, SmoothPurityNormalizedEquivalence,
TowerTracePurityComparison, SmoothPurityNaturality and RationalPurityTraceCoherence.
The theorem docstring carries the complete six-step argument, including the whole-
tower requirement and the treatment of rational arrows without a stable lattice.
The integral geometric comparison realization remains a proof dependency whose
statement is not needed to form this theorem's type; no independent theorem for it
is assumed as an additional hypothesis.

Searches actually made:

- msearch.py leanfinder: "Smooth purity and exceptional counit and smooth trace are
  equivariant for geometric Frobenius on proetale sheaves" returned eight unrelated
  Mathlib hits (etale composition and differentials), no matching theorem.
- msearch.py loogle: '"IsWeilEquivariant"' returned zero hits.
- msearch.py grep: 'IsWeilEquivariant|smoothCoefficientTrace|purity.*Frobenius',
  CategoryTheory, returned zero hits.
- rg in lean/WeilConjectures for the node id and purity/Frobenius found
  EtaleCohomology/Purity/Smooth/WeilEquivariance.lean. Its etale counit and trace
  results assume hcoh identifying the exchange with the exceptional mate. They do
  not assert the canonical pro-etale four-stage statement here, so existing:true
  would lose the content of the node.
- rg in lean/Sheaf for the geometric purity source/mate, integral pullback/tensor,
  Frobenius exchange and rational/common purity found and reused the interfaces
  listed above. TwistedPullbackAdicAgreement.integralH was also checked: it is on
  the larger constructible domain, with a different tensor/shift presentation;
  integralH here is just the finite-Tor restriction of the recorded integralSource.
- The DAG search found the existing rational-weil-naturality-mate node and the
  finite/tower geometric-mate nodes; none states this complete three-square theorem.

Edge cases checked against the formulas:

- d = 0 retains the zero-fold root line and unit shift. No positive-dimension premise
  is added, and ordinaryDerivedLineMap keeps its unit normalization.
- n = 1 is allowed; n = 0 is excluded exactly by the node's positive finite
  coefficient convention, via P.level_pos rather than an arbitrary new bound.
- The empty scheme and zero object are permitted; there are no Nonempty or nonzero
  hypotheses on schemes or complexes. Morphism equations remain meaningful there.
- Arbitrary cohomological and Tor bounds are included by the existing predicates;
  no degree-zero, fixed amplitude or fixed rank restriction is introduced.
- ell equal to the characteristic is excluded by the original coefficient datum.
- Rational phi can be an isomorphism only after localization; it is quantified in
  the rational category itself. Common-stage phi may require a larger coefficient
  field; it is quantified in the entire common-stage category, not a fixed stage.
- Site sizes retain Scheme.{u}, small pro-etale objects in u+1 and morphisms in u;
  coefficients use the published lifts, with no equality of site universes imposed.

The theorem statement and all operation definitions remain as mathematically
checked by L in the return of immutable head dafcdc8aed8f. There is no statement
correction or dependency-module rebinding.

## Repair of returned delivery dafcdc8aed8f

H2: removed lem-pur-finite-geometric-purity-mate and
lem-pur-rational-weil-naturality-mate from the additions to stmt_deps. Their
main mate theorems are not needed to form this theorem's type. In their place
there are two new definition nodes with existing:true records naming exactly
the published coordinate declarations. The public imports resolve to the same
published modules; no copied declaration or alternative canonical map is added.
The module docstring identifies both definition owners.

The finite new node records geometricPurityF/Counit/Iso/Source/Input/B. The field
new node records rational/commonWeilPurityGamma, RationalWeilPurity.H/b/beta/
integralFrobenius/integralExchange and CommonWeilPurity.H/b/beta. The Gammas
retain their literal definitions as specializations of rationalIso/commonIso
of def-pur-canonical-rational-purity-realization. Their parent theorem nodes
remain untouched. The finite mate was already a proof dependency of the item;
its existing proof-dependency entry is preserved.

The two accepted genuine theorem dependencies remain: integral_residue_tor's
second conclusion is used by integralPull's membership proof, and
integralPullbackComposition.choose supplies the actual normalized compositor in
integralB. Neither is replaced by a mere definition owner.

Comparison with current main: before repair the sandbox differed from main
only in lean and stmt_deps. The repair preserves every other existing field,
including the full statement, proof, proof_deps, source and blueprint metadata.
The delivery wrapper refreshes the base and constructs the new single commit;
no direct Git mutation is used. This repair adds two definition-node files and
updates the main module's ownership documentation and this report.

## New nodes

**def-pur-finite-geometric-comparison-data.** This is the definition owner for the
finite fixed-scalar compact-support functor and counit, the canonical realized
purity isomorphism, the independent root-normalized source comparison, its
finite-Tor-domain witness, and the actual proper/open exchange with its specified
bounded-origin extension. Source: the canonical arrows in the latest blueprint
three squares and their Tate/compact-support definitions. Its existing:true
record re-exports six published declarations from
Sheaf.Paper.FiniteGeometricPurityMate, with geometricPuritySource as the primary
declaration and its signature copied verbatim. It makes no mate/equivariance
assertion and adds no Lean file. The DAG search found only the theorem node as
an owner of these helper declarations, precisely the gap identified by L.

**def-pur-field-geometric-comparison-data.** This owns the rational/common H,
canonical tensor/shift/Tate/pullback b, completed integral Frobenius and actual
compact-support exchange, normalized rational/common beta, and the two geometric-
fibre Gamma specializations. Source: the same displayed arrows at field and
completed coefficients and the coefficient transports referenced there. Its
existing:true record re-exports the ten named declarations from
Sheaf.Paper.RationalWeilPurityNaturalityMate, with rationalWeilPurityGamma as the
primary declaration and its signature copied verbatim. It retains the actual
localization and common-stage comparison components, and asserts no naturality,
mate or equivariance theorem. No Lean definition is duplicated.

New-node searches were run during this repair and are recorded as actual outputs
in both nodes' mathlib_searches. For the finite query, "Canonical geometric
Frobenius finite purity source, exceptional counit and compact support comparison
maps", LeanSearch returned eight generic Frobenius/category hits and LeanFinder
eight generic counit/pullback hits; none is this interface. For the field query,
"Canonical rational and common coefficient Frobenius purity tensor Tate
comparison and compact support exchange", LeanSearch returned eight generic
Frobenius/Witt-vector hits and LeanFinder eight purely-inseparable/tensor/support
hits. msearch grep for geometricPurity(F|Counit|Iso|Source|Input|B)|
RationalWeilPurity|CommonWeilPurity returned zero Mathlib hits. rg found no
occurrence in lean/WeilConjectures, but found the exact published definitions in
the two project modules above. DAG scans found no definition node owning them;
blueprint_refs.py search for geometricPuritySource and RationalWeilPurity each
returned zero matches. Accordingly these are existing:true records for existing
declarations, not claims that a new construction was missing from Lean.

## Second reading by NC

Independent second reading by the maintainer's cc reviewer (stage-2 review of immutable head
6a07373a2410). The worker's own clause table is kept unchanged below, as "Author self-check".

Node statement, item by item, with its Lean rendering and verdict:

1. Small pro-etale sites, purity conventions, finite field k0, its closure k, ell != p, finite E,
   A_{E,n} with n >= 1: `P : PurityFiniteSetting.{u}`, with `P.level_pos`. P is arbitrary, so
   every allowed (E, n) is covered. Correct.
2. X0, Y0 separated finite type over k0, and f0 separated finite type:
   `X₀ Y₀ : Over (Spec k₀)` with LocallyOfFiniteType/QuasiCompact/IsSeparated on the structure
   maps, and the same three classes on `f₀.left`. Correct, and no extra hypothesis.
3. f smooth of pure relative dimension d >= 0: `d : ℕ` and
   `[SmoothOfRelativeDimension d (P.frobeniusMap f₀)]`. In the field clauses it is transported to
   `zlFiberMap` by `inferInstanceAs`. d = 0 is included. Correct.
4. g_{X,γ}, g_{Y,γ}: `P.frobeniusGaloisMap` (def-pur-scheme-geometric-frobenius), and
   sfWeilFrobeniusPullback / sfCommonStageWeilFrobeniusPullback / integralP at the other stages.
   No IsOver k is required of these semilinear maps. Correct.
5. Λ in {A_{E,n}, O_E, E, Qbar_ℓ} and K in D^b_ctf: FiniteClause, IntegralClause, RationalClause
   and CommonClause, on the finite-Tor constructible, completed finite-Tor integral, localized
   rational and common-stage categories. All four are conjoined in the theorem. Correct.
6. Strict datum φ_K : P K ≅ K: each clause quantifies over every iso `phi`. The current
   def-pur-tate-datum carries no lattice condition. Correct.
7. H, b_K, τ_d: compositionTwistShift ∘ pullback with geometricPuritySource (∃!-pinned by the
   root-chart formula with target root γ(ζ)), integralH/integralB, and RationalWeilPurity.H/b and
   CommonWeilPurity.H/b. b is built from the canonical tensor-pullback map, the shift
   commutation, the root-line map and the pullback-composition square. No Γ enters b. Correct.
8. E_K = Γ_{PK} ∘ b_K ∘ (QΓ_K)^{-1}, and φ^! = Rf^!(φ) ∘ E_K: `exceptionalStructure` is
   `(Q.mapIso gamma).symm ≪≫ b ≪≫ gammaP ≪≫ gphi`, in diagrammatic order. Correct.
9. φ^pur = H(φ) ∘ b_K: `b ≪≫ hphi`. Correct.
10. Purity square: `Q.map γ.hom ≫ φ^!.hom = φ^pur.hom ≫ γ.hom`. Correct.
11. Compact-support transport φ_{FM} = F(φ_M) ∘ B_M: `BG ≫ F.map φ^!.hom` and
    `BH ≫ F.map φ^pur.hom`, with B equal to geometricPurityB, integralBeta, or rational/common
    beta. Correct.
12. Exceptional counit square: `P.map ε ≫ φ.hom = (BG ≫ F.map φ^!.hom) ≫ ε`. Correct.
13. Trace Tr^sm = ε ∘ Rf_!(γ) and its square:
    `P.map (F.map γ.hom ≫ ε) ≫ φ.hom = (BH ≫ F.map φ^pur.hom) ≫ (F.map γ.hom ≫ ε)`. Correct.

Edge cases: d = 0 (the unit line); n = 1; empty X or Y; K = 0; f = id. None is excluded.
The finite counit and B are defined by zero off the bounded-below and étale-origin domain. All
objects in the clauses (K ctf, HK, GK ≅ HK) lie inside that domain, so the equations refer to
the real maps. Universes: Scheme.{u}, ModuleCat.{u+1}, inherited site universes; no equality is
imposed.

Dependency records:
- The H2 return of dafcdc8a is repaired.
  - def-pur-finite-geometric-comparison-data re-exports, with existing:true, all six
    FiniteGeometricPurityMate declarations that the item uses.
  - def-pur-field-geometric-comparison-data re-exports all ten RationalWeilPurityNaturalityMate
    declarations that the item uses.
  - Grep of the item finds no other declaration of those modules.
  - The side-live DAG has no other def owner of these declarations.
  - Both node statements agree with the published bodies.
- The theorem stmt_deps lem-coef-integral-residue-tor and lem-pod-integral-pullback-composition
  are genuine:
  - `.2` of integral_residue_tor is the membership proof of integralPull;
  - `.choose` of integralPullbackComposition is the compositor used in integralB.
- Review fix: the finite node's lean.statement copied the signature of
  geometricPuritySourceInChart, not that of the primary declaration geometricPuritySource. It is
  now the verbatim signature, and stage2_delivery.check_existing gives no failures and no notes.
- Advisory, not changed:
  - Several definition owners of helpers are not cited in stmt_deps: def-pur-composition-comparisons,
    def-weil-derived-complete-integral-detailed, def-sf-finite-tor-integral-inclusion and others.
  - Two theorem conclusions are used inside helper proofs: lem-weil-frobenius-square-cartesian and
    lem-pur-integral-operations-preserve-constructible. They are reached through
    def-pur-scheme-geometric-frobenius and the cited integral dependencies.

### Author self-check (retained)


This is an author self-reading. The dispatched brief forbids starting another
agent and reserves independent review to the maintainer. For this repair I
reopened the latest source, the complete DAG statement, the delivered module,
and both new node records with the published definition bodies. The following
matches each hypothesis and clause; it does not substitute for independent review.

| Node hypothesis or clause | Exact Lean rendering checked | Finding in this repair |
| --- | --- | --- |
| Finite-field and coefficient conventions, ell different from p, all positive finite levels | P : PurityFiniteSetting; P.field, P.coefficients.different, P.extension, P.level_pos | Same arbitrary P; no excluded positive level. |
| Separated finite-type models X0,Y0 and model map f0 | Over (Spec (.of P.field.k0)); LocallyOfFiniteType, QuasiCompact, IsSeparated binders on X0.hom, Y0.hom, f0.left | Same binders; geometric base changes are P.frobeniusFiber and P.frobeniusMap. |
| Smooth of pure relative dimension d >= 0 | d : Nat; SmoothOfRelativeDimension d (P.frobeniusMap f0) | Same instance. The field definitions transport it locally to zlFiberMap with inferInstanceAs. |
| Actual geometric Frobenius pullbacks | P.frobeniusGaloisMap, sfWeilFrobeniusPullback, sfCommonStageWeilFrobeniusPullback, integralP | Semilinear maps; no k-linearity premise added. |
| A strict Weil datum for each K | Each clause universally quantifies phi : P.obj K ≅ K | Every iso is allowed; no lattice, finite-order or continuity hypothesis added. |
| Finite bounded constructible finite-Tor domain | FiniteClause's K and hK after sfIntrinsicDerivedEquivalence | The same finiteTorConstructible predicate and realization units. |
| Integral derived-complete uniform finite-Tor domain | IntegralClause's finiteTorConstructibleIntegralCategory | Completed coefficient category retained; integralPull uses integral_residue_tor. |
| Rational and algebraically closed domains | sfRationalConstructibleCategory and generalAlgebraicallyClosedConstructibleCategory | Actual localized/common-stage arrows, including those without a stable integral lattice. |
| Prescribed adjunction and compact support | c0 : Compactification f0.left; S : ConstructibleExceptionalCoefficients.System | Arbitrary presentations of the prescribed operations, not added equivariance data. |
| H(K) = Lf*K(d)[2d] | Finite compositionTwistShift; integralH; RationalWeilPurity.H; CommonWeilPurity.H | Same tensor, line and even-shift coordinates. |
| Canonical Gamma at K and PK | geometricPurityIso; integralGamma; rationalWeilPurityGamma; commonWeilPurityGamma | Exact same maps; new definition records supply ownership, not replacement maps. |
| Independent canonical b_K | geometricPuritySource; integralB; RationalWeilPurity.b; CommonWeilPurity.b | Root-normalized Tate map and pullback square retained; no Gamma used to manufacture b. |
| phiPur | b followed by H.mapIso phi in ThreeSquares | Correct source structure for purity and trace. |
| E followed by G(phi) = phi! | exceptionalStructure = (Q.mapIso gamma).symm ≪≫ b ≪≫ gammaP ≪≫ gphi | The inverse is exactly Q(Gamma) inverse, in the required order. |
| Purity square | First conjunct of ThreeSquares: Q.map gamma.hom ≫ phi!.hom = phiPur.hom ≫ gamma.hom | Same first displayed square. |
| Compact-support transport | BH/BG followed by F.map of the respective structure in ThreeSquares | Actual geometricPurityB/integralBeta/field beta at HK and GK. |
| Exceptional counit equivariance | Second conjunct: P.map epsilon ≫ phi.hom = (BG ≫ F.map phi!.hom) ≫ epsilon | epsilon is geometricPurityCounit or S's actual adjunction.counit. |
| Normalized smooth trace | F.map gamma.hom ≫ epsilon | Exactly the counit after purity, no scalar renormalization. |
| Trace equivariance | Third conjunct of ThreeSquares with BH and phiPur | Same second displayed square, with its specified source datum. |
| Every coefficient case | Main theorem conjoins FiniteClause, IntegralClause, RationalClause, CommonClause | All three equations at all four stages. |
| Edge cases | Nat d, P.level_pos, no Nonempty/nonzero binders | d=0, n=1, empty schemes, zero objects and arbitrary allowed amplitudes remain included. |
| Site and coefficient sizes | Scheme.{u}, ModuleCat.{u+1}, the inherited pro-etale category universes | No universe equality or size restriction introduced. |

I checked both new definition nodes clause by clause against the published
signatures and bodies. For the finite node, F/Counit/Iso/Source/Input/B correspond
in that order to its six recorded declarations; the zero extensions and both
realization units agree with the source. For the field node, H/b/beta match in
each field category, integralFrobenius/integralExchange give exactly the completed
comparison described there, and the two Gamma definitions are literal
rationalIso/commonIso specializations with the inherited geometric-fibre
instances. Neither node includes the main mate theorem in lean.declarations.
The original H2 mismatch was ownership of definitions by theorem nodes; it is
repaired by the two definition-node records and the two replacements in
stmt_deps. I found no mathematical clause mismatch and changed no map body or
main theorem signature.

Prior delivery validation: the original file compiled in 18.0 seconds. A fresh
repair compile and the prescribed dry run/delivery are run after these changes;
the fresh results are recorded below when they return.

Fresh repair validation: scompile.py succeeded for the isolated sandbox check
(20.6 seconds) and the final library module (15.9 seconds), without errors or
unexpected warnings. The two existing:true records add no Lean file to compile.

## Worker report

The module states finite evaluation and bounded site transport for the given ordinary
etale Brown adjunction. The reusable realization, finite comparison, system-site and bounded-transport
interfaces now have their own definition nodes; the only
postponed mathematical assertion is brownTowerFiniteSiteComparison.

Hypotheses: p,l are prime via Fact, p ≠ l is _hpl; k is a Field with CharP k p.
E is a finite-dimensional Padic l algebra field. t is an arbitrary integer-ring
element whose principal ideal is the recorded maximal ideal (_ht). X,Y are schemes
over Spec k; IsSeparated and LocallyOfFiniteType plus QuasiCompact on their structure
maps express separated finite type, and f.IsOver expresses that f is a k-morphism.
c : Compactification f is exactly the chosen open/proper factorization. S is the
recorded strict compact-support construction and G is the chosen Brown adjunction.
There is no extra property of f and no finite-base-field assumption.

FiniteEvaluation expresses the unbounded assertions. Ring O t n uses exponent n+1,
so all positive levels including level one occur. realizationX/Y are the exact
constant-section encoding into the fixed-module categories. lower identifies the
finite compact-support functor, right/adjunction choose its ordinary unbounded
right adjoint, and finiteRight plus finite_counit identify it with the recorded
ordinary exceptional adjoint and its counit. chi and chi_transpose specify the
invertible evaluation-extension comparison, with exactly the identity transpose
in the node's coordinates. evaluation is a natural isomorphism on the whole system
category, and counit is the evaluated counit equation. projection_mate fixes the
compact-support coefficient comparison by the actual restriction square supplied
by G. mate_def fixes the exceptional coefficient mate; transition is the equality
with the actual adjoint transition of GQ. mate_identity and mate_composition are
its quotient cocycles. No global invertibility of these unbounded mates is imposed.

Site uses the geometric inclusion Scheme.toProEt and the dependency's ordinary and
universal derived images. Its level_counit fixes the finite site adjunction
normalization. Origin means bounded below with bounded-below finite etale-origin
witnesses, and does not impose compatible choices of witnesses. ProCompact is the
proper/open composite on the actual strict pro-etale categories, fixed by geometric
inverse images, normalized derived adjunctions, and the exact open factorization.
Transport.compactComparison_evaluation fixes its bounded site comparison to the
existing canonical compactSupportSiteComparison. The unit/counit isomorphism and
fullyFaithful fields include all derived morphisms on bounded-below systems.
Transport.bound quantifies over normalized origin C, with each realized evaluation
in the existing constructibleFiniteTor property. It assumes a common lower bound
only on the finite exceptional images. It concludes the same bound on GQ and N
and normalization of N. evaluation_def is the canonical pasted evaluation formula;
it ties these isomorphisms to H.evaluation and both system site comparisons, hence
to their counits and actual transitions. The transported quotient transitions are
therefore the finite counit mates in H.transition, conjugated by these specified
site comparisons, with the same quotient cocycles. counit_formula is the actual
tower map, hom_formula describes its inverse transpose, and hom_brown identifies
this bijection with the Brown adjunction. hom_natural_left/right, hom_additive and
hom_linear state naturality and R-linearity. The scalar on an origin object is
characterized by its site counit; its existence and uniqueness follow from the
invertible site counit. No adjunction on arbitrary pro-etale objects is asserted.

Dependency declarations read and used:
- Sheaf.Paper.EtaleTowerBrownAdjunction: EtaleTowerBrownAdjunction and its theorem,
  with StrictEtaleCompactSupport, StrictEtaleEvaluation and StrictEtaleScalarAction
  reexported from the existing strict-system interfaces.
- Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint (CoefficientEvaluationModels):
  CoefficientEvaluationDerivedPackage, derivedExtension, derivedAdj, derivedBelow,
  derivedUnit, scalar, transition, derivedAssoc and their representative normalization.
- Sheaf.Paper.CoefficientSystemDerivedComparison (CoefficientSystemImageData):
  CoefficientSystemOrdinaryImage, CoefficientSystemUnboundedImage,
  CoefficientSystemDerivedImage and
  IsNormalizedCoefficientSystem. The concrete standard localizations retain the
  site's object universe u+1 and morphism universe u; these are never equated.
- Sheaf.Paper.FiniteCoefficientAdjointComparisons: nu, rnu, lower, ctf and the
  counit-normalized finite exceptional construction.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint:
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification, read at its full
  live signature (which now requires just finite coefficients and c).
- WeilConjectures.Compactification.RefinementCategory: Compactification and Refinement.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite and CoefficientExtension:
  coefficientExtensionIntegers, coefficientExtensionMaximalIdeal, and finite quotients.
- def-weil-pbc-scheme-conventions is a convention record; the listed Mathlib classes
  are used directly, as its lean.note instructs.

Edge cases checked: n=0 denotes exponent one, never R/(1). Identity quotients m=n
use derivedUnit and mate_identity. Three quotient levels use derivedAssoc and the
actual mate_composition equation. Nonflat quotient maps are allowed throughout.
Zero systems and empty schemes are included. The base field can be infinite and
of any positive prime characteristic different from l. Constructible finite-Tor
bounds may depend on n; only the stated common exceptional lower bound is assumed.
Unbounded input Q is allowed for finite evaluation; boundedness is required only
in the site-transport clauses. No smoothness or finite dimension bound is assumed.

Searches (2026-10-24):
- msearch.py leanfinder: "Evaluation of the Brown right adjoint on inverse systems
  of module sheaves equals the finite coefficient exceptional adjoint and bounded
  below etale proetale site transport"; eight unrelated condensed-module hits,
  no exact result.
- msearch.py loogle: "CategoryTheory.Adjunction, CategoryTheory.NatIso, IsIso";
  unknown identifier CategoryTheory.NatIso, no match.
- msearch.py leansearch: "Derived adjoint evaluation on coefficient systems and
  etale proetale bounded below comparison"; evaluation adjunctions and abstract
  derived-adjunction normalization, no statement about these strict systems.
- msearch.py grep: "Brown.*[Ee]val|[Ee]val.*Brown|CoefficientSystem" in
  Mathlib/CategoryTheory; no hits.
- rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  BrownTower, brownTower, finite-site-comparison and the item id: no existing
  declaration for the node. Nearby StrictEtaleExceptionalAdjoint requires a
  global invertible quotient mate on all unbounded inputs and a uniform bound;
  it is stronger and is deliberately not used as the result of this node.
- Read ConstantRingModuleSheaves, ProEtaleConstantModuleEncoding and the constant
  internal module equivalence: their RingCat/ULift/internal-action presentations
  differ from the existing CommRingCat strict-system coefficient sheaf. The helper
  levelRealization is the canonical section restriction for this recorded encoding,
  not a replacement notion or an arbitrary categorical equivalence.

The source was read in literature/blueprint/latest, in the integral-adjunction proof
and purity-transport unit, and the complete twelve-step DAG proof was checked.
No statement correction or dependency-record repair is required. Four new definition
nodes record the comparison interfaces without asserting their existence.

## Second reading by N0

Independent second reading (maintainer reviewer NT-cc, 2026-10-25); it replaces the
author's self-reading delivered at be152aa2, which was not an independent reading (H11).
The Lean was read against the node statement, the twelve-step proof and the declarations
of every statement dependency; the Lean itself is unchanged.

Node clauses and their Lean rendering (brownTowerFiniteSiteComparison):
- distinct primes p, l; field k of characteristic p: `Fact p.Prime`, `Fact l.Prime`,
  `_hpl : p ≠ l`, `Field k`, `CharP k p`. Exact.
- X, Y separated finite type over k, f a k-morphism: `X.Over`, `IsSeparated`,
  `LocallyOfFiniteType` + `QuasiCompact` of the structure maps, `f.IsOver`. Exact
  (def-weil-pbc-scheme-conventions instructs direct use of these Mathlib classes).
- E/Q_l finite, R, uniformizer t, A_n = R/t^n (n ≥ 1): `FiniteDimensional (Padic l) E`,
  `coefficientExtensionIntegers`, `_ht : span {t} = maximal ideal`; `Ring O t n` is
  O/(t)^(n+1), so all positive levels occur. `E : Type (u+1)` is the universe of the
  recorded dependency etaleTowerBrownAdjunction (and of ModuleCat.{u+1} coefficients); not a
  new restriction.
- compactification c: `c : Compactification f`.
- strict etale/pro-etale system categories, derived categories and e_n:
  `StrictEtaleCompactSupport` (S.PX, S.PY) and `ProSystem` with the standard localizations.
- F^et ⊣ G^et the chosen Brown adjunction: arbitrary `S`, `G : EtaleTowerBrownAdjunction S`
  (the dependency's records are pinned by their coherence fields), as "choose" in the node.
- f_n^× the ordinary right adjoint of thm-amb-etale-exceptional-adjoint:
  `ordinaryFiniteRight` = `rightAdjoint` of `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`
  (live signature: only `[Finite Λ]` and c), linked to `H.right n` by `finiteRight` and pinned by
  `finite_counit`.
- χ_n with identity evaluation transpose, invertible on all objects: `H.chi` (an iso) with
  `chi_transpose` = F_n(unit⁻¹ of e_nL_n ≅ 1) ≫ a_n⁻¹, as Step 1.
- natural isos e_nGQ ≅ f_n^×e_nQ for every Q (unbounded): `H.evaluation`, natural iso of
  functors on the whole derived system category.
- they identify evaluated counits with finite counits: `H.counit`, exactly the Step-4 equation.
- transition adjoint of GQ = transpose of coefficient-extended finite counit followed by the
  transition of Q; ordinary exceptional coefficient mates; quotient cocycle:
  `projection` pinned by `projection_mate` (= etaleTowerBrownRestriction), `mate` pinned by
  `mate_def` (mateEquiv of the finite adjunctions), `transition` (Step 5 equation, actual
  transitions via derivedAdj.homEquiv), `mate_identity`, `mate_composition` (with
  derivedUnit/derivedAssoc). Equalities of actual transformations. No unbounded
  invertibility of the mates is asserted (correct: the node does not assert it).
- C bounded-below normalized pro-etale system of etale origin with bounded ctf evaluations:
  `siteY.Origin C`, `IsNormalizedCoefficientSystem`, `FiniteCoefficientAdjoints.ctf` of each
  realized evaluation.
- ν^* ⊣ Rν_* and Q = Rν_*C: `Site.inverse ⊣ Site.direct` from the dependency's
  CoefficientSystemUnboundedImage along `Scheme.toProEt`, `level_counit` fixes the finite site
  counit; Q = `siteY.direct.obj C`.
- common lower bound on Rf_n^!C_n: `∃ a, ∀ n, (finiteExceptional …).obj (e_n C) ≥ a` in
  hom/counit, `∀ a, (∀ n, …) →` in `Transport.bound`; finiteExceptional = ν^*_n ∘ right n ∘
  Rν_{*,n}, which is the dependency's `upper` (rnu ⋙ etaleUpper ⋙ nu) through the pinned
  realization isomorphisms; bounds are invariant (Realization.bound).
- GQ bounded below, N = ν^*GQ bounded-below normalized: `Transport.bound` (same bound a, as
  Step 8 proves).
- canonical counit-preserving N_n ≅ Rf_n^!C_n: `D.evaluation` defined by `evaluation_def` from
  H.evaluation and the two site evaluation isos (hence counit-compatible via H.counit and
  level_counit).
- actual transported counit FN → C: `D.counit`, a morphism of derived systems fixed by
  `counit_formula` (d_{GQ} ≫ counit = ν^*ε ≫ ε^ν), with d = `compactComparison`, invertible on
  bounded-below objects (`compact_iso`) and fixed at each level by
  `compactComparison_evaluation` to the existing ProEtale.compactSupportSiteComparison.
- Hom(B,N) ≅ Hom(FB,C) natural and R-linear for bounded-below origin B: `D.hom` (an Equiv),
  `hom_formula`, `hom_brown` (the Brown homEquiv), `hom_natural_left/right`, `hom_additive`,
  `hom_linear`.
- site comparison fully faithful on bounded-below systems including morphisms:
  `fullyFaithful_X/Y`, `unit_iso_X/Y`, `counit_iso_X/Y`.
- no right adjoint on all unbounded pro-etale complexes: none asserted.

Edge cases: n = 0 is exponent 1; m = n via mate_identity; r ≥ m ≥ n via mate_composition;
nonflat quotients allowed; empty schemes and zero systems included; infinite or imperfect k
allowed; Q unbounded allowed in the finite part; bounds may vary with n except the assumed
common exceptional bound. Universes: sites object universe u+1, morphisms u; derived
categories of systems at u+2, as in the dependencies; no equation of universes imposed.

Searches: rg in lean/Sheaf and lean/WeilConjectures of side-live for BrownTowerComparison,
compact-support system comparisons and exceptional system adjoints: no clash and no
system-level canonical d. StrictEtaleExceptionalAdjoint is stronger (global unbounded
mate invertibility) and correctly not used.

Advisories (no change): `ordinaryFiniteRight`/`ordinaryFiniteAdjunction` have the body of the
dependency's `FiniteCoefficientAdjoints.etaleUpper`/`etaleAdjunction` without their
`[IsNoetherian]` arguments (definitionally the same right adjoint); `Ring` repeats
`strictEtaleBrownRing`; `levelRealization` is the site-generic form of
`Etale.SystemProjection.constantModule`; `proSystemDerived`/`proLevelDerived` repeat the
standard instances of ExceptionalSystemTransport at default priority. Citers that import both
should reuse one instance.
## New nodes

- def-pur-brown-tower-realization (BrownTowerRealization): the site-generic constant
  scalar restriction and its exact derived equivalence, with bound preservation and
  reflection. It extends the existing etale-only presentation to the actual pro-etale
  site; it uses the recorded quotient sheaf and its actual sheafification unit.
- def-pur-brown-finite-evaluation (BrownTowerFiniteEvaluation): finite adjunction and
  comparison data normalized by identity transpose, finite counits, restriction mates,
  and actual quotient transitions and cocycles. Its type asserts no existence.
- def-pur-brown-system-site (BrownTowerSite): geometric ordinary and universal system
  site images, fixed finite-site counit normalization, levelwise origin, transported
  finite exceptional functors and the geometric proper/open compact-support composite.
- def-pur-brown-bounded-transport (BrownTowerBoundedTransport): bounded site transport,
  finite evaluation normalizations, bounds and normalization, and the actual counit
  and natural R-linear Brown Hom bijection. Its type asserts no existence.

These interfaces correspond to the canonical constructions in Zheng 4.1, 4.10,
5.15, 5.16 and 5.22 and the blueprint's first integral-adjunction Hom display.
Searches of DAG nodes and the current blueprint found no complete matching interface.
Mathlib searches (LeanSearch, Loogle and grep) returned general adjunction and
sheafification APIs, all reused. The existing StrictEtaleBrownRealization specializes
to the etale site; it does not provide the site-generic realization or the complete
finite/site comparison data. The split also keeps each definition file within the
prescribed compile limit without changing the existence assertion.

Final interface reading: TransportData contains the actual maps, finite evaluation
isomorphisms, counit and Hom equivalences. Transport is their Prop-valued coherence
record with the same complete equations. The finite-ring witness is explicitly
D.finite in the final theorem, so it is conclusion data rather than an extra
hypothesis. Canonical compact-support normalization includes the explicit transports
between site and finite realizations, avoiding a silent definitional identification.

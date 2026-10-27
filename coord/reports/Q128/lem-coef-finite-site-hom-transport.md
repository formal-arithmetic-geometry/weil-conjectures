## Worker report

The module `Sheaf.Paper.CoefFiniteSiteHomTransport` states
`WeilConjectures.coefFiniteSiteHomTransport`, with its sole theorem proof `sorry`.
Its seven data/predicate helpers expand only the canonical maps and equations in
this node. There are no new mathematical objects, DAG nodes, dependency repairs,
statement corrections, or disputed statements.

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/cor-coef-finite-verdier.proof.md`, especially the evaluation,
transposed evaluation, and quotient-cocycle sentences, together with all six
expanded proof steps of this node. The theorem docstring carries those six steps.

Hypothesis and clause correspondence:

- The global datum is `(D : FiniteFieldDatum.{u})`; `(l : ℕ) [Fact l.Prime]`
  and `_hl : l ≠ D.p` are exactly the prime and distinct-characteristic conditions.
- `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`
  gives the finite extension. Every coefficient ring is the existing
  `Padic.coefficientExtensionRing l E (n + 1)`, with its recorded uniformizer
  and canonical quotient maps. The etale coefficient universe uses the recorded
  `ULift.{u+1,u}`; this changes no coefficient ring mathematically.
- `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]` binds the scheme and its structure
  morphism. The three instances `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` on that morphism say separated finite type, without properness.
- Finite ranges are represented without excluded endpoints: the Lean natural
  `N` represents the paper's upper bound `N+1`, and `i : Fin (N+1)` represents
  exponent `i.val+1`. This is precisely every nonempty finite interval of positive
  levels. `h : j.val ≤ i.val` represents every quotient including identities.
- `Ω` binds all the target objects in the ordinary etale derived categories
  `finiteHomEtale`; `_hΩ` imposes the dependency's exact
  `finiteTorConstructibleEtale` predicate at each positive exponent. There is
  no chosen common Tor bound and no assertion that boundedness implies finite Tor.
- `uΩ i j h` is the given isomorphism from the actual derived quotient extension
  of `Ω i` to `Ω j`. `_hunit` is its equality with the canonical scalar unit
  `coefFiniteSiteEtaleUnit`, rather than an ill-typed equality with an identity.
  `_hcocycle` compares direct extension followed by `uΩ i r` with the iterated
  composite, using `(finiteHomEtaleAssoc ...).hom.app (Ω i)` explicitly.
- `coefFiniteSiteTargetMap` has body
  `(coefFiniteHomSiteIso ...).inv.app W ≫ (finiteHomNu ...).map f`.
  Thus its argument `(uΩ i j h).hom` is exactly the displayed `u^p` in the node,
  not an arbitrary arrow or selected isomorphism. The target objects are exactly
  `(finiteHomNu ...).obj (Ω j)` throughout the conclusion.
- Clause (1), first conjunct: each pulled-back target satisfies the recorded
  intrinsic `finiteTorConstructible` predicate. Its next quantified clause
  preserves every Tor interval via the existing etale `hasTorAmplitudeIn` and
  intrinsic `HasProEtaleTorAmplitude`. All ordered integer bounds a ≤ b are
  quantified (the intrinsic predicate itself requires a ≤ b, so a reversed interval
  would make the clause false for a zero target).
- Clause (1), remaining conjuncts: `IsIso (coefFiniteSiteTargetMap ...)` states
  invertibility of that actual arrow. Its identity equation uses
  `coefFiniteHomProUnit`; its triple equation uses `finiteHomIntrinsicAssoc`.
  Each equation has precisely the direct and successive scalar-extension domains.
- Clause (2): `coefFiniteSiteEtaleHom` and `coefFiniteSiteProHom` are the
  displayed h-maps on the two sites. Their first factors are
  `etaleFiniteHomCanonical` and `proEtaleFiniteHomCanonical` (the existing v),
  followed by the internal-Hom functor's map of `(identity, target transition)`.
  These helper definitions exist on the ambient categories and so apply to every
  finite-Tor constructible input named in the node, on either site.
- The fifth conjunct quantifies every permitted `i,j,h` and every etale
  finite-Tor constructible `K`. `CoefFiniteSiteTargetSquare` is exactly (2),
  written in Lean's left-to-right composition order: `F(h_et) ≫ beta_j` equals
  `chi_H ≫ S_pro(beta_i) ≫ h_pro ≫ Hom(chi_K,identity)`. In particular chi_K
  has the correct direction in the contravariant Hom input. Both composites end
  at `Hom(F_j S_et K, F_j Ω_j)`.
- Clause (3): the final conjunct quantifies every level and permitted etale T.
  `CoefFiniteSitePairingTransport` first states the equality
  `tensor(beta,identity) ≫ ev_pro = mu.inv ≫ F(ev_et)`; `mu` is precisely
  `finiteHomNuTensor`, oriented from pulled-back tensor to tensor of pullbacks.
  Its second equation is `F(delta_et) ≫ beta_(D_et T) = delta_pro ≫
  Hom(beta_T,identity)`. Both delta maps are explicitly the respective closed
  transposes of signed symmetry followed by evaluation, exactly as in the node.
- The two existential symmetry families are output data, not added hypotheses.
  The etale one is fixed componentwise by `finiteHomKoszulIso`; the intrinsic
  one has `RingedDerivedTensorCoherence` on the existing K-flat total-tensor
  models (in particular its signed symmetry model). This is the same signed
  symmetry convention supplied by `coefFiniteHomSiteDescent`, not an arbitrary
  double-dual map. These witnesses only type and specify the signed symmetry
  already named in (3). No isomorphism of delta and no exceptional adjoint occurs.

Dependency declarations read and reused:

| Node/module | Declaration/interface used |
| --- | --- |
| `Sheaf.Paper.FiniteFieldFiber` | `WeilConjectures.FiniteFieldDatum` |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing`, importing the actual coefficient extension rings and quotients |
| `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` | `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact` |
| `Mathlib.AlgebraicGeometry.Morphisms.Proper` | `AlgebraicGeometry.IsSeparated` |
| `WeilConjectures.AlgebraicGeometry.DerivedCategories` | `Etale.DerivedCategoryModule` and ordinary derived cohomology conventions |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` | `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`, `finiteCoefficientDerivedComparison`; intrinsic positive-level presentation used by the recorded Hom interfaces |
| `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes` | `Etale.DerivedCategory.isBoundedConstructible` inside the recorded finite-Tor predicate |
| `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` | `Scheme.intrinsicFiniteTorsionConstructible` inside `finiteTorConstructible` |
| `Sheaf.Paper.FiniteTorAmplitudeSites` | `finiteTorConstructibleEtale`, `finiteTorConstructible`; existing etale and pro-etale interval predicates |
| `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` | Generic recorded derived-change-of-rings interface; scalar extension uses its existing positive-level specializations `finiteHomEtaleReduction` and `coefficientFiniteQuotientDerived` |
| `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` | `Scheme.proEtaleSiteComparisonModules`; actual intrinsic finite-coefficient specialization `finiteHomNu` |
| `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` | Generic `derivedInternalHomOfUniverses` and etale `derivedHom`; existing specializations `finiteHomEtaleInternalHom`, `coefficientFiniteInternalHom` and their closed structures |
| `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison` | Evaluation-defined beta, specialized to the intrinsic ring-sheaf presentation by the existing `finiteHomSiteHom` |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | `finite_duality_site_comparison`, proof's beta invertibility interface |
| `Sheaf.Paper.FiniteCoefficientHomChange` | `finiteCoefficient_derivedHom_change`, actual v maps via the published etale/pro-etale canonical transposes |
| `Sheaf.Paper.CoefFiniteHomSiteDescent` | `coefFiniteHomSiteIso`, `coefFiniteHomProUnit`, preservation, monoidal square, quotient coherence and signed symmetry witnesses |
| `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` | `CoefficientClosedStructure` with evaluation and transpose; `RingedDerivedTensorCoherence` |
| `Sheaf.Paper.ComparisonPullbackExact` | `comparisonPullbackExact`, proof import |
| `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` | `RingedDerivedComparisons.ringedDerivedMonoidalComparisons`, proof import |

Searches performed before writing:

- msearch LeanFinder: `etale proetale pullback transports coefficient compatible
  families internal Hom evaluation biduality`. Eight hits including ordinary
  `SheafOfModules.pullbackObjUnitToUnit` and LightCondensed internal Hom facts;
  none states the target-family transport or this derived scalar/site square.
- msearch Loogle: `CategoryTheory.expComparison_ev`. One hit, a Cartesian closed
  functor theorem, not this derived module-sheaf tensor setting or target family.
- msearch grep: `expComparison|dual.*[Cc]omparison` in `CategoryTheory/Monoidal`.
  Five hits in `Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean`; no match.
- msearch LeanSearch: `derived inverse image coefficient compatible target families
  Hom evaluation double dual`. Eight ordinary module-dual/evaluation hits; no match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and target-family,
  target-transport and bidual/site patterns. Existing duality/pairing modules and
  other unrelated target families were inspected; none states this lemma.
  `grep -rn` of the exact item id in `lean/WeilConjectures` returned no match.
- `rg` of the eight proposed full declaration names against Mathlib and both project
  source roots found no existing declaration. No private copy of a notion was needed.

Edge cases checked: N=0 in Lean is the singleton positive-level family (paper N=1);
all identity quotients and all repeated indices occur. The coefficient at the first
level is A_1, never A_0. Zero targets and zero T are allowed, with every Tor interval
(including reversed endpoints); no nonzero hypothesis occurs. The empty scheme is
allowed. Targets may have different Tor bounds at different levels. Arbitrary maps
u satisfying the supplied unit/cocycle assumptions are retained, not replaced by
canonical targets. The pro-etale object's universe is u+1 and its morphism universe
u throughout; the theorem does not equate them. The h equality and double-dual
identity use ambient Hom objects, so there is no unjustified extra domain condition
on the first dual.

Validation: the initial complete module compiled with no error or unexpected warning
using the prescribed `scompile.py`; the final explicit import list is checked again
by scompile and delivery preflight. No local or global build was run.

## Second reading by Q128

A second pass by the same worker reread the node, source paragraph and complete Lean
file. No separate agent was started, in accordance with the dispatcher's instruction;
the maintainer performs the independent delivery review.

Checked the hypotheses individually against the final theorem binders: the datum,
prime and inequality, finite extension, separated finite-type structure map, all
positive coefficient levels, finite-Tor target condition, target isomorphisms, scalar
unit equation, and quotient cocycle are all present. Checked each conclusion through
`CoefFiniteSiteTargetTransport`: the object and every interval clause, actual-map
invertibility, identity and triple equation, full Hom square, evaluation, and explicit
signed-evaluation transpose identity all match the node. In particular the last Hom
map in the square uses chi (not its inverse), the last double-dual Hom map is
contravariant in beta, and the evaluation equation inserts the inverse tensor
comparison on the F(evaluation) side. Both sites' h maps are actual composites.

The natural upper bound was reindexed by one to avoid a separate positivity binder
without dropping the singleton case. Symmetries are normalized output witnesses,
not assumptions and not arbitrary replacement maps. No mismatch requiring a node
correction, new node or dependency module was found. No mathematical declaration
is proved in this stage-2 module.

## Maintainer review FIX (2026-10-23)

The delivered clause (1) quantified every pair a, b. `HasProEtaleTorAmplitude`
contains the conjunct a ≤ b, while the etale `hasTorAmplitudeIn` does not; for
Ω_j = 0 and a > b the etale hypothesis holds and the pro-etale conclusion fails.
The reviewer added `a ≤ b →`, as in the landed `CoefFiniteHomDescent`. The theorem
signature and lean record are unchanged; the fixed file compiles cleanly.

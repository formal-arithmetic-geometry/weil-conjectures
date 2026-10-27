## Worker report

Item: lem-sfb-kflat-derived-adjunction-transport-shifts. Group Q87, stage 2,
2026-10-22. The module `Sheaf.Paper.KFlatDerivedAdjunctionTransportShifts` states
`AlgebraicGeometry.ProEtale.CondensedRing.kflat_derived_adjunction_transport_shifts`.
It contains one theorem with proof `sorry`, and no new definitions or proofs.

The statement has three conjuncts: the specified unit formula for every M, the
specified counit formula for every N, and `Adjunction.CommShift` for the specified
K-flat/K-injective adjunction with the existing fixed shifts. The last class has
both fields `commShift_unit` and `commShift_counit`, each quantifying over all
integers through `NatTrans.CommShift`.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| R is an arbitrary commutative condensed ring | `(R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]`. The bundled monoid has its actual `MonObj R.X` instance; no presentation by a topological ring is assumed. |
| u : X → Y is any scheme morphism | `{X Y : Scheme.{u}} (f : X ⟶ Y)`. No properness, quasi-compactness or boundedness hypotheses. |
| Coefficients R_T are pulled back from the point | `condensedRingObj R.X X` and `condensedRingObj R.X Y`, the recorded underlying objects of `coefficientRing`. |
| Mod_{R_T} consists of internal module objects | `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R.X T)`. This uses the small pro-etale site and the framework's actual internal-module category. |
| D_T is the ordinary unbounded derived category | `DerivedCategory` of those module categories. No constructible, completed, solid or bounded replacement occurs. The available framework instances select these derived categories. |
| P and G are the specified total derived functors of the full module composites | `moduleObjectDerivedPullback R.X f` and `moduleObjectDerivedPushforward R.X f`, definitionally `(upperStar R.X f).leftDerivedFunctor` and `(lowerStar R.X f).rightDerivedFunctor`. |
| A = D(u*) is exact termwise descent | `(upperStar R.X f).mapDerivedCategory`, the left functor of `mapDerivedCategoryRightDerivedAdjunction`. |
| c : P ≅ A is the canonical exact comparison | `modulePullbackExactComparison R.X f`. Its body applies the recorded `leftDerivedExactComparison` to the specified K-flat functor and its actual `leftDerivedFunctorCounit`. |
| A has termwise shifts and P has their transport through c | Existing `modulePullbackDerivedCommShift`, whose body is `Functor.CommShift.ofIso (modulePullbackExactComparison ...).symm ℤ`. A uses the existing `mapDerivedCategory.CommShift` instance. |
| G has the fixed canonical K-injective shifts | Existing `modulePushforwardDerivedCommShift`, definitionally the published `rightDerivedFunctor.CommShift ℤ`; that instance is transported from the K-injective equivalence and termwise application. |
| aP is exactly the derived ordinary module adjunction | `derivedUpperStarLowerStarAdjunction R.X f`, whose body is `(upperStarLowerStarAdjunction R.X f).derivedAdjunction`. It is never quantified over arbitrary adjunction structures. |
| aA is the exact-left/K-injective-right construction from the same ordinary adjunction | `(upperStarLowerStarAdjunction R.X f).mapDerivedCategoryRightDerivedAdjunction`. This is the published independent derived-unit construction, not a definition of aA by transport of aP. |
| The right adjoint and beta are the same for both constructions | Both definitions call `Adjunction.derived` with `(lowerStar R.X f).rightDerivedFunctorUnit`. The underlying homotopy adjunction is the same `mapHomotopyCategory (.up ℤ)`. These are fixed by the named constructions, not extra arbitrary inputs or assumptions. |
| alphaA composed with c Q_Y equals alphaP | Fixed by the counit-compatible `leftDerivedUnique` defining `leftDerivedExactComparison`, then passed from Qh to Q by `quotientCompQhIso`. Thus the canonical c is used, rather than an arbitrary natural isomorphism satisfying an extra hypothesis. `modulePullbackComplexComparison` is exactly c followed by `mapDerivedCategoryFactors`; `modulePullbackResolutionCounit` is the same comparison written from the resolution counit. |
| etaP_M = G(c_M inverse) composed with etaA_M | First conjunct, `∀ M`, is `aP.unit.app M = aA.unit.app M ≫ G.map (c.inv.app M)`. Lean's composition order agrees with this formula. |
| epsilonP_N = epsilonA_N composed with c_{GN} | Second conjunct, `∀ N`, is `aP.counit.app N = c.hom.app (G.obj N) ≫ aA.counit.app N`. |
| aP is the transport of aA along c, keeping G and beta fixed | The two preceding formulas are the node's precise assertion of transport. They determine the transported adjunction. Both adjunctions retain the same named G and beta by construction. |
| Both unit and counit commute with every fixed integer shift | Third conjunct is `Adjunction.CommShift (F := moduleObjectDerivedPullback ...) (G := moduleObjectDerivedPushforward ...) (derivedUpperStarLowerStarAdjunction ...) ℤ`. The explicit F/G arguments preserve the named instances during elaboration. No new right-adjoint shift is constructed. |

### Recorded dependencies and declarations

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPullback`
  and `moduleObjectDerivedPushforward` in
  `AlgebraicGeometry.ProEtale.CondensedRing`.
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactComparison`:
  `CategoryTheory.Functor.leftDerivedExactComparison`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStarLowerStarAdjunction`,
  `upperStar` and `lowerStar`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj` and preservation of commutativity. This module is publicly
  exposed through the recorded upper/lower-star modules.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its `ModObj`
  data, action-compatible morphisms, category structure and forgetful functor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its integer shifts.
- `Mathlib.CategoryTheory.Triangulated.Functor`:
  `CategoryTheory.Pretriangulated`, `IsTriangulated` and the shift interfaces
  through its public imports. The theorem's claim is shift compatibility,
  not a new or stronger claim of triangulated exactness.
- `Sheaf.Paper.ModuleDerivedFunctorCompositorShifts`:
  `AlgebraicGeometry.ProEtale.CondensedRing.modulePullbackExactComparison`,
  `modulePullbackDerivedCommShift`, `modulePushforwardDerivedCommShift`.
  These already landed canonical definitions are reused through the new definition
  node `def-sfb-module-derived-comparison-shifts`, with `existing: true`. This
  definition node, rather than the theorem node
  `lem-sfb-module-derived-functor-compositor-shifts`, is added to `stmt_deps`.
  Its constructions do not use that theorem's proof. No duplicate Lean definitions
  or extra module are introduced, as required by brief-stage2 sections 1 and 5.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`, used
  to name aA exactly.

The proof-only imports are the five recorded proof dependencies' modules:
`Mathlib.CategoryTheory.Functor.Derived.Adjunction`
(`Adjunction.derivedη_fac_app`),
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
(`Adjunction.mapHomotopyCategory`),
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
(`Functor.mapDerivedCategoryFactors`),
`Mathlib.CategoryTheory.Localization.Predicate`
(`Localization.fullyFaithfulWhiskeringLeft`, `Localization.natTrans_ext`), and
`Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`
(`CategoryTheory.canonicalRightDerivedAdjunctionShift`). Their natural-language
proof is carried in the theorem docstring, following all four node proof steps.

### Sources and edge cases

Read the full item and all statement dependencies' statements and recorded
interfaces; read their Lean signatures, construction bodies and docstrings.
Read Stacks `derived.tex`, lemmas `lemma-pre-derived-adjoint-functors` and
`lemma-pre-derived-adjoint-functors-general` (Tags 0DVC, 0FND), and current
blueprint `sk-thm-sfb-proper-base-change-rational.proof.md`, paragraph (3).

Checked before drafting: f = identity (the formulas reduce to the same ordinary
unit/counit under the canonical comparison); zero ring and zero modules (no
nonzero or nonempty assumption); empty schemes (every scheme is admitted);
M,N arbitrary unbounded objects (no boundedness assumption); n = 0 and negative
n (the conclusion uses ℤ, not ℕ); and scalar-twisted identity adjunctions (the
ordinary adjunction and beta must remain specified, so arbitrary adjunction
variables would be wrong). No excluded characteristic or prime assumptions.
The small site retains its object/morphism universe difference and the
coefficient category remains `Ab.{u + 1}`, as in every recorded module functor.
No extra universe equation is imposed. No statement fault or dispute was found.

### Searches

All remote searches used
`python3 /home/ubuntu/weil-launcher-all/batch2/msearch.py Q87
lem-sfb-kflat-derived-adjunction-transport-shifts <tool> <query>`.

- LeanSearch: `derived adjunction units counits preserve canonical shifts`.
  Eight hits, including `derived_unit`, `derivedη`, `shift_unit_app` and
  `CommShift.commShift_counit`. These give general construction or consequences
  after shift compatibility is supplied; none identifies the two specified
  module adjunctions under their canonical exact comparison.
- LeanFinder: `Canonical derived adjunction transport along left derived exact
  comparison with unchanged right adjoint and fixed shifts`. Eight hits,
  including `derived`, `derivedη`, `derivedε_fac_app`, `derived_unit` and
  `derived'_counit`. None states this full transport plus fixed-shift theorem.
- Loogle: `CategoryTheory.Adjunction.ofNatIsoLeft`. Five hits: transport and
  its unit/counit/Hom formulas. These define transport of an adjunction but do
  not identify the independently specified derived adjunction with it.
- Mathlib grep: `derived_counit|commShift_of_leftAdjoint` in `CategoryTheory`.
  Hits for `commShift_of_leftAdjoint` construct a shift on the right adjoint;
  they do not preserve the fixed K-injective shift demanded here.
- Project/source ripgrep: `leftDerivedExactComparison`,
  `derivedUpperStarLowerStarAdjunction.*CommShift`,
  `derived.*adjunction.*transport`, and the item id in `lean/WeilConjectures`
  and `lean/Sheaf`. No full match. Found and reused the comparison and the
  transported shifts in `ModuleDerivedFunctorCompositorShifts`. The finite
  coefficient shift theorem concerns different module categories and chooses
  an adjoint shift. `NormalizedDerivedAdjunctionTransport` uses equivalences
  and exact right functors, not the present fixed K-injective right functor;
  `PinnedDerivedAdjunctionShifts` is for ordinary structure-sheaf modules.
- Full candidate declaration name
  `kflat_derived_adjunction_transport_shifts` was checked in Mathlib/project
  sources and `dag/lean_names_upstream.json`; no declaration existed.

### Validation and final rereading

The first compile detected only an elaboration issue: asking `.CommShift` on
an adjunction whose left functor unfolds to raw `leftDerivedFunctor` did not
find the named pullback shift instance. Repaired by supplying the definitionally
identical named F and G explicitly to `Adjunction.CommShift`; no additional
hypothesis, instance, definition or mathematical change was made.

The final prescribed `scompile.py` passed both sandbox elaboration (9.0 s) and
library-artifact compilation (13.0 s). There were no errors or unexpected
warnings. Every variable/universe is explicit, `autoImplicit` is false, and
only the theorem proof is postponed.

Reread the node against the final file: both formula directions are correct;
M ranges over D_Y and N over D_X; counit c is evaluated at G N; the right
comparison is fixed by both constructions; the final class demands both
unit and counit compatibility using the existing P and G shifts. No source
statement, dependency implementation or target was changed. The maintainer's
independent delivery review remains the independent review; no other agent
was started.


## Repair of return L (immutable head a7e1c3f46510)

Repaired H2/H13: the returned packet incorrectly used the theorem node
`lem-sfb-module-derived-functor-compositor-shifts` to account for plain
construction data. The item now cites `def-sfb-module-derived-comparison-shifts`
instead. This definition node records the three exact existing definitions and
instances with `existing: true`, `module:
Sheaf.Paper.ModuleDerivedFunctorCompositorShifts`, and `lean.declarations`.
Section 5 explicitly permits an existing project declaration as a new definition
node's binding. Consequently there is no copied definition, wrapper definition,
arbitrary choice, added hypothesis, or use of the compositor theorem's proof.
The underlying published module is retained unchanged. The item's theorem
signature, proof plan, all original dependencies and ordinary/derived adjunction
choices agree with both the returned saved packet and current live source.
The saved packet's initial required dry run passed at d8fc46c0094; the ownership
repair is an additional substantive node/dependency change after that check.

## New nodes

`def-sfb-module-derived-comparison-shifts` owns the canonical exact comparison
and both fixed integer-shift structures by recording their existing declarations
in `Sheaf.Paper.ModuleDerivedFunctorCompositorShifts`. Its source is Stacks
015F/014X/05SE and `def-sfb-left-derived-exact`. Searches found precisely those
three declarations, formerly listed only as helpers of the compositor theorem;
no definition node gave this notion. This node is definition-only: it asserts
neither triangulatedness nor compatibility of an adjunction. Its data already
has complete bodies, with no postponed theorem proof used for the construction.

The definition-node hypotheses and clauses match as follows. A commutative
condensed ring is the existing generic `Λ : Sheaf (coherentTopology Profinite.{u})
Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`, the unbundled presentation of
`Profinite.CondensedRing`; arbitrary schemes and their morphism are
`{X Y : Scheme.{u}} (f : X ⟶ Y)`. Coefficients and the unbounded module categories
are those of `moduleObjectDerivedPullback/Pushforward`, using `condensedRingObj`.
The comparison clause is exactly `modulePullbackExactComparison`, whose body is
`(upperStar Λ f).leftDerivedExactComparison (upperStar Λ f).leftDerivedFunctor
(upperStar Λ f).leftDerivedFunctorCounit`. The transported pullback shift is
`modulePullbackDerivedCommShift`, with body
`Functor.CommShift.ofIso (modulePullbackExactComparison Λ f).symm ℤ`.
The fixed pushforward shift is `modulePushforwardDerivedCommShift`, with body
`inferInstanceAs ((lowerStar Λ f).rightDerivedFunctor.CommShift ℤ)`. Read the full
published K-injective instance: it transports through
`rightDerivedFunctorIsoKInjectives.symm`, independently of any adjunction.
Every definition-node `[id]` citation is listed in its `stmt_deps`; its empty
proof fields reflect that it defines data and states no new assertion.

New-node searches (2026-10-22; exact wrapper result records are in the node):
LeanSearch with the query about the canonical module comparison and fixed shifts
returned eight generic hits, including `totalLeftDerived` and
`CochainComplex.isKInjective_shift_iff`; Loogle `Functor.CommShift.ofIso`
returned that construction and its three compatibility lemmas; Mathlib grep of
the three module helper names returned zero hits. Project grep returned only
their actual declarations/usages in `ModuleDerivedFunctorCompositorShifts`;
DAG grep returned only its theorem node. Blueprint search `canonical exact
comparison` returned zero blueprint nodes. Read Stacks 015F (dual left-derived
case), 014X, 05SE and blueprint proof paragraph (3), and the complete bodies of
`leftDerivedExactComparison`, the three module helpers, both named total derived
functors, and the published K-injective shift construction.

## Second reading by Q87

Self-audit under the dispatcher's no-other-agents instruction; the maintainer
performs the independent review. Reopened both JSON nodes and the final module.
The new definition-node record gives exactly c and the two shifts used in the
item; all three are data defined before any theorem in the published module.
The item's original nine statement dependencies are unchanged; the one added
edge now points to the definition node. No statement-change record is needed:
the mathematical statement and its Lean signature did not change. The theorem
still takes an arbitrary commutative condensed ring and arbitrary scheme map,
uses the small sites with Ab.{u+1}, and has exactly the two unit/counit formulas
and fixed-shift Adjunction.CommShift conjunct. Reviewed identity maps, zero
coefficients/modules, empty schemes, unbounded objects, and zero/negative
integer shifts again; the ownership repair changes none of these cases.

Repair validation: prescribed scompile.py passed sandbox compilation (17.7 s)
and library-artifact compilation (6.8 s), with no unexpected warnings or errors.
The source-only self-check confirmed authorized item fields only, the exact
original theorem signature, and matching new-node citations/dependencies.

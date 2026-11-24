# MDA Cross-Case Report

This report synthesizes the 17 MDA cases using the D/S/P/N/U levels in MDA.md. D is an exact type-correct one-factor intervention that changes workload while preserving the mathematical obligation. An API counterfactual may be D while changing M0; it is not an M0-preserving subtree cut. Inclusive selected-subtree times are not added to direct partitions.

## Cross-case table

| Case | Producer | Gateway | Dominant amplifier and M1 evidence | Boundary/control | Level |
| --- | --- | --- | --- | --- | --- |
| Slow Derived Tensor | Independent monoidal providers with different tensorObj fields | MonoidalCategoryStruct.tensorObj field 0, then Functor.obj | 6,239,530 field calls / 62.825 s; Functor.obj and projections | Regular proposition aliases: full consumer 14,378,617 -> 428; standalone remains slow | S field/gateway; U component; S boundary |
| Derived-Completion Cone | Inline diagram and proof/instance representations; HasSheafify first difference | Functor.comp call 34, tensorObj call 44 | 9,356,262 M1 / 123.321 s; Functor.obj and CategoryStruct.comp | Named diagram: 12,220,822 -> 22; inline restores | S path; D API; U proof ownership |
| EtaleHom | Named predicate versus instantiated forall | Dependent Eq body call 3, DFunLike.coe call 709 | 2,390,795 M1; equivalence/coercion | Whole proposition transport: 3,180,470 -> 7,039 | D producer; S gateway; P field |
| FiniteBaseChange | Scheme.ProEt versus Site ordinary | Dependent Eq body call 2, CategoryStruct.comp 7823 | 130,197,227 M1; Hom/projection/eta | Whole hb transport: 239,340,712 -> 19,783; restoration slow | D producer; S gateway; P field |
| F66Adj | Specialized Over counit versus direct proposition | Eq composition argument 60 | 2,961,163 M1; equivalence and NatTrans.app | Direct counit: 3,897,905 -> 2,881; restoration slow | D producer; S gateway; P field |
| OrderedSpectral | R/H/D provider bundle | RawStratifiedLattices/Exists body | 8,320,909 M1; Quiver.Hom, Mod.Hom, Functor.obj | All-route alignment 10.11 s; each route restoration reopens timeout | S bundle; U/P fields |
| RealPushforward | charpolyRev versus localPolynomial | Polynomial coercion/field, Matrix.charmatrix, stalkObj | 8,002,209 M1; stalk direct groups | Polynomial alignment 17.34M -> 2,873; restoration slow | D API; S gateway; P/U field |
| RealPurity | Mixed polynomial/object APIs; ring leaf insufficient | Coercion/WHNF -> Matrix.charmatrix -> stalkObj | 7,988,264 M1; stalk groups 23.261 s and 20.651 s | Ring leaf N; whole-polynomial transport broad | P producer; S path |
| ImageHomCounit | Raw/wrapper endpoints | Dependent Eq -> composition -> coercion | 1,253,595 direct projection M1 | Whole alignment 6,359,958 -> 2,881; wrapper expansion 9,539,325 | S producer/gateway; P amplifier |
| IntegralComparison | Complete endpoint equation; provider leaf first difference | CategoryStruct.comp -> NatTrans.app | 6,680,881 M1 / 137.497 s | Provider-only alignment N; endpoint wrapper broad | P producer; S gateway |
| NativePullTensor | Hidden Functor.obj providers in Exists.choose | Dependent Iso binder -> Functor.obj lazy delta | 1,120,689 M1 / 48.802 s; mapBifunctor/proofs | Extracted endpoint 11.396/11.355 s -> 0; root effect U | P source; S path; U root |
| PR1556 | Concrete comm-shift versus generated congruence | Composition argument, equivalence WHNF | NatTrans.app, DFunLike.coe, equivalence | Argument-6 alignment 51.229 s -> below timer; restoration 53.273 s | S; API counterfactual |
| PR1625 | Nested app versus whole NatTrans API | Dependent body and projection | NatTrans.app and equivalence/projection | Argument-6 alignment 95.869 s -> below timer; restoration 93.567 s | S path; P field |
| PR1563 | Concrete Eq.mpr/composition versus generic helper | FullSubcategory category WHNF | CategoryStruct.comp, NatTrans.app/Iso.inv | Generic helper 68.2 -> 15.2 s; no local cut | P producer; S gateway; P owner |
| PR1624 | Concrete derived-functor composition | Functor.comp endpoint arguments 2/3 | Generated map_comp propositions, Functor.map | Abstract helper 102 -> 3.18 s; no local cut | S producer/gateway; P owner |
| PR1627 | Direct generated fields | Dependent proof and homMk/composition | Algebra.Hom and induced-Hom projections | liftOfStr 107.63 -> 9.38 s; restoration slow | S API; U field/root |
| PR2122 | Unknown diagonal/Ext/category bundle | Exists.casesOn, then Eq branches | CategoryStruct.comp 8.241 s, mapSingleArrow 8.462 s, Quiver.Hom 6.065 s M1 | No valid original-root one-factor control | U/P producer/gateway; S measured amplifier partition |

## Recurring structure

Producers recur as named versus instantiated propositions, independently built
providers and instances, concrete versus abstract functor composition, raw versus
wrapped endpoints, nested app versus whole natural-transformation APIs, direct
generated fields, and polynomial heads. Gateways recur as dependent bodies or
binders, application arguments/function heads, projection exposure, WHNF/Iota,
and lazy delta through Functor.comp, CategoryStruct.comp, NatTrans.app, or
Functor.obj. Amplifiers recur as projection chains, Functor.obj/map, NatTrans.app,
equivalence/DFunLike coercions, category composition, dependent proposition types,
and additive/Hom structures. A named definition may be only a downstream node.

## Boundaries

Effective boundaries are whole-proposition transport, whole-equality or hb
transport, direct counits, canonical polynomial heads, named regular diagrams,
abstract helpers, shared providers, and generated-field helper constructors.
They are mostly fragile: inlining a named head, restoring a concrete endpoint,
reconstructing an instance, or returning to direct generated fields reopens the
path. The claim is about comparison organization, not intrinsic mathematical
cost. RealPurity's ring leaf and IntegralComparison's provider leaf are negative
controls. NativePullTensor endpoint evidence does not transfer to its root.

## Batch 2 ledger

Existing restoration and puncture pairs for EtaleHom, FiniteBaseChange, F66Adj,
Cone, RealPushforward, PR1556, PR1625, PR1627, and OrderedSpectral were reused.
The remaining candidate outcomes were:

| Candidate | Result | Interpretation |
| --- | --- | --- |
| Cone local abbrev alias around derivedCompletionDiagram | Scratch probe prepared, but historical dependency artifacts were unavailable to the instrumented runner; no Lean result accepted | U |
| OrderedSpectral single-route alignments | Restorations reopen the slow path; no route alone fixes the original | S bundle evidence |
| RealPurity ring leaf | Left/right/both controls negative | N |
| IntegralComparison provider leaf | Provider-only control negative | N |
| ImageHom wrapper expansion | Narrow control worsens 6.36M -> 9.54M | N for spelling fix |
| NativePullTensor endpoint alignment | Succeeds at endpoint, not validly transferred to full root | D endpoint; U root |

No result is an M0-preserving local subtree cut. The Cone alias attempt is
unavailable evidence, not a causal result.

## Answers to section 9

1. Divergences come from named/instantiated propositions, independent providers,
   concrete composition/generated fields, raw/wrapper endpoints, nested app APIs,
   and polynomial heads; PR2122 is unknown.
2. First exposure is through dependent bodies/binders, application arguments,
   projection/WHNF, and lazy-delta branches.
3. Amplifiers are tensorObj, Functor.obj/map, NatTrans.app, category/Hom and
   equivalence projections, dependent proposition types, and additive fields.
4. Dominant direct M1 examples are Cone 123.321 s, SDT 62.825 s,
   FiniteBaseChange 130.197M calls, RealPushforward 8.002M, RealPurity 7.988M,
   and PR2122's three branches totaling 22.767 s. Inclusive rows are not added.
5. Boundaries are named regular definitions, whole proposition/equality transport,
   canonical polynomial heads, abstract helpers, shared providers, and generated
   field helpers.
6. Successful interventions are API-level D controls that preserve the theorem
   but change M0. No validated M0-preserving descendant-only cut exists.
7. Cost moves into a new helper/target conversion or another dependent obligation;
   changed roots prevent paired subtree ownership.
8. Functor.obj, NatTrans.app, CategoryStruct.comp, equivalence/additive projections,
   stalkObj, and provider leaves are often downstream nodes, not producers.
9. The common pattern is representation mismatch -> dependent/application gateway
   -> projection/functor/proof amplifier. Provider bundles, polynomial/object APIs,
   generated fields, and dependent recursors remain distinct families.
10. Unexplained ownership remains for SDT components, Cone proof positions and
    finalization, OrderedSpectral provider fields, NativePullTensor provider
    selection/root effect, PR1627 field-to-root mapping, PR2122 producer/gateway,
    and historical S2/pre-finalization snapshots.

Case reports and reduced traces are stored beside each row under KernelTimeouts
or PerfIssues.

## Evidence index

Each path below is relative to its repository root. The named report cites
the exact selected trace, control probe, and root serial; its adjacent mda
directory contains the reduced trace and validation.

| Case | Report and trace directory |
| --- | --- |
| Slow Derived Tensor | `KernelTimeouts/Historical/SlowDerivedTensor/EXPERIMENTS-SDTKF.md` (historical standalone study) |
| Derived-Completion Cone | `KernelTimeouts/Historical/DerivedCompletionCone/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| EtaleHom | `KernelTimeouts/EtaleHomComparisonReversedExact/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| FiniteBaseChange | `KernelTimeouts/FiniteBaseChangeRestrictionMateTransport/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| F66Adj | `KernelTimeouts/F66Adj/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| OrderedSpectral | `KernelTimeouts/OrderedSpectralRawLattices/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| RealPushforward | `KernelTimeouts/RealPushforward/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| RealPurity | `KernelTimeouts/RealPurity/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| ImageHomCounit | `KernelTimeouts/ImageHomCounit/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| IntegralComparison | `KernelTimeouts/IntegralComparisonPullbackRealizationShifts/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| NativePullTensor | `PerfIssues/Current/NativePullTensor/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| PR1556 | `PerfIssues/Old/PR1556-AmbientCounterexampleCoproducts/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| PR1625 | `PerfIssues/Old/PR1625-TensorSheaf/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| PR1563 | `PerfIssues/Old/PR1563-RawModuleScalarPullback/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| PR1624 | `PerfIssues/Old/PR1624-IntegersSheafHomologyTower/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| PR1627 | `PerfIssues/Old/PR1627-WeilSheafTransport/EXPERIMENTS-MDA.md`, adjacent `mda/` |
| PR2122 | `PerfIssues/Old/PR2122-DiagonalTraceFiniteEtaleIntegralBoundary/EXPERIMENTS-MDA.md`, adjacent `mda/` |

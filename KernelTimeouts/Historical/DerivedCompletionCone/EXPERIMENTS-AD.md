# DefEq Internal Cost Experiments: Derived-Completion Cone

Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, source
`9ba4d01f55c`. The targeted Complete.Defs import closure was rebuilt.
The observational patch is `../Anatomy/kernel/lean-v4.33.1-ad.patch`.
The exact source and compact measured trace are in `probes/anatomy/` and
`probes/ad/`. Runs used one target Lean thread, `timeout 3600`, and
`/usr/bin/time -v`. A kernel deterministic timeout is the expected result
of the original inline declaration, not a successful declaration check.

## Experiment A1: original inline final conversion

**Baseline.** The exact root is `Kernel.isDefEq` between the inferred type
of `inlineCone`'s value and its declared
`Cone (quotPowFunctor J I ⋙ tensorLeft K)` type. The source-level pair is
in `probes/anatomy/inline.lean`; the root begins under eight binders and
enters `Cone`/`Functor.comp`/`tensorLeft`. Unpatched source timed out at
1:56.34 process wall. Final counters timed out at 2:01.32 (+4.3%),
13,486,896 kB peak RSS; the near-final path trace timed out at 2:19.16
(+19.6%), 13,971,856 kB peak RSS. Both reached the same deterministic
timeout. The final counter root was 103.297 s; trace root was 123.761 s.

**Internal cost.** The counter root made 12,220,822 recursive calls,
maximum depth 111, including 76 exception exits at timeout. Exclusive
comparison was 51.471 s (49.8%), outer WHNF 51.826 s (50.2%). It made
43,167,510 WHNF requests, 25,821,810 Delta unfolds (2.081 s direct
Delta time), 24,729,507 Beta, 770,484 Zeta, and 4,248,404 projection
steps. Branch-exclusive comparison plus reduction was largest at
projection exits (40.852 s), second-WHNF exits (30.935 s), and application
exits (26.051 s). These exit labels partition the root but are not
independent mechanisms.

The disjoint dependent-labelled subtree took 38.697 s comparison plus
40.161 s reduction (78.858 s). Proposition-labelled comparison took
12.773 s plus 11.665 s reduction (24.438 s). Binder bodies nested inside
proposition types are assigned to dependent, so these labels do not say
that Pi-domain checking alone used 78.858 s. The root entered 343,920
Pi-domain comparisons and 1,177,638 measured instantiations, but direct
instantiation time was 0.322 s. There were 187,634 proposition-type
entries and 187,630 proof-irrelevance exits. The older nested
`proposition_ms=450.110 s` is overlapping diagnostic time, not a share
of the 103.297 s root.

**Component attribution.** In trace mode, the root path through
`tensorLeft K`/`MonoidalCategoryStruct.tensorObj`/`Functor.obj` argument 6
cost 122.069 s. Its argument 5 led to `CategoryStruct.comp` and took
118.101 s; within it a `DFunLike.coe`/`NatTrans.app` subtree took
105.417 s, or 85.2% of the 123.761 s trace root. Sibling argument 4
cost 3.968 s and the `Small` proposition under a `ShrinkHoms` category
path cost 8.263 s. These are nested prefix totals; only sibling subtrees
may be added. The largest individual child-exclusive times were
`CategoryStruct.comp` 688.164 ms, `Add.proj` 345.370 ms, `Eq` 331.717
ms, and `NSMul.nsmul` 330.710 ms. The top-20 calls with IDs, depths,
and paths are in `profile.txt`. The many `Functor.obj` and algebraic
Delta unfolds have small direct Delta time relative to the root.

The first five million general trace calls had 3,416,239 distinct
ordered node pairs and 1,583,761 exact repeats; repeated captured calls
contributed 0.515 s immediate exclusive time, excluding descendants.
All 187,634 captured proposition pairs were exact-distinct. The final
counters recorded 602,995,532 C++ Expr constructor outputs and
20,134,518,928 bytes of object-size proxy, omitting Lean-generated
constructors and non-Expr objects. Process RSS rose by 10,189,537,280
bytes during the root. Neither figure is live Expr memory or GC time.

## Experiment A2: measured-component ablation

`probes/ad/proof-positions.lean` walks the actual inferred/declared type
pair in the local binder context. It found 36 complete differing proof
positions. All 36 isolated proposition-type comparisons returned equal
in less than the 1 ms timer resolution. They involve `HasSheafify`,
Grothendieck abelianity, monoidal preadditivity, and derived monoidal
families; the 36 positions are not 36 equal shares of parent time.
The expensive component measured in situ is instead the nested
`tensorLeft`/`tensorObj` dependent application path above. Its individual
`CategoryStruct.comp`/`NatTrans.app` argument cannot be replaced in the
source pair while preserving the enclosing dependent telescope and exact
final obligation. The attempted local-instance control in
`probes/ad/let-provider.lean` finished in 2.29 s without a root above
100 ms; it removed the original slow root, so it is an invalid A2
ablation. No causal per-component savings figure is claimed.

## Experiment B: shared provider attempt

The existing explicit-instance control adds a
`MonoidalCategory (DerivedCategory ...)` parameter; it finished in 2.17 s
counters, versus 2.19 s unpatched source, with largest reported root
1.666 ms. The named-diagram control finished in 2.13 s in both modes,
largest counter root 0.125 ms. The local `letI` control also finished
quickly, but changed the value representation and did not enter the
original root. The explicit control changes the binder telescope, and
the named control changes the consumer's diagram term. Neither is a B0
sharing control at the original fixed root. No B1 independently rebuilt
same-path provider and B2 different-path provider can be paired with
them while retaining the exact final conversion. B is invalid here;
fast controls alone do not establish a sharing or pointer-identity
effect.

## Experiment C: dependent comparison

The in-situ trace directly identifies the dependent body under binder 8
and the nested `tensorLeft` application as the source of almost all
root time. Direct binder instantiation was 0.322 s, while the
dependent-labelled comparison/reduction subtree was 78.858 s and the
remaining proposition-labelled subtree 24.438 s in counters. The
36 isolated outer proof-position proposition types were all cheap,
yet the full root entered 187,634 generated proposition comparisons.
This supports a dependent-body and inner proposition fan-out mechanism,
not a 36-position additive explanation. The named and explicit controls
change the root, so they show disappearance of the slow obligation but
cannot quantify the cost of a single binder within that same root.

**Conclusion.** The timeout is a deep, mixed comparison/WHNF computation
concentrated in concrete derived `tensorLeft` structure comparison. The
outer 36 proof differences are cheap as isolated proposition types;
generated inner comparisons do the measured work. A2 and B cannot be
isolated with the available exact-consumer controls.

## READY2 round 2

The path, dependent-exclusive, and Expr-allocation figures above are from
READY2-4.33.1: 12,220,822 calls, 103.297 s counter root, 38.697 s dependent
comparison plus 40.161 s dependent reduction, 602,995,532 Expr constructions /
20,134,518,928 bytes, and 10,189,537,280 bytes RSS/commit delta. The path
trace root was 123.761 s; its `tensorLeft`/`Functor.obj` path reached the
105,417 ms `DFunLike.coe`/`NatTrans.app` subtree.

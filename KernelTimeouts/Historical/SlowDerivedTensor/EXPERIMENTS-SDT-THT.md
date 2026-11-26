# Slow Derived Tensor: Inside the Target Hom

This report records fresh measurements taken in the pinned historical
environment with the observational READY4.2 kernel. The original twelve
binder root and the source instance mismatch were retained. Lean processes
were run on the remote measurement server with a 3600 second timeout and at most two
simultaneous processes. Scratch was isolated in `sdt-tht/`; no shared
checkout was edited. Evidence labels are attached to every claim:

- **[Direct root evidence]**: one fresh same-root capture.
- **[Direct child replay]**: a fresh replay of an exact extracted child.
- **[API/source evidence]**: pinned source or declaration inspection.
- **[Counterfactual]**: a kernel-valid diagnostic with changed arguments.
- **[Inference]**: interpretation of measured structure.
- **[Unknown]**: not isolated by a valid measurement.

## 1. Exact target category and Hom representation (A)

The target category is

```lean
H := DerivedMonoidal DerivedCategory.Qh
  (HomotopyCategory.quasiIso
    (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))
```

`CategoryTheory.DerivedMonoidal` is a regular definition whose result type is
the target type `D`; `instCategoryDerivedMonoidal` delegates to the category
instance of `D`. **[API/source evidence]** The pinned source is equivalent to:

```lean
def DerivedMonoidal (L : C ⥤ D) (W : MorphismProperty C) := D
instance : Category (DerivedMonoidal L W) := inferInstanceAs (Category D)
def toDerivedMonoidal : C ⥤ DerivedMonoidal L W := L
```

`DerivedCategory C` is `HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`.
For the Grothendieck-abalian instance used by this consumer, the chosen
`HasLocalization` is built by `hasLocalizationOfLocallySmall`; its object type
is `ShrinkHoms` applied to the standard quotient localization. Since
`ShrinkHoms` is a type alias, the object type exposes as the same quotient
type, while its category instance is the small-Hom instance described below.
**[API/source evidence]** The inner localization category is a
`CategoryTheory.Quotient` of the localization relation. Its Hom implementation
is:

```lean
Quotient.Hom r s t := Quot (HomRel.CompClosure r s.as t.as)
```

Thus the exact target Hom has the layered form

```lean
Quiver.Hom H X Y
  = Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  = Shrink (Quot (HomRel.CompClosure localizationRelation X.as Y.as))
```

up to the definitional aliases and category projections. A target morphism is
therefore a small-model (`Shrink`) wrapper around a quotient class of an
inner source-category morphism, modulo the equivalence closure of the
localization relation; it is not a roof or a fraction record in this
representation. **[API/source evidence]** The inner category composition uses
`Quotient.comp`, which eliminates the two quotient classes and re-embeds their
composite with `Quot.mk`; the outer `ShrinkHoms` composition uses `equivShrink`
around that inner composition. **[API/source evidence]**

`ShrinkHoms C` is a type alias for `C`. Its category instance replaces each
Hom by `Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)` and uses
`equivShrink` for identity and composition. **[API/source evidence]** The
declaration

```lean
CategoryTheory.ShrinkHoms.instCategory._proof_1
```

has type

```lean
∀ (C : Type u₃) [Category.{u₂,u₃} C]
  [LocallySmall.{u₁} C],
  (X Y : ShrinkHoms C),
  Small.{u₁,u₂} (fromShrinkHoms X ⟶ fromShrinkHoms Y)
```

It is a proof field used to supply the `Small` witness required by the
`Shrink` Hom construction. It is not target morphism data. **[API/source
evidence]**

Pinned source locations are: `DerivedMonoidal` and
`instCategoryDerivedMonoidal` in
`FromJoel/CategoryTheory/Monoidal/Derived.lean:35-39`;
`DerivedCategory` in
`Mathlib/Algebra/Homology/DerivedCategory/Basic.lean:87-88`;
the `ShrinkHoms` category and `_proof_1` in
`Mathlib/CategoryTheory/EssentiallySmall.lean:130-168`;
the quotient localization and its category in
`Mathlib/CategoryTheory/Localization/Construction.lean:105-157`;
the selected localization aliases in
`Mathlib/CategoryTheory/Localization/HasLocalization.lean:52-75`;
the Grothendieck instance that chooses the small-Hom localization in
`WeilConjectures/CategoryTheory/GrothendieckAbelian/HasDerivedCategory.lean:72-84`;
and `Qh` in `Mathlib/Algebra/Homology/Localization.lean:173-178`.
**[API/source evidence]**

| Layer | Exact representation | Fresh observation |
|---|---|---|
| `DerivedMonoidal` | regular type definition reducing to `D` | alias exposure DefEq true, 0 ms in the fresh target probe **[Direct child replay]** |
| `DerivedCategory` | `HomologicalComplexUpToQuasiIso` | source declaration inspected **[API/source evidence]** |
| target category | `instCategoryDerivedMonoidal`, delegated `Category D` | category arguments occur on both sides **[Direct child replay]** |
| `Quiver.Hom` | category Hom of the localization category | head is `Quiver.Hom/4` **[Direct child replay]** |
| localization Hom | `Quot (HomRel.CompClosure r X.as Y.as)` | inner quotient implementation **[API/source evidence]** |
| `ShrinkHoms` | Hom is `Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)` | outer target Hom layer **[API/source evidence]** |
| target morphism | `equivShrink` of an inner quotient class | no roof/fraction constructor exposed **[API/source evidence]** |

## 2. `Qh.map` transport (B)

The fresh probes recovered the exact source functors and the instantiated
uncurried map body. The left and right source functors are the same printed
syntax but have unequal elaborated expressions. Their first operational
divergence is the monoidal-category argument of `curriedTensor`; the left
side is `HomotopyCategory.MonoidalCategory.instMonoidalCategory`, while the
right side is `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures`.
The universe-instantiated `HomotopyCategory.quasiIso` is also unequal.
**[Direct child replay]**

The exact uncurried map body is:

```lean
(F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
```

The fresh result has head `CategoryTheory.CategoryStruct.comp/7`, with
`NatTrans.app/8` as the first argument and `Functor.map/8` as the second.
The fresh expression sizes of the complete body were 561,239 and 482,697
nodes without sharing. **[Direct child replay]**

At the `Qh` definition, `Qh` is `HomologicalComplexUpToQuasiIso.Qh`, defined
as `CategoryTheory.Quotient.lift _ HomologicalComplexUpToQuasiIso.Q ...`.
The chosen localization functor itself is the quotient functor followed by
`ShrinkHoms.equivalence.functor`; the generic quotient lift defines its inner
map by `Quot.liftOn hf (fun f => F.map f)`. Therefore `Qh.map m` produces an
outer `equivShrink` of the inner quotient-lifted image of the represented
source morphism. **[API/source evidence]** The fresh selected map output is
typed as `Quiver.Hom` and retains the target object/category arguments; no
separate roof, fraction, or normalization constructor appears. **[Direct
child replay; API/source evidence]**

The fresh target probe measured:

| Operation | Fresh result |
|---|---:|
| complete map-body DefEq | 13,135 ms wall **[Direct child replay]** |
| target Hom type comparison | 621 ms wall **[Direct child replay]** |
| alias-left/right/both exposure checks | 0 ms each **[Direct child replay]** |
| same pair with morphism arguments shared | 1,089 ms wall **[Counterfactual]** |
| same pair with all selected object and morphism arguments shared | 0 ms wall **[Counterfactual]** |

The `Qh.map` delta itself was not isolated as a separate timer in this
probe; the expensive number is comparison of the resulting target morphism
terms. **[Unknown]** The output comparison still exposes the source
`quasiIso` and monoidal-instance mismatch, so transport carries the mismatch
into the target quotient Hom. **[Direct child replay; Inference]**

## 3. Pre-transport versus post-transport (C)

The fresh exact source-functor comparison (`F_L` versus `F_R`) succeeded in
142 ms and reached the unequal `curriedTensor` monoidal instance and unequal
universe-instantiated `quasiIso`. **[Direct child replay]** This is a source
provider comparison, not a separately constructed common-typed pair of the
two individual `whiskerRight` morphisms.

The post-transport exact map comparison took 13,135 ms in the fresh target
probe. Its first selected structural divergence is the same source-side
`HomotopyCategory.quasiIso`/monoidal-instance path under a target
`CategoryStruct.comp`; the target Hom type itself compared in 621 ms.
**[Direct child replay]**

| Comparison | Fresh measurement | First expensive divergence |
|---|---:|---|
| source provider `F_L ≟ F_R` | 142 ms | `curriedTensor` monoidal instance and `quasiIso` universes **[Direct child replay]** |
| target map body | 13,135 ms | same source mismatch under `CategoryStruct.comp` **[Direct child replay]** |
| target Hom type | 621 ms | dependent target quotient/category parameters **[Direct child replay]** |
| target map with shared morphisms | 1,089 ms | residual object/type context **[Counterfactual]** |
| target map with shared objects and morphisms | 0 ms | no remaining selected mismatch **[Counterfactual]** |

The source mismatch is already visible before transport, and the target
comparison adds a large dependent-context workload. A numerical subtraction
of “transport overhead” is invalid because the source and target checks share
recursive descendants and caches. **[Inference]**

## 4. `ShrinkHoms.instCategory._proof_1` (D)

The declaration is the `Small` witness for the original Hom type before it is
shrunk. It is reached while the target Hom type is formed through the
`ShrinkHoms` category instance and its `Hom` field. **[API/source evidence]**
The fresh target map Hom comparison took 621 ms, while the full map body took
13,135 ms; the fresh `map_comp` equality-carrier Hom comparison took 625 ms.
**[Direct child replay]**

The declaration is proof/data at the typeclass level, not a proposition proof
that is used as a target morphism. The fresh probes did not expose a separate
event-level exclusive timer for `_proof_1`; assigning its entire Hom-type
time to that declaration would be unsound. **[Unknown]** The supported
conclusion is that `_proof_1` is a necessary small auxiliary gateway in the
Hom type, not the main 13-second morphism-term comparison. **[Inference]**

## 5. Target object provenance and dependent endpoints (E)

The target objects are produced by `curriedTensor.obj` and then by the
`Qh`/`toDerivedMonoidal` target functor. The fresh map body has unequal
`DerivedMonoidal` object expressions and unequal `Quiver.Hom` type hashes,
although both Hom types compare successfully. **[Direct child replay]**
The target objects are therefore dependent inputs to the Hom type; they are
not an independent morphism carrier.

The all-arguments-shared counterfactual reaches sub-millisecond resolution,
whereas sharing only morphisms leaves 1,089 ms. **[Counterfactual]** This
shows that object-dependent endpoints are necessary for a measurable
residual, but they are not sufficient to explain the 13,135 ms original map
comparison. **[Inference]** Aligning only the tensor object does not remove
the source-derived morphism path in the established source controls.
**[API/source evidence from prior control; not a new number]**

## 6. Target Hom, morphism, and composition costs (F)

The fresh selected target composition has a cheap head relative to its
arguments: the body head is `CategoryStruct.comp/7`, while the full body is
13,135 ms and the target Hom type is 621 ms. **[Direct child replay]** The
same-root baseline remains the non-overlapping attribution reference:

| Same-root subtree | Calls | Exclusive time |
|---|---:|---:|
| root | 6,239,533 | 63.617 s |
| `U.obj` | 56,018 | 0.721 s |
| `U.map` | 1,902,386 | 18.956 s |
| `U.map_id` | 84,173 | 0.846 s |
| `U.map_comp` | 4,196,856 | 43.090 s |

The root-wide aggregate for `CategoryStruct.comp` head delta was only 0.017 s
and is not a charge for its argument descendants. **[Direct root evidence
from baseline instrumentation]** The fresh map replay identifies the dominant
argument as `NatTrans.app/8` (13,116 ms selected comparison), with the inner
`Functor.map/8` at 629 ms. **[Direct child replay]** These replays overlap
with the full map comparison and must not be added to it.

## 7. `map_comp` amplification (H)

The fresh `map_comp` replay found five pointer-shared binder domains: three
`Prod` object domains followed by two `Quiver.Hom` domains. Each domain
comparison completed at 0 ms. **[Direct child replay]** The conclusion was an
equality in a target `Quiver.Hom`.

| Occurrence | Fresh expression / timing |
|---|---|
| equality carrier | `Quiver.Hom`, 625 ms **[Direct child replay]** |
| LHS mapped morphism | one `CategoryStruct.comp`, 14,233 ms **[Direct child replay]** |
| RHS first map argument | `NatTrans.app` 13,811 ms and inner map 672 ms **[Direct child replay]** |
| RHS second map argument | final RHS composition 25,696 ms; its two intermediate compositions each 14,242/14,256 ms **[Direct child replay]** |
| final RHS result type | same target `Quiver.Hom` carrier and dependent endpoints **[Direct child replay]** |

The RHS is more expensive because it contains two separately transported
uncurried maps inside a final target composition, while the LHS contains one
uncurried map of the product composite. The fresh replay difference is
11,463 ms (25,696 minus 14,233), but this is a replay difference, not a
non-overlapping same-root charge. **[Inference; Direct child replay]** The
same target Hom type is structurally repeated under distinct morphism
arguments; the binder domains themselves are pointer-shared. **[Direct child
replay]**

## 8. G controls and interaction

| Control | Fresh outcome | Changes original M0? |
|---|---|---|
| G1 shared morphism arguments | 1,089 ms in target map replay **[Counterfactual]** | Yes, diagnostic only |
| G2 shared objects and morphisms | 0 ms resolution **[Counterfactual]** | Yes, diagnostic only |
| G3 source provider comparison | 142 ms **[Direct child replay]** | No, exact source diagnostic |
| G4 shared target endpoints | not separately type-correctly isolated in this probe **[Unknown]** | N/A |
| G5 aligned source provider | prior kernel-valid aligned control is millisecond-scale **[API/source evidence from prior control]** | Yes, counterfactual |
| G6 alias exposure | 0 ms checks; target quotient pointer shared after exposure **[Direct child replay]** | No, transparency diagnostic |
| G7 alternative target representation | no valid type-preserving alternative available **[Unknown]** | N/A |

These controls show that source-derived morphisms account for most of the
selected target comparison, while object-dependent Hom endpoints account for
a measurable residual. They do not quantify an intrinsic penalty of an
alternative target category because no such valid intervention exists.
**[Inference; Unknown]**

## 9. §14 decision outcome

**Outcome E (mixed source/transport/target interaction), with Outcome C’s
target-dependent component and no independent Outcome B proof.** **[Inference]**

The source mismatch is directly present before transport (142 ms provider
comparison and the unequal monoidal-instance/quasiIso branches), and the
post-transport target map comparison is much larger (13,135 ms). **[Direct
child replay]** The target Hom carrier is measurable but comparatively small
(621–625 ms), while target composition heads are cheap and their source-
derived arguments dominate. **[Direct child replay; Direct root evidence]**
Sharing morphisms reduces the target map to 1,089 ms, and sharing objects as
well reaches sub-millisecond resolution. **[Counterfactual]** Therefore the
target is the context in which the source mismatch is compared, with
dependent target objects/Homs contributing a residual; the data do not show
that the `DerivedMonoidal` wrapper or the target Hom carrier independently
creates the main slowdown. **[Inference]**

## 10. Remaining unknowns

1. A non-overlapping same-root split of the two RHS intermediate maps was not
   captured; replay timings overlap. **[Unknown]**
2. A separately timed `Qh.map` delta reduction, distinct from comparison of
   its quotient output, was not isolated. **[Unknown]**
3. No valid type-preserving alternative target category representation was
   available for an intrinsic target amplification experiment. **[Unknown]**
4. The exact exclusive event time of
   `ShrinkHoms.instCategory._proof_1` inside the full root was not isolated;
   the 621/625 ms figures are Hom-type replay totals, not a charge to the
   proof witness. **[Unknown]**

## 11. Final questions, answered

1. **Concrete target morphism:** an outer `Shrink`/`equivShrink` wrapper around
   a `Quot` class in `Quot (HomRel.CompClosure localizationRelation X.as Y.as)`,
   exposed as `Quiver.Hom` through the chosen localization category.
   **[API/source evidence]**
2. **`_proof_1`:** the `Small` witness used by `ShrinkHoms.instCategory` to
   construct `Shrink` Hom sets; reached through target Hom formation.
**[API/source evidence]**
3. **`Qh.map`:** `Qh` is `Quotient.lift`; map is `Quot.liftOn` of the
   represented source morphism through the inner localization functor,
   followed by the chosen `equivShrink` outer map. **[API/source evidence]**
4. **Pre-transport cost:** the exact source provider pair costs 142 ms in the
   fresh replay and already diverges at the source monoidal instance/quasiIso.
   **[Direct child replay]**
5. **Post-transport cost:** the exact target map replay costs 13,135 ms;
   sharing morphisms reduces it to 1,089 ms. **[Direct child replay; Counterfactual]**
6. **Objects and Hom types:** target object expressions differ; target Hom
   type comparison is 621 ms, and sharing objects plus morphisms removes the
   selected work. **[Direct child replay; Counterfactual]**
7. **Hom carrier contribution:** measurable at 621–625 ms, but far below the
   13–26 second target morphism comparisons. **[Direct child replay]**
8. **Composition:** the head is cheap; source-derived composition arguments
   are expensive. **[Direct root evidence; Direct child replay]**
9. **`map_comp`:** RHS repeats target Hom/morphism work in two independently
   constructed uncurried maps; binder domains are pointer-shared.
   **[Direct child replay]**
10. **Additional RHS descendants:** the two `NatTrans.app` outer-map paths
    and their target compositions account for the fresh 25,696 ms RHS replay.
    **[Direct child replay]**
11. **Amplifier status:** target Hom/object dependencies are a dependent
    residual and transport context; the main work follows the source
    mismatch. An independent target representation multiplier is unquantified.
    **[Inference; Unknown]**
12. **Evidence boundary:** root totals and same-root exclusive times are
    direct root evidence; exact map/Hom/map-comp numbers are direct child
    replays; shared-argument and aligned-provider results are counterfactuals;
    causal wording about interaction is inference. **[Evidence classification]**


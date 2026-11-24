# MDA: PR2122 finite-etale integral boundary

Case: `PR2122-DiagonalTraceFiniteEtaleIntegralBoundary`
Lean / Mathlib: Lean 4.35.0 / pinned current measurement tree
Root declaration: `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteEtale_integralBoundary`
Source snapshot: `1ef1fddac73` (the historical `Before.lean` probe)

## Measurement validity

The original theorem value was checked with all 14 theorem binders, 12 local
lets (`T`, `E`, `A`, `S`, `M`, `L`, `y`, `f`, `beta`, `hb'`, `hE`, `hd`), and
the original dependent `Exists.casesOn` motive and witness context. No final
branch was extracted. The MDA root is `36801`; the exact root pair is retained
in the reduced trace. The new field-aware trace has a complete aggregate
partition, although its bounded raw window entered 136 calls.

## 4.1 Gateway-to-cost

The root is an `Eq` whose three arguments are the non-overlapping cost
partitions below. M1 exclusive time is from aggregate rows; selected subtree
times are inclusive and must not be summed.

| Gateway ID | Parent M0 path | Kernel branch/component | Exact child pair | Source/API candidate | M1 calls | M1 exclusive time | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| `36801:3` | `Eq` argument 0 | application / `argument[0]` | `Quiver.Hom` / `Quiver.Hom` | derived-category hom endpoint; source owner unresolved | 277,200 | 6,065.050 ms | S for measured partition; P for source role |
| `36801:339957` | `Eq` argument 1 | application / `argument[1]` | `SpTowerClasses.mapSingleArrow` / same | map-single-arrow / Ext endpoint path | 652,939 | 8,461.597 ms | S for measured partition; P for source role |
| `36801:1206456` | `Eq` argument 2 | application / `argument[2]` | `CategoryStruct.comp` / `CategoryStruct.comp` | category composition endpoint | 819,137 | 8,240.809 ms | S for measured partition; P for source role |
| `36801:1206457` | argument 2 | second WHNF / WHNF-Iota exposure | `EquivLike.coe` / `EquivLike.coe` | downstream equivalence representation | 819,137 | inclusive 8,496.954 ms | S for path; overlapping |
| `36801:339958` | argument 1 | lazy delta / `argument[15]` | `Ext.hom` / `Ext.hom` | downstream Ext hom representation | 652,931 | inclusive 8,487.242 ms | S for path; overlapping |
| `36801:7` | argument 0 | lazy delta / `argument[1]` | `Functor.obj` / `Functor.obj` | nested functor object path | 138,598 | inclusive 4,826.371 ms | S for path; overlapping |

The complete root totals are 2,227,198 calls, 1,749,276 M1 calls, and
23,180.333 ms comparison-exclusive time. M1 accounts for 22,767.456 ms
(98.2%). M2 is 12,631 calls / 351.939 ms.

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen at | Kernel path | M1 subtree calls | M1 exclusive time | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `Exists.casesOn` motive/witness interface | expansion boundary candidate | root | dependent recursor | not separable | not separable | no valid branch-local control | U |
| `Quiver.Hom` over `DerivedCategory` | cost amplifier candidate | `36801:3` | application argument 0 | 277,200 | 6,065.050 ms | none valid | S for cost partition, P for role |
| `SpTowerClasses.mapSingleArrow` | cost amplifier candidate | `36801:339957` | application argument 1 | 652,939 | 8,461.597 ms | none valid | S for cost partition, P for role |
| `CategoryStruct.comp` | cost amplifier candidate | `36801:1206456` | application argument 2 | 819,137 | 8,240.809 ms | none valid | S for cost partition, P for role |
| `EquivLike.coe` -> `Equiv.toFun` -> `Function.comp` | downstream amplifier | `339958` / `1206457` | WHNF-Iota exposure | overlapping | overlapping | none valid | S for path |
| `Functor.obj`, `Prefunctor.obj` | downstream amplifier | `36801:7` / `15` | lazy delta/application | 138,596 in selected branch | inclusive 4,822.400 ms | none valid | S for path |
| `AddCommGroup` -> `AddGroup` -> `SubNegMonoid` projections | downstream field path | `36801:108` | projection[0] chain | 9,053 in selected subtree | inclusive 2,613.692 ms | none valid | S for path |

The trace source field remains `unknown`: the Kernel could not prove a user
declaration from the supplied namespace prefix. Therefore these rows identify
exact Kernel expression/API path nodes, not demonstrated source authorship.

## 4.3 Root-to-source causal chain

```text
Source theorem with concrete DiagonalAb/sheaf-category, derived-category,
functor-composition, ring, and Ext constructions
  -> original dependent Exists.casesOn value with 14 binders and 12 lets
  -> exact root Eq/Eq pair (M0; first printed root pair is ReflQuiver.toQuiver
     on the inferred side versus CategoryStruct.toQuiver on the expected side)
  -> Eq argument 0/1/2 application gateways
  -> Quiver.Hom, SpTowerClasses.mapSingleArrow, CategoryStruct.comp
  -> EquivLike.coe / Equiv.toFun / Function.comp and Functor.obj paths
  -> AddCommGroup/AddGroup/SubNegMonoid projection chains
  -> 1,749,276 M1 calls and 22,767.456 ms M1 exclusive time
```

The first root pair and all child pairs are directly measured. The link from
the source constructions to the first divergence is **U/P**: the source
snapshot names the concrete data, but no pre-finalization expression or
type-correct one-factor replay identifies which source choice produced the
`ReflQuiver.toQuiver` versus `CategoryStruct.toQuiver` representation.

## 4.4 MISMATCH-TO-DEFINITION ATTRIBUTION REPORT

| Case | Mismatch producer | Expansion gateway | Cost amplifier | Best one-factor intervention and effect | Evidence |
| --- | --- | --- | --- | --- | --- |
| PR2122 | Unknown; concrete category/functor/Ext bundle is only a source-guided hypothesis | Dependent `Exists.casesOn` interface, then Eq argument application; first measured large descendants are `CategoryStruct.comp` and `mapSingleArrow` | `CategoryStruct.comp` (8.241 s M1), `SpTowerClasses.mapSingleArrow` (8.462 s M1), and `Quiver.Hom` (6.065 s M1), with equivalence/functor/projection descendants | No valid original-root-preserving one-factor intervention. Extracting the final branch changes the dependent motive and is invalid. The broad split/factored module is an API-level counterfactual only; its speedup cannot be assigned to this root. | Producer/gateway U/P; amplifier S measured partition |

### Root details

1. **Mismatch producer**

   Source/API choice: not demonstrated. The source uses concrete diagonal
   finite-etale/integral-boundary data and a dependent `obtain` pattern. The
   exact first divergence visible in the checked root is
   `ReflQuiver.toQuiver` versus `CategoryStruct.toQuiver` inside the `Eq`
   proposition. Evidence: **U/P**.

2. **Expansion gateway**

   The original recursor boundary is `Exists.casesOn`; its final branch type
   depends on the motive and witness. The first large measured M1 gateways
   after the root are application argument 2 (`CategoryStruct.comp`) and
   application argument 1 (`SpTowerClasses.mapSingleArrow`), followed by
   WHNF exposure of `EquivLike.coe` and `Equiv.toFun`. Evidence: **S** for
   the measured Kernel path, **U/P** for the source-level gateway.

3. **Cost amplifier**

   The three Eq argument subtrees partition the M1 cost: 277,200 / 6,065.050
   ms for `Quiver.Hom`; 652,939 / 8,461.597 ms for `mapSingleArrow`; and
   819,137 / 8,240.809 ms for `CategoryStruct.comp`. Nested paths include
   `Ext.hom`, `EquivLike.coe`, `Equiv.toFun`, `Function.comp`, `Functor.obj`,
   `Prefunctor.obj`, and a measured `AddCommGroup` projection chain. Evidence:
   **S** for measured subtree partition.

4. **Intervention**

   The only attempted narrow operation, extracting or replacing the final
   dependent branch, does not preserve the root obligation and fails validity.
   The existing split/factored module changes imports and helper boundaries;
   it is not an M0-preserving control. No before/after effect is attributed to
   a single declaration. Evidence: **U**.

5. **Boundary stability**

   The dependent recursor interface is an effective validity boundary: it
   prevents standalone branch comparison. It is not a demonstrated cheap
   boundary. Puncturing it by branch extraction changes the telescope and
   invalidates the theorem. Status: **untested for cost; stable as a validity
   constraint**.

6. **Remaining uncertainty**

   Missing evidence is a pre-finalization expression and a valid control that
   aligns one source/API representation while retaining the original motive,
   witness, and branch. The next smallest useful experiment is to instrument
   elaboration/value construction to dump the instantiated motive and witness
   child pair before `Exists.casesOn` consumes it; a standalone dependent branch
   must not be used.

## Reduced evidence

The reduced, validated MDA trace and analysis are in the case `mda/` folder.
The full raw JSONL was scratch-only and is not retained in the case tree.

## Audit note

The three Eq-argument M1 groups are **S** as measured cost partitions, not D
causal interventions. Their source owners and the `Exists.casesOn` gateway
remain **U/P**: no pre-finalization pair or valid original-root one-factor
control exists. Branch extraction is invalid under the dependent motive.

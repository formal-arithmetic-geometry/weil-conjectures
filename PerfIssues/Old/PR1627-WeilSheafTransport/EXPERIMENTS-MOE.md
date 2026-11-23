# MISMATCH ORIGIN AND BOUNDARY STABILITY REPORT

Case: PR1627-WeilSheafTransport
Lean / Mathlib: Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); current source `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`; case source `1ef1fddac73`.
Declaration / root: `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor`; generated `_proof_1`, `_proof_2`, `_proof_3`; dependent `id` proof domains.

## 1. STAGE SNAPSHOTS

### S0 source

Slow source constructs `powFunctor` directly:

```text
obj K := IsoAlgebra.mk K.carrier (K.frobeniusPowIso r)
map phi := ObjectProperty.homMk { f := phi.hom.f, h := frobeniusPowIso_hom_naturality phi r }
```

The aligned control delegates to `IsoAlgebra.liftOfStr`; this is a source/API
change, not a provider-only perturbation. No macro-generated representation
was identified in the direct source.

### S1 macro-expanded

No additional macro-originated divergence was observed. The captured `#moe_elab`
probe expanded ordinary lambda syntax without changing its relevant Expr. The
generated-field source uses ordinary applications and structure notation.

### S2 elaborated

The source-local declaration writes `ObjectProperty.homMk` in `map`, but the
saved S2 command elaborates only `(fun (x : Nat) => x)`. It does not snapshot
the `powFunctor` value before finalization. The later stored-value replay
found this first structural difference in `_proof_2`'s dependent proof
argument:

```text
path = root/body/arg/fn/fn/fn
left  = @ObjectProperty.homMk
        (Endofunctor.Algebra (frobeniusPowPullback k0 l Y r))
        (Algebra.instCategory (frobeniusPowPullback k0 l Y r))
        (Algebra.IsIsoStr (frobeniusPowPullback k0 l Y r))
right = @CategoryStruct.id
```

The left head is the generated-field hom wrapper; the right head is the
dependent `id` domain. It is visible while checking the stored generated
value argument. `_proof_3` is a negative
control: the corresponding checked argument reported no first structural
difference.

### S3 finalized

Declaration processing generates opaque theorem constants `_proof_1`,
`_proof_2`, and `_proof_3`. `_proof_2` has nine type binders but eight value
binders in the stored ConstantInfo. This type/value asymmetry alone does not
show when the `homMk`/`id` pair appeared. No pre-finalization Expr for the
generated law was saved.

### S4 stored ConstantInfo

```text
powFunctor       def       regular:59   type/value binders 8/8
frobeniusPowIso  def       regular:58   type/value lambda telescopes
frobeniusPowPullback def   abbrev      type/value lambda telescopes, 8 binders
liftOfStr        def       regular:6
CategoryStruct.id def      abbrev
_proof_1         theorem   opaque       9/9 binders
_proof_2         theorem   opaque       9/8 binders
_proof_3         theorem   opaque       13/13 binders
```

`frobeniusPowPullback` and the generated theorem constants are fixed in the
imported environment after storage.

### S5 Kernel root

The root is the generated `powFunctor` law-field application and its dependent
`id` proof-argument domain. The source-local `_proof_2` replay returns
`Kernel.isDefEq = true` for the structurally different pair above. READY4.2
root 15228 has 10,904,899 calls, depth 61: M1 2,619,482 calls (24.021%), M2
1,512,663, and Matched 6,772,753. The largest counters replay is 40.808 s
(20.611 s comparison, 20.198 s reduction); the trace is 47.557 s.

### S6 Kernel-exposed descendants

READY4.2 reports M1->M1 1,180,833 edges, M1->Matched 2,662,551, and M1->M2
1,492,777. The wide M1 tree reaches depth 61 and fan-out 18. The trace has
7,231,443 WHNF requests, 4,193,774 beta steps, 2,539,771 delta unfolds, and
110,104 projections. The largest root reports no Pi-domain event because the
expensive dependent domain is a proposition argument inside an application.

## 2. FIRST DIVERGENCE

Exact path: `_proof_2`, `root/body/arg/fn/fn/fn`,
`@ObjectProperty.homMk (Endofunctor.Algebra (frobeniusPowPullback ...)) ...`
versus `@CategoryStruct.id`.

Earliest *verified* stage for the exact pair: S4, in the stored generated
`_proof_2` value. The direct `homMk` construction is source-authored at S0;
whether the paired `id` domain first differed at S2 or during finalization is
unresolved. Status: active at the dependent application boundary, not
merely latent in a definition body. It later propagates through M1/M2. The
corresponding `_proof_3` argument is structurally aligned.

## 3. ORIGIN

Source-authored: yes. The direct `IsoAlgebra.mk`/`ObjectProperty.homMk`
construction and separate `id` proof argument are written API terms.

Macro-generated: not observed.

Elaborator-selected: refinement only. Elaboration supplies implicit universe,
category, algebra, and `Algebra.IsIsoStr` arguments to `ObjectProperty.homMk`
and resolves the dependent `id` expected type. The first head difference is
the source/API choice, not a demonstrated alternate instance route.

Declaration-finalization-generated: generated opaque `_proof_*` theorems are
observed at S4. The nine-versus-eight binder asymmetry is in stored type and
value; without an S2 law Expr, it does not demonstrate a finalization-induced
change to the first pair.

Environment/import-frozen: yes for `frobeniusPowPullback`, `liftOfStr`,
`CategoryStruct.id`, and stored `_proof_*` metadata.

Kernel-exposed: yes for descendants. Reduction exposes dependent bodies and
drives M1/M2 work; it does not create the initial `homMk`/`id` choice.

Conclusion: mixed, with source-authored divergence refined by elaboration and
recursively exposed by the Kernel.

## 4. ELABORATOR PROVENANCE

Relevant implicit data: `k0`, `l`, `Y`, universe level, category instance for
`frobeniusPowPullback`, algebra instance, `Algebra.IsIsoStr`, and the dependent
`id` domain. The final term contains concrete
`Algebra.instCategory (frobeniusPowPullback k0 l Y r)` and
`Algebra.IsIsoStr (frobeniusPowPullback k0 l Y r)` arguments.

No trace showed competing providers or an independently reconstructed provider.
No separate `Coe`/`FunLike` insertion was identified as the first difference.
No targeted transparency perturbation was run because no assignment was found
whose final Expr changed under a fresh metavariable state. Thus no independent
Elaborator optimization or transparency causal claim is made.

## 5. KERNEL INPUT AND COST

Stored `powFunctor` is regular; generated laws are opaque theorem constants.
`frobeniusPowPullback` is an `abbrev`; `CategoryStruct.id` is an `abbrev`;
`liftOfStr` is `regular:6`. READY4.2 gives M1 24.021% of calls and median
64.767% of exclusive time across repeats, M2 1,512,663 calls, and Matched
10.538% of exclusive time. Repeated exact pairs account for 2.865 s in the
bounded trace (11.2% of comparison-exclusive time), which does not establish
allocation causality.

## 6. CHEAP-BOUNDARY INVENTORY

### P6-B1: generic `IsoAlgebra.liftOfStr`

Kind: regular named helper (`regular:6`). Current fast conversion: the aligned
source has no generated-field root above the 100 ms threshold. Stored outer
head is `liftOfStr`, versus direct `IsoAlgebra.mk`/`ObjectProperty.homMk` in the
slow source. Punctures: inline the helper body, replace it with direct fields,
use concrete `simp`/`rfl`, or reconstruct the proof in a downstream type.
Direct construction restores the 10,904,899-call root. Status: fragile. Risk:
changing it to `abbrev`, expanding it in a consumer, or mixing raw vocabulary.

### P6-B2: named `frobeniusPowPullback`

Kind: named data-level `abbrev` used as the dependent algebra domain. It keeps
the helper's outer domain compact. Punctures: unfold it, substitute the raw
Frobenius pushforward, or rebuild the dependent `id` type. Direct source
re-exposes the root; an abbrev-only replay was not isolated. Status: fragile /
untested in isolation.

### P6-B3: generated proof abstraction

Kind: finalized opaque theorem constants `_proof_1`-`_proof_3`. Punctures:
inline the proof, use concrete `rfl`/`simp`, or put raw proof/data construction
in a downstream declared type. The source-local replay exposes the dependent
pair before opacity can discharge it; no proof-only replacement preserving the
full telescope type-checked. Status: fragile.

## 7. CONTROL RESULTS

Original: direct generated fields; READY4.2 root 15228 and the counts above.
Perturbed elaboration: no valid provider or transparency ablation preserved the
root while changing only one inferred argument. The generic-helper control is
a construction-boundary diagnostic, not an Elaborator isolation.

Frozen replay: the stored `_proof_2` value argument checks and replays
the stored pair with `Kernel.isDefEq = true`; the first difference is the exact
`homMk`/`id` path. The generic whole-root `#moe_root` attempt was stopped
because full structural hashing exceeded the raw snapshot budget; the bounded
source-local replay and metadata walk are retained.

Kernel-metadata control: none; no same-Expr/different-hint replay was built.
Same root obligation: original and restored/aligned whole-root controls preserve
the root; `MatchedGeneric` is only a one-call diagnostic and does not preserve
the generated telescope.

## 8. CONCLUSION

Earliest verified exact divergence: S4, `_proof_2` path
`root/body/arg/fn/fn/fn`; the direct `homMk` API is source-authored at S0.
Most likely origin: source-authored direct generated-field API, refined by
implicit algebra/category arguments; S2 versus finalization timing is unknown.
Elaborator contribution: plausible refinement, not demonstrated as an
independent cause. Kernel contribution: demonstrated broad M1 propagation and
M2 fallback after reduction. Cheap-but-fragile boundaries: `liftOfStr`, named
`frobeniusPowPullback`, and opaque generated proof constants.

Uncertain: exact M0 pair identity in the full event stream, the complete
instance-search candidate trace for `ObjectProperty.homMk`, and whether a
targeted transparency change can select a different type-preserving provider.
No claim is made that `_proof_3` has the same mismatch; its checked argument
is structurally aligned even though the surrounding field can still be costly.

## Audit note and Batch 2 boundary test

The earlier S2 label used a `run_meta` walk of the *stored* `_proof_2` value
as though it were a pre-finalization snapshot. `source-generated.snapshot`
contains only an unrelated lambda at S2 and `MOE_META`/`MOE_DIFF` records for
the generated S4 declarations. The exact pair is therefore first verified at
S4; a finalization contribution remains unresolved. E3 puncture: use the
type-correct direct `IsoAlgebra.mk`/`ObjectProperty.homMk` source in place of
the fast `IsoAlgebra.liftOfStr` helper. The saved direct construction restores
the 10,904,899-call generated-law root; the helper control has no law-field
root above 100 ms. This tests the construction boundary, not an isolated
unfold of `liftOfStr` or a provider selection.

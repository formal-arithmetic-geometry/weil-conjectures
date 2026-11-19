# ProjectiveLineCohomologyChartBoundary classification

Case ID: `chartBoundaryClass_eq` and `exists_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass`.
Module: `WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyChartBoundary`.
Lean / Mathlib: 4.35.0 with built dependencies; revision `1ef1fddac73e`.
Imports/options: original module imports, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms.

## 1. Phase attribution

The successful complete module takes 372.17 s wall, 371.31 s user CPU, and 3,213,756 KB peak RSS. Kernel skipping under the same synchronous setting still takes 357.69 s wall and preserves the 172 s `exact` and 174 s `refine`; cumulative type checking falls to 5.09 ms. Original profiler totals: 350 s tactic execution and 14.5 s Kernel type checking. The two single-step controls each remove roughly half the elapsed time, while [BothSorry.lean](probes/BothSorry.lean) reduces it to 17.96 s. This is predominantly tactic elaboration; no Kernel A–F label is assigned from tactic names alone.

## 2. Expensive calls

The first hotspot is the `exact` closing `chartBoundaryClass_eq`, after `rw [chartBoundaryClass, gysinClass_eq]`:

```lean
exact (shiftSupportedClass_comp_counit Λ _ 2 _).symm
```

The profiler gives 172 s tactic time and 3.43 s type checking. Replacing only this call with typed `sorry` yields 198.26 s wall; the other 175 s `refine` remains. The second hotspot is the final theorem's `refine (hres _ _ _ _).trans ...` application, which composes `hres`, a `congrArg` over `Θ ≫ ·`, and `map_supportedClassMap_comp_rightDerivedUpperShriekBaseChangeMap_comp_map` at concrete zero-locus/derived-functor arguments. The profiler gives 174 s tactic time and 3.52 s type checking for the declaration. Replacing just this `refine` and its closing `exact` yields 192.36 s wall while the earlier 171 s `exact` remains. Replacing the entire final theorem proof after the first `refine` gives 194.95 s, so the first existential `refine` is not the main cost. Replacing both expensive blocks gives 17.96 s. The exact inner Meta conversion pairs have not been dumped.

## 3. Structure and mechanism

Both calls match general identities against concrete derived-functor expressions for a zero locus and Kummer boundary. The second call includes `.app`, `.map`, shift-isomorphism and composition endpoints. The controls establish which source calls trigger elaboration, but do not distinguish `Meta.isDefEq`, WHNF, or instance synthesis within them. No Kernel expression diff, generated proof constant, recursor/cast count, or shared DAG size was measured. **Kind: elaborator tactic matching; inner mechanism unclassified.**

## 4. Confidence and caveats

Source-level cost sites are **confirmed** by profiler timing and independent one-block controls. Phase is **strongly supported** by the 350 s versus 14.5 s profiler split. A focused `trace.Meta.isDefEq` or `trace.profiler` run would be required to name the inner conversion. `sorry` probes are diagnostic and are not valid proofs; the original module succeeds.

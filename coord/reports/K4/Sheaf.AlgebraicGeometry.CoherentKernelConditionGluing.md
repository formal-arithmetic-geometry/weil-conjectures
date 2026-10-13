## What changed

Replaced the hole in `Sheaf.AlgebraicGeometry.CoherentKernelConditionGluing` with a
proof that constructs the intersection cover and flattens finite local generating
families. The proved private helper `SheafOfModules.finite_generators_of_cover`
adapts Mathlib's `QuasicoherentData.bind`: `CoversTop.over` composes the covers;
`Over.iteratedSliceEquiv` and `pushforwardPushforwardEquivalence` move the generating
families; `GeneratingSections.map` and `ofEpi` preserve their finite index types.
The intersection cover is proved pointwise from `hU`, without nonemptiness assumptions.

Added proof-only imports of `Mathlib.CategoryTheory.Sites.CoversTop.Over` and
`Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType`. The latter isolates
the restriction comparison for one open and one fixed rank. The item applies it to
each cover member, with `fun V g ↦ hK i V n g`; it then carries out the cover gluing
in Lean. All three original public imports remain necessary for the interface.

Corrected the conclusion's implicit index universe to `LocalGeneratorsData.{u}`.
The original theorem had an unintended independent index universe, which the source
does not require. The full old/new interfaces and downstream check are recorded in
`coord/changes/coherent-kernel-local-generators-universe.md`. No definitions or target
statements changed, and no other existing module was adapted.

The two delivered modules compiled cleanly with `lcompile.py --all`. The unchanged
`CoherentKernelConditionDescent` also compiled against the corrected item in the
sandbox overlay, then its temporary validation copy was removed from the delivery.
The source was read from the Stacks Project's `modules.tex`, downloaded to the
sandbox scratchpad because the local repository contains only literature lists.

## Proved and sorry left

Closed the original hole of `AlgebraicGeometry.coherent_kernel_condition_local_generators`
(node `lem-weil-pbc-coherent-kernel-condition-descent-local-generators`) by a
compiling reduction. No sorry remains in the item. The cover-flattening helper is
fully proved and has no holes.

Added one hole: `AlgebraicGeometry.coherent_kernel_intersection_finiteType`, node
`lem-weil-pbc-coherent-kernel-intersection-finite-type`, in its own module
`Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType`.
This is a decomposition (one closed hole, one added hole, net zero), not an
axiom-free proof of kernel descent. The remaining statement has no cover or gluing
conclusion: it compares restriction to a single intersection at one fixed rank.

## No longer needed

No existing import was removed and no library module is claimed globally pruned.
The parent node now directly depends only on the single-intersection comparison.
The former direct proof dependencies `def-pc-scheme`,
`def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`, and `pqf-def-coherent`
are not separately invoked in its Lean proof. Scheme and module notions remain
statement dependencies, and restriction infrastructure remains needed by the new
comparison. In particular the gluing argument does not need
`Sheaf.AlgebraicGeometry.Coherent` or a coherence assumption on `F`.
The unit's realized statement and steps are untouched.

## Where the brief, the DAG or earlier work was wrong

The original implicit `LocalGeneratorsData` index universe was independent of `u`.
`#check` printed `coherent_kernel_condition_local_generators.{u, u_1}`, and the
compiler rejected a constructed `Type u`-indexed witness against the arbitrary
`u_1` conclusion. The source statement only asks for local finite generating data;
the interface now explicitly uses the site universe, as `IsFiniteType` does.
The unchanged sole downstream caller compiled successfully.

The original node cited definitions and the restriction functor but did not expose
the actual kernel/site comparison. That comparison is now a rank-specific node;
the cover and finite-generator gluing have actual Lean proofs. Edge cases checked
for the new statement: `U` or `W` empty gives an empty intersection; `n = 0` gives
a zero source; `U = ⊤` reduces to applying the local condition on `W`. None requires
surjectivity of `f` or finite type of `F`. For the main theorem, an empty index type
and `hU` force every open to be empty, and the pointwise cover proof is vacuous.

LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder and Loogle
returned the finite-generator definitions and restriction interface, but no exact
kernel comparison. The logged grep searches and scoped repository searches found
no duplicate. Blueprint searches for `kernel restriction` and `finite type kernel`
found no imported blueprint node with the new statement.

## New nodes

`lem-weil-pbc-coherent-kernel-intersection-finite-type` states only the fixed-rank
single-open restriction comparison. Its source is Stacks Modules, Definitions
01BV (`definition-coherent`), 01B5 (`definition-finite-type`), and Section 01AF
(`section-kernels`). Its docstring gives the free-module restriction, transitivity,
sectionwise kernel, and finite-generating-family transport argument. Its blueprint
origin is inherited through the parent descent node to
`thm-weil-pbc-finite-etale-lifting`, and it preserves the same unit route.

Change record: `coord/changes/coherent-kernel-local-generators-universe.md`.

## Second reading by K4

1. I compared both delivered modules with the repository versions. The only
existing declaration whose signature differs is
`coherent_kernel_condition_local_generators`; the universe correction is declared
in `coord/changes/coherent-kernel-local-generators-universe.md`, and the new
single-intersection declaration is recorded by its new node. No target statement
or definition was changed.

2. I compiled both modules with `lcompile.py --all`. The gluing theorem has no
remaining hole. The only remaining `sorry` is the named split theorem
`coherent_kernel_intersection_finiteType`; searches found no forbidden axiom,
unsafe declaration, or hollow definition. The proof dependencies account for the
single split theorem, and the changed universe is used by the downstream caller.

3. I checked the split statement against the fixed-rank restriction argument and
its edge cases: empty intersections and rank zero are immediate, while `U = ⊤`
specializes to the local condition on `W`. It has no unnecessary cover,
surjectivity, or finite-type hypothesis, and its docstring and DAG node give the
source and a complete proof plan. No duplicate declaration was found in the
library or Mathlib searches.

4. I checked the proof from the target downward. It applies the split comparison
at each cover member, proves the intersection family covers pointwise, and then
uses the iterated-slice equivalence and `CoversTop.over` to flatten finite local
generators. The unit's realized statement and steps remain represented by the
parent node; no route-changing import or unused import was introduced.

5. The parent node's `proof`, `proof_deps`, and `proof_origin` now match the Lean
proof, and the child node has the required module, declaration, source, blueprint,
and split status fields. The report records the one-hole decomposition and the
universe change. No existing module required adaptation.

I changed only this second-reading report section after the first reading: no Lean
proof or DAG content was altered.

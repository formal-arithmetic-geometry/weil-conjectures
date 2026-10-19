## Worker report

The module `Sheaf.CategoryTheory.PretriangulatedKernelSplit` states
`CategoryTheory.Functor.preservesKernel_of_pretriangulated`; its proof is
`sorry`, as required for stage 2.  It has no definitions, new nodes,
dependency-module repairs, or statement correction.  The theorem uses
Mathlib's `Preadditive`, `HasZeroObject`, `HasShift`, `Pretriangulated`,
`Functor.Additive`, `KernelFork`, and `IsLimit` directly.

The node's hypotheses and conclusion are rendered clause by clause as follows.

- The source category is `{C : Type u₁} [Category.{v₁} C]`, with
  `[Preadditive C]`, `[HasZeroObject C]`, `[HasShift C ℤ]`, additive integer
  shifts `[∀ n : ℤ, (shiftFunctor C n).Additive]`, and `[Pretriangulated C]`.
  These are exactly the Mathlib encoding recorded by
  `def-weil-triangulated-category`.
- The target category is `{D : Type u₂} [Category.{v₂} D] [Preadditive D]`,
  rendering the node's preadditive target with independent object and
  morphism universes.
- `F : C ⥤ D` and `[F.Additive]` render the supplied additive functor,
  using `CategoryTheory.Functor.Additive` from
  `def-weil-pbc-additive-functor`.
- `{X Y K : C}`, `d : X ⟶ Y`, and `k : K ⟶ X` render the morphism and the
  candidate kernel arrow.  `hk : k ≫ d = 0` is the kernel-zero clause.
- `hK : IsLimit (KernelFork.ofι k hk)` is the universal kernel clause: every
  arrow into `X` killed by `d` factors uniquely through `k`.  Since `IsLimit`
  is a structure, the conclusion is expressed in the standard categorical
  form `Nonempty (IsLimit ...)` rather than assuming a chosen target kernel.
- The conclusion's fork is
  `KernelFork.ofι (f := F.map d) (F.map k) ...`; its condition is proved by
  functoriality and additivity, namely `F.map k ≫ F.map d = 0` from `hk` and
  `F.map_zero`.  `Nonempty (IsLimit ...)` says exactly that `F.map k` is a
  kernel of `F.map d`, with no existence of any other kernel required.

The recorded dependencies used are Mathlib declarations.  The source
category interface is `CategoryTheory.Pretriangulated` in
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`; the preadditive
interface is `CategoryTheory.Preadditive` in
`Mathlib.CategoryTheory.Preadditive.Basic`; and additivity is
`CategoryTheory.Functor.Additive` in
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.  The node's reviewed
Mathlib proof dependencies are used at stage 3: the split-monomorphism
instance `CategoryTheory.Pretriangulated.instSplitMonoCategory`, the
zero-third distinguished-triangle biproduct decomposition
`CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`,
and the triangle exactness declarations recorded by
`lem-weil-pbc-hom-into-triangle-exact`.  This stage only states the result.

I checked edge cases before writing: `d = 0` (the kernel arrow may be an
isomorphism), `d = 𝟙 _` (the kernel is zero), a split inclusion, the zero
functor, and the zero category.  The statement remains meaningful because it
requires only the supplied source kernel and does not assume target kernels,
abelianness, completeness, or nonzero objects.  Independent universes for C
and D do not exclude any case.

Searches for an existing declaration were made with the required tools:

- `msearch.py ... leanfinder "An additive functor from a pretriangulated category to a preadditive category preserves an existing kernel"` returned homological-functor and additive-functor results, but no theorem with this split-kernel conclusion.
- `msearch.py ... loogle "CategoryTheory.Pretriangulated, CategoryTheory.Functor.Additive, KernelFork.IsLimit"` returned no hits (the query's `KernelFork.IsLimit` name is not a standalone declaration).
- `msearch.py ... grep "preservesKernel_of_pretriangulated|KernelFork.ofι" CategoryTheory` found only generic kernel-fork and homological declarations, with no combined theorem.
- `rg` over `WeilConjectures/` for `pretriangulated.*kernel`, `kernel.*pretriangulated`, and `preservesKernel_of_pretriangulated` found no existing project declaration.  `rg` over `lean/Sheaf` found no duplicate.

The module compiles cleanly with `scompile.py`; the only postponed proof is
the theorem proof.  No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

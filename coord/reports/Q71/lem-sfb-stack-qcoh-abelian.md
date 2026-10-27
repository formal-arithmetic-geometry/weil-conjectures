## Worker report

The module `Sheaf.AlgebraicGeometry.StackQcohAbelian` states
`CategoryTheory.stack_qcoh_abelian`, with its entire proof postponed by `sorry`.
It states exactly Stacks Project, stacks-sheaves.tex, Tag 06WV,
lemma-quasi-coherent-algebraic-stack (2). I read the statement and proof of 06WV,
including the preceding warning that the inclusion in all module sheaves need
not be exact. There is no statement correction, new definition, or dependency
repair. Only the item's `lean` record changes.

Hypothesis and clause correspondence:

- The size convention is rendered by explicitly declared universes `u v w`.
  `S : AlgebraicGeometry.Scheme.{u}` supplies an arbitrary base scheme.
  `F : BasedCategory.{v, w} (Over S)` retains the total category over schemes
  over S, with independent morphism and object universes. No equality of site
  universes is imposed. Write q = max (u + 1) v w in this explanation only:
  it is the recorded structure-sheaf and module universe, large enough for the
  site and the regular-function rings. All Lean terms spell it out.
- An algebraic stack over S is exactly `(hF : IsAlgebraicModuliStack F)`.
  Unfolding the recorded definitions, `hF.1.1` is `IsFibredInGroupoids F`.
  It supplies the structure-sheaf construction without adding a separate
  fibredness hypothesis or choosing an atlas as part of the statement.
- The big fppf site and its structure ring sheaf are the dependency's
  `moduliFppfTopology F` and `moduliModuleRings F hF.1.1`. The latter is the
  existing `moduliStructureSheaf` with commutativity forgotten. Its sections
  are regular functions on the underlying scheme, transported by the
  dependency's canonical ULift ring equivalence, with scheme pullback maps.
- Sheaves of structure modules are the ambient
  `SheafOfModules.{q} (moduliModuleRings F hF.1.1)`, definitionally the recorded
  `ringedSiteModules.{q}`. There is no replacement module category.
- The node's full subcategory of locally presented modules is exactly
  `(SheafOfModules.isQuasicoherent.{q}
  (moduliModuleRings F hF.1.1)).FullSubcategory`. Mathlib's
  `IsQuasicoherent` means existence of `QuasicoherentData`: a family covering
  the terminal object with presentations on its slices. `Presentation`
  consists of arbitrary small generators and generators of the kernel, so
  its presentation is by small direct sums, not finite direct sums.
  The dependency's two slice-sheafification instances make this predicate
  available at q. `FullSubcategory` retains every ambient module morphism
  between the qualifying objects, with the inherited composition.
- The conclusion `Nonempty (Abelian (...).FullSubcategory)` says this very
  category admits an abelian structure. Mathlib's `Abelian` contains data,
  including a preadditive structure, so `Nonempty` makes the assertion a
  proposition suitable for a theorem with a postponed proof. Its finite
  products, kernels, cokernels and normal mono/epi fields are exactly the
  recorded meaning of abelianity; zero objects and finite biproducts follow.
- No finite type, finite presentation of modules, quasi-compactness,
  Noetherianity, separatedness, characteristic, nonemptiness or chosen
  presentation is required. There is no claim that the full inclusion is
  exact or that ambient kernels remain quasi-coherent.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, a locally
  ringed space with an affine neighborhood of each point.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, with its existing `IsModuliStack`,
  representable diagonal, and existence of a smooth surjective atlas.
  The underlying `IsModuliStack` and `IsFibredInGroupoids` signatures were
  read in `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `moduliFppfTopology`, `moduliStructurePresheaf`, `moduliStructureSheaf`,
  `moduliModuleRings`, `moduliSliceHasWeakSheafify` and
  `moduliSliceWEqualsLocallyBijective`. The same module's
  `IsQuasicoherentModuliAlgebra` confirms the existing general-site
  `SheafOfModules.IsQuasicoherent` is the intended module notion.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.isQuasicoherent`, `IsQuasicoherent`, `QuasicoherentData`,
  and `Presentation`, read with their signatures and docstrings. These
  already give the full subcategory, so no new QCoh definition is needed.
- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`, matching
  the `mathlib_match` of `def-sp-abelian`. The size-convention node has no
  declaration; its universe requirements are stated directly above.

The proof docstring follows all four DAG proof steps: smooth atlas and flat
self-relation; module descent and inversion of the cocycle convention;
preadditivity and transport of finite products (including the empty family);
transfer of abelianity by `abelianOfEquivalence`.

Available proof-only dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` and
`Mathlib.CategoryTheory.Abelian.Transfer` (the Mathlib match
`CategoryTheory.abelianOfEquivalence` of
`lem-sfb-preadditive-abelian-equivalence`). The source signatures were read.
The preadditive definition is supplied by `Abelian.Basic`'s imports.
`lem-sfb-fppf-groupoid-stack-presentations`,
`lem-sfb-smooth-atlas-module-descent`, and
`lem-sfb-flat-space-groupoid-abelian` currently have neither Lean records
nor Mathlib matches, so they have no modules to import. They are proof-only
prerequisites: the statement itself uses none of their unstated interfaces.

Edge cases checked before writing: an empty base or empty stack still has
its ordinary zero module and trivial module category; no nonemptiness binder
excludes it. The zero sheaf and presentations with empty sets of generators
or relations remain allowed. Infinite small presentations are allowed, as
are non-Noetherian affine schemes and non-quasi-compact stacks. On an affine
scheme stack the assertion specializes to the usual abelian module category,
while the big-fppf inclusion need not preserve kernels. Relations in the
atlas proof may be algebraic spaces, not schemes. None of these checks
requires a restriction to finite modules or to an affine diagonal.

Searches for an existing statement:

- `msearch.py leanfinder`, query “Quasi coherent modules on an algebraic stack
  form an abelian category”: eight hits, including
  `AlgebraicGeometry.Scheme.Modules.instAbelian`,
  `SheafOfModules.instAbelian`, `PresheafOfModules.instAbelian`, condensed
  module abelianity, and `SheafOfModules.QuasicoherentData.X`. None states
  abelianity of the quasi-coherent full subcategory on an algebraic stack.
  The ambient sheaf-module abelian instance was read: it concerns all
  sheaves, not the subcategory here.
- `msearch.py loogle`, query `"Quasicoherent", "Abelian"`: zero hits.
- `msearch.py grep`, query
  `quasi.?coherent.*[Aa]belian|[Aa]belian.*quasi.?coherent`: zero hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, for
  quasi-coherent/abelian and stack/QCoh/moduli/abelian combinations, found
  the scheme-only `QuasiCoherentGrothendieckGenerators` and unrelated
  module/level-structure material, but no stack-QCoh abelianity statement.
  The recorded stack algebra module and space QCoh module were read;
  they give the needed notion but not this theorem.
- `grep -rn "lem-sfb-stack-qcoh-abelian" lean/WeilConjectures`: no hits.
  Searches for `stack_qcoh_abelian|StackQcohAbelian` in the project and in
  `dag/lean_names_upstream.json`: no existing declaration.

Validation: the delivered file was compiled separately with `scompile.py`
against the published live library. Both the sandbox and library-module
passes succeeded (4.6 seconds and 9.8 seconds), with no errors or unexpected
warnings. `autoImplicit` is explicitly disabled; all universes and variables
are bound. No diagnostic declarations remain. The required dry run and
final delivery are performed after this report is written.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePresentationKernelGermEffacement` states
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_quotient_killing_kernel_germ`.
It has one theorem with proof `sorry`, and no new definitions. The five-step proof in its
docstring follows the node and Stacks Properties 01PJ, injectivity paragraph, read in
`literature/stacks-project/properties.tex`, lines 3143–3166. The statement, dependencies,
and proof of the item are unchanged. No statement dispute was found.

Hypotheses and conclusions, clause by clause:

- A scheme is `(X : Scheme.{u})`; quasi-compactness is `[CompactSpace X]`.
- Quasi-separatedness is `[QuasiSeparatedSpace X]`, equivalent to quasi-separatedness of
  the terminal morphism by `AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated`.
- The two O_X-module sheaves are `(G F : X.Modules)`. This is Mathlib's
  `SheafOfModules.{u} X.ringCatSheaf`, the same category as
  `CategoryTheory.ringedSiteModules X.ringCatSheaf`, with its inherited linear morphisms.
- Finite presentation of G is `[SheafOfModules.IsFinitePresentation.{u} G]`.
- Quasi-coherence of F is `[SheafOfModules.IsQuasicoherent.{u} F]`. There is no finite-type
  assumption on F and no Noetherian hypothesis on X.
- The linear map is `(α : G ⟶ F)` and the point is `(x : X)`.
- The germ `s` belongs to the object obtained by applying the dependency's
  `PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x` to `G.val`.
  This is the ordinary Zariski stalk of the underlying presheaf of modules, over the
  ordinary stalk ring, not an étale stalk. The hypothesis `hs` is exactly its induced
  linear map applied to `s` being zero.
- The submodule is represented by `∃ (K : X.Modules) (ι : K ⟶ G), Mono ι ∧ ...`.
  In the category of module sheaves a mono is sectionwise injective, so this is precisely
  a submodule of G up to the canonical identification with its sectionwise image.
  It imposes no choice of a second kernel or a different quotient construction.
- Its quasi-coherence and finite type are the next two conjuncts
  `SheafOfModules.IsQuasicoherent.{u} K` and `SheafOfModules.IsFiniteType.{u} K`.
- Containment in the sectionwise kernel is written explicitly as
  `∀ (U : X.Opens) (t : Γ(K, U)), α.app U (ι.app U t) = 0`.
  This quantifies over every open and every section, not merely global sections or stalks.
- Q is exactly the categorical `cokernel ι` in `X.Modules`, as requested by the node;
  q is its canonical `cokernel.π ι`. Their construction is Mathlib's existing cokernel,
  the sheaf cokernel rather than the un-sheafified sectionwise quotient.
- The quotient's finite presentation is
  `SheafOfModules.IsFinitePresentation.{u} (cokernel ι)`.
- The following conjunct applies the same module stalk functor to `(cokernel.π ι).val`
  and requires its value at `s` to be zero; thus it is precisely `q_x(s) = 0`.
- Finally `∃ β : cokernel ι ⟶ F, cokernel.π ι ≫ β = α` supplies the linear factorization
  and its required equality (Lean's composition order is q followed by β).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  imported through `Mathlib.AlgebraicGeometry.Modules.Sheaf`, which also supplies
  `Scheme.Modules`, `Scheme.Modules.Hom.app`, and the canonical abelian category.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, available through the scheme imports.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`
  and `quasiSeparatedSpace_iff_quasiSeparated` justify the underlying-space formulation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent general-site abbreviation for `SheafOfModules` specialized by `X.Modules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: `SheafOfModules.IsFiniteType`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation` and `SheafOfModules.IsQuasicoherent`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: the preceding two finiteness/coherence
  predicates and `AlgebraicGeometry.RingedSpace.IsCoherent`. Its public import of
  Mathlib quasicoherence supplies the separate quasi-coherence notion needed here;
  the live dependency binding is preserved.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj`, `stalkMap`. The functor is used
  directly on the underlying presheaf of each module sheaf and the underlying maps.

The already stated proof dependencies are imported without `public`: spectral spaces,
`QuasicoherentFiniteTypeAffine`, `Modules.QuasicoherentKernel`,
`Modules.QuasiCoherentCokernelImage`, `ModuleFiniteTypeImageExtension`,
`ModuleFiniteTypeSubmoduleExtension`, and `ModuleFinitePresentationCokernel`.
Open restriction is already provided by the public `Modules.Sheaf` import. The qcqs-to-spectral
node has no current Lean binding; it is described in the proof, with no new axiom or restatement.

Edge cases were checked before drafting. If X is empty there is no x, so the universal
statement is vacuous. If s is zero, K = 0 and Q is canonically isomorphic to G suffice.
If α is injective its kernel germ must be zero, giving the same case. If α = 0 the
cyclic local submodule extends into all of G, and β can be zero. Zero sheaves and finite
presentations with zero generators or relations are allowed by the existing definitions.
The statement covers affine schemes over arbitrary commutative rings, including
non-Noetherian rings. There is no characteristic or rank restriction. All variables
and the sole universe u are explicitly bound; no new site or test-object universe is added.

Searches for an existing theorem:

- `msearch.py leanfinder`: “A kernel germ of a morphism from a finitely presented sheaf to
  a quasi-coherent sheaf on a qcqs scheme is killed by quotienting by a finite type
  quasi-coherent submodule of the kernel”. Eight hits on `QuasicoherentData`, its finite
  presentation class, `quasicoherentDataOfIsFinitePresentation`, `presentation`, and
  finite presentation implying quasi-coherence/finite type. No effacement theorem.
- `msearch.py loogle`: `SheafOfModules.IsFinitePresentation, CategoryTheory.Limits.cokernel`.
  Zero hits.
- `msearch.py grep`: `kernel|effac|germ|quotient` in `AlgebraicGeometry/Modules`.
  Ten hits: restriction/germ formulas in `Sheaf.lean` and affine presentation/cokernel
  calculations in `Tilde.lean`, not the global existence theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for kernel-germ names,
  `finitePresentation` with quotient/kernel, and effacement/germ killing. The matches
  include internal Hom/stalk kernel comparisons, affine-limit sheaf approximation,
  and the parent's filtered-colimit theorem; none state this item. Direct grep of
  the item id in `lean/WeilConjectures` has no match. The chosen declaration name
  also has no match in the upstream or project sources.
- `msearch.py leansearch`: “A germ in the kernel of a sheaf morphism is killed by a
  finitely presented quotient through which the morphism factors”. Eight hits: categorical
  kernels, scheme-map ideal kernels, finite-presentation constructors, global-section
  germs, a structure-sheaf germ-zero lemma, `Module.FinitePresentation.fg_ker_iff`, and
  finite presentation of local generators. None is the required sheaf existence theorem.

Validation: `scompile.py Q20 lem-weil-pbc-finite-presentation-kernel-germ-effacement`
compiled the module against the live published build in both sandbox and library module
modes (6.2 s and 5.8 s on the repair run of 2026-10-23), without errors or warnings.
The saved packet also passed the initial repair dry run against the current live
branch (commit 4fe36dbded1); the returned dependency-record defect is repaired below.

## Repair of returned delivery

The immutable head reviewed by the maintainer was `4bf95d93b18e`. The single
H13/H4 return concerns rebinding `pqf-def-coherent` from Q25's
`AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` to a different primary
declaration. Removed `dag/nodes/sec-abelian-varieties/pqf-def-coherent.json` from the
packet, as requested. The live record and its primary declaration remain byte-identical;
no dependency module or definition is introduced. The item Lean file is unchanged.

Added the requested item `lean.note`: the quasi-coherent hypothesis on F uses
Mathlib's `SheafOfModules.IsQuasicoherent` (Stacks 01BE), publicly re-exported by
`WeilConjectures.AlgebraicGeometry.Coherent`. The conclusion imposes quasi-coherence
and finite type on K separately. Neither predicate is replaced by the conjunction
recorded as the live dependency's primary declaration. This follows the reviewer's
first repair option and preserves all existing consumers.

The six other statement-dependency records are untouched. Comparison with the current
live item confirms that only its `lean` field changes. No source statement, proof plan,
or statement dependency changes. Self-check confirms every hypothesis and conclusion
listed above still matches the theorem; in particular F has no finite-type assumption.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

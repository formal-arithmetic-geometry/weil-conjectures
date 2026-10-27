## Worker report

The module `Sheaf.AlgebraicGeometry.StackQCohDirectSums` states
`CategoryTheory.moduli_qcoh_direct_sums`, with its proof `sorry`. No node statement,
proof, dependency list or dependency interface is changed. There are no new DAG nodes.
The four helper declarations give actual data for evaluation of global scalars,
restriction of scalars on each section value, the submodule of compatible families,
and the corresponding global-sections functor. They belong to the canonical map
being stated, rather than introducing a different notion of quasi-coherence or sections.
The module has `autoImplicit false` and explicitly declares every universe and binder.

Clause-by-clause correspondence:

- Base scheme: `{S : Scheme.{u}}`. The stack over this base is
  `C : BasedCategory.{v, w} (Over S)` with `hC : IsAlgebraicModuliStack C`.
  Its fibred-groupoid structure is precisely `hC.1.1`, a component of algebraicity,
  not an extra assumption or a choice of an atlas.
- Size convention and arbitrary small family: the module keeps `u`, `v`, `w`
  independent. `A : Type (max (u + 1) v w)` is small in the existing ambient
  module universe, which contains the schemes and the total site's objects and
  morphisms. It imposes no finiteness or nonemptiness condition.
- Quasi-coherent module sheaves on the actual big fppf site:
  `F : A → ModuliQCoh C hC.1.1`. `ModuliQCoh` is the dependency's full subcategory
  for Mathlib's `SheafOfModules.IsQuasicoherent` over `moduliModuleRings C hC.1.1`.
  It is the local free-presentation predicate, not cartesian data assumed in place
  of quasi-coherence.
- Existence and the displayed Hom universal property:
  `∃ c : Cofan F, Nonempty (IsColimit c) ∧ ...`. A colimiting cofan says that,
  for every quasi-coherent G, precomposition with its legs is the specified
  bijection from `c.pt ⟶ G` to families `∀ a, F a ⟶ G`.
- Agreement with the coproduct in all module sheaves: the second conjunct is
  `Nonempty (IsColimit (...ι.mapCocone c))`, using the existing full-subcategory
  inclusion `ι`. It retains exactly the same summand maps and apex. This is
  agreement up to the unique isomorphism intertwining coprojections. Mathlib's
  ambient sheaf colimit is the module sheafification of the presheaf colimit;
  thus this also identifies it with the sheafification of the presheaf direct sum,
  without asserting that arbitrary section evaluation preserves coproducts.
- Every scheme test, with the dependency's genuine restriction and tensor
  pullback: for every `r : ModuliSchemeRestriction C hC.1.1` and `x : C.obj`,
  the third conjunct is `Nonempty (IsColimit ((r.restriction x).mapCocone c))`.
  Its apex is `r.restriction x |>.obj c.pt` and legs are the restricted summand
  maps. Consequently the unique canonical comparison from the ordinary module
  coproduct to this apex is an isomorphism, not merely an arbitrary iso between
  two objects. All its terms are quasi-coherent by `r.quasicoherent`. The
  dependency identifies the ambient-universe structure sheaf with the original
  one by canonical ULift ring equivalences, and compares its tensor pullback to
  `Scheme.Modules.tensorPullback` with the actual section unit. Quantifying over
  `r` makes this independent of any normalized realization chosen in stage 3;
  existence is already the dependency theorem `exists_moduliSchemeRestriction`.
- Quasi-compactness: `IsQuasiCompactModuli C → ...` occurs only in the final
  conjunct. This is precisely existence of a smooth surjective atlas from a
  scheme with `CompactSpace` underlying space, and does not require a
  quasi-separated diagonal.
- The global-section ring is exactly
  `moduliGlobalSectionsRing (moduliStructureSheaf C hC.1.1)`, already defined by
  the dependency as the ring of compatible families, with pointwise operations.
  `moduliGlobalScalarEvaluation` evaluates such a family, and
  `moduliSectionValue` restricts scalars along that ring homomorphism.
  `moduliSectionsSubmodule` has carrier the same compatible families as
  `SheafOfModules.sections` / `moduliGlobalSections` after forgetting to sets;
  its additive operations and global scalar action are pointwise. The helper
  adds the required module structure to those sections, with no new section
  selection or replacement of the site.
- The global-section comparison is the last colimiting cofan, obtained by applying
  the inclusion followed by `moduliModuleGlobalSections`. It is a colimit in
  `ModuleCat` over the actual global regular-function ring. Equivalently, the
  canonical map from the direct sum of section modules to sections of the sum,
  with legs induced by the original summand maps, is an isomorphism of modules.
- Naturality in the family is encoded without an arbitrary comparison choice:
  all comparisons preserve the cofan legs. Given maps `F a ⟶ G a`, the two
  composites in the comparison square have the same composite with each
  coprojection. The coproduct universal property forces their equality. The
  existence and all preservation assertions quantify over the whole family F.
  This is the categorical formulation of the stated natural isomorphisms.
- No quasi-separatedness, separatedness, Noetherian, finite-index or nonempty
  hypothesis occurs. No conclusion is restricted to affine scheme tests.

Dependency declarations read and used (imports are also inherited publicly through
those modules where appropriate):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `moduliFppfTopology`, `moduliStructureSheaf`, `moduliModuleRings`,
  `moduliGlobalSections`, `moduliGlobalSectionsRing`. The recorded primary
  declaration `IsQuasicoherentModuliAlgebra` is for algebras; this module uses
  its recorded underlying ringed site and the same `SheafOfModules.IsQuasicoherent`
  predicate on modules, as the item requires.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes Mathlib's
  `SheafOfModules.IsQuasicoherent`, the pertinent first clause of pqf-def-coherent;
  it does not impose the conjunction with finite type.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`,
  `tensorPullbackSectionId`, through the recorded restriction interface.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction`:
  `ModuliQCoh`, `ModuliSchemeRestriction`, its `restriction` and `quasicoherent`
  fields, and `exists_moduliSchemeRestriction`; read the whole interface,
  including its normalized tensor and realization comparisons.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `IsQuasiCompactModuli`, the
  relevant clause of this dependency, not `IsQuasiSeparatedAlgebraicModuliMap`.
- The convention-only size node has no declaration to import.

All available proof-dependency modules are imported. They are
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`,
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.Topology.Defs.Filter` (already inherited), and
`WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation`, in addition
to the statement imports. The unstated proof-only nodes
`lem-sfb-fibred-fppf-ringed-inverse-image` and
`lem-sfb-smooth-atlas-module-descent` currently have no recorded module and therefore
cannot yet be imported. Neither is needed to type this stage-2 statement; their
proof roles are retained in the theorem docstring and unchanged DAG proof plan.

Edge cases checked before drafting: empty A gives an initial/zero module, whose
scheme restrictions and section modules are zero; zero summands give the same.
A singleton yields the original module and its identity cofan. An empty stack or
empty quasi-compact atlas has only zero compatible module sections, so the final
claim still applies. An infinite family is unrestricted; quasi-compactness supplies
finite support of an individual section, not finiteness of A. A non-quasi-compact
stack still has the coproduct and scheme-test conclusions, but the final implication
asserts nothing without quasi-compactness. Arbitrary non-affine scheme tests are
covered; preservation there is a statement about module sheaves, not about their
section evaluation. Independent site universes are retained, not equated.

Searches made with the prescribed msearch.py interface:

- LeanFinder: `Coproducts of quasi coherent modules on algebraic stacks and global
  sections on quasi compact stacks`. Eight results: scheme-module colimits and
  abelianity, scheme affine-transition-limit sections, and scheme coproducts.
  No stack quasi-coherent direct sum / quasi-compact section theorem.
- LeanSearch: `Global sections of quasi coherent sheaves on a quasi compact algebraic
  stack commute with arbitrary direct sums`. Eight results: generic site global
  sections, scheme sections and the quasi-coherence predicate; no target theorem.
  Read the actual Mathlib section APIs instead of trusting the search result's
  inaccurate prose description of the direction of the global-section adjunction.
- Loogle: `SheafOfModules, coproduct` reports unknown identifier `coproduct`, no
  hits. Follow-up `SheafOfModules.sectionsFunctor` finds exactly the type-valued
  sections functor and its obj/map equations. Read its full source and
  `PresheafOfModules.sections`, `sectionsMap`, `unitHomEquiv`. It supplies
  compatible families but not the global-regular-function module structure or
  coproduct preservation theorem.
- msearch grep: `isQuasicoherent.*(sigma|coproduct)|globalSections.*(sigma|coproduct)`
  has no Mathlib match. Direct rg in Mathlib finds scheme colimits, the local
  presentation predicate and sectionwise constructions. The source of
  `ModuleCat.sectionsSubmodule` assumes a fixed coefficient ring; it does not
  directly give the varying-local-ring module presheaf construction needed here.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `moduliModuleGlobalSections|moduliSectionsSubmodule|moduliSectionValue|moduliGlobalScalarEvaluation|moduli_qcoh_direct_sums`
  found no existing declaration. Concept searches for stack direct sums found
  only unrelated derived-scheme direct sums. Upstream `isQuasicoherent_sigma`
  is the scheme-only proof input, not this stack statement.

Sources opened: the local Stacks source, Tag 06WN's statement and scheme-slice
proof, and Tag 04YC's equivalence with a quasi-compact smooth scheme atlas.
The module docstring reproduces all six steps of the accepted DAG proof, including
the finite-support and faithful-atlas argument for global sections. The statement
is not disputed and needs no correction or dependency repair.

Validation: every compile uses scompile.py. The initial checks exposed only
elaboration of bundled module maps and the explicit ring argument of ModuleCat.of;
these were repaired in the helper constructions without altering the statement.

The final scompile invocation passed against the current server sources in 7.2 s,
with no errors or unexpected warnings. Its local attempt ran out of device space;
the wrapper automatically used its authorized server confirmation, which succeeded.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module `Sheaf.TraceFormula.DerivedBasisLocalExtSheaf` states
`AlgebraicGeometry.derived_basis_local_ext_sheaf`, with `sorry`, and defines no new objects.
It states Stacks Project Tag 0D66(2), read at `cohomology.tex`,
`lemma-vanishing-and-glueing`, including its proof and the reduction to part (1).
The node's statement is unchanged. The retained attempt contained only a `#check` test;
that file is preserved in `scratch/Test.lean`, outside the delivery's Lean tree. The
initial required dry run diagnosed the absent item node record. This delivery supplies
that record, the statement module and this report.

Hypothesis and conclusion correspondence:

- A morphism of arbitrary ringed spaces is `{X Y : RingedSpace.{u}} (f : X ⟶ Y)`.
  `RingedSpace` is Mathlib's `SheafedSpace CommRingCat`, with the induced morphisms of
  presheafed spaces. `f.hom.base` is continuous and `f.hom.c` is the structure-sheaf map.
  In particular there is no assumption that either space or the morphism is locally
  ringed. The dependency's Mathlib record names `LocallyRingedSpace.Hom`, but explicitly
  identifies its inherited `PresheafedSpace.Hom` base and sheaf map; those are exactly
  the general ringed-space morphisms used here. The source and signatures of both were
  read. No substitute structure or additional stalk hypothesis is used.
- The basis is the collection `(B : Set (Opens Y))`. `hB` asserts
  `IsTopologicalBasis ((fun V : Opens Y ↦ (V : Set Y)) '' B)`. Since members are already
  open, this is precisely that every open is a union of basis members. It does not
  require closure under finite intersections, nonemptiness, or a countable basis.
- The module category is the existing `SheafOfModules.{u} (moduleRings X)`;
  `ringedSiteModules` is the transparent general-site alias of this very category.
  Its standard Mathlib abelian structure is used, without choosing another instance.
- `K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))` allows unbounded objects.
  The two `HasDerivedCategory.{w}` binders choose localization Hom size, on X and on
  every open slice. They impose no boundedness or geometric assumption; the standard
  localization supplies them in a sufficiently large universe. All universe variables
  (`u`, `w`) and all term variables are explicitly bound, with `autoImplicit false`.
- `((Opens.map f.hom.base).obj V)` is the actual inverse-image open. Restriction is
  `(SheafOfModules.overFunctor (moduleRings X) U).mapDerivedCategory`, induced by
  restricting complexes termwise. Its module category uses `(moduleRings X).over U`,
  the restricted structure sheaf on the slice site of opens contained in U. This site
  is canonically equivalent to the opens of U; this is the established project encoding
  already used by `derived_hom_mayer_vietoris` and `derivedOpenHomRestriction`.
- `hneg` quantifies over every `V ∈ B` and every integer `i < 0`. Its `Subsingleton`
  asserts vanishing of exactly `Hom(K|f⁻¹V, (L|f⁻¹V)⟦i⟧)`. A Hom group contains zero,
  so `Subsingleton` means the zero abelian group, not emptiness of a type.
- The first conclusion quantifies over every open V, with the identical shifted Hom
  expression and every integer `i < 0`; it is exactly the asserted extended vanishing.
- The second conclusion gives
  `H : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}` and an additive equivalence
  `e V` between H(V) and the exact unshifted local derived Hom group, for every open V.
  The final universally quantified equation identifies each restriction H(V) → H(U)
  with the existing `derivedOpenHomRestriction` along the inverse-image inclusion.
  Thus H, e and this equation express that this precise Hom assignment, with its
  canonical restrictions and group law, is a sheaf. Pointwise unrelated group
  isomorphisms would be insufficient; restriction compatibility is included. Conversely
  the sheaf asserted in the node supplies H and its identity identifications, so the
  presentation adds no mathematical conclusion or hypothesis.

Dependency declarations read and used:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom`, with the inherited general
  `AlgebraicGeometry.PresheafedSpace.Hom` (base and structure map),
  `Mathlib.Geometry.RingedSpace.SheafedSpace`'s induced category, and
  `Mathlib.Geometry.RingedSpace.Basic`'s `AlgebraicGeometry.RingedSpace`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and its localization/shift structures.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`, with Mathlib's sectionwise linear morphisms.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` and the retained Mathlib `Sheaf`
  convention. Here the site is the opens with `Opens.grothendieckTopology`.
- `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`:
  `AlgebraicGeometry.moduleRings`, `moduleOverFunctor_additive`,
  `moduleOverFunctor_limits`, `moduleOverFunctor_colimits`, the analogous
  `moduleOverMap_*` instances, and `AlgebraicGeometry.derivedOpenHomRestriction`.
  I read the current published module via `scompile.py --source`, including the
  canonical comparison formula using `mapDerivedCategoryCompIso` and
  `mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap ...)`. The definition node
  `def-trf-ringed-derived-open-hom-restriction` now owns this statement API. The item
  cites that node instead of the Mayer–Vietoris exactness theorem.

The module imports each recorded proof-dependency module that is stated, as required
by the stage rules. The single unstated proof dependency
`lem-trf-unbounded-direct-image-section-presheaf` has no Lean record or Mathlib match,
so there is no module to import yet. It is needed only in the postponed proof, not
for typing this statement; no dependency wait or new duplicate statement is introduced.
The main theorem's docstring gives the node's full five-step argument: natural internal
Hom/derived sections comparisons; sheafification vanishing from the basis; a nonnegative
injective representative; sectionwise kernels; and restriction-compatible identification
with H^0 of the direct image, including the empty open.

Edge cases checked before writing: X or Y empty; empty B on an empty Y; empty inverse
image of a nonempty open; V empty; K or L zero; shifts -1 and arbitrarily negative i;
unbounded K and L; a basis not closed under intersections; and a ringed morphism with
nonlocal stalk maps. The sheaf is on the full opens site, so the empty cover is included.
The theorem neither asserts vanishing at i=0 nor restricts its sheaf clause to B.

Searches for an existing theorem:

- `msearch.py`, LeanFinder: “Negative Ext vanishing on a basis implies derived Hom
  presheaf is a sheaf”. Eight hits: `Sheaf.H`, `Sheaf.cohomologyPresheaf`,
  `Sheaf.cohomologyPresheafFunctor`, `Abelian.Ext`, `hasExt_iff`, `HasExt.standard`,
  and the two Grothendieck-abelian sheaf instances. None is this criterion.
- `msearch.py`, Loogle: `"DerivedCategory", "sheaf"`. Zero hits.
- `msearch.py`, grep in `Mathlib/Algebra/Homology`:
  `negative.*Ext|Ext.*negative|homPresheaf`. Zero hits.
- `rg` in upstream `WeilConjectures` for the item id: no match. A concept search for
  derived Hom sheaves / basis and Ext found specialized etale or Weil-sheaf internal
  Hom APIs and unrelated algebraic basis results, not this ringed-space theorem.
- `rg` in `lean/Sheaf` for Hom presheaves and derived restrictions found
  `DerivedMorphismPresheaf`, `EtaleDerivedMapPresheaves`, `RingedSiteDerivedRestriction`,
  `OpenHomTriangleRealization`, and `DerivedHomMayerVietoris`. The first two concern
  different specialized sites; the next gives object restriction only. The last two
  supply the canonical restriction maps used here and only a two-open Mayer–Vietoris
  result, not the arbitrary-basis sheaf criterion. The published upstream version of
  `DerivedHomMayerVietoris` is imported to avoid the retired library-side duplicate.

Validation: `scompile.py Q137 lem-trf-derived-basis-local-ext-sheaf` compiled the module
both as a sandbox file and with its intended library module name, cleanly (10.1 s and
15.0 s in the first check). No warnings or errors. The repair adds a definition node recording an existing API;
there is no new Lean definition, statement correction, dependency-module repair or dispute.


## New nodes

`def-trf-ringed-derived-open-hom-restriction` records the existing canonical map
`AlgebraicGeometry.derivedOpenHomRestriction` in
`WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`, together with `moduleRings`
and the six `moduleOverFunctor_*` / `moduleOverMap_*` instances. It defines the restriction
of local derived Hom by applying derived further restriction and conjugating with the
canonical comparison. Source: Stacks 08BW's restriction maps and 0D66(2)'s Hom assignment.
Its four definition dependencies supply ringed spaces, module sheaves, derived categories,
and the open-covering site. The primary Lean signature is copied verbatim from the
published source, including its explicit three localization-universe binders. The body
uses `mapDerivedCategoryCompIso` and the derived `overFunctorMap` isomorphism; it does
not use the Mayer–Vietoris theorem. The new record is `existing: true`, so no module or
construction is duplicated. The pre-existing general-site derived-restriction node gives
object restriction but does not own this Hom map or the ringed-space instances.

Searches (2026-10-19): LeanSearch's query “Canonical restriction on derived Hom of sheaves
of modules along an inclusion of open subsets of a ringed space” returned eight ordinary
restriction/global-section hits. LeanFinder's query “Restrict morphisms in the derived
category of module sheaves to a smaller open subset” returned eight ordinary restriction
hits. The Mathlib grep `derivedOpenHomRestriction|moduleOverFunctor_|moduleOverMap_`
in `Algebra/Category/ModuleCat` returned zero hits. Source/library rg found the retained
library-side module and consumers; `scompile.py --source` gives its exact published
upstream replacement. DAG rg found theorem records and consumers but no owning definition
node; `blueprint_refs.py search 'derived open Hom restriction'` returned zero blueprint
matches. The new node stores the search-tool results verbatim and these local results.

Edge cases: W empty, U empty, X empty, W=U with identity inclusion, either E or F zero,
unbounded E and F, and arbitrary inclusions without any cover. All are permitted by the
read definition. Its map uses the canonical isomorphism, so no arbitrary-map choice or
new hypothesis has been inserted.

## Repair of independent return L at 2afec1ee4ccc

H2/theorem stmt_dep is repaired by replacing the added
`lem-sc-derived-hom-mayer-vietoris` statement dependency with the new definition node
`def-trf-ringed-derived-open-hom-restriction`. The latter explicitly lists precisely the
plain declarations used to type the item. The theorem module stays byte-identical.
The saved packet was compared with the current shared node: only `lean` and `stmt_deps`
differ, and the mathematical statement and proof are unchanged. The delivery wrapper
rebases the repaired packet on current newtargets-dag. An initial saved-packet dry run
was invoked before editing, as required; it waited for the shared fetch.

## Second reading by Q137

Self-check of the repair (no separate worker was started, per the dispatcher's instruction):
opened the item node, its unchanged Lean file, the new definition node and the published
upstream source. The original independent review L accepted every mathematical clause
of this exact Lean file; its one requested ownership repair is now applied. For the new
node, X is `RingedSpace`, the ring alias is `moduleRings`, r_T is `overFunctor`, s_i is
`overMap`, the three derived categories are explicit binders, and the displayed formula
is exactly `e.inv.app E ≫ ...map f ≫ e.hom.app F` in the source. Its listed instances
supply additivity and preservation of finite limits and colimits. There is no cover,
vanishing, or boundedness assumption. Rechecked the item's basis, all negative shifts,
all-open vanishing, additive sheaf identifications and canonical restriction equation:
all are unchanged. No mathematical mismatch or statement correction was found.

Repair validation: the saved-packet dry run passed at `baebcf9d3d`. After applying the
requested ownership repair, `scompile.py` compiled the unchanged file cleanly as both
`Sheaf.Stage2.Sandbox0` (12.5 s) and
`Sheaf.TraceFormula.DerivedBasisLocalExtSheaf` (9.5 s). The repaired packet dry run
passed preflight and all file checks at `7eb3d060c2`, including the existing declaration
check for the new definition node. The final self-check verified the exact item signature,
unchanged mathematical statement, exact new definition-dependency citations and the
`existing: true` record without a file.

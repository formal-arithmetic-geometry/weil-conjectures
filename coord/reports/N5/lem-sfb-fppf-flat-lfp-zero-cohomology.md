## Worker report

The module `Sheaf.AlgebraicGeometry.FppfFlatLfpZeroCohomology` states
`AlgebraicGeometry.Scheme.fppf_flat_lfp_zero_cohomology`, with `sorry` as its only
postponed proof. It also constructs the instance
`AlgebraicGeometry.Scheme.fppfStructureModuleEnoughInjectives` by applying the
existing Grothendieck-category theorem and enough-injectives construction.
This helper contains no postponed data or new axiom.

Sources read: Descent `definition-parasitic` (06ZL) and
`lemma-cohomology-parasitic` (0755), including the full fppf proof;
Cohomology on Sites `lemma-cohomology-modules-abelian-agree` (03FD), including
the objectwise assertion and its proof. The statement is exactly part (1) of
0755 specialized to sheaves and written with its explicit sectionwise
hypothesis; no source correction is needed.

Hypothesis and conclusion correspondence:

- The size convention is expressed by explicit universes `u w`: schemes are
  `Scheme.{u}`, the over-site has object universe `u+1` and morphism universe `u`,
  and module/abelian values lie in `max (u+1) w`. Increasing `w` allows arbitrarily
  large coefficients without equating the site's object and morphism universes.
  The ambient category is small in that common universe.
- The arbitrary scheme is `(S : Scheme.{u})`. The site is
  `fppfTopology.over S` on `Over S`, exactly the recorded big fppf site.
- The structural ring is the existing `sfbFppfRings S`. Its definition is
  `sheafCompose` forgetting commutativity of `sfbFppfStructureSheaf S`;
  the latter is `Sheaf.over` of `Scheme.Γ`, using `isSheaf_Γ`. Thus its values
  and restrictions are the actual global regular functions and their pullbacks.
  It is not a variable ring, constant coefficient ring, or selected arbitrary ring.
- The arbitrary module sheaf is
  `P : ringedSiteModules.{max (u+1) w} (sfbFppfRings S)`; this is the recorded
  transparent abbreviation of Mathlib's `SheafOfModules`.
- The entire sectionwise hypothesis is `hP : ∀ V : Over S,
  Flat V.hom → LocallyOfFinitePresentation V.hom →
  Subsingleton (P.val.obj (op V))`. A module is zero precisely when its
  underlying additive group has one element. There is no constraint on other
  objects, and there is no quasi-coherence, affineness, qcqs, or finiteness binder.
- The first conjunct quantifies over exactly the same `V`, flatness and local
  finite-presentation hypotheses, followed by all `q : ℕ`. Naturals encode all
  integers q≥0, including q=0. The functor is
  `SheafOfModules.toSheaf ... ⋙ sheafToPresheaf ... ⋙
  CategoryTheory.evaluation ... (op V)`, with `rightDerived q` applied AFTER
  composing, and then evaluated at P. Thus the resolutions are in module sheaves,
  as required; it does not derive evaluation after forgetting P first.
- Each conclusion is categorical `IsZero` of an object of `AddCommGrpCat`,
  expressing vanishing of the group. The second conjunct explicitly repeats this
  at `Over.mk (𝟙 S)` for every q, as the stated particular case.
- Enough injectives is not a hypothesis: the public helper instance is the
  existing `IsGrothendieckAbelian.enoughInjectives` applied to
  `SheafOfModules.isGrothendieckAbelianOfUniverses` with site universes `u+1,u`,
  ring universe `u`, and extra bound `w`. It preserves Mathlib's abelian structure.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`. The precoverage consists of jointly surjective
  flat locally finitely presented families; the slice is the specified big site.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, its
  stalkwise characterization, `Flat.comp`, `Flat.isStableUnderBaseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `locallyOfFinitePresentation_comp`, and its base-change instance.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`;
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution`; `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `Functor.rightDerived` (injective resolutions and degreewise homology).
- `Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`:
  `Scheme.sfbFppfStructureSheaf`, `Scheme.sfbFppfRings`, including their
  sectionwise construction; no quasi-coherent equivalence or quasi-coherence
  condition is used. The new definition node
  `def-sfb-big-fppf-structure-sheaf` records both existing plain declarations,
  and is the statement dependency. The equivalence theorem is not cited.
- Proof imports include `WeilConjectures.CategoryTheory.SiteCechComplex`:
  `CategoryTheory.SiteCechComplex`, and
  `WeilConjectures.CategoryTheory.SiteCechVanishingCriterion`:
  `CategoryTheory.Sheaf.isZero_H'_of_siteCech_vanishing`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`:
  `SheafOfModules.isGrothendieckAbelianOfUniverses`; and
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`:
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`.
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`:
  `CategoryTheory.module_abelian_evaluation_comparison` and its general-site
  interface `module_abelian_evaluation_comparison_general`; the comparison
  retains degree-zero normalization and every compatible resolution-lift formula.
- The permanence proof dependency imports
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, together with the flat
  and finite-presentation modules. Its only clause used here is base change of
  local finite presentation; no qcqs hypothesis enters the signature.

The docstring follows all four DAG proof steps: stability of the collection
under covering arrows and iterated fibre products; zero Cech terms, including
empty products; the Cech criterion and module/abelian comparison; degree zero
and the identity arrow.

Edge cases checked mathematically before writing: q=0 is covered by the
section hypothesis and the normalized comparison; the identity is flat and lfp
and is explicitly included. The empty scheme and empty coverings cause no
problem (products of zero abelian groups, including empty products, are zero).
The zero sheaf satisfies the hypothesis. An arbitrary nonflat/non-lfp test
object has no sectionwise requirement. Arbitrary characteristic and nonaffine,
non-quasi-separated schemes are allowed. Repeated indices in Cech products
are covered by base change, not by an assumption that overlaps are affine.
The universe bound includes the full site's objects and arrows.

Searches actually run through msearch.py (N5, this item):

- LeanFinder: `A sheaf of structure modules on the big fppf site zero on flat
  locally finitely presented objects has zero derived evaluation cohomology`:
  eight hits (finite-presentation/quasi-coherence definitions and `Sheaf.H`);
  none states this vanishing theorem.
- Loogle: `"Sheaf", "cohomology", "zero"`: zero hits.
- Mathlib grep in `CategoryTheory/Sites`:
  `parasitic|fppf.*cohom|fppf.*structure`: zero hits.
- LeanSearch: `A parasitic sheaf on the big fppf site has zero cohomology on flat
  locally finitely presented objects`: eight hits, including `Sheaf.H` and
  `Sheaf.cohomologyPresheaf`, otherwise module finite-presentation notions;
  no match for this theorem.
- Direct rg of project `Sheaf` and `WeilConjectures` for fppf structural rings,
  module/cohomology and parasitic terms found the existing
  `SchemeBigFppfQuasicoherentEquivalence` structure sheaf and the distinct affine
  quasi-coherent acyclicity theorem. The latter has an affine hypothesis, positive
  degree, and quasi-coherent coefficients, so is not this result.
- Direct rg of `WeilConjectures` for the exact item id found no match. Direct rg
  of both source trees and `dag/lean_names_upstream.json` for the proposed theorem
  and instance names found no match. No duplicate notion is introduced.

The repair adds one definition node recording existing declarations, with no
new module or copied definition. The item changes only its Lean record and
stmt_deps. No unusable dependency or statement fault was found. The sole theorem proof is `sorry`; the helper instance is a real
application of existing constructions.

Validation: the first compile found namespace shadowing of `evaluation` by
`AlgebraicGeometry.Scheme.evaluation`; using `CategoryTheory.evaluation` fixed it.
The next compile succeeded with one line-width warning, which was repaired.
The prescribed clean compile and delivery preflight are run before delivery.


## Repair of returned delivery ceda640af9e7

H2: repaired. The returned packet cited the theorem node
`lem-sfb-scheme-big-fppf-quasicoherent-equivalence` merely to access its plain
structure-sheaf definitions. Removed that theorem from stmt_deps and cited the
new definition node `def-sfb-big-fppf-structure-sheaf` instead. Its existing:true
record names both `AlgebraicGeometry.Scheme.sfbFppfStructureSheaf` and
`AlgebraicGeometry.Scheme.sfbFppfRings` in the already published module, without
moving, copying, or editing either declaration. The consumer Lean module is
byte-identical to the returned delivery retained in the sandbox. The node copy
was rebased onto current main (whose differences from the retained packet were
only lean and stmt_deps), preserving all other current fields. No repair note
exists for this item. The maintainer explicitly checked the Lean substance and
requested only this definition-node repair.

## New nodes

`def-sfb-big-fppf-structure-sheaf` defines the actual sheaf of global regular
functions on the big fppf site, with canonical pullback restrictions, and its
version with commutativity forgotten. Source: Descent Tag 03DU,
`definition-structure-sheaf` (1), the big-site structure sheaf.
The existing declarations in SchemeBigFppfQuasicoherentEquivalence.lean
lines 136-146 give these definitions exactly: Sheaf.over of Scheme.Γ, then
sheafCompose with forget₂ CommRingCat RingCat. The Lean record is existing:true.
The empty scheme has its ordinary zero ring of sections, identity restrictions
and composite restrictions are the functor's, and all scheme universes are
retained. This adds no mathematical assumption or theorem.

New-node searches actually run: LeanSearch query 'The structure sheaf on the
big fppf site of a scheme assigns global regular functions to every scheme
over the base' returned eight global-sections and scheme-sheaf hits, no exact
fppf-over-site structure sheaf. LeanFinder query 'Structure sheaf on the big
fppf site obtained by restricting the global sections functor to schemes over
a base' returned eight similar scheme-sheaf/global-sections hits. Mathlib
grep 'fppf.*[Ss]tructure|[Ss]tructure.*fppf|isSheaf_Γ' in AlgebraicGeometry
returned zero hits. Direct rg of WeilConjectures and Sheaf found the exact
existing project definitions named above; no duplicate definition is written.
DAG grep found uses of structure sheaves and the separate algebraic-space
ringed-comparison definition, but no standalone scheme big-fppf structure-sheaf
node. blueprint_refs.py search 'big fppf structure sheaf' returned zero matches;
its ancestor query returned None, retained as null in blueprint.from.node with
the item's recorded via chain extended by the item. Current server source was
also read through scompile.py --source and agrees with these declarations.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

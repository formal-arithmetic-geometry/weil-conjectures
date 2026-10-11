## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ClosedSubsetProperOverBase.lean` defines
`AlgebraicGeometry.Scheme.IsClosedSubsetProperOver` and
`AlgebraicGeometry.Scheme.Modules.HasSupportProperOver`. Both are full Prop-valued definitions,
with no sorry, additional theorem, chosen unknown data, or statement correction. The support
is written inline, as required by the standing brief's SUPPORT OF A MODULE convention.

Hypothesis and clause correspondence:

- Schemes X and S: explicitly bound `{X S : Scheme.{u}}`, with the universe `u` declared.
- The specified morphism f: `(f : X ⟶ S)` in both predicates.
- Locally of finite type: `[LocallyOfFiniteType f]` in both predicates. This is retained even
  though condition (1) itself can be defined without this assumption; the node and 0CYM have it.
- A closed subset Z of X: `(Z : TopologicalSpace.Closeds X)` in the first definition.
- The ideal of local sections vanishing on Z: `IdealSheafData.vanishingIdeal Z`, the very
  construction used in the recorded `reduced_induced_closed_subscheme` dependency. Its affine
  ideals are the vanishing ideals of the inverse image of Z in each affine spectrum.
- The reduced induced closed subscheme and its inclusion: the `.subscheme` and `.subschemeι`
  of that ideal. The dependency theorem states the sectionwise evaluation description,
  radical affine ideals and their localizations, reducedness, closed immersion, image Z,
  quotient-spectrum pullback squares, and uniqueness over X. The definition uses its
  existing data rather than constructing a private substitute or choosing from a sorry.
- Composite f after the inclusion: `(IdealSheafData.vanishingIdeal Z).subschemeι ≫ f`.
- Clause (1), properness: `IsProper` of this composite. The dependency's uniqueness over X
  supplies the mathematical independence of subscheme representatives; no new theorem
  concerning this independence is needed to define the canonical representative.
- An arbitrary O_X-module F on the underlying Zariski space: `(F : X.Modules)`.
  Mathlib's `Scheme.Modules` is `SheafOfModules.{u} X.ringCatSheaf`. No quasi-coherence,
  finite-type or coherence restriction is added.
- Clause (2), its support: the inline set
  `{x : X | ¬ Subsingleton
    ((PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).obj F.val)}`.
  The recorded functor's object is `stalkObj`, whose carrier is exactly the Mathlib abelian
  presheaf stalk of `F.val.presheaf`, definitionally the carrier of `F.presheaf.stalk x`.
  A module is zero precisely when its carrier is subsingleton; negating this means F_x ≠ 0.
  This is an explicit definition of the support locus inside the predicate, with no separate
  conflicting support construction (and is not `IdealSheafData.support`).
- Clause (3), support closed and proper: `∃ Z : TopologicalSpace.Closeds X,
  (Z : Set X) = <the support set> ∧ IsClosedSubsetProperOver f Z`.
  Existence of such a bundled closed set is precisely closedness of the support, and the
  equality forces the properness test to apply to that exact set, rather than its closure
  or some larger closed set. Conversely a closed support supplies that witness directly.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper` (extends
  separatedness, universal closedness and locally finite type; universal closedness implies
  quasi-compactness, so this is the node's finite-type properness).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`,
  and `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, as supplied in
  the imported reduced-induced dependency's statement. They are not redundant assumptions.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`, with its
  Mathlib `vanishingIdeal`, `subscheme` and `subschemeι` data.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, used through
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`'s `AlgebraicGeometry.Scheme.Modules`.
- `Sheaf.Topology.PresheafModuleStalkFunctor`: `PresheafOfModules.moduleStalkFunctor`
  and its `stalkObj` object construction, applied to the existing `F.val`.

Edge cases checked before writing: Z empty gives the empty reduced closed subscheme,
whose map is proper; Z all of X uses X_red, not X with its possible nilpotents. Empty X
has empty support for every module. The zero module has subsingleton stalks, hence empty
support. A module with a nonclosed support fails the existential closed-set equality;
there is no automatic closedness assumption and no substitution of its closure. A nonproper
support is rejected by the properness conjunct. Arbitrary base schemes, nonreduced schemes,
and all characteristics remain allowed. There are no index-universe restrictions. The
universe choice `X.Modules` follows the project's scheme-module convention exactly.

Sources opened: local Stacks TeX is absent on this machine, so the official pages
https://stacks.math.columbia.edu/tag/0CYM,
https://stacks.math.columbia.edu/tag/0CYL,
https://stacks.math.columbia.edu/tag/01AT,
https://stacks.math.columbia.edu/tag/01J4 and
https://stacks.math.columbia.edu/tag/0CYS were read. They confirm the reduced induced
properness condition and the nonzero-stalk support. As the node explicitly says, its
closed-support predicate extends the phrase to arbitrary modules; Stacks uses it in the
finite-type quasi-coherent case where closedness holds automatically.

Searches performed using `/home/ubuntu/weil-launcher/msearch.py`:

- leanfinder: `closed subset proper over base scheme and support of sheaf of modules proper
  over base` returned eight hits on `Scheme.IdealSheafData.support`, `.supportSet`,
  `.isClosed_supportSet`, `.support_map`, `.mem_support_iff`, `.mem_supportSet_iff`,
  `.coe_support_mkOfMemSupportIff` and `Scheme.Hom.support_ker`. These concern zero loci of
  ideal sheaves and scheme-theoretic images, not this proper-support notion. The retrieved
  prose descriptions were checked against the actual source rather than trusted.
- loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`
  returned zero hits.
- leansearch: `closed subset of scheme proper over base; support of sheaf of modules`
  was unavailable (Internal Server Error); the other searches succeeded.
- grep in Mathlib/AlgebraicGeometry: `properOver|ProperOver|supportProper|SupportProper`
  returned zero hits.
- rg in the source `WeilConjectures/` and project `lean/Sheaf/`:
  `properOver|ProperOver|supportProper|SupportProper|moduleSupport|Modules.*support`
  found no matching predicate. Source hits involved supports of section zero loci.
- `grep -rn 'def-weil-pbc-closed-subset-proper-over-base'` in the source returned no hits.
- Broader source support inspection found `WeilSheaf.support` in `WeilSheaf/Stalk.lean`:
  it concerns geometric stalks of Weil sheaves at closed points, a different coefficient
  category and set of points, and cannot represent the Zariski O_X-module support here.
- rg of `IsClosedSubsetProperOver|HasSupportProperOver` across Mathlib, project Lean,
  source Lean and `dag/lean_names_upstream.json` found no declaration-name collision.

No new nodes or dependency repairs are needed. No STATEMENT-DISPUTED or node faults.
Server single-file compile completed cleanly in 1.7 seconds (exit code 0, no warnings).
The independent second reader will write the second-reading section and deliver.

## Second reading by H1

The node introduces the following data and clauses, matched against
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:

- Schemes `X S : Scheme.{u}` and a morphism `f : X ⟶ S` are the binders of
  `Scheme.IsClosedSubsetProperOver` and `Scheme.Modules.HasSupportProperOver`.
  The instance `[LocallyOfFiniteType f]` is present in both definitions, exactly
  as required by the source's standing hypothesis.
- A closed subset `Z : TopologicalSpace.Closeds X` is represented by
  `IdealSheafData.vanishingIdeal Z`; its reduced induced closed subscheme and
  inclusion are the existing `.subscheme` and `.subschemeι` supplied by
  `reduced_induced_closed_subscheme`.  This is the node's vanishing ideal and
  reduced induced structure, rather than a private construction.
- Clause (1), properness, is rendered exactly by
  `IsProper ((IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)`.
- For `F : X.Modules`, the support locus is the inline set of points whose
  stalk object is not `Subsingleton`, using
  `PresheafOfModules.moduleStalkFunctor X.ringCatSheaf` applied to `F.val`.
  This is definitionally the nonzero-stalk locus in the node.
- Clause (3) is the existential bundled closed set `Z` whose underlying set is
  exactly that support locus and for which `IsClosedSubsetProperOver f Z` holds.
  Thus closedness and properness are both required, with the same quantifier
  order as the node.

The source places (Stacks 0CYM/0CYL, 0CYS, 01AT, and 01J3/01J4) were checked
against these clauses.  The empty closed set, the whole set (giving the reduced
scheme), empty schemes, zero modules (empty support), arbitrary characteristics,
and arbitrary base schemes are all covered.  No extra Noetherian, finite-type
module, quasi-coherence, characteristic, or universe restriction was introduced.

Searches (LeanFinder/Loogle/grep and source-project `rg`) found no existing
declaration for either proper closed subsets over a base or proper support of a
scheme module; the only support hits concern ideal sheaves, affine modules, or
Weil-sheaf stalks.  The dependency declarations and their signatures were read,
including `reduced_induced_closed_subscheme`; no dependency was unusable and no
new node was needed.  There was no mismatch to repair and no statement
correction.  The module compiled cleanly with `scompile.py` (exit code 0; only
the expected definition declarations, no warnings).

## Worker report

The module `Sheaf.AlgebraicGeometry.CompactificationMiddleOverBase` states
`AlgebraicGeometry.Compactification.compactification_middle_over_base`.
Its whole proof is `sorry`; no definitions or auxiliary theorems are introduced.
The node is unchanged except for its `lean` record. No statement correction,
new node, dependency repair, or mathematical dispute is needed.

The source is the current blueprint main-20261015, unit
`sk-def-sfb-dc-setting/_section.md`, statement paragraph 3. It says that a given
compactification's middle scheme stays separated and finite type over the base
field and that both arrows are base morphisms. This item's generalization to a
qcqs scheme base and explicit uniqueness and quasi-compactness are valid by the
five proof steps recorded in the node. The declaration docstring reproduces
those steps, with their dependency ids and Stacks tags.

Hypotheses and objects, clause by clause:

- `S : Scheme.{u}`, `[CompactSpace S]`, and `[QuasiSeparatedSpace S]` express
  precisely the stated scheme base and its two topological conditions. The latter
  class means that the intersection of two compact opens is compact; compactness
  here does not include any Hausdorff hypothesis.
- `{X Y : Over S}` bundles the two schemes and the explicitly named structure
  morphisms: `X.left`, `Y.left`, `X.hom = a_X`, `Y.hom = a_Y`. This is the
  recorded category of schemes over the base, not a change of objects.
- `(f : X ⟶ Y)` supplies its underlying scheme map `f.left`, together with exactly
  `f.left ≫ Y.hom = X.hom`, which is `a_Y ∘ f = a_X`.
- `[IsSeparated Y.hom]` is separatedness of `a_Y`.
- `[LocallyOfFiniteType Y.hom]` and `[QuasiCompact Y.hom]` are both parts of finite
  type, as the finite-type dependency's record explicitly prescribes.
- `(c : BoundaryCompactification f.left)` is the dependency's recorded notion
  of an arbitrary compactification. Its underlying upstream compactification is
  `c.obj.obj`, with `Z`, `i`, `g = p`, `comm : f.left = i ≫ g`, an open-immersion
  instance on `i`, and a properness instance on `g`. The intermediate full
  subcategory records quasi-compactness of `i` as `c.obj.property`. The outer
  boundary-refinement category adds no restriction to its objects: it specifies
  which refinements are morphisms. No density hypothesis is imposed.

Conclusions, clause by clause:

- `(∃! aZ : c.obj.obj.Z ⟶ S, c.obj.obj.i ≫ aZ = X.hom ∧
  c.obj.obj.g ≫ Y.hom = aZ)` is existence and uniqueness of the structure morphism
  making both maps base morphisms. Its second equation explicitly identifies
  `aZ = a_Y ∘ p`; its first is the other required triangle. Uniqueness concerns
  all such structure morphisms, without geometric restrictions in its predicate.
- The existing `c.obj.obj.overObj.hom` is definitionally `c.obj.obj.g ≫ Y.hom`.
  Hence `IsSeparated c.obj.obj.overObj.hom` states separatedness for exactly that
  unique structure, and `LocallyOfFiniteType c.obj.obj.overObj.hom` together with
  `QuasiCompact c.obj.obj.overObj.hom` states its finite type.
- `CompactSpace c.obj.obj.Z` is absolute quasi-compactness of the middle scheme.
- `c.obj.obj.overI ≫ c.obj.obj.overG = f` states the factorization in `Sch/S`.
  These are the existing canonical slice arrows, whose `.left` maps are
  definitionally `c.obj.obj.i` and `c.obj.obj.g`. Thus they use exactly the given
  underlying morphisms, not new chosen arrows.
- `IsOpenImmersion c.obj.obj.overI.left`, `QuasiCompact c.obj.obj.overI.left`,
  and `IsProper c.obj.obj.overG.left` explicitly retain the quasi-compact open
  immersion and proper map in that slice factorization.
- The binders include no finite-type or separatedness assumption on `X.hom`.
  The given `c` is universally quantified data; the conclusion never asserts
  that a compactification exists, nor chooses one.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`,
  `Scheme.Hom.isOver_iff`; the bundled form is `CategoryTheory.Over` and its
  morphisms from `Mathlib.CategoryTheory.Comma.Over.Basic`, read in full at
  their definitions, including `Over.w`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  extending separatedness, universal closedness and local finite type.
  `IsSeparated` is the diagonal-closed-immersion class in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.Compactification.BoundaryRefinement`:
  `QuasiCompactObjects`, `boundaryRefinementProperty`, `BoundaryCompactification`,
  and `DenseBoundaryCompactification` were inspected. The statement uses the
  dependency's recorded `BoundaryCompactification` directly.
- `WeilConjectures.Compactification.Defs`: `Compactification`, including its
  complete fields and docstring; accessed through the recorded dependency.
- `WeilConjectures.Compactification.Over`: `overObj`, `overI`, `overG`,
  `overObj_hom`, `overI_left`, `overG_left`, `overI_overG`, and the instances
  `locallyOfFiniteType_overObj`, `quasiCompact_overObj`, `isSeparated_overObj`.
  These implement the canonical construction used in the conclusion.

All statement-dependency modules are public imports. Proof dependencies are
Mathlib leaves: separated composition is `IsSeparated.instCompScheme`, finite
 type composition is `locallyOfFiniteType_comp` and `quasiCompact_comp`, and
absolute quasi-compactness is `QuasiCompact.compactSpace_of_compactSpace`.
Their source signatures were inspected and their modules are already imported
by the statement dependencies, so no additional proof imports are necessary.

Edge cases checked before drafting:

- Empty base: any scheme with a structure map to it is empty, including `Z`
  via `p` and `a_Y`. Both triangles, uniqueness and quasi-compactness remain valid.
- Empty source: the statement allows any given proper middle scheme over `Y`
  with the specified empty open immersion, without density or nonemptiness.
- Identity compactifications and empty middle schemes are allowed.
- Nonreduced schemes, arbitrary characteristic, and non-Noetherian qcqs bases
  are retained. The theorem does not use a field, an affine-base hypothesis,
  smoothness, density, or a compactification-existence theorem.
- Only separatedness and finite type of `a_Y` are used for the geometric
  conclusions. No property of `a_X` is smuggled into the binders. An actual
  compactification may itself imply properties of the underlying `f`, as intended.
- All objects use an explicit arbitrary universe `u`; all variables are bound
  and `autoImplicit` is disabled. There are no restricted test-object universes.

Searches for an existing full statement (2026-10-21):

- `msearch.py leanfinder`: “A compactification of a morphism of schemes over S
  lifts uniquely to the slice category over S; its middle scheme is separated
  finite type over S and quasi-compact if the target is separated finite type
  and S is qcqs”. Eight hits, including `Scheme.Hom.isOver_iff` and valuative
  criteria; none states the full result.
- `msearch.py leansearch`: “A factorization of a scheme morphism over a base has
  a unique structure morphism on the middle scheme making both arrows morphisms
  over the base”. Eight hits, mostly generic `Factorisation` data and the
  slice factorization-system instance; none combines this result's clauses.
- `msearch.py loogle`: `AlgebraicGeometry.IsSeparated,
  AlgebraicGeometry.Compactification` reported the project-only compactification
  name unknown to the search service. The follow-up query
  `AlgebraicGeometry.IsSeparated, CategoryTheory.CategoryStruct.comp` returned
  twelve hits including separated composition, not the full statement.
- `msearch.py grep`: `Compactification|compactification|IsOver` in
  `AlgebraicGeometry/Over.lean` returned the five `IsOver` interface hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for compactification,
  middle-over-base, and unique structure morphisms located the existing
  `Compactification.Over` API and `Sheaf.SixFunctors.CompactificationOverBase`.
  The former covers the canonical maps and geometric properties separately,
  but lacks the combined uniqueness and absolute quasi-compactness statement.
  The latter asserts compactification existence under different hypotheses,
  so neither can be recorded as an exact existing declaration of this node.
- Direct search of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib's algebraic
  geometry directory and `dag/lean_names_upstream.json` found no existing
  declaration named `compactification_middle_over_base`. Searching the item's
  id in `lean/WeilConjectures` also found no attachment.

Validation: `scompile.py NX lem-sfb-compactification-middle-over-base` compiled
both the sandbox and the library-named module on the server without errors or
warnings (7.4 s and 9.2 s). No local compiler or global build was run.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

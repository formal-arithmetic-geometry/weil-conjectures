## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupTorsorStackification` states
`AlgebraicGeometry.SchemeAction.affineGroup_torsor_stackification` with one `sorry`.
It gives the arbitrary-affine-group version of Stacks 0370 and 04WM. No definition
is introduced and no theorem is proved. The natural-language proof in its docstring
follows all eight DAG proof steps, including affine effectivity without finite
presentation of the descended object and the inverse-right-translation convention.

Clause-by-clause correspondence:

- Field k: `(k : Type u) [Field k]` uses the Mathlib field declaration.
- Group scheme G over k: `G : Over (Spec (CommRingCat.of k))` with `[GrpObj G]`.
  The recorded internal group object supplies multiplication, inverse and unit.
- Affine G: `[IsAffineHom G.hom]`. Over the affine scheme Spec k this is equivalent
  to affineness of G. There are no smoothness or finite-type binders.
- Arbitrary k-scheme V with left action: the second `Over` object V and `[ModObj G V]`.
  The action is a scheme morphism, with unit and associativity laws. No affineness,
  separation, smoothness or finite-type condition on V occurs.
- Size and site: explicit universe `u`; schemes and fields have size u, total objects
  have size u+1 and total arrows size u. The base is `Over (Spec (CommRingCat.of k))`.
  `IsFppfStackification`, `IsFppfModuliStack` and `IsLocallyTrivial` all use precisely
  `Scheme.fppfTopology.over S`, the recorded big fppf topology. The arbitrary level
  u supplies the chosen size bound, rather than imposing a countability condition.
- The action groupoid: `actionGroupoid G V`, with `ActionObject.point : base ⟶ V`
  and `ActionHom.label : X.base ⟶ G`; its equation is `label • X.point = base ≫ Y.point`.
  Over an identity this is exactly g·x=y. Composition label is (g'∘b)g.
- Stackification A: the binders `A`, `i` and `hi : IsFppfStackification i` specify
  an arbitrary stackification of that action groupoid. This is the existing
  universal-property formulation of the same stackification, as documented in
  def-sfb-fppf-stackification; it is not an arbitrary extra map or an assumed
  equivalence. The local-description theorem is imported for the proof route.
- Objects of T: `torsorGroupoid G V` uses existing `TorsorObject`. Its `space`
  and `base` are schemes over k; `action`, `projection` and `invariant` give a
  left G_T action over T. `local_trivial` is the existing fppf covering-sieve
  condition, giving equivariant cartesian trivializations G×W→P. Its `map` and
  `equivariant` fields are precisely the specified equivariant map P→V.
- Arrows of T: existing `TorsorHom` has an equivariant scheme map, a cartesian
  base square, and `commutes` with the maps to V. Over id_T these are exactly
  the equivariant T-isomorphisms in the item. Cartesian arrows encode the actual
  fibre-product pullbacks, up to their canonical unique isomorphisms.
- T is an fppf stack: the first conjunct `IsFppfModuliStack (torsorGroupoid G V)`
  is the existing total-category stack condition. It includes fibred-in-groupoids,
  unique gluing of arrows and effective object descent on every covering sieve.
  This uses the generic fibred-groupoid convention from the recorded stable-moduli
  dependency, without imposing any stable-curve condition on these torsors.
- Pullback-compatible equivalence A≃T: the based functors F and H, with the first
  two `Nonempty` isomorphism clauses, give both inverse natural isomorphisms.
  Isomorphisms in the category of based functors are vertical, not merely ordinary
  natural isomorphisms of total categories. Since the categories are fibred in
  groupoids, based functors preserve the cartesian pullback arrows.
- Extension and object/arrow formulas: the final clause
  `Nonempty (i.comp F ≅ trivialTorsorFunctor G V)` identifies the extension with
  the existing canonical functor. `trivialObject.map` is the actual morphism
  (h,t)↦h·x(t); `trivialArrowMap` is the actual map (h,t)↦(hg(t)⁻¹,b(t)).
  Thus the convention is specified up to the invertible comparison inherent in
  extending a functor along stackification. No uncharacterized functor is substituted.
- Scheme torsors: `TorsorObject.space : Over S`, not an algebraic space or a
  sheaf selected from an existence proposition.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, specialized to
  `Over (Spec (CommRingCat.of k))` (def-sc-group-scheme).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms
  (def-pc-scheme). Size convention def-weil-size-convention has no declaration.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; the slice site is `GrothendieckTopology.over`
  (def-pc-fppf-site). These are publicly available through the reused modules.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `CategoryTheory.IsModuliStack` and the
  vertical morphism convention. The fppf specialization below uses those notions.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `CategoryTheory.Pseudofunctor.exists_groupoid_stackification_local_description`.
  Its full signature and docstring were read; this is a private proof import
  because the theorem statement uses the existing equivalent based-category
  universal-property interface, not a private replacement for it.
- `Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids`:
  `AlgebraicGeometry.SchemeAction.actionGroupoid`, `torsorGroupoid`,
  `trivialTorsorFunctor`, and their existing defining objects and arrows.
- `Sheaf.CategoryTheory.SiteStackification`: `CategoryTheory.IsFppfModuliStack`
  and `CategoryTheory.IsFppfStackification`.

The last two landed definition nodes are added to stmt_deps to record the notions
already present in Lean. All previous statement dependencies are preserved. No new
node and no dependency repair is needed. The node statement is unchanged.

Proof-only imports: `WeilConjectures.AlgebraicGeometry.AffineFlatDescent`
(`Over.DescentDatum.isEffective_of_isAffineHom_flat_affine`) and
`Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction`
(`fppf_family_isEffective_of_affine_singletons`), plus the local-description
module above. The remaining affine permanence, affine local-target and representable
fpqc descent prerequisites are in the imported Mathlib Affine/Fpqc modules.
`lem-sfb-stack-fully-faithful-local-equivalence` has no recorded Lean or Mathlib
match in the read DAG, so there is no module to import for it yet; it is used only
in the natural-language proof, not to formulate the statement. No construction or
statement dependency is missing.

Searches for existing notions and exact statements (2026-10-24):

- msearch.py leanfinder, query "The stackification of the action groupoid of an
  affine group scheme is equivalent to the fppf stack of scheme torsors with
  equivariant maps, without smoothness or finite type": 8 hits, including affine
  scheme/CommRing equivalence and abstract pseudofunctor descent equivalences;
  no affine-group scheme-torsor comparison.
- msearch.py leansearch, query "affine group scheme action quotient stack equivalent
  to torsors": 8 hits, on AddTorsor, affine equivalences and ordinary action quotients;
  none is this theorem.
- msearch.py loogle, query "CategoryTheory.GrpObj,
  CategoryTheory.IsFppfStackification, AlgebraicGeometry.SchemeAction.torsorGroupoid":
  0 hits, unknown project-only IsFppfStackification, as expected for Mathlib search.
- msearch.py grep, query `torsor|[Ss]tackification`, CategoryTheory: 0 hits reported.
  Direct rg searches in Mathlib and the project independently located and read the
  internal group, action, site, based-category and pseudofunctor stack APIs.
- rg on WeilConjectures for torsor/stackification located abelian sheaf torsors and
  their H1 results, not the present quotient-stack comparison. rg for this item's
  blueprint id in WeilConjectures returned no match.
- rg on lean/Sheaf located `actionGroupoid_torsor_comparison`, and the action/torsor
  and stackification definition modules. The comparison has additional Smooth,
  LocallyOfFiniteType and QuasiCompact binders and is therefore not an exact match.
  All of its reusable definitions work for arbitrary G; they are imported unchanged.
- rg on the DAG found def-sfb-scheme-action-torsor-groupoids and
  def-sfb-fppf-stackification, so neither notion was duplicated. Searching the full
  proposed declaration name in Mathlib/upstream/project and dag/lean_names_upstream
  found no existing declaration.

Source reading: examples-stacks.tex, situation-quotient-stack, proof of
lemma-group-quotient-stack-in-groupoids (0370), and proposition-equal-quotient-stacks
(04WM), including the definition of F_p and its right-translation formula. The
scheme-effectivity proof route follows the item's descent.tex 0245/02W3 expansion.

Edge cases checked before writing: empty T and V, trivial G, noncommutative G
(composition is hg⁻¹b⁻¹=h(bg)⁻¹), alpha_p in characteristic p, and affine groups
of infinite type such as an infinite product of additive groups. The binders
exclude none of these. Nonseparated V is allowed because representable fpqc descent
needs no separation. Local triviality does not assert that P→T is fppf, so infinite
type causes no extra condition. Empty covering sieves are included by the stack
predicate. No statement-disputed flag and no node fault was found.

Validation: scompile.py Q86 lem-sfb-affine-group-torsor-stackification compiled the
sandbox and library-named module cleanly on the server (14.8 s / 4.2 s), with no
unexpected warnings. All variables and universes are explicit; autoImplicit is false.

## Second reading by Q86

The dispatcher expressly forbids starting other agents, and the brief assigns the
independent delivery review to the maintainer. This section records my own separate
second pass, not an independent-agent review. I reopened the item, the delivered
module, SchemeActionTorsorGroupoids and SiteStackification, and compared each binder
and conjunct against the correspondence above. The only geometric hypothesis is
IsAffineHom on G; ModObj is the actual left action on arbitrary V. In particular,
the smooth finite-type assumptions of the nearby comparison were not retained.
The three isomorphism clauses give the two-sided equivalence and the exact canonical
extension, with vertical components. I recomputed the inverse right translation and
its composition order for noncommuting labels, and checked the local-triviality and
cartesian-arrow fields encode scheme torsors and fibre-product pullback. The
universal-property stackification is the existing equivalent interface documented
in def-sfb-fppf-stackification. No mismatch requiring a statement correction was
found. The only DAG additions are the two already-landed definition dependencies.

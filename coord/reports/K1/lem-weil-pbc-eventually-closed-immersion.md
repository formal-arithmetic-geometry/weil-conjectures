## Worker report

The module `Sheaf.AlgebraicGeometry.EventuallyClosedImmersion` states
`AlgebraicGeometry.eventually_isClosedImmersion_of_isLimit`, with a single `sorry` proof.
The statement agrees with the node and Stacks Project, Limits, Lemma 0A0N
(https://stacks.math.columbia.edu/tag/0A0N, read directly because the local literature
checkout does not contain limits.tex). No node correction or additional notion is needed.

Hypothesis and conclusion correspondence:

- The scheme T is `(T : Scheme.{u})`; quasi-compact and quasi-separated are
  `[CompactSpace T] [QuasiSeparatedSpace T]` on its underlying topological space.
- The nonempty directed set is `{I : Type w} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`, using the directed-preorder convention.
- The inverse system is `(D : Iᵒᵖ ⥤ Scheme.{u})`; its functor laws encode identity
  and composition of transitions. A morphism `op i' ⟶ op i` encodes `i ≤ i'`.
- Its compatible structure maps h_i are the components of
  `(h : D ⟶ (Functor.const Iᵒᵖ).obj T)`. Naturality says
  `D.map a ≫ h.app j = h.app i` for `a : i ⟶ j`.
- Closed immersion transitions are
  `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)]`.
  Affineness follows from Mathlib's closed-immersion instance; no separate affine
  hypothesis is added.
- Each stage is quasi-compact and quasi-separated through the two binders
  `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and
  `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`.
- Locally finite type stage maps are
  `[∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]`.
- The limit with its projections is `(c : Cone D) (_hc : IsLimit c)`;
  its point is Z and `c.π.app i` is p_i. This uses the category-of-schemes limit,
  exactly the notion of the limit dependency, with no chosen-limit replacement.
- The induced map is `(f : c.pt ⟶ T)` with
  `(_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f)`. This is the defining compatibility
  of the induced map, not an extra geometric assumption. Nonemptiness ensures
  uniqueness of such a map.
- The limit map being a closed immersion is `[IsClosedImmersion f]`.
- The existence conclusion and its parenthetical are together
  `∃ i : I, ∀ j : I, i ≤ j → IsClosedImmersion (h.app (op j))`.
  Reflexivity includes h_i itself; the remaining j give precisely every later stage.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention node, not a new
  declaration. Its scheme properties are Mathlib's `Scheme`, `CompactSpace`, and
  `QuasiSeparatedSpace` here. The latter is imported from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: a closed embedding with
  surjective stalk maps. Its full declaration and docstring were read.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`: affine inverse images of affine
  opens. Its full declaration and docstring were read. Here it is implied by
  closed immersion transitions and does not need a redundant binder.
- `lem-weil-pbc-limit-affine-transition`: imported
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`; its recorded
  `AlgebraicGeometry.exists_limit_affine_transition` signature and complete docstring
  were read. The theorem supplies existence of a limiting cone; the present
  statement takes any such cone and its `IsLimit` witness, using the same Mathlib
  `Cone` and `IsLimit` notions. Stage 2 does not invoke this existence proof.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: finite type induced maps on
  affine pairs. Its full signature and docstring were read, as was `QuasiCompact`.
  No finite-presentation or morphism-quasi-compact hypothesis is substituted.

Edge cases checked before writing: I is explicitly nonempty; no antisymmetry is
assumed. A singleton or a directed preorder with equivalent distinct indices is
allowed. Empty T forces all stage schemes empty because they have maps to T, and
is allowed. An empty limit is allowed even when earlier stages are nonempty; the
source lemma still asserts eventuality. The proof docstring accommodates an empty
finite affine cover and an algebra with no generators. There are no field,
characteristic, nonzero ring, nonempty scheme, or finite-index restrictions.
The independent index universe w does not restrict scheme size or quantify over
undersized test schemes. Every universe and variable is explicitly bound.

Searches for an existing statement:

- msearch.py leanfinder: "inverse limit of schemes over T with closed immersion
  transition maps, whose induced limit map is a closed immersion, is eventually
  a closed immersion". Eight results: closed immersions are universally closed,
  pullback closed immersions, composition criteria and the affine Spec criterion;
  none states eventual closed immersions of the structure maps.
- msearch.py loogle: "AlgebraicGeometry.IsClosedImmersion,
  CategoryTheory.Limits.IsLimit, AlgebraicGeometry.LocallyOfFiniteType".
  Zero hits.
- msearch.py leansearch: "Inverse limit of schemes with closed immersion transitions
  over a quasi compact quasi separated base, locally finite type stage maps, and
  closed immersion limit map implies eventually closed immersion stage maps".
  Service unavailable: Internal Server Error; no verdict inferred from failure.
- msearch.py grep, AlgebraicGeometry: regex
  `eventually.*[Cc]losed|exists.*[Cc]losedImmersion|closedImmersion.*limit`.
  Three results, all equalizer/pullback closed immersion instances, no match.
- rg of the same regex in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
  and repository `lean/Sheaf`: related closed immersion existence statements,
  none for stage-to-base structure maps. Also searched the item id in both trees
  and the proposed theorem names in `dag/lean_names_upstream.json`; no match.
  In particular the full signature and docstring of
  `Scheme.exists_isClosedImmersion_comp_π` in
  `WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:5020`
  were read. It concerns `g : Y ⟶ c.pt` and concludes closed immersion of
  `g ≫ c.π.app k` (Tag 081B(1)); it is a different statement.

The proof docstring carries all six node proof steps and names their dependencies.
No definitions, auxiliary theorems, or proofs beyond the required sorry are added.
Server compile via scompile.py succeeded cleanly in 1.6 seconds.

## Second reading by K1

I independently expanded the node statement into its objects, hypotheses, and conclusion and
matched each item against `EventuallyClosedImmersion.lean`.

- The base scheme is `(T : Scheme.{u})` with `[CompactSpace T]` and
  `[QuasiSeparatedSpace T]`, exactly the quasi-compact, quasi-separated `T` of the node.
- The index is `{I : Type w}` with `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, and
  `[Nonempty I]`, exactly a nonempty directed set. The inverse system is
  `D : Iᵒᵖ ⥤ Scheme.{u}`; arrows in `Iᵒᵖ` encode transitions from a later index to an
  earlier one.
- The structure maps are the natural transformation
  `h : D ⟶ (Functor.const Iᵒᵖ).obj T`, whose components are `h.app i` and whose
  naturality is the required compatibility with transitions.
- The transition hypothesis is
  `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)]`, matching closed-immersion
  transitions; the node's parenthetical affineness is a consequence supplied by its
  dependency and is not an extra assumption.
- Stage hypotheses are
  `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]`,
  `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`, and
  `[∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]`, exactly the three corresponding
  assumptions in the node.
- The limit is an arbitrary cone `c : Cone D` with `_hc : IsLimit c`; its point and
  projections render `Z` and `p_i`. The induced map is `f : c.pt ⟶ T`, with
  `_hf : ∀ i, c.π.app i ≫ h.app i = f`, exactly the compatibility clause. The class
  `[IsClosedImmersion f]` renders that the limit map is a closed immersion.
- The conclusion is `∃ i : I, ∀ j : I, i ≤ j →
  IsClosedImmersion (h.app (op j))`, which is precisely eventual closed immersion,
  including the node's parenthetical persistence (the latter follows by composition
  with the transition closed immersions).

No mismatch was found and no statement or dependency was changed. The opposite-category
encoding, universe binders, and all hypotheses are explicit; no field, characteristic,
nonzero, finite-index, or nonempty-scheme assumption was added. Edge cases checked include
`I` a singleton or a preorder with equivalent distinct indices, empty `T` (and hence empty
stages under their structure maps), an empty limit, and the vacuous finite affine cover when
`T` is empty. The statement permits all cases covered by the source, including no restriction
on characteristic and no `n = 0` parameter.

I searched Mathlib, `WeilConjectures/`, and repository `lean/Sheaf/` with grep/rg for
`eventually.*[Cc]losed`, `exists.*[Cc]losedImmersion`, and the relevant theorem names; I also
ran the LeanFinder, Loogle, and LeanSearch queries recorded by the worker. The only related
source declaration, `Scheme.exists_isClosedImmersion_comp_π`, concerns a different map and
is not an existing implementation of this node. Thus this module is required. Compilation
with `scompile.py` succeeded without errors or warnings.

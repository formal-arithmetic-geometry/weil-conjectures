## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedFibreSingleton` states
`AlgebraicGeometry.preimage_singleton_eq_empty_or_singleton_of_injOn_closedPoints`.
Its only proof is `sorry`; it defines no new notion. The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The schemes are `(X Y : Scheme.{u})`. Their structures over the field are
  `[X.Over (Spec (CommRingCat.of k))]` and `[Y.Over (Spec (CommRingCat.of k))]`.
- Local finite type of `X` over `k` is
  `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]`.
- The morphism is `(f : X ⟶ Y)`. The node does not require compatibility with the
  two structure morphisms, so no `f.IsOver` hypothesis is added.
- Distinct closed points have distinct images is exactly
  `(hf : Set.InjOn f (closedPoints X))`.
- Each closed point of `Y` is `(p : Y) (hp : p ∈ closedPoints Y)`.
- The fibre as a set is `f ⁻¹' {p}`. The empty alternative is `f ⁻¹' {p} = ∅`.
- The singleton alternative is `∃ x : X, x ∈ closedPoints X ∧ f ⁻¹' {p} = {x}`.
  This both asserts that `x` is closed in `X` and identifies the entire underlying fibre.
  It implies `f x = p` without an extra clause. It makes no claim that the scheme-theoretic
  fibre is reduced or is a spectrum of the base field.

Dependency declarations read and used:

- `def-weil-algebraic-closure`: `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; its signature and docstring give splitting of
  every polynomial, equivalently a root for every nonconstant polynomial. The recorded
  `AlgebraicClosure` construction was also read; this statement only needs `IsAlgClosed`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, applied to the structure morphism.
  Its full affine-local signature and docstring were read. `QuasiCompact` was read too,
  but is not used: the node requires only locally finite type.
- `def-weil-pbc-scheme-conventions`: this is a convention record with no declaration or
  module. Its relevant meanings are Mathlib's `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  in `Mathlib.AlgebraicGeometry.Scheme`, and `Scheme.Over` in
  `Mathlib.AlgebraicGeometry.Over`. Their signatures and docstrings were read.
- `def-weil-closed-points`: `closedPoints` in `Mathlib.Topology.JacobsonSpace`,
  `Set.ofPred (IsClosed {·})`, with `mem_closedPoints_iff` confirming the singleton meaning.

All binders and the universe are explicit. The common arbitrary universe is the universe of
Mathlib's category of schemes and accommodates the field and both schemes together.
The proof docstring carries both node proof steps and names the proof dependency.

Edge cases checked: the empty scheme satisfies the injectivity hypothesis vacuously and
has empty fibres; points outside the image give the empty alternative; a singleton fibre
with nilpotents is allowed, since only its underlying set is identified. No quasi-compactness,
separatedness, properness, reducedness, or restriction on characteristic is assumed. A constant
map from the affine line fails closed-point injectivity as expected. A nonclosed point in a
closed fibre contradicts the closure lemma used by the node's proof.

Searches made using `/home/ubuntu/weil-launcher/msearch.py`:

- `leanfinder`: “A scheme locally of finite type over an algebraically closed field with
  injective map on closed points has empty or singleton fibres over closed points”. Eight
  hits, including Jacobson fibres, finite fibres, and images of closed points; none states
  this result.
- `loogle`: `Set.InjOn, closedPoints, AlgebraicGeometry.LocallyOfFiniteType`. Zero hits.
- `grep`: `injective.*closed|[Ff]iber.*singleton|[Ff]ibre.*singleton`, subdirectory
  `AlgebraicGeometry`. Six hits on unrelated constructions and immersion facts; no match.
- `leansearch`: “injective on closed points scheme fibre over closed point empty singleton”.
  Service unavailable, Internal Server Error; no absence conclusion drawn from this search.
- Local `rg` of `lean/Sheaf` and `WeilConjectures` for closed-fibre/singleton names found
  only unrelated cohomology, fibre-map range, and quasi-finiteness results.
- Local `rg` of the Curve source and `lean/Sheaf/AlgebraicGeometry` for
  `InjOn.*closedPoints|closedPoints.*InjOn|singleton.*closedPoints|preimage.*singleton`
  found only uses of preimages of singletons, no matching declaration.
- `grep -rn` for the item's id in `WeilConjectures` returned no hits.
- A full-name collision search of `dag/lean_names_upstream.json`, Mathlib,
  `WeilConjectures`, and `lean/Sheaf` returned no hits for the proposed declaration name.

The local Stacks source tree is absent. Read the primary sources online:
[Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S), the point-separation fibre argument,
and [Tag 0478](https://stacks.math.columbia.edu/tag/0478), the Jacobson property of schemes
locally of finite type over a field. The node already isolates the set-theoretic consequence
used in that proof. No statement correction or disputed statement is needed.

## Second reading by K1

Independently read the sandbox node and module, all four statement-dependency nodes,
Mathlib's actual declarations, and the proof-dependency node and its landed module.
The statement is faithful; no Lean or node change is needed.

Objects, hypotheses, and conclusions, in node order:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
  Verdict: exact. `IsAlgClosed` in Basic.lean:62 says every polynomial splits, with
  its documented root characterization matching def-weil-algebraic-closure.
  This uses the recorded leaf's algebraically-closed notion, not a chosen algebraic closure.
- Scheme X locally of finite type over k: `(X : Scheme.{u})`,
  `[X.Over (Spec (CommRingCat.of k))]`, and
  `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]`. Verdict: exact.
  Over.lean:29 supplies precisely a structure morphism. FiniteType.lean:43 supplies
  the affine-local finite-type condition recorded by def-weil-finite-type-morphism;
  quasi-compactness is not part of the node's locally finite-type hypothesis.
- Scheme Y over k: `(Y : Scheme.{u})` and
  `[Y.Over (Spec (CommRingCat.of k))]`. Verdict: exact; no local finite-type condition on Y.
- Morphism f from X to Y: `(f : X ⟶ Y)`. Verdict: exact.
  Read Scheme.lean:42, :73, and :108: schemes are locally affine locally ringed spaces,
  their morphisms are locally ringed-space morphisms, and the function coercion is
  the underlying point map. The convention dependency refers to these existing notions.
  The node specifies a morphism of schemes, so there is no missing IsOver assumption.
- Distinct closed points have distinct images:
  `(hf : Set.InjOn f (closedPoints X))`. Verdict: exact injectivity restricted to
  the closed points of X; not injectivity on all points or on rational points.
  JacobsonSpace.lean:38 and :43 identify closedPoints with closed singletons.
- For every closed point p of Y: `(p : Y) (hp : p ∈ closedPoints Y)`.
  Verdict: exact universal quantification after f and its hypothesis.
- Empty fibre: `f ⁻¹' {p} = ∅`. Verdict: exact underlying set-theoretic fibre.
- Singleton fibre consisting of a closed point of X:
  `∃ x : X, x ∈ closedPoints X ∧ f ⁻¹' {p} = {x}`.
  Verdict: exact; equality identifies the whole fibre and entails f(x) = p.
  The disjunction covers precisely the two alternatives. No assertion about reducedness
  or scheme-theoretic residue fields is introduced.

Source reading: the local Stacks tex tree is absent. Read the upstream varieties.tex
at https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
labels lemma-separate-points-tangent-vectors and lemma-locally-finite-type-Jacobson,
and the rendered primary-source pages [0E8S](https://stacks.math.columbia.edu/tag/0E8S)
and [0478](https://stacks.math.columbia.edu/tag/0478).
The former assumes a proper k-scheme and discusses the canonical projective morphism;
this node isolates its closed-fibre argument. Its stated generalization is valid:
only local finite type (the Jacobson property from 0478), continuity, and separation
of closed points are needed. Properness and the sections/tangent-vector hypotheses
serve the surrounding very-ampleness proof and are not needed in this isolated node.
The source's singleton wording necessarily permits empty fibres outside the image.
The docstring contains both node proof steps: closedness of the inverse image and
closed specializations force every fibre point closed, then injectivity gives uniqueness.
Read infinite_closedPoints_inter_closure_singleton in the proof dependency's module:
its field, local finite-type, and nonclosed-point hypotheses match this use.

Edge cases: X empty gives empty fibres and vacuous injectivity; Y empty allows no p
and hence imposes no impossible conclusion; a p outside the image gives the empty
alternative. A zero ring gives an empty scheme, which is covered; a zero field is
excluded by the node itself. Nilpotents at a singleton point are allowed. There is
no n or index-set parameter. All characteristics are allowed. The arbitrary common
universe u is the universe required by Mathlib's Scheme category and Over structures;
objects from smaller universes can be lifted into a common one. No finiteness,
Noetherian, separatedness, or properness instance is accidentally assumed.
Every variable and universe is explicitly bound.

Independent searches (different terminology from the worker):

- leanfinder via msearch: "A continuous map from a Jacobson scheme injective on closed
  points has subsingleton inverse images of closed points". Eight hits, including
  preimage_closedPoints_subset, Scheme.Hom.closePoints_subset_preimage_closedPoints,
  and LocallyOfFiniteType.jacobsonSpace. None is this statement. The first assumes
  injectivity on all points and only concludes that preimages of closed points are closed;
  the others concern images of closed points or the Jacobson property.
- loogle via msearch: `Set.InjOn, IsClosed, Set.Subsingleton`: zero hits.
- leansearch via msearch: "In a Jacobson space injectivity on closed points implies a
  closed fibre is empty or a singleton": Internal Server Error, unavailable;
  no absence inference from that failed service.
- rg on Mathlib AlgebraicGeometry and JacobsonSpace, WeilConjectures, and lean/Sheaf:
  `subsingleton.*(fiber|fibre|preimage)|((fiber|fibre|preimage).*(subsingleton|closedPoints))`
  and `InjOn.*closedPoints|closedPoints.*InjOn`. Only stronger injectivity/immersion
  results, unrelated contracted fibre-image statements, and closed-point image lemmas.
  No matching declaration. The full proposed declaration name has no collision in
  dag/lean_names_upstream.json or any of those three Lean trees.

No mismatches found and no definitions duplicated. There are no new definition nodes,
dependency modules, or statement corrections to audit. One named theorem has only
`sorry`; there are no definitions and no proved auxiliary results. Header, namespace,
source tags, import uses, and 100-character line convention are correct. The node's
lean.statement is verbatim the theorem signature. Server scompile passed cleanly
(1.6 seconds, no warnings). Second reading changed only this appended report section.

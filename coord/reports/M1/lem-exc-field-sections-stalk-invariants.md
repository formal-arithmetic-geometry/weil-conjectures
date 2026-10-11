## Worker report

The module states `AlgebraicGeometry.Scheme.fieldSections_stalkInvariants` for a separable
closure `Ks` of `K` embedded in an algebraic closure `Ω`. It asserts the existence of the
canonical pointed lifts and a sheaf-natural absolute Galois action on each geometric
stalk, characterizes that action by changing pointed lifts, and gives the required
section/invariant bijections and naturality formulas. The sole proof is `sorry`.

Hypotheses: `[Field K]`, `[Field Ks]`, `[Algebra K Ks]`, and
`[IsSepClosure K Ks]` render the field and its separable closure;
`[Field Ω]`, `[Algebra Ks Ω]`, `[Algebra K Ω]`, `[IsScalarTower K Ks Ω]`,
`[IsAlgClosed Ω]`, and `[Algebra.IsAlgebraic K Ω]` render the embedded algebraic
closure. `s` and `hs` identify the geometric point with the spectrum morphism
induced by the field embedding. `F : Sheaf (Spec (.of K)).smallEtaleTopology
(Type (u + 1))` is an arbitrary sheaf of sets on the small etale site.

Clauses: `lift L` and the equality of its `left` with the spectrum map of the
inclusion `L -> Ks -> Ω` give the chosen lift for every finite separable
intermediate field. `action F : MulAction Gal(Ks/K) ...` is a group action on
the Mathlib geometric stalk. Its first universal formula says that `g` sends
the germ at `x` to the germ at `x'` when an extension `τ` of `g` changes the
lift from `x` to `x'`. `Set.BijOn (pointSmallEtale s).toPresheafFiber ...
Set.univ {m | ... L.fixingSubgroup ...}` is the bijection from sections over
`Spec L` to `H_L`-fixed stalk elements. For `j : L ->_K L'` and an extending
`g`, the next equation matches `F.obj.map (etaleSpecMap j).op` with the action
of `g` on germs. The following conjunction states that `g` sends fixed
elements to `H_L'`-fixed elements and that any two extensions `g,g'` agree
on them. The final conjunction gives naturality for every sheaf morphism
`φ : F ⟶ F'`, both on the canonical germs and on the Galois action. The
group action law supplies compatibility with composition of embeddings.

Dependencies used: `def-pc-field-extension` via Mathlib `Algebra` in
`Mathlib.Algebra.Algebra.Defs`; `def-kun-separably-closed` via `IsSepClosed`
in `Mathlib.FieldTheory.IsSepClosed` and `IsSepClosure` in the source;
`def-weil-geometric-point` via `Scheme.SpecToEquivOfField` in
`Mathlib.AlgebraicGeometry.ResidueField` and `Spec.map`;
`def-weil-pbc-etale-site` via `Scheme.smallEtaleTopology` in
`Mathlib.AlgebraicGeometry.Sites.Etale`;
`def-weil-pbc-geometric-stalks` via `Scheme.pointSmallEtale` in
`Mathlib.AlgebraicGeometry.Sites.EtalePoint` and `Point.sheafFiber` and
`Point.toPresheafFiber` in `Mathlib.CategoryTheory.Sites.Point.Basic`.
`Scheme.etaleSpec` and `Scheme.etaleSpecMap` come from
`WeilConjectures.AlgebraicGeometry.Sites.Hilbert90`; the finite separable
etale instance is `Algebra.Etale.of_finite_of_isSeparable` in
`WeilConjectures.Mathlib.RingTheory.Etale.Field`.

Edge cases checked: `L = K` gives the `G`-fixed global sections; when `K`
is separably closed, `Ks = K` and the group is trivial; the identity embedding
is covered with `g = 1`; an empty sheaf is allowed because no nonemptiness
assumption appears; the field characteristic is unrestricted. All field types
share universe `u`, matching Mathlib's `Scheme.{u}` and `etaleSpec` types;
set-valued sheaves use `Type (u + 1)` to support the site-size colimit.

Searches: `msearch.py ... leanfinder "sections etale sheaf finite separable
extension invariant geometric stalk absolute Galois group"` returned only
unrelated finite-etale field and Galois results. `msearch.py ... loogle
"AlgebraicGeometry.Scheme.pointSmallEtale,
CategoryTheory.GrothendieckTopology.Point.sheafFiber"` returned no hit.
`msearch.py ... grep "stalk.*invariant|invariant.*stalk|Galois.*sheaf"
AlgebraicGeometry/Sites` returned no hit. Searches in
`WeilConjectures/` and `lean/Sheaf/` found uses of geometric stalks but no
Galois action on set-valued stalks and no section/invariant theorem; the exact
item-id search in the source repository returned no hit. The node's earlier
Mathlib searches also found no match. No separate definition node is needed:
the action uses Mathlib's existing `MulAction`, and the theorem characterizes
the action by its effect on germs rather than introducing another notion.

Server compilation of the module completed cleanly.

## Second reading by M1

I read the item node, all five statement-dependency nodes and their recorded declarations,
the delivered module, and Stacks etale-cohomology.tex at section-galois-action-stalks
(Tag 03QW) and lemma-global-sections-point (Tag 04JM), including its direct proof.
The local Stacks copy is /home/ubuntu/c1-stacks-review/etale-cohomology.tex,
lines 8515--8730; the repository's literature directory has no downloaded Stacks tex.
The source assumes a field base and a geometric point, with no characteristic,
Noetherian or finiteness condition on the sheaf. The node specializes the geometric
point to an algebraic closure and applies the global-section result over each L.

Object/hypothesis/conclusion checklist, in the order of the node:

- Field K: `(K : Type u) [Field K]`; exact. `Algebra K Ks` is precisely the field
  extension of def-pc-field-extension (`Mathlib.Algebra.Algebra.Defs.Algebra`).
- Separable closure Ks: `[Field Ks] [Algebra K Ks] [IsSepClosure K Ks]`; exact.
  I opened def-kun-separably-closed and Mathlib.FieldTheory.IsSepClosed: `IsSepClosure`
  has `sep_closed : IsSepClosed Ks` and `separable : Algebra.IsSeparable K Ks`.
  Its separability includes algebraicity; it is the closure notion in the dependency,
  not an arbitrary separably closed extension.
- Embedded algebraic closure Omega: `[Field Ω] [Algebra Ks Ω] [Algebra K Ω]
  [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]`; exact.
  The field algebra maps are injective, and the scalar tower expresses the compatible
  inclusions. No perfectness or characteristic restriction is imposed.
- Geometric point: `s : Spec (.of Ω) ⟶ Spec (.of K)` and `hs` identifying it with
  `Spec.map` of the given algebra map; exact compatible point. The dependency's
  `Scheme.SpecToEquivOfField` signature is the same spectrum-morphism notion;
  there is no private geometric-point definition.
- Absolute Galois group: `Gal(Ks/K)` with the imported Mathlib Krull topology; exact.
  The node asserts no separate topological property here. The lift-change formula
  specifies the canonical action, rather than an arbitrary action on an unrelated set.
- Arbitrary sheaf of sets: `F : Sheaf (Spec (.of K)).smallEtaleTopology
  (Type (max (u + 1) v))`; exact with an independent value-universe parameter added
  in this reading. I checked `smallEtaleTopology` against def-weil-pbc-etale-site:
  it is the small etale site, not the big site or the finite etale subcategory.
- Stalk M: `(pointSmallEtale s).sheafFiber.obj F`; exact. In EtalePoint the fiber
  consists of lifts of s to the neighbourhood. In Point.Basic, `presheafFiber`
  is the colimit over the opposite category of elements, and `sheafFiber` is its
  restriction to sheaves, exactly def-weil-pbc-geometric-stalks.
- Induced action: `action F : MulAction Gal(Ks/K) M`, with the first universal
  equation involving `τ`, `hτ`, `x`, `x'`, `hx`, and `toPresheafFiber`; exact.
  I checked the direction against the source equation: the new lift is
  `Spec.map τ ≫ x.left`, precisely x composed with Spec(tau). It is the left action
  of 03QW (Spec reverses composition), so no inverse is missing.
- Every finite separable intermediate field: `L : IntermediateField K Ks`,
  `[FiniteDimensional K L] [Algebra.IsSeparable K L]`; exact. Separability is
  automatic for these subfields of a separable closure, so the explicit instance
  does not impose a new mathematical assumption. `etaleSpec K L` is the source's
  existing spectrum object; the local instance is its finite-separable etaleness.
- Chosen lift: existential `lift L` followed by its `.left` equality with
  `Spec.map ((algebraMap Ks Ω).comp L.subtype)`; exact canonical inclusion.
- Subgroup H_L: `L.fixingSubgroup`; exact. I read Galois.Basic's membership
  characterization (fixing every element of L) and its equivalence with `Gal(Ks/L)`.
- Section/invariant bijection: `Set.BijOn (toPresheafFiber ... (lift L) F.obj)
  Set.univ {m | ∀ g ∈ L.fixingSubgroup, (action F).smul g m = m}`;
  exact, including injectivity, surjectivity and landing in the invariant subset.
- Naturality for every K-embedding: `j : L →ₐ[K] L'`, extending `g` with `hg`,
  and the equation comparing `F.obj.map (etaleSpecMap j).op` with `action F`;
  exact. Field algebra homomorphisms are embeddings. I opened `etaleSpecMap`:
  its direction is Spec L' to Spec L, as required, and `hg` is equality in Ks.
- Image consists of H_L'-invariants and is independent of extension: the next
  conjunction, quantified over `g g'`, `hg hg'`, and every `m` with `hm`;
  exact. In particular this is not limited to an unproved chosen representative.
  Composition compatibility is supplied by `MulAction` and the pullback functor.
- Naturality in every morphism of sheaves: final conjunction for `φ : F ⟶ F'`,
  comparing canonical germs with `sheafFiber.map φ` and asserting equivariance;
  exact, for the same action family chosen before the universal sheaf quantifier.

Edge cases: `L = ⊥` gives sections over K and invariants under the whole Galois
 group; `L = ⊤` is included whenever finite. If K is separably closed the closure
and group are trivial and the formula becomes the usual section/stalk bijection.
Identity embeddings, inclusions, and non-surjective embeddings are all covered.
The empty sheaf and singleton sheaf require no additional instance. Neighbourhoods
may include the empty scheme, with no pointed lift and thus no spurious germ.
There is no index set, integer n, additive zero object or torsion parameter here;
no positive characteristic is excluded. Field universes may be placed in a common
arbitrary u as required by Mathlib's Scheme and the existing etaleSpec declarations.
The added independent v permits arbitrarily large sets of sections on this fixed
site, while the max with u+1 ensures that its stalk colimit exists in Type.

Independent searches used different words from the first reader:

- msearch leanfinder: "fixed points of absolute Galois action on fiber functor of
  small etale topos" returned abstract finite Galois-category results, not this
  theorem about arbitrary set-valued sheaves and finite separable extensions.
- msearch loogle: `"sheafFiber"` returned the generic site fiber constructions,
  colimit properties and shrink-Yoneda comparison, not a Galois invariant theorem.
- msearch grep: `fixingSubgroup|fixedPoints|MulAction` in AlgebraicGeometry/Sites
  returned no hits. msearch leansearch with a natural-language section/fixed-point
  query returned HTTP 500 and was recorded unavailable, not as a negative result.
- Independent rg over WeilConjectures and lean/Sheaf for stalk/Galois/fixed,
  sections/invariant and the proposed declaration found no duplicate. I opened
  WeilGroup.globalSections_eq_invariants: it concerns linear representations of
  Weil groups and defines sections as equivariant linear maps; it is not this
  etale-sheaf theorem. ColimitsOver and FiniteGaloisSectionsDescent concern finite
  descent, not the absolute Galois stalk formula. The exact item-id search in the
  source and upstream-name record had no hit. Existing dependency notions are used
  directly; no new definition node or dependency module is needed.

Mismatches repaired: the original value universe was tied to u+1; I introduced v
and changed every sheaf binder to Type (max (u+1) v), keeping the site fixed. The
original proof docstring compressed the four node steps and omitted their dependency
ids; I expanded it to include site restriction, finite descent, germ injectivity,
quotient invariance, conjugation, independence and sheaf naturality with all cited
nodes. The source IsSepClosed extension module was imported without using its
additional declarations; I replaced it with Mathlib.FieldTheory.IsSepClosed, the
actual provider of IsSepClosure. No mathematical node statement was changed and
there is no statement_change or citer audit to perform. The stored lean.statement
was regenerated from the theorem signature (with whitespace normalized as in the
original record). Only a named theorem has sorry; no definition or proof data is hollow.
All variables and universes are explicitly bound, lines are at most 100 characters,
and the module and theorem retain their source and blueprint tags. The corrected
module compiled cleanly on the server in 2.6 seconds, with no warnings.

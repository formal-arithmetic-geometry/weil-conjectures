## Worker report

Module: `Sheaf.Topology.InverseImageClosedPushforwardConstant`.
Declaration: `TopCat.inverse_image_closed_pushforward_constant`.
This states the complete comparison, with `sorry` as the only theorem proof.
No node correction, new node or dependency module is needed.

Hypotheses and clauses, in the order of the node:

- Topological spaces and continuous map: `(X Y : TopCat.{u}) (f : X ⟶ Y)`.
  The morphism bundles precisely a continuous map, with no separation assumptions.
- Closed subset and arbitrary set: `(W : Set Y) (hW : IsClosed W) (R : Type u)`.
  No inhabitedness, cardinality, ring structure or topology on R is assumed.
- Preimage: `let Z : Set X := f ⁻¹' W`. Its closedness follows from continuity
  and hW, and is not an extra hypothesis.
- Sections of the two closed direct images: the local presheaf expressions P and Q
  have objects `LocallyConstant {y : Y // y ∈ unop V ∧ y ∈ W} R` and
  `LocallyConstant {x : X // x ∈ unop U ∧ x ∈ Z} R`. These are exactly locally
  constant functions on the indicated intersections with the subspace topology.
  Their maps are `LocallyConstant.comap` along subtype inclusion, i.e. restriction.
  Structural functor identity/composition fields are reflexivity, not mathematical
  auxiliary theorem proofs. These section formulas are written directly in the
  theorem, as in the landed sibling ClosedPushforwardConstantRestriction; no new
  global definition of a sheaf or inverse-image functor is introduced.
- The assertion that these are sheaves is `∃ (hP : P.IsSheaf) (hQ : Q.IsSheaf)`.
  A and B bundle these same presheaves with the witnesses. Proof irrelevance means
  there is no choice of section data here and no change of the claimed objects.
- Direct image of B: `(Sheaf.pushforward (Type u) f).obj B`, whose underlying
  presheaf is precomposition with `(Opens.map f).op`. This is B(f⁻¹V).
- The maps alpha_V form a sheaf morphism: `∃ alpha : A ⟶ ...`, followed by the
  equality for every open V and section g. Its right side is comap by the continuous
  map x ↦ f(x) on the intersections. The membership proofs are precisely x.2.1
  (image in V) and x.2.2 (image in W). The type of alpha includes naturality.
- Inverse image and its specified unit: L is the dependency's
  `Functor.sheafPullbackConstruction.sheafPullback`; adj is its
  `sheafAdjunctionContinuous`, not the abstract chosen left adjoint. Thus L is
  sheafToPresheaf followed by presheaf left Kan extension and sheafification, and
  adj.unit is the colimit coprojection followed by sheafification, as required.
- The adjoint comparison is `let beta := (adj.homEquiv A B).symm alpha`.
  Its unit compatibility is also explicitly stated pointwise over every V and g:
  `beta.hom.app (op ((Opens.map f).obj V)) ((adj.unit.app A).hom.app (op V) g)
  = alpha.hom.app (op V) g`. This is exactly alpha-flat composed with eta.
- Uniqueness with that compatibility: the final universally quantified beta'
  clause states that any morphism `L.obj A ⟶ B` satisfying those same equations
  equals beta. Existential alpha is uniquely prescribed by its components, and
  existence of the adjoint beta is built into homEquiv.symm.
- Isomorphism: `IsIso beta` in the sheaf category.
- Sectionwise conclusion: `∀ U : Opens X, Function.Bijective (beta.hom.app (op U))`.

Dependency declarations read and used:

- def-weil-pbc-topological-inverse-image is a Mathlib dependency, with no lean
  record required. Its recorded construction is
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`
  in `Mathlib.CategoryTheory.Sites.Pullback`; its left functor is the construction
  `sheafPullback` in that namespace. Read the full definitions and docstrings.
  The recorded clause-(1) declarations are `TopCat.Presheaf.pushforward` in
  `Mathlib.Topology.Sheaves.Presheaf` and `TopCat.Sheaf.pushforward` in
  `Mathlib.Topology.Sheaves.Functors`, whose full definitions were read.
- lem-weil-pbc-sets-inverse-image-colimits-finite-products is also Mathlib:
  `TopCat.Sheaf.pullbackPushforwardAdjunction` in
  `Mathlib.Topology.Sheaves.Functors`, and
  `CategoryTheory.Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat`
  in `Mathlib.CategoryTheory.Sites.Pullback`. Read both full signatures, the
  `Opens.map f` RepresentablyFlat instance in SheafCondition.Sites, and
  `Adjunction.leftAdjoint_preservesColimits` in CategoryTheory.Adjunction.Limits.
  For clause (a) this statement uses the equivalent explicitly constructed
  adjunction already recorded by the preceding dependency, preserving its unit.
  Finite-limit preservation is not needed to state this item's conclusion.
- `LocallyConstant.comap` in `Mathlib.Topology.LocallyConstant.Basic` was read:
  it is precomposition with a continuous map and needs no topology on the target.

Edge cases checked mathematically before writing:

- W empty: P and Q have singleton sections on every open; beta is the terminal
  sheaf comparison. No failure at R empty.
- W = Y: this is inverse image of the constant sheaf, including disconnected
  spaces; locally constant maps, rather than globally constant maps, are essential.
- R empty: sections on nonempty intersections are empty, on empty intersections
  singleton; at a point of Z both relevant stalks are empty, elsewhere singleton.
- X or Y empty, and the empty open: all formulas and unit equations remain typed;
  sheaf sections on the empty open are singleton and the bijection remains valid.
- f constant or noninjective/non-surjective: no such restriction occurs anywhere.
- Arbitrary spaces/sets are supported at the common explicit universe u, with no
  finite, small-cardinality, inhabited or locally connected assumption.

Searches for an existing exact statement:

1. msearch.py leanfinder, query "inverse image of direct image of constant sheaf on
   a closed subset is constant sheaf pushed forward from preimage": eight results
   included pullbackObjObjOfImageOpen, skyscraperPresheaf_eq_pushforward,
   CompHausLike locally-constant comap, constant-sheaf reflection and scheme
   restriction maps. None states closed direct-image base change for arbitrary f.
2. msearch.py loogle, query "TopCat.Sheaf.pullback, TopCat.Sheaf.pushforward":
   one result, TopCat.Sheaf.pullbackPushforwardAdjunction, only the adjunction.
3. msearch.py grep, query "IsClosedEmbedding|closed_pushforward|closedPushforward"
   in Topology/Sheaves: zero hits. Direct rg for LocallyConstant / locally constant
   in Mathlib/Topology/Sheaves also had no result.
4. rg in WeilConjectures/Topology for closedPushforward, closed constant and
   LocallyConstant: no matching notion. Whole WeilConjectures search found étale
   local systems and other unrelated constant-sheaf results. Search for this node
   id in all WeilConjectures had zero results.
5. rg in lean/Sheaf found ClosedPushforwardConstantRestriction, a different theorem
   restricting to a closed subset, whose full module was read; no existing exact
   arbitrary-map comparison. The new declaration name had zero hits in lean/Sheaf,
   dag/lean_names_upstream.json and the source topology modules.

The local Stacks tex files are absent on this machine. Opened the authoritative
source pages https://stacks.math.columbia.edu/tag/0CAL (the reduction),
https://stacks.math.columbia.edu/tag/008H (inverse-image stalks),
https://stacks.math.columbia.edu/tag/00AE (closed-direct-image stalks), and
https://stacks.math.columbia.edu/tag/007T (stalkwise isomorphism criterion).
They agree with the node's proof; the module docstring carries all five steps and
names their DAG dependencies. No STATEMENT-DISPUTED issue was found.

Validation: server single-file compilation was used; the initial invalid adj.left
projection was replaced by the explicit L, and the reported overlong line was
split. The final server compile is clean. deliver2.py --no-push printed OK:
the commit compiles and passes preflight except for the second reading, which the
second reader writes. Nothing was pushed.

## Second reading by C1

Independent second reading: opened the delivered node and Lean file, both
statement-dependency nodes, their Mathlib declarations, and the landed sibling
`ClosedPushforwardConstantRestriction.lean`. No Lean or node change is needed.

Source verification: the repository has no Stacks .tex checkout. Downloaded the
upstream `modules.tex` and `sheaves.tex` into this item's `scratchpad/` and read
`section-constructible`, `lemma-constructible-in-constant` (0CAL),
`section-presheaves-functorial`, `lemma-stalk-pullback` (008H),
`section-closed-immersions`, `lemma-stalks-closed-pushforward` (00AE), and
`lemma-points-exactness` (007T). Also checked the authoritative tag pages:
https://stacks.math.columbia.edu/tag/0CAL,
https://stacks.math.columbia.edu/tag/008H,
https://stacks.math.columbia.edu/tag/00AE,
https://stacks.math.columbia.edu/tag/007T.
The auxiliary comparison is not explicitly stated in 0CAL; it supplies its
reduction. The spectral, constructibility and finiteness hypotheses of 0CAL
belong to that application. The source stalk lemmas and their section-wide
assumptions require only continuous maps, topological spaces, sheaves of sets,
and a closed inclusion. There is no missing separation or finiteness hypothesis.

Object/hypothesis/conclusion inventory and Lean correspondence (H3):

1. X and Y are arbitrary topological spaces; f is continuous.
   `(X Y : TopCat.{u}) (f : X ⟶ Y)` bundles exactly these data. PASS.
2. W is a closed subset of Y; R is an arbitrary set.
   `(W : Set Y) (hW : IsClosed W) (R : Type u)` supplies precisely these
   hypotheses; there is no topology, algebraic structure or inhabitedness on R.
   PASS.
3. Z is the closed preimage of W, not an independently chosen subset.
   `let Z : Set X := f ⁻¹' W` fixes it; continuity and hW imply closedness.
   PASS.
4. A and B are the closed direct images of the constant sheaves on W and Z.
   P and Q have sections `LocallyConstant {y : Y // y ∈ unop V ∧ y ∈ W} R`
   and `LocallyConstant {x : X // x ∈ unop U ∧ x ∈ Z} R`. These subtypes
   have the intersection subspace topology. Their maps are comap along inclusion,
   exactly restriction. `∃ (hP : P.IsSheaf) (hQ : Q.IsSheaf)` asserts the
   sheaf property, and `A := ⟨P, hP⟩`, `B := ⟨Q, hQ⟩` retain these section
   data. Existential proof witnesses add no hypothesis or choice of objects.
   PASS.
5. Direct image is B(f⁻¹V), with the induced restriction maps.
   `Sheaf.pushforward (Type u) f` is the dependency's actual direct-image
   functor; its underlying presheaf is precomposition by `(Opens.map f).op`.
   PASS.
6. The prescribed alpha components compose g with f on f⁻¹V ∩ Z, and are natural.
   `∃ alpha : A ⟶ (Sheaf.pushforward (Type u) f).obj B` includes naturality.
   The following universal V,g equation uses `LocallyConstant.comap` on
   `x ↦ ⟨f x.1, x.2.1, x.2.2⟩`; these proofs put the image in V ∩ W.
   Thus every component is prescribed, with no change in quantifier order. PASS.
7. Inverse image and eta must use the recorded presheaf-colimit/sheafification
   adjunction. L is `Functor.sheafPullbackConstruction.sheafPullback` and adj is
   `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`. Read both
   definitions in Sites/Pullback: L is sheafToPresheaf, left Kan extension, then
   presheafToSheaf; adj composes the Kan-extension and sheafification adjunctions
   and restricts fully faithfully. Read `lanAdjunction_unit`, `comp_unit_app`
   and `map_restrictFullyFaithful_unit_app`: its unit is the coprojection followed
   by sheafification, as the dependency requires. PASS.
8. Alpha-flat is the corresponding morphism, uniquely compatible with eta.
   `let beta := (adj.homEquiv A B).symm alpha` fixes the corresponding map.
   The universal V,g compatibility equation is beta after eta equals alpha.
   The last universal beta' clause asserts uniqueness for exactly that equation.
   These are the node's specified comparison, not an unspecified isomorphism.
   PASS.
9. Alpha-flat is an isomorphism, and bijective over every open of X.
   `IsIso beta` and `∀ U : Opens X, Function.Bijective (beta.hom.app (op U))`
   give both conclusions without weakening or strengthening. PASS.

Dependency check (H4): def-weil-pbc-topological-inverse-image records exactly the
construction used for L and adj. The second dependency records the abstract
`TopCat.Sheaf.pullbackPushforwardAdjunction` and finite-limit preservation.
Read that signature, `sheafPullbackIso`, the recorded finite-limit instance,
and `RepresentablyFlat (Opens.map f)`. Its clause (a) is the same adjunction up
to the recorded canonical left-adjoint isomorphism; using the construction
adjunction preserves the first dependency's specified unit. No extra instance
is assumed by the theorem. Clause (b) is not needed to state this comparison.
Read `LocallyConstant.comap`: it is actual precomposition of locally constant
functions with continuous maps. P and Q are local section descriptions explicitly
required by the node, not new competing global definitions. No new definition
nodes, dependency modules, or statement corrections are present (H12/H13/4c).

Edge cases: W empty gives singleton sections on all opens even for empty R;
W = Y gives the ordinary constant-sheaf comparison, including disconnected
spaces. For empty R, sections are empty on nonempty intersections and singleton
on empty intersections; the stalk argument still applies. Empty X or Y and empty
opens remain covered. No injectivity, surjectivity or local connectedness of f
is required. The arbitrary common universe u imposes no cardinality bound: all
three input sets can be placed in a common universe, and u may be enlarged.
There are no index-set, zero-object, n or characteristic parameters to restrict.

Independent searches (H4), with different wording from the first worker:

- msearch leanfinder: `base change for closed embeddings of topological spaces
  and locally constant sheaves of sets`. Eight hits, all CompHausLike/condensed
  locally constant functor constructions; none is the arbitrary-space theorem.
- msearch loogle: `LocallyConstant, CategoryTheory.IsIso`. No hits.
- msearch grep: `closed.*constant|constant.*closed|base.change`. Hits concern
  unrelated rings, matrices, profinite functions and ringed-space open immersions.
- Direct rg over Mathlib/Topology/Sheaves, source WeilConjectures/Topology and
  project lean/Sheaf/Topology for closed/constant together with pullback,
  inverse-image or base-change: only the project's restriction sibling, which
  was read and has a different conclusion. Broader source/project searches for
  locally constant and closed pushforward found etale-local-system declarations,
  not this topological comparison. The proposed full name and node id are absent
  from WeilConjectures and dag/lean_names_upstream.json.
- msearch leansearch attempted the continuous-map/closed-subset inverse-image
  comparison in natural language; the service returned Internal Server Error.
  Recorded unavailable, with no search verdict inferred from it. The successful
  LeanFinder, Loogle and direct source searches support the no-duplicate finding.

H5/H6/H8/H9: the only mathematical theorem proof is `sorry`; no hollow definition
or auxiliary theorem is introduced. The reflexive identity/composition fields
construct the presheaves. All binders and universe u are explicitly bound.
The module and declaration docstrings name the source and blueprint id; the
five proof steps include the objects and adjunction, germ/unit computation,
evaluation inside Z, singleton stalks outside Z, and the stalkwise isomorphism
criterion giving section bijections. Imports supply sheaf functors, the Type-valued
sheafification instance and locally constant maps; namespace/path/header and
line lengths follow the conventions. The node's lean.statement equals the
complete file signature verbatim. No mismatch was found; changed only this report.

Validation: second-reader scompile of
`lean/Sheaf/Topology/InverseImageClosedPushforwardConstant.lean` returned exit 0,
compiled in 1.5 seconds, with no diagnostics. Delivery dry run and push follow.

## Reviewer fix (R-icp1102)

The inverse image and its adjunction were switched from
`Functor.sheafPullbackConstruction.sheafPullback` / `.sheafAdjunctionContinuous` to the
project's one spelling of the inverse image of sheaves of sets, `TopCat.Sheaf.pullback (Type u) f`
with `TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f`, as landed in
lem-weil-pbc-h0-spectral-closed-restriction (M1 f4fd3341a) (H4/H12: one definition per notion).
`TopCat.Sheaf.pullbackIso` (= `sheafPullbackConstruction.sheafPullbackIso`) identifies it with the
sheafified presheaf inverse image of def-weil-pbc-topological-inverse-image, and alpha-flat, its
unit compatibility, uniqueness, `IsIso` and sectionwise bijectivity transport along that canonical
isomorphism. Everything else is unchanged; recompiled clean as L.

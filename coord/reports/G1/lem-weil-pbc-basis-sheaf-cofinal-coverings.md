## Worker report

The module `Sheaf.Topology.BasisSheafCofinalCoverings` states
`TopologicalSpace.Opens.gluing_of_cofinal_coverings`, with its sole theorem proof `sorry`.
It does not define a new presheaf, covering, or sheaf structure. These notions are expressed
using existing Mathlib objects and explicit quantifiers. The node is unchanged except for `lean`.
There are no dependency modules, new nodes, or statement corrections.

Source read: Stacks Project, Sheaves on Spaces, Lemmas 009L and 009K, at
https://stacks.math.columbia.edu/tag/009L and https://stacks.math.columbia.edu/tag/009K.
The local `literature/stacks-project/sheaves.tex` is absent on this machine, so those original
source pages were opened instead. The source's implication (2) to (1) is the node's claim,
with the node's stronger, global pairwise-intersection closure retained exactly.
The declaration docstring carries all five elementary steps of the node's proof.

Clause correspondence:

- Topological space: `{X : Type u} [TopologicalSpace X]`.
- Set of open subsets and basis: `(B : Set (Opens X)) (hB : IsBasis B)`.
  A member is a subtype element `U : B`. `Opens.IsBasis` is Mathlib's topological-basis
  predicate on the underlying sets of these opens.
- Closure under all pairwise intersections: `hcap : ∀ U V : B, U.val ⊓ V.val ∈ B`.
  The local abbreviation `meet U V` packages this very intersection with its membership
  proof; it creates no alternative intersection operation or global declaration.
- A presheaf of sets on this basis: `F : Bᵒᵖ ⥤ Type v`, using the preorder category of
  the subtype `B`. The values are `F.obj (op U)`. The local abbreviation
  `res U V h := F.map (homOfLE h).op` is exactly restriction along `V ≤ U`.
  `Functor.map_id` and `Functor.map_comp` give the stated identity and transitivity laws.
- A basis family inside `U`: `V : I → {W : B // W ≤ U}`, for arbitrary `I : Type w`.
  The containment proof carries no extra assumption: every member of a family whose
  union is `U` is already contained in `U`. Conversely this encoding gives precisely
  the original family after forgetting the containment proofs.
- Covering equality: `(⨆ i, (V i).val.val) = U.val`, an equality of opens whose underlying
  sets are the union of the family. No nonemptiness, finiteness, or distinctness is imposed.
- A set of selected coverings of each `U`: `C U I V : Prop` is its membership predicate.
  It is inspected only for covering families. Its values on noncovering families are
  irrelevant; restricting this predicate to the union-equality subtype is literally a
  set of coverings, and any set of coverings yields such a predicate. This unbundling
  avoids introducing a second covering structure.
- Cofinality is the first implication hypothesis: for every `U I V` satisfying the union
  equality, there exist `J` and `W` satisfying their own union equality, `C U J W`, and
  `α : J → I` with `∀ j, (W j).val ≤ (V (α j)).val`. This is exactly the specified
  refinement, including its chosen map of index sets.
- Gluing on selected coverings is the second implication hypothesis: for every covering
  with `C U I V`, every family `s : ∀ i, F.obj (op (V i).val)` compatible on every
  `meet (V i).val (V j).val` has `∃! t : F.obj (op U)` whose restrictions equal `s i`.
  The two `res` terms use `inf_le_left` and `inf_le_right` for the inclusions of the
  pairwise intersection. The equality has precisely the intersection value as codomain.
- The conclusion repeats that exact gluing assertion for every covering, with the
  selected-cover predicate removed, and no other change.
- The finite-cover sentence in parentheses is an example, not an additional hypothesis
  or conclusion. It is obtained by taking `C U I V := Finite I`, assuming every covering
  has a finite-indexed refinement. Empty finite index types are included.

Dependency declarations: the node's `stmt_deps` is empty, so there are no recorded
node declarations to import. The Mathlib declarations used are:
`TopologicalSpace.Opens` and `TopologicalSpace.Opens.IsBasis`
(`Mathlib.Topology.Sets.Opens`);
`Preorder.smallCategory` and `CategoryTheory.homOfLE`
(`Mathlib.CategoryTheory.Category.Preorder`);
`CategoryTheory.Functor`, its `obj` and `map`, and its identity/composition laws
(`Mathlib.CategoryTheory.Functor.Basic`, available through the imports);
and the standard category of types (`Mathlib.CategoryTheory.Types.Basic`).
Their source definitions/docstrings were read. All three imports are used.
The meet and restriction `let` expressions are only notation for existing intersections
and maps, so no missing mathematical notion calls for a new definition node.

Edge cases checked before drafting:

- Empty `I` is permitted. Its supremum is the empty open, so it is a covering exactly
  when `U` is empty. A map `J → I` forces the refining index type to be empty too.
  Gluing for that selected refinement says `∃! t, True`, hence exactly one section over
  the empty basis member. The conclusion says the same. No `Nonempty I` assumption.
- Empty topological space and even empty basis are allowed: with no basis members,
  all covering assertions are vacuous. No inhabited-space or inhabited-basis assumption.
- Disjoint basis members have empty intersection, which `hcap` requires to belong to
  the basis. Compatibility is therefore a meaningful equality in `F(empty)`.
- Repeated covering members and arbitrary infinite index types are allowed. Universes
  `u`, `v`, `w` are independent and explicit, and the statement is polymorphic in all
  three. All index types in the chosen covering universe are quantified, not merely
  finite/countable types; section values are not restricted to the universe of `X`.
- The gluing hypothesis is quantified over every basis member, not merely over the
  member being covered. This preserves the essential use over each `V i` in proof step 4.

Searches for an existing statement (performed with `msearch.py`; digests in `searches.jsonl`):

- Lean Finder: `A presheaf of sets on an intersection closed basis is a sheaf if it glues
  on a cofinal system of coverings`. Eight hits, principally
  `TopCat.Presheaf.isSheafOpensLeCover_iff_isSheafPairwiseIntersections`,
  `isSheaf_iff_isSheafPairwiseIntersections`, `IsSheafOpensLeCover`, and associated
  equivalences. They concern presheaves on all opens and equivalent sheaf conditions,
  not gluing for an arbitrary cofinal selection on a basis; no exact match.
- Loogle: `CategoryTheory.Presieve.IsSheafFor, TopologicalSpace.Opens.IsBasis`.
  Zero hits.
- Mathlib grep: `cofinal|IsBasis` under `Topology/Sheaves`. Eleven hits: pairwise
  intersection diagram cofinality, stalk results, and cover-density/basis equivalences.
  None gives this cofinal-covering theorem.
- LeanSearch: `Sheaf gluing on a basis can be checked on a cofinal system of coverings`.
  Service unavailable: Internal Server Error. No verdict from this unavailable service.
- Source/project grep: `basis.*[Ss]heaf|[Ss]heaf.*[Bb]asis|[Cc]ofinal.*[Cc]over`
  in `WeilConjectures` and `lean/Sheaf`. Only unrelated lisse-sheaf, affine-cohomology,
  locally-free-module and torsor hits in the source; none in `lean/Sheaf`.
- Source grep for the exact node id: no hits.
- Name collision check: `cofinal_coverings|gluing_of_cofinal` across Mathlib,
  `WeilConjectures`, and `lean/Sheaf`: no hits.

Validation: server single-file compilation succeeded with exit code 0 and no warnings.
The initial elaboration failure in one intersection-inclusion argument was repaired by
explicitly giving `inf_le_left`/`inf_le_right` their two underlying-open arguments.
`set_option autoImplicit false` additionally checks that no implicit variable is auto-bound.
No statement dispute or node fault was found.

## Second reading by G1

I independently read the sandbox node and theorem, the repository's base node,
Mathlib declarations below, and the Stacks TeX source. The TeX was obtained from
https://raw.githubusercontent.com/stacks/stacks-project/master/sheaves.tex into
`scratchpad/sheaves.tex`; I read Section `section-bases`, lines 3686–3888, including
`definition-presheaf-basis`, `definition-sheaf-basis`, the definition of cofinality,
and both `lemma-cofinal-systems-coverings` and its `standard-case` version.
I also opened tags https://stacks.math.columbia.edu/tag/009J,
https://stacks.math.columbia.edu/tag/009K and https://stacks.math.columbia.edu/tag/009L.
There is no implicit separation, compactness, finiteness, or nonemptiness assumption.
The node deliberately uses the globally intersection-closed special case of 009L
and its (2) implies (1) direction. The Lean says precisely that node's claim.

Object/hypothesis/conclusion checklist, independently extracted from the node:

1. A topological space X: `{X : Type u} [TopologicalSpace X]`. Exact; no extra instances.
2. A set B of opens forming a basis: `(B : Set (Opens X)) (hB : IsBasis B)`.
   Exact. I opened `Opens.IsBasis` at Mathlib/Topology/Sets/Opens.lean:318:
   it is `IsTopologicalBasis` of the corresponding underlying sets.
3. Every pair of basis members has intersection in B: `hcap : ∀ U V : B,
   U.val ⊓ V.val ∈ B`. Exact. The local `meet` is that intersection with its
   membership proof; it is not a separate notion or an additional assumption.
4. A presheaf of sets on B with identity/transitive restrictions: `F : Bᵒᵖ ⥤ Type v`.
   Exact. I opened `Preorder.smallCategory`, `homOfLE`, and `Functor` in their
   Mathlib source modules. The subtype order is inclusion of opens, there is exactly
   one morphism for each inclusion, and `F.map_id` / `F.map_comp` encode the two laws.
   `res U V h = F.map (homOfLE h).op` has exactly the required direction.
5. A B-covering of U with arbitrary index set: `I : Type w`,
   `V : I → {W : B // W ≤ U}`, and `(⨆ i, (V i).val.val) = U.val`.
   Exact. The containment proof is implied by the union equality for the unbundled
   family in the node; bundling it adds no restriction. Opens supremum is union.
6. A selected collection C(U) of such coverings: the dependent predicate `C`.
   Exact. Membership is always guarded by the covering equality; arbitrary values
   on families that do not cover have no effect, so this is a set of coverings.
7. Cofinality for every U and every cover: the first implication hypothesis
   quantifies `U I V`, then produces `J W`, its covering equality, `C U J W`,
   and `α : J → I` with `(W j).val ≤ (V (α j)).val`. Exact refinement direction
   and quantifier order; a refinement is chosen after the cover, before sections.
8. Unique gluing on every selected covering of every basis member: the second
   implication hypothesis quantifies `U I V`, union equality and C-membership,
   then every `s : ∀ i, F.obj (op (V i).val)`, assumes the two restrictions agree
   in `F.obj (op (meet (V i).val (V j).val))` for all i,j, and concludes
   `∃! t : F.obj (op U), ∀ i, res U (V i).val (V i).property t = s i`.
   Exact compatibility, existence, uniqueness, and restriction equations.
9. Conclusion for all B-coverings of all U: the final `∀ U I V` repeats exactly
   the gluing formula in item 8, with C-membership removed. Exact; not merely
   separatedness, and not a claim confined to the original U.
10. The parenthetical finite-cover example is a specialization, not a separate
    conjunct. Taking C-membership to be `Finite I` gives it, including empty covers.

Edge cases: `I = Empty` is allowed, and its union equality forces `U = ⊥`.
A refinement map to Empty forces J empty; the selected gluing condition then
says exactly that F(U) has one element. If an empty open belongs to B, this case
is included; the theorem does not require it to belong to every basis.
An empty space, an empty basis when it is a basis, repeated covering opens,
disjoint members, and arbitrary infinite index types are all allowed. Disjoint
members force the empty intersection into B through hcap, exactly as the node says.
Universes u, v, w are explicit and independent: X, sections, and cover indices
have no equality or size constraint tying them together. The theorem is polymorphic
in w; both the original and refining covers use that arbitrary covering universe.
The proof's auxiliary intersections are indexed by the same J and need no larger
universe. Zero objects, schemes, n and characteristic do not occur in this lemma.

Independent searches, recorded through msearch.py in searches.jsonl:

- LeanFinder: `Unique amalgamation for compatible sections over a basis follows
  from gluing for a collection of covers refining every open cover`. Eight hits,
  including `TopCat.Presheaf.IsSheafUniqueGluing`, `IsGluing`, and the unique-gluing
  equivalence. I opened UniqueGluing.lean:45–83 and its theorem signatures:
  these use a presheaf on all opens and impose all covers, not a cofinal selection
  for a presheaf on B. None is this theorem or a reusable basis-gluing definition.
- Loogle: `"IsSheafFor", "refine"`: zero hits.
- Mathlib grep `refin|subsieve|coverage` in CategoryTheory/Sites, followed by
  `cofinal|refinement|subsieve` in Topology/Sheaves. I opened
  `Presieve.isSheafFor_subsieve` at Sites/IsSheafFor.lean:787: it requires sheafness
  for every pullback of a sieve, an assumption not supplied by the selected-cover
  hypothesis without the present argument. Other hits concern sheafification or
  cofinality of the pairwise-intersection diagram, not refinement of covers here.
- Independent source/project rg: `amalgamat|cofinal.*cover|cover.*cofinal|
  gluing_of_cofinal`. Source hits are uses of amalgamation for sheaves and torsors;
  there is no matching basis/cofinal-cover theorem, and no project hit.
  The full name also has no hit in dag/lean_names_upstream.json.

There are no statement dependencies, new nodes, dependency modules, or statement
corrections to audit. The explicit formulas use existing Mathlib intersections,
functors, and quantifiers; no private mathematical definition is introduced.
The theorem docstring matches all five elementary proof steps, including uniqueness
over each covered member in step 4. Header, source/blueprint docstrings, namespace,
imports, bound variables, and line widths are correct. Only the named theorem has
`sorry`; no theorem was proved and no hollow definition occurs.

Mismatches found: none in the Lean or mathematical statement. I preserved the
module unchanged and reformatted `lean.statement` from whitespace-normalized text
to the literal multiline signature in the file. The only other change is this
second-reading section. Server single-file compilation passed with exit code 0
and no warnings (1.1 seconds). Dry-run and delivery results follow from deliver2.py.

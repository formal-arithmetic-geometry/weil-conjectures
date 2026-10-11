## Worker report

The module `Sheaf.Topology.SheafOnBasisExtends` states
`TopologicalSpace.Opens.exists_sheaf_extension_of_basis_gluing`, with its proof `sorry`.
There are no definitions, helper theorems, new nodes, dependency replacements or statement
corrections. The item's statement dependencies are empty. Its statement is unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The topological space is `(X : TopCat.{u})`; bundling introduces no extra property.
- The set of open subsets is `(B : Set (Opens X))`, and its basis property is
  `(hB : IsBasis B)` using Mathlib's `TopologicalSpace.Opens.IsBasis`.
- Closure under pairwise intersections is
  `(hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)`; meet of opens is intersection.
- The presheaf of abelian groups is `(F : Bᵒᵖ ⥤ AddCommGrpCat.{max u v})`.
  The subtype `B` has its inherited inclusion preorder category. Its value at `U` is
  `F.obj (op U)`, and `r_{U,V}` is `(F.map (homOfLE hVU).op).hom`.
  The functor laws are exactly the identity and composition laws in the node.
  All values are abelian groups and all arrows group homomorphisms by `AddCommGrpCat`.
- In `hglue`, `U : B` is the open being covered, `I : Type (max u v w)` is the cover index,
  and `V : I → {W : B // W ≤ U}` lists its basis members with inclusions into `U`.
  Every member of a family whose union equals `U` is contained in `U`, so these inclusion
  witnesses add no hypothesis. `(⨆ i, (V i).val.val) = U.val` is precisely the union equality.
- `s : ∀ i, F.obj (op (V i).val)` is the family of sections. The two explicit
  `F.map (homOfLE ...).op` terms in `∀ i j, ...` restrict to the same basis member
  `⟨(V i).val.val ⊓ (V j).val.val, hcap (V i).val (V j).val⟩`.
  Their equality is the compatibility on pairwise intersections, exactly as in the node.
- `∃! t : F.obj (op U), ∀ i, (F.map (homOfLE (V i).property).op).hom t = s i`
  says existence and uniqueness of a section restricting to each member of the family.
- `∃ Fext : TopCat.Sheaf AddCommGrpCat.{max u v} X` is the sheaf of abelian groups on `X`.
  This is Mathlib's usual sheaf for the open-cover Grothendieck topology.
- `∃ iota : ∀ U : B, Fext.presheaf.obj (op U.val) ≅ F.obj (op U)` is the family of group
  isomorphisms in the requested direction. Isomorphisms in `AddCommGrpCat` are precisely
  invertible group homomorphisms, equivalently group isomorphisms.
- The last equality, quantified over `(U V : B) (hVU : V ≤ U)` and every section
  `t : Fext.presheaf.obj (op U.val)`, states
  `iota_V(t|_V) = r_{U,V}(iota_U(t))`, with the restriction on the extension given by its
  presheaf map. No uniqueness of the extension or other additional conclusion is asserted.

Definitions and modules used: `TopologicalSpace.Opens.IsBasis` from
`Mathlib.Topology.Sets.Opens`; `TopCat.Sheaf` and `TopCat.Sheaf.presheaf` from
`Mathlib.Topology.Sheaves.Sheaf`; `CategoryTheory.homOfLE` and the inclusion preorder category
from `Mathlib.CategoryTheory.Category.Preorder`; `AddCommGrpCat` and its homomorphisms from
`Mathlib.Algebra.Category.Grp.Basic`. The first three are provided by the sheaf import;
the explicit group import provides the value category. No project-specific notion is copied.

Edge cases checked before writing:

- An empty index is allowed: there is no `Nonempty` assumption. If its union equals `U`, then
  `U` is empty and unique gluing forces `F(U)` to have exactly one element, as required.
- The empty space is allowed, including an empty basis. With no basis members, the comparison
  clause is vacuous and the zero sheaf gives the extension; if the empty open belongs to the
  basis, its group is forced to be trivial by empty-cover gluing.
- Empty intersections must belong to the basis when they occur; `hcap` states exactly this,
  and compatibility uses the actual intersection, including the empty open.
- Zero groups and repeated basis opens are allowed. Compatibility for two identical opens
  forces their sections equal because restriction to their intersection is the identity.
- The group universe is `max u v`, large enough for the products of stalks indexed by points
  of `X`, while `v` is arbitrary and imposes no size ceiling on input abelian groups.
- The index universe `max u v w` always contains `u`, the universe of the basis. Thus gluing
  is tested on every covering subfamily of the basis and is not vacuous due to a too-small
  index universe. Any family from a still larger universe is reindexed by its image in `B`:
  choose one representative per distinct open; compatibility forces all repeated sections
  equal, and unions and unique gluing are unchanged. Empty families remain empty. This
  represents arbitrary set-indexed covering families without a countability restriction.

Source reading: the local checkout omits `literature/stacks-project/sheaves.tex`, so I opened
[Stacks 009N](https://stacks.math.columbia.edu/tag/009N),
[Stacks 009Q](https://stacks.math.columbia.edu/tag/009Q) and
[Stacks 009J](https://stacks.math.columbia.edu/tag/009J) directly.
The theorem is the existence portion of the extension lemma specialized to abelian groups;
the node already states the intersection-closed basis version of the sheaf condition.
The docstring carries all four steps of the node's proof, naming its three proof dependencies.
No statement dispute or node fault was found.

Searches made (2026-10-11):

- `msearch.py ... leanfinder "A sheaf of abelian groups on an intersection closed basis of
  open sets extends to a sheaf on the whole topological space"`: eight hits, including
  `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`, pairwise-intersection variants,
  `TopCat.subpresheafToTypes.isSheaf`, `TopCat.subsheafToTypes`, and unique-gluing variants.
  These concern presheaves on all opens, or local predicates; none states this extension.
- `msearch.py ... loogle "TopCat.Sheaf, TopologicalSpace.IsTopologicalBasis"`: zero hits.
- `msearch.py ... leansearch "A sheaf of abelian groups on a basis extends to a sheaf on the
  topological space"`: unavailable, Internal Server Error. No mathematical verdict inferred.
- `msearch.py ... grep "extend.*[Bb]asis|[Bb]asis.*extend|inducedFunctor" Topology/Sheaves`:
  five hits in `SheafCondition/Sites.lean`, for cover density and extending morphisms.
  Read `coverDense_inducedFunctor` and the surrounding basis comparison declarations:
  these do not extend an object from the explicit elementary gluing hypothesis.
- `rg` for the item id and extension/basis-presheaf phrases in the source `WeilConjectures`
  and project `lean/Sheaf`: no extension-from-basis statement. Found and read
  `Sheaf.Topology.BasisSheafSectionsGerms` and `Sheaf.Topology.BasisSheafCofinalCoverings`,
  which concern germs and cofinal gluing, respectively; neither states this conclusion.
- `rg` for `exists_sheaf_extension_of_basis_gluing|SheafOnBasisExtends` in
  `dag/lean_names_upstream.json`, Mathlib, source `WeilConjectures`, and project `lean/Sheaf`:
  no collision. The original node's recorded comparison-lemma search also shows why
  `Functor.sheafInducedTopologyEquivOfIsCoverDense` is a general tool, not this statement.

Validation: the server single-file compile succeeded without errors or warnings (1.2 seconds).
All variables and universes are explicit, there are no `let` binders, and the sole proof is
`sorry`. The delivery dry run is the final validation; the independent second reading is left
for the designated second reader.

## Second reading by E1

I reread the node statement, its Stacks source (Section 009H, Lemmas 009M,
009N, and 009Q, with 009L for the intersection-closed sheaf condition), and the
module independently. The correspondence is as follows.

- The topological space is `X : TopCat.{u}`; `B : Set (Opens X)` is the set of
  opens, and `hB : IsBasis B` is exactly the basis hypothesis.
- Closure under intersections is `hcap : ∀ U V : B, U.val ⊓ V.val ∈ B`.
- The basis presheaf is `F : Bᵒᵖ ⥤ AddCommGrpCat.{max u v}`. Its values are
  abelian groups, and its maps are group homomorphisms. Functor identity and
  composition laws render the two presheaf laws in the node.
- The gluing hypothesis quantifies `U : B`, an arbitrary-universe index type
  rendered as `I : Type (max u v w)`, and basis members below `U` rendered by
  `V : I → {W : B // W ≤ U}`. The supremum equality is the union equality.
  The two displayed `F.map (homOfLE ...).op` terms are restrictions to the
  basis intersection and their equality is pairwise compatibility.
- `∃! t : F.obj (op U)` and the following restriction equations render unique
  gluing. Empty index types, repeated members, and zero groups remain allowed.
  The universe parameter `w` is polymorphic and `max u v w` contains the basis
  universe, so the hypothesis is not vacuous for any allowed cover indexing.
- The conclusion `∃ Fext : TopCat.Sheaf AddCommGrpCat.{max u v} X` is a sheaf of
  abelian groups on `X`. The family `iota : ∀ U : B, ... ≅ F.obj (op U)` has the
  required direction, and the final equality is precisely compatibility with
  restriction for every `V ≤ U` and section `t`.

No hypothesis is added or omitted, and all conclusion clauses and quantifier
orders agree with the node. The empty space and empty basis are admitted;
empty covers force the corresponding unique-gluing condition exactly as in the
source. Empty intersections are covered by `hcap`, and `n = 0` or
characteristic assumptions do not occur in this topological lemma. No universe
or variable is left implicit under the module's `autoImplicit false` setting.

I searched Mathlib and the slopmaster2/project sources with `rg` for
`exists_sheaf_extension_of_basis_gluing`, `SheafOnBasisExtends`, and
extension/basis-presheaf variants, and ran the recorded `msearch.py` LeanSearch,
LeanFinder, Loogle, and grep searches. The hits are general induced-topology,
germ, or sheaf-condition comparison tools; none is this statement. The node has
no statement dependencies, so there are no dependency declarations to replace.
The source and Lean were consistent; I found no mismatch and made no changes.
The module recompiles cleanly with `scompile.py` (only its permitted `sorry`
proof remains).

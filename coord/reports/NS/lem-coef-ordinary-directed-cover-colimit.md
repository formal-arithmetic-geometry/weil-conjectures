## Worker report

The module `Sheaf.CategoryTheory.OrdinaryDirectedCoverColimit` states
`CategoryTheory.Limits.ordinary_directed_cover_colimit`, with its sole proof `sorry`.
It introduces no definitions, helper axioms or additional nodes. The original node's
statement, statement dependencies, proof and proof dependencies are unchanged.

The earlier worker's rejection concerned an unchanged stage-1 split already merged by
NY. That merge supplied the five-step natural-language proof, but no Lean record.
This delivery supplies the missing stage-2 statement, rather than redelivering the split.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Fix a universe and take small sets/categories in it | Explicit `universe u v`; `I : Type u`, `C : Type u`, `[SmallCategory C]`. The target category's object universe is independently `v`. |
| Nonempty poset with upper bounds for every finite subset | `[PartialOrder I] [Nonempty I]` and `hdir : ∀ i j, ∃ k, i ≤ k ∧ j ≤ k`. Pairwise upper bounds and nonemptiness are equivalent to the stated finite-subset condition: induct on a finite subset, using any index for the empty subset. This is no restriction to linear orders or chosen binary suprema. |
| Full subcategories with literal increasing inclusions | `S : I → ObjectProperty C`, `(S i).FullSubcategory`, and `hmono : Monotone S`. Mathlib's full subcategory uses exactly all ambient arrows between the selected objects; `(S i).ι` is its inclusion. The object at stage `j` of a stage-`i` object is literally `⟨c.obj, hmono hij c.obj c.property⟩`. |
| Every object belongs to a stage | `hcover : ∀ c : C, ∃ i : I, S i c`. |
| Ordinary category with small Hom sets and all small colimits | `{A : Type v} [Category.{u} A] [HasColimitsOfSize.{u, u} A]`. Both shapes and Hom sets use the fixed small universe, without equating the object's universe to it. |
| Functor on the whole category | `F : C ⥤ A`. |
| Chosen local colimit cocones for the restrictions | `s : ∀ i, Cocone ((S i).ι ⋙ F)` and `hs : ∀ i, IsColimit (s i)`. The point `(s i).pt` is `L_i`, and `(s i).ι.app c` is its specified leg. |
| Chosen total colimit cocone | `t : Cocone F`, `ht : IsColimit t`; its point and legs are exactly `L` and `λ_c`. |
| Unique transition satisfying the local-leg equations | First iff clause: an arbitrary `a : (s i).pt ⟶ (s j).pt` satisfies all leg equations iff it equals `eqToHom (e i).symm ≫ D.map (homOfLE hij) ≫ eqToHom (e j)`. Taking this displayed map establishes existence; the iff establishes uniqueness among all maps satisfying the equations. |
| Transitions define an I-diagram on precisely these objects | The conclusion supplies `D : I ⥤ A` and `e : ∀ i, D.obj i = (s i).pt`. Equality transport records exactly the chosen vertices, not alternative vertices up to an unspecified isomorphism. `D` carries identity and composition laws. Thus the specified transition maps obey these laws after the displayed equality transports. |
| Unique maps to L with specified legs | `v : D ⟶ (Functor.const I).obj t.pt` and the second iff clause. The actual map from `L_i` is `eqToHom (e i).symm ≫ v.app i`. The iff says this is the unique map with every prescribed `λ_c` composite. Naturality of `v` states compatibility with all transitions. |
| L with these maps is a colimit cocone | `Nonempty (IsColimit (⟨t.pt, v⟩ : Cocone D))`. `IsColimit` is structure-valued; `Nonempty` expresses its universal property propositionally. No colimit witness is assumed for this new diagram. |
| For every H, compatible families are in bijection with cocones on F with vertex H | For each `H : A`, the existential `E` is an equivalence from the subtype of families `f : ∀ i, (s i).pt ⟶ H` satisfying `u_ij ≫ f j = f i`, to `F ⟶ (Functor.const C).obj H`. The latter is precisely the family of cocone legs with that fixed vertex and their naturality equations. |
| The correspondence is the specified composite/factorization correspondence | For every `g`, index and local object, `(s i).ι.app c ≫ (E.symm g).val i = g.app c.obj`. Thus the inverse sends a cocone to its local colimit factorizations. Since `E` is an equivalence, substituting `g = E f` gives the forward composite-leg equation as well; it cannot be an unrelated bijection. Local colimit uniqueness determines each factorization. |
| The canonical comparison is an isomorphism with the specified legs | `IsIso (colimit.desc D (⟨t.pt, v⟩ : Cocone D))`, followed by the equation that its composite with `colimit.ι D i` is `v.app i`. The arrow is Mathlib's actual canonical desc map, not an arbitrary isomorphism. Transporting its source leg by `eqToHom (e i).symm` yields exactly the map on `L_i` specified above. |
| Empty C and empty stages allowed | Neither `C` nor `(S i).FullSubcategory` has a nonemptiness binder. Their chosen colimits may be initial objects. |

Dependency read and used: `def-weil-pbc-category-colimit`, with recorded module
`Mathlib.CategoryTheory.Limits.HasLimits`, declaration `CategoryTheory.Limits.colimit`
and accompanying recorded declarations `Cocone`, `IsColimit`, `colimit.desc`, `IsFiltered`.
I read its full node, the `Cocone` structure/docstring in `Limits/Cones.lean`, the
`IsColimit` structure/docstring in `Limits/IsLimit.lean`, and the generated dual
declarations for `colimit`, `colimit.ι`, and `colimit.desc` in `Limits/HasLimits.lean`.
I also read `IsFiltered` in `Filtered/Basic.lean`; the theorem spells out directedness
directly, so needs no separate filteredness assumption. The same sole dependency is
also every non-elementary proof dependency, so its module is publicly imported.
The other imports provide the Mathlib full-subcategory construction and the canonical
category on a poset. No project notion has been privately copied.

Source read: `literature/stacks-project/categories.tex`, lines 1300--1340, including
Definition 002F and the empty-diagram observation. The directed-cover assertion is
the agent-formulated argument recorded in the node, not a numbered Stacks theorem.
All five proof steps are reproduced in the theorem docstring for stage 3.

Edge cases checked before writing:

- Empty `C`: the cover condition is vacuous, all stages are empty, and chosen colimits
  are initial. The transition maps are unique. A nonempty directed poset is connected,
  so this diagram of initial objects again has an initial colimit. For every `H`, both
  sets in the equivalence are singleton sets. Nothing in the signature excludes this.
- An empty early stage: its colimit is initial, so all required transition/family maps
  from it are unique. No choice of an object inside this stage is required.
- A singleton index: `hcover` forces that full subcategory to contain every object;
  the assertion becomes uniqueness of chosen colimits with the same specified legs.
- Incomparable indices: only a common upper bound is used. There is no total-order or
  binary-supremum assumption. The common-stage argument compares both local choices.
- Parallel arrows of `C`: fullness puts both arrows in any stage containing their
  endpoints, so the argument includes their cocone equations, without a thinness
  assumption on `C`.
- The empty index is explicitly excluded by the source, and by `[Nonempty I]`.
  This binder also supplies an upper bound for the empty finite subset in the
  finite-subset formulation of directedness. No additional nonemptiness is imposed.
- A large object universe for `A` remains possible independently of the fixed small
  universe for Hom sets and indexing categories.

Searches for an exact existing statement:

- `msearch.py` leanfinder, query "Colimits over a directed increasing cover of a small
  category by full subcategories assemble to the total colimit": 8 hits. They concern
  small-object transfinite iteration and locally directed open gluing of schemes;
  none states this ordinary full-subcategory cover theorem for arbitrary targets,
  chosen local cocones and the specified family-to-cocone bijection.
- `msearch.py` loogle, query `"IsColimit", "FullSubcategory"`: 0 hits.
- `msearch.py` grep, query
  `directedCover|[Dd]irected.*[Uu]nion|[Uu]nion.*[Cc]olimit` in `CategoryTheory/Limits`:
  2 hits, both `ConcreteCategory/Basic.lean` on surjectivity from the union of values
  of a concrete colimit. These do not assemble variable full indexing subcategories.
- `rg` for `directedCover`, directed-colimit terms, and
  `directed.?cover|cover.*full subcategor|full subcategor.*cover` in the project's
  `WeilConjectures` and `lean/Sheaf`: no exact ordinary statement. Read
  `Sheaf.CategoryTheory.DirectedCoverColimitAssembly.directed_cover_colimit_assembly`:
  its domain is a simplicial set and its target a quasicategory, with coherent
  simplicial cones and prisms. It does not state the ordinary cocone bijection.
- `grep -rn 'lem-coef-ordinary-directed-cover-colimit'` in `WeilConjectures`: no match.
- Read Mathlib's `ObjectProperty.FullSubcategory`, `ObjectProperty.ι`, `ιOfLE`,
  `homOfLE`, and `leOfHom` to use their actual interfaces rather than duplicate them.

Validation: the prescribed `scompile.py NS lem-coef-ordinary-directed-cover-colimit`
accepted the delivered module cleanly (1.3 seconds for its library compilation).
Every universe and variable is explicitly bound; there are no auxiliary theorems or
definitions, no file-local notation/instances and no non-sorry proof.
There are no statement disputes, node corrections or dependency-interface repairs.

The node copy adds only `lean`, with the theorem signature extracted verbatim from
the file, branch `newtargets-dag`, group `NS`, and the current UTC date.

## Second reading by NS

Independent maintainer second reading, 2026-10-17, of immutable delivery
67ecf5475b21f496f7e7dcd3f55f926e9b731038. I did not write or previously review this
delivery. I read packet.md, the complete check-brief2.md, the snapshot item and its sole
statement dependency, the delivered module and report, the source places, and the exact
Mathlib declarations. This section replaces the previous non-reading placeholder.

Hypothesis and conclusion audit (H3):

| Node object or clause | Exact Lean rendering and verdict |
| --- | --- |
| Fixed small universe; small nonempty poset | `I : Type u`, `PartialOrder I`, `Nonempty I`: exact. |
| Every finite subset has an upper bound | `hdir : ∀ i j, ∃ k, i ≤ k ∧ j ≤ k`: exact together with nonemptiness, by induction on the finite subset; the empty subset uses any index. |
| Small ordinary category | `C : Type u`, `SmallCategory C`: objects and morphisms small in the same universe. |
| Increasing literal full subcategories covering all objects | `S : I → ObjectProperty C`, `Monotone S`, `hcover`: exact. Mathlib `FullSubcategory` has underlying ambient objects and every ambient morphism, with `ι` the forgetful inclusion. The stage-j object `⟨c.obj, hmono hij c.obj c.property⟩` has exactly the same underlying object. No strict-fullness or closure-under-isomorphism hypothesis is added. |
| Target has small Hom sets and all small colimits | `A : Type v`, `Category.{u} A`, `HasColimitsOfSize.{u,u} A`: exact. Target objects have an independent universe; no equality of that universe with u is imposed. |
| Functor, chosen local and total colimit cocones | `F`, `s`, `hs`, `t`, `ht`: exact restrictions via `(S i).ι ⋙ F`, with their actual chosen points and legs. |
| Unique specified transitions | First iff quantifies over every candidate `a` and all local legs. Its right side is the transported `D.map (homOfLE hij)`. Substituting that right side gives existence; the converse gives uniqueness. Exact, not arbitrary transition maps. |
| These maps form the I-diagram | Existential `D : I ⥤ A` supplies identity and composition; `e i : D.obj i = (s i).pt` supplies precisely the chosen vertices. Transporting back along e preserves both laws. Equality transport introduces no new objects or unspecified isomorphisms. |
| Unique specified maps to L and their compatibility | Second iff characterizes `eqToHom (e i).symm ≫ v.app i` on every local leg. Naturality of `v` gives compatibility with the transitions, after cancelling the inverse equality transports. Exact. |
| L is a colimit of this diagram | `Nonempty (IsColimit (⟨t.pt,v⟩ : Cocone D))`: exact propositional existence of the universal-property structure. This is a conclusion about a specified cocone, not a hollow construction. |
| Bijection for every H | `∀ H, ∃ E : { f // compatibility } ≃ (F ⟶ const H)`: exact compatible families and fixed-vertex cocones. The inverse leg equation specifies the factorization of every g through each chosen local colimit. Substituting `g = E f` and using `E.symm_apply_apply` gives the forward composite equation, so E cannot be an arbitrary bijection. |
| Canonical comparison and its legs | `IsIso (colimit.desc D ⟨t.pt,v⟩)` and the final `colimit.ι ≫ colimit.desc = v.app` equations: exact canonical arrow and all specified legs. `HasColimitsOfSize` supplies the small I-colimit without an additional assumption. |
| Empty category or empty stages allowed | Neither C nor any stage has a nonemptiness assumption: exact. |

Source and dependency audit:

- Read Stacks `literature/stacks-project/categories.tex:1300-1340`, especially tag
  002F, label `definition-colimit`, and the following empty-colimit observation.
  It supplies precisely the cocone universal property. The delivery correctly labels
  the directed-cover theorem as agent-formulated, rather than attributing it to a
  separately numbered Stacks theorem.
- Read `def-weil-pbc-category-colimit.json` in full. Its recorded Mathlib interface is
  used directly: `Cocone` in `Limits/Cones.lean:122-138`, `IsColimit` in
  `Limits/IsLimit.lean:58-72`, and the generated duals `colimit`, `colimit.ι`,
  `colimit.isColimit`, `colimit.desc` in `Limits/HasLimits.lean:174-250`.
  `HasColimitsOfSize` at lines 133-145 quantifies over both small shape universes.
  Also read `IsFiltered` in `Filtered/Basic.lean:76-100` and the canonical poset
  category and `homOfLE` in `Category/Preorder.lean:37-89`.
- Read `ObjectProperty/FullSubcategory.lean:31-109,145-165`: real ambient-object
  construction, induced morphisms, inclusion and inclusion for a predicate inequality.
  The theorem uses these notions, with no private replacement.
- All five proof steps are sound applications of the dependency's universal property.
  Step 1 gets both maps and functor laws by uniqueness. Step 2 uses an upper bound to
  compare choices and a common stage plus fullness for each ambient arrow. Step 3
  restricts and uniquely factors, proving compatibility and both inverse identities.
  Step 4 combines this bijection with `ht` to give the total universal property and
  the canonical isomorphism. Step 5 treats initial objects for empty diagrams.
  The module docstring reproduces all five steps, with source and blueprint markers.
- `stmt_deps = proof_deps = [def-weil-pbc-category-colimit]`; the union of proof-step
  uses is exactly this list. No missing helper, new node, unusable dependency interface,
  source-based correction, citer audit requirement, or universe repair arises.
- For blueprint context, read the indicated paragraph beginning `For K` in
  `prop-coef-integral-exceptional-adjoint.proof.md` and the actual consumer
  `lem-coef-cellular-tree-presentable-approximations`, Step 12. Its small nonempty
  filtered support poset, increasing covering full subposets with the root, chosen
  restriction colimits and specified comparison legs fit this ordinary theorem.

Independent one-definition-per-notion checks (H4): searched Mathlib CategoryTheory,
upstream `WeilConjectures`, and group `lean/Sheaf` with the alternative phrases
`full.subcategor ... cover/union`, `cover/union ... full.subcategor`, and
`directed ... cover/union`. No exact existing ordinary theorem was found. Opened
`DirectedCoverColimitAssembly.lean` and its actual theorem signature: it concerns
simplicial sets, quasicategories and coherent cones, and is not this ordinary statement.
The worker report also records the required semantic, type-pattern and text searches.
The existing Mathlib notions, rather than new definitions, are used throughout.

Edge cases independently checked: empty C (both sides of the bijection are singleton,
all stage points initial); empty early stages (unique maps out of initial objects);
singleton I (uniqueness of chosen colimits); incomparable indices with a common upper
bound (no linearity or supremum assumption); parallel arrows (both occur in a full
stage containing the endpoints); empty I excluded exactly as the node requires; large
target object universe independent of the small Hom/index universe. No zero-object,
characteristic or geometric assumptions occur.

Mechanical and compiler checks: the item's `lean.statement` is byte-for-byte equal to
the file text from `theorem ordinary_directed_cover_colimit` up to, excluding, ` := by`.
All record fields are present; `existing` is false and the module/file/name agree.
All variables and universes are bound, all Lean lines have at most 100 characters,
imports serve the statement, and the namespace is upstream-compatible. The single
proof is exactly `by sorry`; there are no definitions, helper axioms or local proofs.
No pro-etale substitute occurs.

Reproduced the sole per-file compile by invoking:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py NS lem-coef-ordinary-directed-cover-colimit /home/ubuntu/weil-launcher-nt/reviews-stage2/NS__lem-coef-ordinary-directed-cover-colimit__67ecf5475b21/snapshot/lean/Sheaf/CategoryTheory/OrdinaryDirectedCoverColimit.lean
```

Exit 0; sandbox and library compile both clean, 0.9 seconds each, no diagnostics.
The installed wrapper currently routes to server `nt_srv_compile.py --wire-confirm`,
which reports a private `nt-local-compile-.../.lbuild` overlay. This verifies the exact
snapshot through the prescribed wrapper; it is not a global build. The worker's
recorded 1.3-second clean compile is consistent with this reproduction.

Finding and correction: H11 (substantive second-reading record absent, despite the
heading being present). The original section merely said there was no worker second
reading. Under the explicit maintainer requirement for a real section, I replace that
placeholder with this independent clause-by-clause audit, retaining the complete
Worker report. No Lean or JSON record needs correction. This is a mechanical report
repair and is supplied as a complete merge-tool-compatible replacement report.

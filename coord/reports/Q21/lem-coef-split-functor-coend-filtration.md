## Worker report

Repair of the return on immutable head 29149a83adfc. That return identified a stage-1-only
packet with no Lean module, binding, signature, or compile evidence. The retained sandbox
contained only dispatcher metadata. This packet supplies the substantive stage-2 statement
in `lean/Sheaf/SixFunctors/SplitFunctorCoendFiltration.lean`, the item's `lean` record, and
this report. It retains the current main-branch node verbatim outside `lean`. The delivery
wrapper rebases the packet onto current `newtargets-dag` before checking and pushing.

The main declaration is
`CategoryTheory.SplitFunctorCoend.exists_relativeFiltration`. It asserts
`Nonempty (RelativeFiltration.{u} C)` for every category `C : Type v` with
`Category.{w} C` and `HasColimitsOfSize.{u, u} C`. The structure is the complete mathematical
witness, not a hypothesis or an arbitrary map selected from an existence theorem. The
construction definitions have real data, and the only `sorry` is the named main theorem.
No structure field is chosen from this theorem in any definition.

The node is an explicitly agent-stated categorical extension of Dugger's skeletal
argument, not a claim that Dugger literally states this general functor version. I read
[Dugger's primer](https://pages.uoregon.edu/ddugger/hocolim.pdf), Section 3.4, proof of
Theorem 3.5 (printed p.10), and Section 19 (printed pp.90--93), together with all sixteen
steps of the node's categorical proof. The module/theorem docstrings record this
provenance and give the complete sixteen-step proof plan, including the mixed
face/degeneracy check and the endomorphism relations. The theorem is not proved in stage 2.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| C cocomplete, in containing universes | Independent universes `u v w`; `C : Type v`, `Category.{w} C`, `HasColimitsOfSize.{u, u} C`. These are the small colimits for simplicial sets in `Type u`; neither object nor Hom universe of C is equated with u. The size-zero simplex coend is obtained by Mathlib's size-shrinking theorem inside the two construction definitions. |
| Simplicial sets and maps | Mathlib `SSet.{u}` and its ordinary functor-category morphisms, with no finiteness or nonemptiness requirement. |
| T a simplicial diagram of functors | `S.obj.X : SimplicialObject (SSet.{u} ⥤ C)` for `S : Data.{u} C`. |
| Every T_p preserves all small colimits | First component of `S.property`: `∀ d, PreservesColimitsOfSize.{u, u} (S.obj.X.obj d)`. |
| Given colimit-preserving N_q and natural transformations N_q → T_q | `S.obj.s.N q`, `S.obj.s.ι q` in Mathlib's `SimplicialObject.Splitting`, and the second component of `S.property` gives preservation for every N_q. |
| Canonical degeneracy coproduct map is an isomorphism, identity included | Mathlib `Splitting.isColimit'`, whose cofan is `Splitting.cofan'`. Its index is all epimorphisms `[p] → [q]`, including `IndexSet.id`, and its legs are exactly `s.ι q ≫ X.map σ.op`. Epimorphisms of the simplex category are precisely the surjective monotone maps. Saying that this cofan is colimiting is equivalent to the canonical map from the chosen coproduct being an isomorphism. This uses the existing splitting notion without an extra degeneracy assumption. |
| Define R_T(K) by the displayed coequalizer | `coendDiagram T K` has `(b,a)` value `T_b(K ⊗ Δ[a])`. `realization T K` is Mathlib `coend` of that diagram. `multispanIndexCoend` has arrow-α source `T_b(K ⊗ Δ[a])` and its two maps are `T(α)` and `T_b(K ◁ stdSimplex.map α)`. Mathlib's multicoequalizer is the same coproduct/coequalizer universal property. |
| Canonical coend coprojections and action on i and on T | `realizationι` is the actual `coend.ι`; `RelativeFiltration.coendIso` and `ι_coend` identify `R` and `ι` with those actual constructions. `ι_map` and `ι_data` fix both functorial actions on every coend summand. Thus R(i) is the canonical map, not an unconstrained comparison. |
| Every map i:K→L | `Arrow SSet.{u}`, with its genuine commuting-square morphisms. No mono, cofibration or model-category hypothesis occurs. |
| Countable filtration, starting at Z_{-1}=R_T(K) | `F : (Data.{u} C × Arrow SSet.{u}) ⥤ ℕ ⥤ C`. Degree 0 represents -1, and degree p+1 represents p. `initialIso` is the canonical categorical identification of stage 0 with R(K), and `initial_natural` makes it natural. Equality of a chosen pushout with a chosen coend object is expressed by the canonical isomorphism, not a definitional equality of choices. |
| Its colimit is R_T(L), and it factors R_T(i) | `c`, `isColimit`, and `c_initial`. In particular the initial cocone component equals `initialIso.hom ≫ R.map i`; this is stronger than an unrelated isomorphism of colimit objects and is exactly the claimed factorization. |
| The displayed relative boundary object | `boundarySquare i p` is Mathlib `Functor.PushoutObjObj.ofHasPushout` applied to the actual cartesian product bifunctor and `i`, `boundary p.ι`. Its `pt` is `(L × ∂Δ[p]) ⨿_(K × ∂Δ[p]) (K × Δ[p])`, in that order; its `inl`, `inr` are the two canonical maps. |
| Its canonical map to L×Δ[p], after N_p | `cell x p := N_p.mapArrow.obj (Arrow.mk (boundarySquare i p).ι)`. Thus its underlying arrow is exactly `N_p.map` of the pushout-product arrow. This is not a replacement by a latching object or by an arbitrary map. |
| Each pth transition is a pushout of that arrow | Fields `attach`, `disk`, and `pushout`, with transition `F.map (homOfLE (Nat.le_succ p))`. `IsPushout` supplies the full universal property. |
| The bottom map is induced by the identity splitting summand and coend maps | `disk_eq` says `disk = (s.ι p).app (L × Δ[p]) ≫ j` at stage p+1. `j_c` identifies each retained summand with its full coend coprojection; `j_step`, `j_relation`, and `j_K` give its truncation, simplex-operator and K-compatibility equations. |
| The attaching map is face-induced | `attach_face` specifies its L-leg on every codimension-one face using `SSet.boundary.ι k`, `T.map (SimplexCategory.δ k).op`, and the retained lower-degree `j` map. All other proper faces factor through these. Preservation of the boundary face colimit makes these component equations determine the entire L-leg, including all intersections. |
| The attaching map on the K-leg is induced by the coend maps | `attach_K` is exactly `N_p(K × Δ[p]) → T_p(K × Δ[p]) → R_T(K) → F(i)(p)`; together with the face formula it determines the whole upper attaching map by the pushout universal property and N_p's colimit preservation. At p=0 the boundary is empty, so its other leg is unique. |
| Natural in i and maps respecting specified splittings | `Data` is a full subcategory of Mathlib `SimplicialObject.Split`, whose morphisms contain both `F:T→T'` and `f q:N_q→N'_q` with `ι q ≫ F_q = f q ≫ ι' q`. The one functor `F` acts on their product with the arrow category. `initial_natural`, `c_natural`, and `j_natural` specify the canonical actions. `attach_natural` and `disk_natural` explicitly state naturality of the attaching squares themselves, using the canonical `boundaryMap`. |
| p=0 and empty K,L, no enrichment or model structure | All quantifiers range over ℕ and arbitrary `SSet`; the assumptions mention only ordinary categories, colimits, and the stated splittings. |

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set`: `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic` (simplicial objects of `Type u`).
  I also read the recorded `degenerate`, `nonDegenerate`, `Subcomplex`, and `Finite`
  declarations and docstrings; their extra predicates are not required by this item.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `Cocone`,
  `IsColimit` from `Mathlib.CategoryTheory.Limits.HasLimits` and the chosen-colimit API.
  The theorem uses the actual `Cocone`/`IsColimit` universal property; the realization
  uses its Mathlib coend implementation, not a private colimit definition.
- `def-weil-pbc-trivial-kan-fibration`: the relevant first sentence is exactly
  `SSet.stdSimplex` from `...SimplicialSet.StdSimplex` and `SSet.boundary` from
  `...SimplicialSet.Boundary`. I read the recorded `modelCategoryQuillen.I` declaration
  and boundary description too. Only the standard simplex/boundary is used, so the
  module imports the smaller boundary module and assumes no Kan or model structure.
- Additional existing Mathlib constructions: `SimplicialObject.Splitting`,
  `SimplicialObject.Split` and `Split.Hom` from `...SimplicialObject.Split`;
  `ObjectProperty.FullSubcategory`; `coend`, `coend.ι`, `multispanIndexCoend` from
  `...Limits.Shapes.End`; `curriedTensor SSet` (the cartesian product instance in
  `...SimplicialSet.Monoidal`); `Functor.PushoutObjObj.ofHasPushout` and
  `Functor.PushoutObjObj.mapArrowLeft` from `...Pullback.PullbackObjObj`;
  `Functor.mapArrow`; `SSet.boundary.ι`.

The seven construction abbreviations/definitions and the witness structure are helpers
for the owning theorem's statement, listed in `lean.declarations`. They combine the
existing Mathlib notions just named; they introduce no independent missing notion,
no additional postponed theorem and no new DAG node. There are no dependency repairs
or statement corrections. The recorded `proof_deps` are precisely the three definition
leaves above, supplied by these imports; no extra unstated proof dependency is imported.

Edge cases checked before drafting and again in the second pass:

- p=0: no proper faces or proper surjections; the splitting is T_0=N_0 and
  `boundary_zero` gives the empty boundary. Since N_0 preserves the initial object,
  the displayed relative cell is N_0(K)→N_0(L); the pushout transition is the initial
  transition from stage 0 to stage 1. `attach_face` is required only in positive
  degree, while `pushout` and `attach_K` include zero.
- Empty K: every T_p(K×Δ[p]) is initial by colimit preservation, giving the absolute
  skeletal filtration. Empty L: a map from K forces K empty degreewise; all coends
  and stages are initial. No Nonempty binder excludes either case.
- i=id: the relative boundary map is an isomorphism, and all transitions are
  isomorphisms, yielding the constant relative filtration up to its canonical maps.
- Arbitrary noninjective i (e.g. Δ[1]→Δ[0]) remains allowed: `boundarySquare` is an
  ordinary pushout and does not treat its objects as unions or subobjects.
- p=1: both endpoints in `Fin 2` are specified by `attach_face`; the K-leg equality
  supplies their compatibility with the common R(K) map. Nonidentity endomorphisms
  of [p] are included in `j_relation`, not silently omitted.
- Universes: u, v, w are independent. Shrinking u-small colimits to the small simplex
  indexing category does not equate any site or coefficient universes, and works
  also when u=0. The input functor and arrow categories may live in larger containing
  universes without requiring colimits indexed by those entire input categories.

Existing-declaration searches performed on 2026-10-17:

| Tool | Query | Result |
| --- | --- | --- |
| `msearch.py leanfinder` | `split simplicial diagram of colimit preserving functors coend relative skeletal filtration pushout boundary` | Eight hits, notably `SimplicialObject.Splitting.isColimit`, `isColimit'`, `cofan'`, `cofan`, and `desc`, plus Dold--Kan splitting and subcomplex multicoequalizers. Reused the exact splitting API; none states this relative filtration. |
| `msearch.py loogle` | `CategoryTheory.Limits.coend, SSet.boundary, SimplexCategory.Truncated` | Zero hits. Direct source inspection found the actual ordinary coend and boundary APIs used here. |
| `msearch.py grep` in `CategoryTheory` | `split.*[Ff]unctor\|coend\|skeletal` | 25 capped hits concern skeleton categories and unrelated splitting, not the theorem. |
| `msearch.py leansearch` | `coend simplicial object split skeletal filtration pushout` | Eight hits on `SimplicialObject.Split` and `Splitting`; no theorem match. |
| `rg` in upstream and `lean/Sheaf` | `lem-coef-split-functor-coend-filtration\|split.*[Ff]unctor\|coend.*[Ff]iltration` | No item declaration. Related `WeightedCoendSkeletalFiltration` and `FreeBarCellFiltration` modules were read. The former uses cosimplicial weighted coends with two relative latching arrows; the latter is a particular free bar in simplicial sets. Neither is this split diagram of arbitrary colimit-preserving functors. |
| DAG statement/record inspection | `SimplicialObject.Splitting\|SimplicialObject.Split\|split simplicial object\|split simplicial diagram` | Related hypercover and bar nodes are specialized and supply no competing general definition. The tensor-coend-skeletal-pushouts node requires enrichment/tensors; `def-coef-simplicial-realization-map` is a tensor realization map with that extra data. No exact statement or input notion was replaced. |
| `rg` in `dag/lean_names_upstream.json` | item id | No hit. |
| `rg` in Mathlib, upstream and `lean/Sheaf` | `SplitFunctorCoend\|exists_relativeFiltration\|boundarySquare\|RelativeFiltration` | No declaration-name collision. |

Validation: the final delivered module compiled through `scompile.py Q21
lem-coef-split-functor-coend-filtration <module>` both as a sandbox and at its actual
library module path. Latest clean run: sandbox 2.2 s, library 3.0 s; no error and no
warning. An intermediate attempt to inline the large Leibniz functor's map exceeded
Lean's default heartbeat budget; replacing that expression by the existing
`PushoutObjObj.mapArrowLeft` through `boundaryMap` repaired elaboration, without raising
any limit. The prescribed delivery dry run also passed server preflight and compilation (commit
6d86e03080, before this report-only count correction). No global build or direct compiler
invocation was used. Every universe and
variable is bound explicitly, with `set_option autoImplicit false`.

Return checklist: H1/H3 now have the complete compiled statement; H2 has its exact
signature and declaration binding; H1/H11 have this clause-by-clause report and the
substantive second pass below; H8 has source/blueprint docstrings for every top-level
helper and the theorem, whose docstring includes all sixteen proof steps. No
STATEMENT-DISPUTED issue remains or was identified.

## Second reading by Q21

This is the author's separate second pass, not a claim that another agent reviewed the
packet. The dispatcher brief forbids starting another agent; the maintainer supplies
the independent review. I reopened the current node, all three dependency records,
the Mathlib split/coend/pushout definitions, and the complete Lean module.

The hypotheses match: Data contains T, N and ι, and only their stated colimit
preservation and Mathlib's equivalent cofan splitting. In particular I checked that
`Split.Hom.comm` is the exact compatibility required of maps of specified splittings,
that the identity surjection is an index, and that there is no requirement of enrichment,
monomorphy, cofibrancy, or nonempty simplicial input. The category's object/Hom and
simplicial-set universes remain independent.

For the conclusion I expanded `coendDiagram` and `multispanIndexCoend`: its α-summand
is T_b(K×Δ[a]), and the maps have the two directions in the node, rather than the
opposite tensor-coend convention. I checked `boundarySquare` against Mathlib's
`PushoutObjObj`: its first leg is L×∂Δ[p] and second is K×Δ[p], so `attach_K`
correctly uses `inr`, while `attach_face` uses `inl`. I checked each composition in the
face formula: N_(p+1)(L×Δ[p]) goes by ι_(p+1), T(δ_k), and the retained degree-p
summand into stage p+1. The target is Z_p, the required preceding term for the
(p+1)st attachment. At p=0 there is no face equation to omit: the empty boundary's
map is uniquely determined, while the K-leg and pushout are still required.

I also checked the indexing and factorization: F(0)=Z_{-1}, F(p)=Z_{p-1},
F(p+1)=Z_p; `pushout` uses exactly this transition. `c_initial` fixes the initial map
to be R(i), and `isColimit` refers to that very cocone. `ι_coend` plus `ι_map` and
`ι_data` prevent R from having an arbitrary action. `j_relation` includes all
endomorphisms; `j_K`, `j_step`, and `j_c` fix its compatibility with the relative
truncations and full coend.

One point was made more explicit during this pass: the initial version encoded
naturality of the filtration, its endpoints and summands, with attaching-square
naturality following from uniqueness and the face/K formulas. I added the actual
`attach_natural` and `disk_natural` equations so that the two naturalities of the
attaching squares are directly present in the formal statement as well. The canonical
boundary corner map is the real Mathlib construction `mapArrowLeft`, not an arbitrary
comparison. This final version compiled cleanly, as recorded above.

All edge cases in the worker report remain admitted by the final signature. I found
no further mathematical mismatch, no hollow definition, no unbound implicit variable,
and no reason to change the node's statement, proof or dependencies.

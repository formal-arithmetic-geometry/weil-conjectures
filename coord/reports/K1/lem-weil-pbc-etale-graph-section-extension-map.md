## Worker report

Module: `Sheaf.AlgebraicGeometry.EtaleGraphSectionExtensionMap`. Three theorem statements
jointly render the node, all with `sorry` proofs:
`AlgebraicGeometry.etale_graph_clopen`,
`AlgebraicGeometry.etale_graph_section_extension_map`, and
`AlgebraicGeometry.etale_graph_preimage`. No definitions or new nodes are introduced.

Source read: [Stacks 0F4L](https://stacks.math.columbia.edu/tag/0F4L), first paragraph of
the proof, and [Stacks 01KT](https://stacks.math.columbia.edu/tag/01KT). The local Stacks
checkout is absent, so these source pages were read online. The existing node statement
agrees with that construction specialized to finite étale π and module coefficients.
No statement correction or dispute is needed.

Hypotheses and objects, matched individually:

- Schemes X and U: `{X U : Scheme.{u}}`, with explicit universe `u`.
- Finite étale π: `(π : U ⟶ X) [IsFinite π] [Etale π]` in all three statements.
- Commutative Λ: `(Λ : Type (u + 1)) [CommRing Λ]` in the extension statement.
- Sheaf of constant Λ-modules: `M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  This is the constant-coefficient encoding explicitly authorized by the `lean.note` of
  `def-weil-pbc-etale-sheaves` for the six-functor chapters. It matches the recorded
  `etaleLowerShriek` and `lowerStar` signatures; it is not a substitute category chosen
  to avoid their interfaces. The general `SheafOfModules` encoding was also read.
- V an object of X_et: `(V : X.Etale)` in the geometry and preimage statements.
- X-morphism φ: `(φ : V.left ⟶ U) (h : V.hom = φ ≫ π)`. This does not assume φ is
  étale: `Etale φ` is a conclusion of `etale_graph_clopen`.
- V_U and projections: `pullback V.hom π`, `pullback.fst`, and `pullback.snd`.
  In the comparison theorem `B := MorphismProperty.Over.pullback @Etale ⊤ π` is exactly
  the dependency's base-change functor, and `B.obj V` is the étale U-object whose
  underlying scheme is that pullback and whose structure map is `pullback.snd`.
- (V,φ): in the comparison statement it is denoted `W : U.Etale`. The geometry
  statement supplies étaleness of every φ in the node, so every (V,φ) occurs among
  these W. `L.obj W` is the original V as an X-object, with structure map φ ≫ π.
  This reindexing includes all X-morphisms, without an extra étaleness hypothesis.
- Section s: `s : M.obj.obj (op W)`. Candidate extended section t:
  `t : M.obj.obj (op (B.obj (L.obj W)))`.

Clause 1:

- `(V,φ)` is an étale U-object: `Etale φ` in `etale_graph_clopen`.
- The graph is `pullback.lift (𝟙 V.left) φ (by simp [h])`.
- Its U-site morphism is `γ : W ⟶ B.obj (L.obj W)`, the unit of the existing
  `MorphismProperty.Over.mapPullbackAdj`. Its definition was read: its underlying
  scheme morphism is precisely `pullback.lift (𝟙 _) W.hom (by simp)` and it commutes
  with the second projection. Using this existing morphism avoids a new graph definition.
- The graph image is open and closed: `IsOpenImmersion Γ ∧ IsClosedImmersion Γ`.
- The explicit open subscheme identification is
  `∃ O, (O : Set (pullback V.hom π : Scheme.{u})) = Set.range Γ ∧
  ∃ γ : V.left ≅ O.toScheme, γ.hom ≫ O.ι = Γ`.
  Thus the asserted isomorphism has the actual graph as its composite with inclusion.

Clause 2:

- Extension `e` is the `ModuleCat` morphism obtained by composing the Kan-unit
  summand inclusion with the component of c. Its type explicitly has domain M(W)
  and codomain M(V_U). A `ModuleCat Λ` morphism is Λ-linear, so the linearity clause
  is included in the type, with no extra theorem or assumed linearity.
- `M.obj.map γ.op t = s` is the graph restriction condition.
- The complement-zero condition quantifies `T : U.Etale` and `j : T ⟶ V_U` with
  `IsOpenImmersion j.left` and `Set.range j.left = (Set.range γ.left)ᶜ`, and says
  `M.obj.map j.op t = 0`. These are exactly the presentations of the complementary
  open subscheme. Such a presentation exists because clause 1 makes the graph closed;
  its open inclusion composed with q_V is étale. Quantifying every presentation makes
  the statement independent of a choice of the complementary open scheme. It neither
  asserts vanishing elsewhere nor permits a vacuous condition: the canonical complement
  inclusion is one of the quantified j. Other presentations differ by an isomorphism.
- The biconditional `(graph restriction ∧ complement restriction) ↔ t = e s`
  asserts both existence (take `t = e s`) and uniqueness of the required extension.

Clause 3:

- `P := sheafToPresheaf ... ⋙ L.op.lan` is the presheaf underlying the recorded
  `Etale.etaleLowerShriek` before sheafification. The recorded declaration was read in
  `WeilConjectures/SixFunctors/Etale/LowerShriek/EtaleMap.lean`, lines 45–56: its body is
  `sheafPullbackConstruction.sheafPullback L`, the same left Kan extension followed by
  sheafification. The source's `CategoryTheory/GrothendieckAbelian/HasLeftKanExtension.lean`
  was also read (lines 23–46 and 90–280): lifts index a final discrete subcategory of
  the comma category, so this existing Kan extension is the prescribed direct sum.
  Its `lanUnit` at W is precisely inclusion of the summand for φ = W.hom. Thus this
  does not introduce a different P or require a missing definition node.
- `D := Etale.lowerStar ... π ⋙ sheafToPresheaf ...` is the recorded direct image,
  with underlying presheaf retained. Its defining formula is precomposition with B.op;
  `lowerStar_obj_val_obj` confirms the section formula is definitionally M(V_U).
- `∃ c : P ⟶ D` is one natural transformation between functors from module sheaves
  to module presheaves. Each `c.app M` is therefore a presheaf morphism, and naturality
  of c in M is precisely `P.map α ≫ c.app M' = c.app M ≫ D.map α`, the node's equation.
- The stated composite defining e fixes the value of `(c.app M)` on each summand
  inclusion to the unique graph extension. Since components of c are Λ-linear and
  P(V) is the direct sum, this is precisely the finite-sum formula in the node.
  Natural transformations of presheaves already carry compatibility with restriction;
  no additional pointwise function lacking a naturality condition is substituted.
- The last key-point sentence is separately explicit in `etale_graph_preimage`:
  for `a : V' ⟶ V`, `Γ'` uses `a.left ≫ φ` and
  `aU := (MorphismProperty.Over.pullback @Etale ⊤ π).map a`; its conclusion is
  `aU.left ⁻¹' Set.range Γ = Set.range Γ'`.

Dependency declarations and their source modules read:

- Finite étale category: Mathlib `CategoryTheory.MorphismProperty.Comma`,
  `MorphismProperty.Over`, specialized to `@IsFinite ⊓ @Etale`; base-change definition
  `MorphismProperty.Over.pullback` in `OverAdjunction`. Only the finite étale property
  of π is needed in this item, rather than the category of finite étale objects.
- Scheme conventions: convention-only node; used `Scheme`, `IsFinite`, `Etale`,
  `IsOpenImmersion`, `IsClosedImmersion` in their Mathlib meanings.
- Étale site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology`; category `Scheme.Etale`, including its instances for
  structure maps and maps between objects, in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- Étale sheaves: `Sheaf.AlgebraicGeometry.EtaleSheaves`, its recorded mixed declaration
  and docstrings, and its explicit permission for constant-coefficient `ModuleCat` sheaves.
- General module sheaves: `Mathlib.Algebra.Category.ModuleCat.Sheaf`, `SheafOfModules`
  and `SheafOfModules.Hom` signatures/docstrings. The constant-coefficient encoding
  above is used consistently with the two recorded six-functor dependency signatures.
- Fibre product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`, plus scheme pullbacks.
- Étale base change and finite limits: `MorphismProperty.Over.pullback` in
  `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`, and the finite-limit
  preservation instance and `mkIdTerminal` in `Mathlib.CategoryTheory.Limits.MorphismProperty`.
- Sum extension: `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`,
  `Etale.etaleLowerShriek`; its existing pre-sheafification Kan construction is used.
- Direct image: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `Etale.lowerStar` and the objectwise section formula. Its derived-direct-image
  declaration is irrelevant to this node's underived presheaf construction.

Edge cases checked: empty V and U, empty graph/complement, and zero sheaf and zero
coefficient ring are admitted. On the empty complement the sheaf condition gives only
zero sections, as required. An empty lift index is allowed by the Kan extension and
produces the zero direct sum. No nonemptiness, connectedness, characteristic, finiteness
of section modules, or nonzero-ring assumption is introduced. Universe `u` is arbitrary;
`ModuleCat.{u+1}` follows the recorded functor signatures for schemes in universe u.

Searches run for this item (2026-10-11):

- msearch LeanFinder, query `finite etale graph section extension by zero natural map
  sum presheaf to direct image`: eight hits including Zariski gluing, module-sheaf free
  sections, and topological sheaf facts; no exact graph-section presheaf statement.
- msearch Loogle, query `Functor.lan, Functor.lanUnit`: zero hits, unknown identifier
  `Functor.lan`. This was an unsuccessful name query, not evidence of absent Kan extensions;
  those definitions were then located and read directly in Mathlib.
- msearch grep, query `graph.*section|extensionByZero|lowerShriekToLowerStar`: six
  unrelated graph/topology hits, none this statement.
- msearch LeanSearch, query `finite etale graph extension section by zero sum presheaf
  direct image natural transformation`: UNAVAILABLE, Internal Server Error. No no-match
  verdict is inferred from the unavailable service.
- `rg` over the project's `lean/Sheaf` and source `WeilConjectures` for graph, extension,
  and `etaleLowerShriek`, then exact node id and each proposed full declaration name:
  existing Kan-extension/shriek definitions were found, but no exact statement or name
  collision. The node-id query returned no source declaration for this item.
- Source grep for `lanUnit` located the Kan unit in
  `Mathlib/CategoryTheory/Functor/KanExtension/Adjunction.lean`, which was read.
- Source grep for `op_lan_overMap` located the existing lift-index/final-discrete-functor
  implementation in `WeilConjectures/CategoryTheory/GrothendieckAbelian/HasLeftKanExtension.lean`.

The final module compiled on the server without errors or warnings. The independent
second reading is left to the dispatcher’s second worker; no review is claimed here.

## Second reading by K1

Independent reading of the repository node, sandbox module, all nine statement-dependency
nodes, and the declarations behind their records. Verdict: the three theorem signatures
jointly render the node without added hypotheses or omitted conclusions. No signature,
node statement, definition, or dependency record was changed. The only Lean repair adds
explicit DAG dependency references to the existing nine-step proof docstring (H8).

Source checked independently: Stacks `etale-cohomology.tex`,
`lemma-shriek-into-star-separated-etale` (0F4L), and `schemes.tex`,
`lemma-section-immersion` (01KT), read as raw TeX from
`https://raw.githubusercontent.com/stacks/stacks-project/master/` because the local
Stacks directory is absent. Also read the beginning of the extension-by-zero section
and equation `equation-j-p-shriek`. The source assumes separated etale j and arbitrary
ring coefficients; the node deliberately specializes to finite etale pi and commutative
coefficients. Finiteness gives the required separatedness. There is no blanket
Noetherian, field, characteristic, connectedness, or quasi-compactness assumption on X
or on the site objects. This item is only the presheaf construction; injectivity after
sheafification in the remainder of 0F4L is not part of its statement.

Object/hypothesis/clause checklist, in node order:

1. Schemes X and U: `{X U : Scheme.{u}}`; arbitrary explicit universe u. PASS.
2. Finite etale pi: `(π : U ⟶ X) [IsFinite π] [Etale π]` in each theorem.
   Both instances express the node's hypotheses, with no additional property. PASS.
3. Commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`. PASS.
4. Module sheaf M on U_et: `M : Sheaf U.smallEtaleTopology (ModuleCat.{u+1} Λ)`.
   The dependency `def-weil-pbc-etale-sheaves` explicitly authorizes this encoding for
   six-functor chapters alongside `SheafOfModules` over the constant ring sheaf.
   I read `EtaleSheaves.lean`, Mathlib `SheafOfModules` and its `Hom`, and the actual
   `etaleLowerShriek` and `lowerStar` signatures. This is the authorized encoding,
   not a private replacement of the category. PASS.
5. V in X_et: `(V : X.Etale)`; an X-morphism phi is
   `(φ : V.left ⟶ U) (h : V.hom = φ ≫ π)`. `Etale φ` is a conclusion,
   not an extra hypothesis. PASS.
6. V_U, p_V, q_V: `pullback V.hom π`, `pullback.fst`, `pullback.snd`.
   Read Mathlib `pullback`, `pullback.lift`, and `MorphismProperty.Over.pullback`:
   `B.obj V` has this underlying scheme and second projection to U.
   Base change supplies etaleness over U; composing with pi supplies etaleness over X.
   The finite-limit dependency's recorded Mathlib instance and terminal object were
   read; its reversed product order is already allowed by its match. PASS.
7. (V,phi) is an object of U_et: `Etale φ` in `etale_graph_clopen`.
   In the section theorem this is reindexed as `W : U.Etale`, with original X-object
   `L.obj W`. Conversely every pair (V,phi) of the node gives such a W by clause 1;
   `L.obj W` is V over X, up to the equality h of its structure map. No lift is lost.
   Read Mathlib's `Scheme.Etale`, `Over.mk`, and `Over.map` signatures. PASS.
8. Graph is a U-site morphism: in geometry its underlying map is
   `Γ := pullback.lift (𝟙 V.left) φ (by simp [h])`; in the section theorem it is
   `γ : W ⟶ B.obj (L.obj W)`, the unit of `Over.mapPullbackAdj`.
   I read that adjunction's body: its unit is exactly this pullback lift and its
   homMk equation is the second-projection compatibility. PASS.
9. Graph image is open and closed, and V is isomorphic onto its open subscheme:
   `IsOpenImmersion Γ ∧ IsClosedImmersion Γ`, followed by an open O with
   `(O : Set _) = Set.range Γ` and `∃ γ : V.left ≅ O.toScheme, γ.hom ≫ O.ι = Γ`.
   This explicitly identifies the isomorphism with the actual graph, not merely an
   unrelated isomorphism of schemes. PASS.
10. For each s there is exactly one extended t: the biconditional ending `t = e s`
    holds for every s and t. At t = e s it gives existence; in the other direction
    it gives uniqueness. `M.obj.map γ.op t = s` is exactly graph restriction. PASS.
11. Complement restriction is zero: the universal condition on
    `T : U.Etale`, `j : T ⟶ B.obj (L.obj W)`, with `IsOpenImmersion j.left`
    and `Set.range j.left = (Set.range γ.left)ᶜ`, states `M.obj.map j.op t = 0`.
    Clause 1 makes the complement open. Its canonical open-subscheme inclusion,
    composed with q_V, defines one such T and j by etale composition. Thus this
    quantification cannot be vacuous. Any other such open immersion is isomorphic
    over V_U to that canonical complement, so it imposes exactly the same condition,
    not vanishing on additional opens. PASS.
12. Extension is Lambda-linear: e is a morphism in `ModuleCat Λ`, namely
    `(L.op.lanUnit.app M.obj).app (op W) ≫ (c.app M).app (op (L.obj W))`.
    It is therefore a linear map with the precise domain and codomain M(W), M(V_U).
    No linearity hypothesis on a freely chosen function is substituted. PASS.
13. P_M is the dependency's sum presheaf with the stated restrictions:
    `P := sheafToPresheaf ... ⋙ L.op.lan`. Read `EtaleMap.lean` and Mathlib
    `Sites/Pullback.lean`: the recorded shriek definition is this very Kan extension
    followed by sheafification. Read the lift-index construction in the source
    `CategoryTheory/GrothendieckAbelian/HasLeftKanExtension.lean`: the indexing comma
    category has a final discrete subcategory of the factorizations phi of V.hom.
    Each final object carries M(V,phi), so its colimit is exactly the direct sum,
    including its canonical inclusions. `Functor.lanUnit` was read in Mathlib's
    `Functor/KanExtension/Adjunction.lean`; at W it selects the identity comma object,
    hence the summand indexed by W.hom. Contravariance sends phi along a to phi a
    with restriction M(a); the induced coproduct map adds colliding summands. PASS.
14. Direct image: `D := Etale.lowerStar ... π ⋙ sheafToPresheaf ...`.
    Read `UpperLowerStar/Defs.lean`: `lowerStar_obj_val_obj`,
    `lowerStar_obj_val_map`, and `lowerStar_map_hom_app` confirm respectively
    M(V_U), restriction by a_U, and componentwise action of alpha. PASS.
15. The component c sends a finitely supported family to the sum of its extensions:
    `∃ c : P ⟶ D` together with the composite defining e specifies every summand
    inclusion. A module morphism out of this coproduct is determined by those maps;
    linearity gives exactly the finite-sum formula. The same c works for every M
    and W, so the quantifier order includes the node's natural family. PASS.
16. c_M is a presheaf morphism: `c.app M` is a natural transformation of
    module-valued presheaves, which already contains restriction compatibility. PASS.
17. Naturality in M and every alpha: outer `c : P ⟶ D` is a natural transformation
    of functors on the module-sheaf category. Its naturality equation is
    `P.map α ≫ c.app M' = c.app M ≫ D.map α`, exactly the node's equation.
    No restriction to isomorphisms or to individual sheaves is made. PASS.
18. Key preimage identity for each a: `etale_graph_preimage` binds
    `(V V' : X.Etale) (a : V' ⟶ V)` and the original phi and h;
    Γ' is the lift with second component `a.left ≫ φ`, aU is `B.map a`, and
    `aU.left ⁻¹' Set.range Γ = Set.range Γ'` is precisely the node's equality. PASS.

Edge cases: empty X, U, V and V' are allowed; no nonemptiness instance appears.
An empty lift set gives the initial module in the pointwise Kan formula, so c is
its unique map. For an empty graph, or graph equal to all V_U, the complementary
open is respectively all or empty; the empty covering forces sheaf sections on the
empty scheme to be the zero module. Zero sheaves and the zero coefficient ring are
allowed by ModuleCat and CommRing. No integer n is a binder here; empty support
(n = 0 in the finite-sum interpretation) maps to zero by linearity. Characteristic
is unrestricted. Universe u is bound; the coefficient/module universe u+1 agrees
with both recorded functors, and arbitrary sizes are covered by choosing u large
enough (smaller schemes/rings may be lifted). No implicit field, finite-module,
Noetherian, or nonzero-ring condition occurs.

Independent searches on 2026-10-11:

- msearch LeanFinder: `sections of sheaf extend uniquely by zero on clopen subscheme
  graph finite etale morphism`. Eight hits: structure-sheaf gluing, zero on a cover,
  and other scheme-section facts, none this construction.
- msearch Loogle: `IsOpenImmersion, IsClosedImmersion` failed because the short name
  was unknown. Retried with `AlgebraicGeometry.IsOpenImmersion,
  AlgebraicGeometry.IsClosedImmersion`: three immersion-factorization/diagonal hits,
  none the graph section construction.
- msearch LeanSearch: `finite etale graph extension by zero sections natural presheaf
  comparison`: UNAVAILABLE (Internal Server Error); no absence verdict based on it.
- rg on Mathlib, source WeilConjectures, and project lean/Sheaf using
  `graph.*(extension|section)`, `extend.*(clopen|complement)`,
  `lowerShriekToLowerStar`, and `shriek.*[Ii]nto.*[Ss]tar`: found unrelated
  compactification/blowup graphs and six-functor comparison declarations. I opened
  `SixFunctors/Etale/LowerShriek/Comparison.lean`: its comparison is for the
  sheafified compactification-based shriek, or for open immersions; it is not the
  finite-etale presheaf graph construction or its section characterization.
- Exact proposed names and node id were searched in dag/lean_names_upstream.json,
  source WeilConjectures and project lean/Sheaf: no collision or existing statement.
  Existing Kan-extension notions are reused, not redefined.

H12/H13: this delivery has no new definition nodes or dependency modules. The existing
records suffice; the convention-only dependency has no declaration to import and the
finite-etale-category match only supplies pi's finite-etale terminology here.
H5/H6: there are no definitions, and all three theorem proofs remain `by sorry`.
The inline `by simp` terms only certify well-typed pullback lifts in the statements.
H8/H9: source places and the exact blueprint tag occur in each declaration docstring;
the main docstring has all nine proof steps, now with explicit dependency ids. The sole
import supplies the existing shriek, star, site, Kan and geometric constructions and is
used. Namespace, bound universe and 100-character lines were checked. The node's
`lean.statement` is verbatim the main theorem signature, unchanged by the docstring repair.

No mathematical mismatch, private definition, hidden hypothesis, source correction, or
unit-level fault was found. Only missing explicit proof-dependency citations were repaired.

Verification: prescribed scompile server compile passed in 2.1 seconds, no errors or
warnings. A direct signature comparison and line-width check passed.

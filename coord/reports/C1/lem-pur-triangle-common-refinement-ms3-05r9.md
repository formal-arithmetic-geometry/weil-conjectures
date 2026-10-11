## Worker report

The module `Sheaf.CategoryTheory.TriangleCommonRefinement` states
`CategoryTheory.triangle_common_refinement_and_equalization`, with one `sorry` and no definitions.
It unpacks the category in the node using Mathlib triangle morphisms rather than creating a
second category definition. There are no new nodes, dependency modules, or statement changes.

Hypothesis and clause correspondence:

- The pre-triangulated category is `{C : Type u} [Category.{v} C] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]`. All universes and variables are explicit.
- The saturated compatible multiplicative system is `(S : MorphismProperty C)` with
  `hS : S.IsSaturatedMultiplicativeSystem` (MS1--MS4) and
  `[S.IsCompatibleWithTriangulation]` (MS5--MS6). These are precisely the two conjuncts
  of the dependency's `IsSaturatedTriangulatedMultiplicativeSystem`; that convenience
  predicate additionally requires the octahedral instance in its binders. Using its
  recorded constituent declaration and Mathlib compatibility avoids adding TR4 to the
  node's explicitly pre-triangulated setting, as in the source Tag 05R9.
- The fixed distinguished triangle is `(T : Triangle C) (hT : T ∈ distTriang C)`.
- Objects over T are distinguished triangles `D i` and morphisms `s i : D i ⟶ T`
  satisfying `S (s i).hom₁ ∧ S (s i).hom₂ ∧ S (s i).hom₃`. This is exactly all
  three denominator conditions. `TriangleMorphism` includes all three commuting
  triangle squares, including the shifted third square.
- A finite family is `∀ (I : Type w) [Finite I] (D : I → Triangle C)
  (s : ∀ i : I, D i ⟶ T)`, with the preceding distinguishedness and S conditions.
  Its predecessor is `∃ (U : Triangle C) (t : U ⟶ T)`, distinguished U and all
  three components of t in S. For each i there is `a : U ⟶ D i` with all components
  in S and `a ≫ s i = t`: exactly an arrow over T to each object.
- The second conjunct quantifies two distinguished triangles D,E over T with
  denominator maps s,t. Parallel arrows `a b : D ⟶ E` have all six components
  in S and satisfy `a ≫ t = s` and `b ≫ t = s`.
- The equalizer is a distinguished U with denominator `r : U ⟶ T` and arrow
  `q : U ⟶ D`, all six components in S and `q ≫ s = r`. The last three equalities
  are `q.homₖ ≫ a.homₖ = q.homₖ ≫ b.homₖ` for k=1,2,3, exactly agreement
  of the parallel composites componentwise. Equality of triangle morphisms and
  componentwise equality are equivalent by Mathlib's `Triangle.hom_ext`.

Dependency declarations read and used:

- `def-weil-triangulated-category` is a Mathlib leaf. Read the full class and
  docstring of `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, the octahedral
  `CategoryTheory.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Triangulated`,
  and `Triangle`, `TriangleMorphism`, their composition/category instance and extensionality
  in `Mathlib.CategoryTheory.Triangulated.Basic`.
- `def-pur-saturated-triangulated-localization` records
  `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`, imported here.
  Read the whole module. Use its recorded
  `CategoryTheory.MorphismProperty.IsSaturatedMultiplicativeSystem` and Mathlib's
  `CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation`
  (`Mathlib.CategoryTheory.Localization.Triangulated`). The latter was also read in full.

Source: the local `literature/stacks-project/derived.tex` is absent, so opened
https://stacks.math.columbia.edu/tag/05R9. Its outward/filtered construction has the
inward/cofiltered dual used by this node. The proof in the docstring follows all three
DAG proof steps, including saturation of comparison maps, completion, rotation,
MS3 repairs, finite iteration, the empty family and componentwise equalization.
No false statement or typing fault was found; no STATEMENT-DISPUTED flag.

Edge cases: I may be empty (identity denominator of T is a predecessor), singleton,
or any finite type in an arbitrary universe w. No Fintype choices or nonemptiness
are imposed. Zero/contractible triangles and the minimal system of isomorphisms
are admitted. The maximal system is also admitted. Equal arrows a=b are admitted
and the identity on D can equalize them. No nonzero-object or characteristic
restriction appears. Triangle equality covers the shifted third square.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py`:

- leanfinder: "finite common refinements and equalization of distinguished triangle
  morphisms in a saturated multiplicative system" returned eight hits: localization
  completion, subcategory fraction calculus and cone-characterization statements,
  and t-structure completion. None gives both conclusions about denominator triangles.
- loogle: "CategoryTheory.TriangleMorphism, CategoryTheory.IsCofiltered" gave zero
  hits and reported unknown identifier CategoryTheory.TriangleMorphism.
- leansearch: "distinguished triangles multiplicative system common refinement
  equalization" was unavailable (Internal Server Error); no mathematical verdict.
- grep: "cofiltered|equaliz|refinement" in CategoryTheory/Triangulated gave zero hits.
- Direct rg: `common_refinement|equaliz|cofiltered` in Mathlib's localization
  triangulated module gave zero hits. `triangle.*[Rr]efinement|[Dd]enominator.*[Tt]riangle|
  common_refinement` in dag/lean_names_upstream.json, lean/Sheaf and upstream
  WeilConjectures/CategoryTheory found no matching statement (one unrelated adjoint
  denominator docstring). The item id search in upstream WeilConjectures gave no hits.
  `triangle.*[Rr]efinement|[Cc]ofiltered|Triangle.*[Dd]enominator` in project and upstream
  CategoryTheory found only unrelated pro-diagram, Galois and resolution declarations.
  New theorem name is absent from the upstream/project sources and Mathlib searches.

Validation: server single-file compilation succeeded in 1.3 seconds, exit code 0,
with no errors or warnings. Delivery dry run is the final check; second reading is
left to the independent reader as instructed.


## Second reading by C1

Independent reading of the delivered node and TriangleCommonRefinement.lean, both statement
 dependencies, and their declaration sources. Verdict: the statement matches the node; no
Lean or node repair was needed. Added this independent audit and fresh search results only.

Source checked: the repository has no local Stacks derived.tex. Read the actual TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex,
label lemma-limit-triangles (Tag 05R9), together with
https://stacks.math.columbia.edu/tag/05R9. The source assumes only a pre-triangulated
category and a saturated compatible multiplicative system. Its outward construction is
dualized for this node's inward arrows; the node asks only for refinements and equalization,
not the source's additional cofinality conclusions. Rotation, completion and cancellation
in the source support the dual construction. No extra octahedral hypothesis is justified.

Object/hypothesis/conclusion checklist, with the Lean rendering and individual verdicts:

- Ambient pre-triangulated category: `{C : Type u} [Category.{v} C] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]`. Read Mathlib's Pretriangulated class (TR1--TR3) against
  def-weil-triangulated-category. PASS: these are the recorded pre-triangulated
  structures; binary biproducts follow from them. No IsTriangulated/TR4 assumption.
- System of arrows: `(S : MorphismProperty C)`. PASS: arbitrary class of arrows,
  not just quasi-isomorphisms, isomorphisms, or arrows from a triangulated subcategory.
- Multiplicativity and saturation: `(hS : S.IsSaturatedMultiplicativeSystem)`.
  Read IsMultiplicativeSystem and IsSaturatedMultiplicativeSystem in the dependency
  module, and Mathlib HasLeftCalculusOfFractions/HasRightCalculusOfFractions.
  PASS: identities/composition, both square completions and both cancellation
  directions are MS1--MS3; the dependency's four-object implication is MS4.
- Compatibility: `[S.IsCompatibleWithTriangulation]`. Read its Mathlib class and
  IsCompatibleWithShift in Shift/Localization. PASS: shift invariance plus a third
  S-component completing each S-square of distinguished triangles is MS5--MS6.
  All integer shifts impose no extra hypothesis: the source's shift-by-one iff,
  iterated in both directions, gives this using invariance under the canonical
  shift isomorphisms (isomorphisms belong to a saturated system).
  The recorded dependency's convenience predicate additionally binds TR4, so
  the statement correctly uses its recorded constituent definition and Mathlib
  compatibility instead. This is no private replacement definition.
- Fixed distinguished triangle: `(T : Triangle C) (hT : T ∈ distTriang C)`.
  PASS: all six pieces of the node's fixed triangle are in T.
- Objects over T: `D i : Triangle C`, `s i : D i ⟶ T`, distinguishedness
  of every D i, and `S (s i).hom₁ ∧ S (s i).hom₂ ∧ S (s i).hom₃`.
  PASS: exactly the denominator triangles. Read TriangleMorphism and its
  comm₁/comm₂/comm₃ fields in Mathlib Triangulated/Basic; the last square uses
  the shifted first component, as required.
- Finite family: `∀ (I : Type w) [Finite I] (D : I → Triangle C)
  (s : ∀ i : I, D i ⟶ T)`, followed by the preceding object conditions.
  PASS: every finite family, including repetitions and the empty family.
- Common predecessor: `∃ (U : Triangle C) (t : U ⟶ T)`, U distinguished,
  all three components of t in S, and `∀ i, ∃ a : U ⟶ D i`, all three
  components of a in S with `a ≫ s i = t`. PASS: one object with an arrow
  to each original object over T; no uniqueness or universal property added.
- Parallel pair: the second conjunct quantifies distinguished D,E, denominator
  maps `s : D ⟶ T`, `t : E ⟶ T`, then `a b : D ⟶ E`, all their
  components in S, and `a ≫ t = s`, `b ≫ t = s`. PASS: precisely arrows
  of the stated category with common source and target, in that order.
- Equalizing object and arrow: `∃ (U : Triangle C) (r : U ⟶ T) (q : U ⟶ D)`,
  U distinguished, all components of r,q in S, `q ≫ s = r`, followed by
  `q.homₖ ≫ a.homₖ = q.homₖ ≫ b.homₖ` for k=1,2,3.
  PASS: the arrow is to the common source and equalizes after precomposition,
  componentwise. Read comp_hom₁/₂/₃ and Triangle.hom_ext: these are exactly
  equality of the composite triangle morphisms, with no fourth condition.

Edge cases: `[Finite I]` permits I empty, when U=T and t=identity suffice by
MS1; no Nonempty or Fintype assumption. Zero and contractible triangles are
admitted, and identical parallel arrows are admitted (identity equalizes them).
The system of isomorphisms and the maximal system are covered. Universes u,v,w
are separately bound; w has no relation imposed to u,v. There is no scheme,
ring, characteristic, natural-number truncation, or geometric nonemptiness
hypothesis here: empty schemes and n=0 do not parameterize this node.

Independent searches, with different queries from the first reader:

- msearch leanfinder: "cofiltered category of distinguished triangles over a fixed
  triangle whose three components are denominators". Eight hits, including
  TStructure.exists_triangle, triangle_map_exists, Localization.distinguished_cocone_triangle,
  ObjectProperty.trW and Triangulated.Subcategory.W_iff. None states the two
  denominator-triangle conclusions for an arbitrary saturated system.
- msearch loogle: "CategoryTheory.Triangle, CategoryTheory.IsCofiltered".
  No hits; service reports unknown identifier CategoryTheory.Triangle, so this
  query supplies no mathematical evidence of absence.
- msearch leansearch: "finite families of distinguished triangles common predecessor
  and parallel morphism equalizer". Service unavailable (Internal Server Error);
  recorded without a mathematical verdict.
- Direct rg for cofiltered/equaliz/common refinements/common predecessors/denominator
  triangles in Mathlib Triangulated and Localization, upstream WeilConjectures and
  project lean/Sheaf. Localization hits concern equality of localized arrows,
  not simultaneous distinguished-triangle refinements. Project hits concern
  essential-constant pro-diagrams and denominator completion, not this statement.
  Broader triangle/refinement and triangle/cofiltered searches over the full project
  and upstream found only unrelated triangle comparison, localization and resolution
  modules; inspected their relevant occurrences. Searching the new theorem name and
  item id in upstream and dag/lean_names_upstream.json found no declaration.

H4/H5/H6/H8/H9 checks: there are no definitions, no hollow data and no new nodes
or dependency modules. All notions are recorded dependency declarations or Mathlib
Triangle/morphism primitives. The only theorem has exactly `by sorry` as its proof.
The declaration and module docstrings carry the source and blueprint id. The theorem
proof docstring follows all three DAG proof steps: saturation of comparison maps,
completion and rotated square repair, finite iteration including empty I, rotated
parallel equalization, then identification with the stated category conditions.
No correction or citer verdict review is needed because statement_change is absent.
The signature is verbatim equal to lean.statement, every variable and universe is
bound, the import is used, and every line is at most 100 characters.

Validation: fresh scompile of the sandbox file on the server succeeded, exit code 0,
compiled in 1.3 seconds with no warnings or errors. Initial relative-path invocation
from the read-only repository could not find the sandbox file; reran with its absolute
sandbox path. No tool workaround or project-library edit was used.

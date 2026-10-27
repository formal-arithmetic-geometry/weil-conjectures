## Worker report

Delivered module: `Sheaf.CategoryTheory.AdjunctionGeneratorDefectCriterion`.
Its sole declaration is
`CategoryTheory.Adjunction.generator_defect_criterion`, with proof `sorry`.
There are no definitions or helper axioms. The node changes only in `lean`.

Hypothesis-by-hypothesis correspondence:

- The two triangulated categories are `C : Type u₁`, `D : Type u₂`, with independent
  morphism universes `v₁`, `v₂`. `Preadditive`, `HasZeroObject`, `HasShift _ ℤ`,
  additivity of all shifts, `Pretriangulated`, and `CategoryTheory.IsTriangulated`
  are exactly the structure specified by `def-weil-triangulated-category`.
- The specified exact functors are `F : C ⥤ D` and `U : D ⥤ C`, with their
  `CommShift ℤ` structures and `IsTriangulated` instances. Mathlib derives their
  additivity from exactness, so it need not be separately assumed.
- The specified natural Hom bijections and their unit are `adj : F ⊣ U`,
  `adj.homEquiv`, and `adj.unit`. `[adj.CommShift ℤ]` makes the unit and counit
  commute with the specified comparisons, equivalently making the adjunction's
  Hom correspondence compatible with shifts. This is not an arbitrary unit map.
- The generating class is `G : ObjectProperty C`, with no finiteness or nonemptiness
  assumption. `T₀` is a replete full triangulated subcategory by the two recorded
  Mathlib classes. `hG : G ≤ T₀` and `hT₀` specify that it is the least such class.
  This is exactly the finite closure in the node: the objects having a finite
  construction from zero and generators form a replete triangulated class, since
  a shift or isomorphism adds one operation and an extension joins two finite
  constructions. Every replete triangulated class containing `G` contains all
  those constructions by induction. Conversely, minimality puts `T₀` inside that
  class. Thus these binders characterize the stated `T₀`; they impose no extra
  generation assumption and introduce no competing definition. In particular,
  Mathlib's retract-closed `triangEnvelopeIter` would be the wrong closure here.
- `hdefect` quantifies over every `G₁,G₂` belonging to `G`, every cone object `R`,
  and every pair `g,h` completing the actual `adj.unit.app G₂` to a distinguished
  triangle. Its conclusion `∀ n : ℤ, Subsingleton (G₁ ⟶ R⟦n⟧)` expresses vanishing
  of each Hom group; the preadditive structure supplies its zero morphism.
  No cone is assumed to belong to `T₀` and no unit is assumed invertible.

Clause-by-clause conclusions, in conjunction order:

1. For `P,Q` in `T₀` and every integer `n`, the specified function
   `f ↦ F.map f ≫ (F.commShiftIso n).hom.app Q` is bijective. Its codomain is
   precisely `F.obj P ⟶ (F.obj Q)⟦n⟧`.
2. Applying `adj.homEquiv` to this function after undoing that same comparison
   gives `f ≫ adj.unit.app (Q⟦n⟧)`. This equality is stated for all objects, as
   in the node's proof Step 1; it does not require generator membership.
3. `Nonempty (T₀.ι ⋙ F).FullyFaithful` states full faithfulness of the specified
   restriction, rather than existence of an unrelated fully faithful functor.
4. `(T₀.ι ⋙ F).essImage.IsTriangulated` gives the full triangulated replete image.
   Here `Functor.essImage` already means closure under arbitrary isomorphisms;
   its `IsClosedUnderIsomorphisms` instance is built into Mathlib. Its full
   subcategory is `ObjectProperty.FullSubcategory`.
5. The next clause takes arbitrary `A,B` isomorphic to `F.obj P,F.obj Q` through
   `eP,eQ`, an arbitrary arrow `a`, and every distinguished cone triangle
   `Triangle.mk a b c`. It produces a source arrow `f` with
   `F.map f ≫ eQ.hom = eP.hom ≫ a`, a source cone `R` in `T₀`, a distinguished
   source triangle, and an isomorphism from its image under `F.mapTriangle` to
   the specified target triangle. This also states lifting for every arrow:
   every `a` has a distinguished cone triangle by TR1. Taking identity `eP,eQ`
   recovers the strict image-object assertion. There is no uniqueness assertion
   for the cone isomorphism.
6. For any full replete triangulated `U₀` equal to the essential image, the last
   clause gives an equivalence `E : T₀.FullSubcategory ≌ U₀.FullSubcategory`.
   Its forward functor, after inclusion, is naturally isomorphic to the specified
   restriction by `e`. The existential shift structures make `E.functor` and
   `E.inverse` triangulated, the equivalence unit/counit shift compatible through
   `E.CommShift ℤ`, and `e` shift compatible through `NatTrans.CommShift e.hom ℤ`.
   In particular the quasi-inverse is exact for the inherited triangulations.

Dependency declarations used:

- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `CategoryTheory.IsTriangulated` in `.Triangulated`, and
  `CategoryTheory.Functor.IsTriangulated` in `.Functor` (as its `mathlib_match`
  explicitly specifies). Publicly available through the two public imports.
- `def-weil-triangulated-subcategory`:
  `CategoryTheory.ObjectProperty.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Subcategory`, together with its inherited
  pretriangulation, triangulation, shifts, and inclusion functor instances.
  Both dependencies are Mathlib leaves, with no `lean` record required.
- `Mathlib.CategoryTheory.Triangulated.Adjunction` supplies
  `CategoryTheory.Adjunction.CommShift`, `Functor.CommShift`, equivalence shifts,
  and their exactness interfaces. `Functor.essImage` and `FullyFaithful` are
  imported Mathlib notions, not local copies.
- The proof-only import `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`
  exposes `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`
  recorded by `lem-weil-pbc-five-lemma`. The other proof dependencies are already
  exposed by the public imports: `Triangle.coyoneda_exact₂`,
  `Triangle.yoneda_exact₂`, `Pretriangulated.isIso₃_of_isIso₁₂`, and
  `Functor.asEquivalence`. There are no missing dependency modules.

Edge cases checked before writing:

- Empty `G`: no generator or inhabited-class binder is present. The least
  replete triangulated class consists of zero objects; all its Hom sets and
  their images are singleton. All conclusions remain valid.
- Only zero generators: the defect condition is automatic because Hom out of
  zero is zero, and the same closure and conclusions result.
- `n = 0`, negative `n`, and both zero source/target objects are all included.
  The integer shift is not silently identified with a strict equality.
- A proper finite triangulated closure need not contain any nonzero retract of
  one of its objects, and no such hypothesis or conclusion was inserted.
- Categories, Hom sets and the class of generators are not required to be small
  in one common universe. `u₁,u₂,v₁,v₂` are explicitly independent.
- If `U₀` is only replete-isomorphic to strict images, `essImage` and the arbitrary
  isomorphisms in the cone clause retain that case.

Searches for an existing statement (2026-10-22):

- `msearch.py ... leanfinder`: "An exact left adjoint is fully faithful on the
  finite triangulated closure of generators when every shifted unit cone is
  right orthogonal to every generator". Eight hits included
  `Adjunction.isTriangulated_leftAdjoint`, triangulated adjunction constructors,
  and `ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated`.
  None states this criterion and all its conclusions.
- `msearch.py ... loogle`: `"IsTriangulated", "Adjunction"`. Eleven hits on
  `Adjunction.IsTriangulated` and its constructors, identity and composition;
  none states a finite-generator unit-defect criterion.
- `msearch.py ... grep`, restricted to `CategoryTheory/Triangulated`:
  `triangulatedClosure|triangulatedClosure|generator.*[Ff]aithful|[Ff]aithful.*generator`.
  No hits.
- `rg` of project `lean/WeilConjectures` and `lean/Sheaf` for generator/full-faithful
  patterns and candidate defect names found
  `WeilConjectures.CategoryTheory.Triangulated.FullyFaithfulGenerator`.
  Read the complete file: `Functor.homBijective_of_generator` and
  `fullyFaithfulOfGenerator` treat a single generator for the entire source
  category, assuming bijections rather than the unit-cone condition; they do
  not state this node. The remaining hits were unrelated scalar/sheaf material.
- Exact node-id `grep -rn` under `lean/WeilConjectures` returned no hits.
  Exact `generator_defect_criterion` search in Mathlib and both project roots
  also returned no hits before writing.
- Read Mathlib `Triangulated/Generators.lean` to check the tempting closure API:
  `triangEnvelopeIter` explicitly uses `retractClosure`, so it was not substituted
  for the finite closure. Read the dependency declarations and their docstrings,
  and the local blueprint paragraph (3), Stacks `lemma-representable-homological`,
  `lemma-third-isomorphism-triangle` and `lemma-exact-equivalence`.

No statement correction or disputed mathematical assertion is needed. No new
notion has been defined: the closure is characterized using the recorded
subcategory notion, and all maps, shifts and triangles are Mathlib constructions.

Validation: `scompile.py Q27 lem-sfb-adjunction-generator-defect-criterion` on the
complete module passed both its sandbox compile (3.6 s) and library-module compile
(2.4 s), with no errors or warnings. All variables and universes are explicit;
there is one named theorem and one `sorry`. No proof was supplied in stage 2.

## Second reading by Q27

This is a separate rereading by the same dispatched worker; the dispatcher forbids
starting other agents. The maintainer's delivery review will be independent.

Reread the node and final signature together, checking the hypotheses and all six
conjuncts above. The closure's minimality is restricted exactly to replete
triangulated classes, not to thick or localizing ones; every finite construction
is allowed, including the zero construction with no generators. The vanishing
hypothesis quantifies over all distinguished triangles on the actual unit. The
shifted map uses the given `F` and its own comparison; the adjunction formula
undoes that comparison before taking the adjunct. The cone conclusion includes
arbitrary objects isomorphic to images, and places its source cone back in `T₀`.
The final equivalence is tied to the specified restriction by a shift-compatible
natural isomorphism and asserts exactness of both directions. The replete-image
claim follows the literal Mathlib definition of essential image. There is no
remaining missing clause or extra mathematical hypothesis.

The initial compile found a namespace-resolution error: the unqualified
`IsTriangulated C` inside a declaration named `Adjunction.*` resolved to the
adjunction class. Qualified the two ambient category instances as
`CategoryTheory.IsTriangulated`. Also spelled out the equivalence's shift
compatibility and both functors' exactness as conjuncts so no local instance proof
is hidden in the statement. The resulting full module compiled cleanly.

## Worker report

Item: lem-pur-coefficient-action-adjoint-generation. The delivery adds
`Sheaf.CategoryTheory.CoefficientActionAdjointGeneration`, with the single postponed theorem
`CategoryTheory.coefficientActionAdjointGeneration`. The helpers
`CategoryTheory.coefficientActionAdjointMate` and
`CategoryTheory.coefficientActionAdjointIsoLocus` are actual definitions belonging to this
node's specified construction, with no postponed data or auxiliary postponed theorems.
The natural-language node and its dependencies are unchanged.

Sources read: the item's full statement and all five proof steps; Zheng, Construction 2.26,
printed p. 15 (PDF text extracted from pages 15–17), specifying inverse projection comparison
followed by the counit before transposition; the full statement of blueprint
`sec-six-functors-basics/sk-lem-sf-determination/det-sf-determination-localizing.md`; and
Stacks `more-algebra.tex`, `remark-P-resolution`, Tag 09PB, including its final property
criterion. This is the node's abstract argument; no smoothness hypothesis is introduced.

Hypotheses, in statement order:

- The commutative ring C is `R : Type u` with `[CommRing R]`. Its ordinary unbounded derived
  module category is `DerivedCategory (ModuleCat.{max u v} R)` under
  `[HasDerivedCategory.{w} (ModuleCat.{max u v} R)]`. The size parameter w selects morphism
  size; the additional v allows modules in any universe at least that of R. The ring in
  degree zero is `(DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
  (ModuleCat.of R (ULift.{v} R))`, exactly the free rank-one generator used by the recorded
  `derivedModuleFreeGeneration` interface. ULift supplies the same ring module in the
  chosen module universe; it imposes no finiteness or nonzero assumption.
- The locally small triangulated categories are `A : Type uA`, `B : Type uB` with separate
  `Category.{vA}`, `Category.{vB}`, zero objects, preadditivity, integer shifts, additive
  shift functors, `Pretriangulated` and `IsTriangulated`. Their set-indexed coproducts are
  `HasCoproducts.{max u v}`. These are the set sizes of the coefficient module category,
  exactly as in the generation dependency; no equality of hom universes is imposed.
- The two bifunctors are curried as `TA : A ⥤ D ⥤ A` and `TB : B ⥤ D ⥤ B`, where D is
  the displayed derived module category. Thus `(TA.obj K).obj V` denotes T_A(V,K).
  `∀ K, (TA.obj K).CommShift ℤ` and its TB counterpart give coherent coefficient shifts;
  `∀ K, (TA.obj K).IsTriangulated` and its TB counterpart give coefficient exactness.
  `NatTrans.CommShift (TA.map f) ℤ` and its TB counterpart express naturality of these
  specified coefficient-shift comparisons in the category variable. They are the
  bifunctorial comparisons, not independently chosen comparisons at individual objects.
- `uA : TA.flip.obj R[0] ≅ 𝟭 A` and `uB : TB.flip.obj R[0] ≅ 𝟭 B` are the natural unit
  identifications. `flip` is Mathlib's existing bifunctor flip, not a new notion.
- `F`, `G`, their `CommShift ℤ` and `IsTriangulated` structures, and `adj : F ⊣ G` give
  the exact adjunction. `[adj.CommShift ℤ]` is Mathlib's precise compatibility of the
  specified F/G shifts with the adjunction, including both unit and counit. Its counit
  equation is the node's displayed equation, using the composite `G ⋙ F` shift.
- `P : F ⋙ TB ≅ TA ⋙ (Functor.whiskeringRight D A B).obj F` is the natural projection
  isomorphism in both V and K, oriented T_B(V,FK) to F(T_A(V,K)). `hshift` writes its
  coefficient-shift square explicitly, using the inherited composite shift on TA(K) ⋙ F.
  `hunit` is P at the ring followed by `F.map (uA.hom.app K)` equal to `uB.hom.app (F.obj K)`.
- A_M is literally `TA.obj (G.obj M)` and B_M is literally `TB.obj M ⋙ G`. The former's
  exactness is supplied by the action hypothesis; the latter's exactness is explicitly
  recorded in `[∀ M, (TB.obj M ⋙ G).IsTriangulated]`, as the node assumes. Its shift is
  Mathlib's canonical composite of the supplied TB and G shifts, not another shift datum.
  The two `PreservesColimitsOfShape (Discrete I)` families state preservation of all
  set-indexed coproducts for both coefficient functors, including the empty family.

Construction and conclusions, clause by clause:

- The helper `coefficientActionAdjointMate TA TB adj P V M` is defined by
  `adj.homEquiv _ _ ((P.inv.app (G.obj M)).app V ≫ (TB.map (adj.counit.app M)).app V)`.
  Thus it is exactly the specified transpose, with the specified adjunction and P, and
  neither an arbitrary map nor a map chosen by a nonemptiness assertion.
- The first conjunct is naturality in V: A_M(h) followed by alpha(W,M) equals alpha(V,M)
  followed by B_M(h). The second conjunct is naturality in M: the action on G(h) followed
  by alpha(V,N) equals alpha(V,M) followed by G of the B-action on h. Together these are
  naturality in both variables of the given bifunctors.
- The third conjunct is alpha at R[0] followed by G of uB equal to uA at GM, matching
  `G(u_B) ∘ alpha = u_A` with Lean's left-to-right categorical composition.
- The fourth conjunct is alpha(V[n],M) followed by the composite B_M shift comparison
  equal to the A_M shift comparison followed by alpha(V,M)[n]. It quantifies over every
  integer n, including negative and zero shifts.
- `coefficientActionAdjointIsoLocus` is the `ObjectProperty D` given by invertibility of
  this explicit alpha. Its full subcategory is the L_M of the node. No new independent
  notion is introduced: this helper names the specific locus the node already defines.
- For every M, the final conjunct first puts R[0] in L_M, then gives closure under every
  object isomorphism, every integer shift, the third vertex of every distinguished
  triangle whose first two vertices belong, and every retract `Retract V W` with W in
  the locus. Shift and cone closure also give the rotated forms of two-out-of-three.
- The coproduct clause quantifies over arbitrary families and any colimit cocone
  `Cofan.mk S ι`, not just a chosen coproduct object, so it is the full replete coproduct
  closure requested by the node. It includes empty and infinite index types.
- The final two clauses are `coefficientActionAdjointIsoLocus ... M = ⊤` and
  `∀ V, IsIso (coefficientActionAdjointMate ... V M)`. They state both L_M = D(C-Mod)
  and invertibility of every specified component. No uniqueness/determination theorem
  for natural transformations from their value at the ring is asserted.

Dependency declarations used and read in full with docstrings:

- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory` and `HasDerivedCategory`, together with the derived zero/shift/
  triangulated instances and the localization functor. `singleFunctor` is the existing
  degree-zero embedding used in the generation dependency.
- def-weil-triangulated-category: its mathlib_match is used directly:
  Mathlib.CategoryTheory.Triangulated.Pretriangulated, `CategoryTheory.Pretriangulated`;
  Mathlib.CategoryTheory.Triangulated.Triangulated, `CategoryTheory.IsTriangulated`;
  Mathlib.CategoryTheory.Triangulated.Functor, `CategoryTheory.Functor.IsTriangulated`.
  The node has no lean record and needs no repair.
- Proof dependency def-weil-pbc-adjunction-mate: Mathlib.CategoryTheory.Adjunction.Mates,
  `CategoryTheory.mateEquiv`, read with its complete TwoSquare signature and formula.
  It is exposed by Shift.Adjunction; the concrete component is constructed directly
  with the adjunction hom equivalence, as the item itself specifies.
- Proof dependency det-sf-determination-localizing:
  Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus,
  `CategoryTheory.NatTrans.isoLocus_localizing`, imported privately for the proof plan.
- Proof dependency lem-pc-derived-module-free-generation:
  WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration,
  `CategoryTheory.derivedModuleFreeGeneration`, imported privately for the proof plan.
- Mathlib.CategoryTheory.Shift.Adjunction, `CategoryTheory.Adjunction.CommShift`, and
  Shift.CommShift, `CategoryTheory.Functor.CommShift` and composite instance, were read
  to check that the displayed shift orientations and counit compatibility agree.
- Mathlib.CategoryTheory.Whiskering, `CategoryTheory.Functor.whiskeringRight`, and
  Functor.Category, `CategoryTheory.Functor.flip`, supply the existing curried interfaces.

Edge cases checked before and after writing: the zero ring is permitted; no Nontrivial or
faithfulness hypothesis appears. Zero categories and zero functors are permitted when the
stated units/adjunction exist. Empty coproducts are covered by arbitrary I and arbitrary
colimit cocones; negative, zero and positive shifts use ℤ. Coefficients are fully unbounded;
there is no boundedness, perfectness, dualizability, Tor-amplitude or compactness restriction
on V or M. Independent object and hom universes for A and B are preserved. The module
universe max u v matches the existing free-generation theorem, including its ULift generator.
The mate uses P inverse, so its orientation agrees with Zheng Construction 2.26. No node
fault or STATEMENT-DISPUTED issue was found.

Searches actually run:

- msearch.py leanfinder: "An exact coproduct preserving coefficient action adjunction mate
  is invertible by generation of the unbounded derived module category by its unit ring".
  Eight hits, including Gabriel–Popescu tensor adjunctions, exact-functor Ext maps and
  K-projective hom equivalences; none states this specified coefficient-action mate theorem.
- msearch.py loogle: `"Adjunction", "CommShift"`. Twelve hits give the existing adjunction
  shift compatibility and left/right adjoint shift constructions. The exact existing
  `Adjunction.CommShift` class is used; none gives the generation result of the item.
- msearch.py grep: `coefficientActionAdjoint|isoLocus|mateEquiv` in CategoryTheory.
  Twenty hits include the existing ordinary mateEquiv API and closed-monoidal uses;
  no match for this generation theorem. Existing mate machinery is retained.
- rg in both lean/WeilConjectures and lean/Sheaf for coefficient-action terms and for
  `coefficientActionAdjoint|coefficient_action_adjoint|adjoint_generation`, and the latter
  in dag/lean_names_upstream.json: no declaration for this item; broad coefficient-action
  hits are specialized geometric or algebraic statements. grep for the node id in
  lean/WeilConjectures returned no occurrence. Read the existing localizing iso-locus
  and derived module free-generation modules rather than restating their theorems.

Validation: scompile.py compiled both the sandbox probe and the actual module cleanly
(5.0 s and 4.1 s respectively); no errors or non-sorry warnings. Auto-bound implicits are
explicitly disabled. All definitions contain actual data, every theorem proof is solely
`sorry`, and all declarations carry the owning node's blueprint/source docstrings. The
node's lean.statement is extracted verbatim from the theorem keyword up to `:=`.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

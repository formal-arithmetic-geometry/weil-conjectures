## Worker report

Item: lem-sfb-dg-quasi-isomorphism-localization. The module
`Sheaf.CategoryTheory.DgQuasiIsomorphismLocalization` defines the cohomology-isomorphism
class `CategoryTheory.DgAlgebra.homotopyQuasiIsomorphisms` on the existing dg homotopy
quotient and states `CategoryTheory.DgAlgebra.quasi_isomorphism_localization`.
The sole theorem proof is `sorry`. The definition is the actual predicate that each
induced cohomology map is an isomorphism; it contains no postponed data or proof.

Hypothesis and clause correspondence:

- The universe convention is rendered by explicit `universe u uE vE`. Component
  modules and the dg algebra use universe u; the homotopy quotient has object
  universe u+1 and morphism universe u, whereas its localization has both universes
  u+1. The strict universal property is stated for arbitrary target object and
  morphism universes uE and vE. No equality of these universes is imposed.
- The sole mathematical input is `(A : Algebra.{u})`. The recorded
  `DgAlgebra.Algebra` is `Mon` in integer cochain complexes of integer modules,
  hence associative, unital, and not assumed commutative. The complex identity
  gives d squared zero and the chain multiplication gives the signed Leibniz rule.
- `RightModule A` is the already recorded right module object (using the reversed
  monoidal category), with the specified right dg Leibniz rule. There are no
  boundedness, nonzero, flatness, small-index, or commutativity hypotheses.
- `HomotopyCategory A` is the actual quotient by action-preserving homotopies.
  In degree zero, cocycles in the graded A-linear Hom complex are exactly chain
  maps; boundaries are d h + h d with h of degree minus one. Thus the recorded
  quotient realizes exactly the H^0 Hom morphisms in the node, including its
  unsigned right A-linearity convention; no ordinary-complex homotopy category
  is substituted for the dg-module category.
- The existential `_s : HomotopyStructure A` fixes the source's unchanged-action
  shifts and signed cone triangles using its `ShiftComparison`, `ConeComparison`,
  and `distinguished_iff` fields. `_t : IsTriangulated (HomotopyCategory A)`
  asserts the octahedral axiom as a conclusion. None of these is a hypothesis.
- Cohomology is `HomotopyStructure.cohomology n`. Its `cohomology_factors` field
  fixes it to the homology functor of the actual underlying integer complex,
  namely kernel modulo image in each integer degree.
- The target is the existing `Derived A`, the actual Gabriel--Zisman localization
  of right dg modules at quasi-isomorphisms. The existential `Qh` has source the
  recorded homotopy quotient. `homotopyQuotient A ⋙ Qh = Q A` characterizes it
  canonically on both objects and morphisms; this is not an unconstrained map.
  The quotient functor is identity on the underlying dg objects and full, so
  such a factorization is unique (Mathlib `Quotient.lift_unique'`).
- The existential target preadditive, zero, shift, shift-additive, pretriangulated,
  and triangulated structures are the assertion that D(A,d) carries its
  localization triangulation. They do not assume `DerivedStructure A`, which
  would already assume triangulatedness and additionally demand coproducts.
- MS1--MS6 are exactly
  `(homotopyQuasiIsomorphisms A).IsSaturatedTriangulatedMultiplicativeSystem`
  from the dependency's recorded declaration. In particular MS4 is the stated
  saturation axiom, not merely two-out-of-three. The next three conjuncts
  separately display both `HasLeftCalculusOfFractions` and
  `HasRightCalculusOfFractions` and `HasTwoOutOfThreeProperty`.
- `Qh.IsStrictLocalizationAt` is the dependency's exact universal property:
  inversion, unique strict factorizations of functors, and a bijection on
  natural transformations. The target universes are explicitly uE and vE.
- `_aQ : Qh.Additive`, `_sQ : Qh.CommShift ℤ`, and `Qh.IsTriangulated`
  render exactness, including coherent integer-shift comparisons.
  `∀ T, T ∈ distTriang (Derived A) ↔ T ∈ Qh.essImageDistTriang` fixes the
  distinguished triangles to precisely those isomorphic to images of the
  specified distinguished cone triangles in K(A,d).
- The kernel clause is the exact equivalence
  `IsZero (Qh.obj M) ↔ ∀ n : ℤ, IsZero ((HomotopyStructure.cohomology n).obj M)`.
  `IsZero` is used on actual objects of additive categories, not on bare types.
- Opening Mathlib's `CategoryTheory.Pretriangulated.Opposite` scope chooses the
  specified opposite structures, not new or arbitrary structures. Its shift n
  is the opposite of shift -n. Its triangle is the unsigned reversal with the
  shifted original third arrow. Both opposite categories' `IsTriangulated`
  assertions are included, as are the opposite class's full MS1--MS6 assertion,
  `Qh.op.IsStrictLocalizationAt`, and opposite exactness `Qh.op.IsTriangulated`.
  Coherent opposite shift comparison comes from the scoped Mathlib instance.

Dependency declarations used, with full source signatures and docstrings read:

- `def-weil-size-convention`: metatheoretic convention; its lean record expressly
  has no module or declaration. Rendered by the universe parameters above.
- `def-pur-saturated-triangulated-localization`:
  `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`,
  declarations `CategoryTheory.MorphismProperty.IsMultiplicativeSystem`,
  `IsSaturatedMultiplicativeSystem`, `IsSaturatedTriangulatedMultiplicativeSystem`,
  and `CategoryTheory.Functor.IsStrictLocalizationAt`. The source was read in full.
- Added already-landed statement dependencies `def-sfb-dg-derived-category` and
  `def-sfb-dg-homotopy-structure`: modules
  `Sheaf.CategoryTheory.DgAlgebraDerivedCategory` and
  `Sheaf.CategoryTheory.DgAlgebraHomotopyStructure`; declarations `Algebra`,
  `RightModule`, `underlying`, `Derived`, `Q`, `ShiftComparison`, `ConeComparison`,
  `homotopyRel`, `HomotopyCategory`, `homotopyQuotient`, and `HomotopyStructure`,
  all in `CategoryTheory.DgAlgebra`. Both modules were read completely. These
  recorded definitions supply the precise dg notions already introduced inline
  in the unchanged statement. No dependency node was modified.
- Proof dependency `lem-sfb-dg-homotopy-acyclic-localization` is imported privately
  from `Sheaf.CategoryTheory.DgHomotopyAcyclicLocalization`; read
  `CategoryTheory.DgAlgebra.homotopy_acyclic_localization` and its property definition.
- The remaining proof dependencies are recorded Mathlib matches, all available
  through the imports: the acyclic cone `trW` fraction and triangulation instances
  in `Mathlib.CategoryTheory.Triangulated.Subcategory`; `Localization.lift`,
  `fac`, `liftNatTrans`, `natTrans_ext` in `Localization.Predicate`;
  `Triangulated.Localization.pretriangulated`, `isTriangulated` and
  `Functor.distTriang_iff` in `Localization.Triangulated`; opposite triangulation
  and exactness instances in `Triangulated.Opposite.Triangulated` and `.Functor`.
  `Localization.Opposite` is imported privately for the final strict-property proof.

Edge cases checked before writing:

- The zero dg algebra and zero modules are included; no nontriviality binder.
  For an acyclic or contractible module, the kernel equivalence says precisely
  that its localized object is zero. The identity map and the map 0 to an acyclic
  object satisfy the cohomology-isomorphism predicate.
- Arbitrary unbounded integer complexes and genuinely nonzero-degree dg algebras
  are included. Graded commutativity is never imposed; the monoidal-opposite
  module object is the right module convention of Stacks.
- Degree zero and negative degrees are included in every cohomology and shift
  quantifier. Changing a differential by the shift sign does not change its
  kernels or images. Opposite shifts reverse n, including n=0 and negative n.
- The target universes uE and vE can coincide, differ, or exceed u+1. The homotopy
  morphism universe is u, unlike the localization's u+1; the explicit instantiation
  of `IsStrictLocalizationAt` preserves that difference.
- The source specifies cone connecting map -p in the already recorded Mathlib
  convention. Opposite reversal inserts no additional minus sign. MS6 opposite
  is the rotated original MS6, with both rotation signs canceled.

Searches for an existing statement (all msearch results also in searches.jsonl):

1. msearch leanfinder, query "Quasi-isomorphisms of differential graded modules
   form a saturated triangulated multiplicative system with both calculi of
   fractions": 8 hits, principally ordinary DerivedCategory left/right fraction
   instances, ordinary HomologicalComplex two-out-of-three, and ordinary-complex
   localization. None is the theorem for arbitrary dg-algebra module actions.
2. msearch loogle, query `"quasiIso", "HasRightCalculusOfFractions"`: one hit,
   `DerivedCategory.instHasRightCalculusOfFractionsHomotopyCategoryIntUpQuasiIso`,
   for ordinary complexes in an abelian category, not the dg module quotient.
3. msearch grep, query `IsSaturatedTriangulatedMultiplicativeSystem|DGModule|DgAlgebra`
   under Mathlib Algebra/Homology: zero hits.
4. msearch leansearch, query "Quasi isomorphisms of differential graded modules
   admit left and right calculi of fractions and the derived localization has
   acyclic kernel": 8 ordinary-derived-category results; none exact.
5. rg searches over lean/WeilConjectures, lean/Sheaf and
   dag/lean_names_upstream.json for `DgAlgebra|dgQuasi|dgHomotopy` and the item id:
   found the recorded dg definitions and acyclic-cone theorem but no localization
   theorem or opposite-compatible saturation theorem. The new declaration names
   have no existing source occurrence. Mathlib's generic localization, quotient,
   cone-system and opposite APIs were opened and reused rather than duplicated.

Sources opened: literature/stacks-project/dga.tex at the triangulation proposition,
acyclic lemma, and definition of the unbounded derived category (Tags 09KJ, 09KW,
09KX). Opposite conventions were checked in the named Mathlib source. The module
contains the complete nine-step natural-language proof from the node, with the
necessary identification of the two existing localization models explained.

Validation: scompile.py compiled both the sandbox form and the delivered module
form cleanly, with no errors or non-sorry warnings. An initial explicit universe
instantiation incorrectly raised the source morphism universe; corrected to u
while retaining u+1 for the target. No statement correction, new definition node,
dependency repair, or STATEMENT-DISPUTED fault is needed.

## Second reading by Q07

This is a fresh worker rereading of the finished node and module; no independent
agent was started, as the dispatcher explicitly prohibits starting other agents.
The maintainer's independent delivery review remains separate.

Checked each clause against the unchanged statement: arbitrary associative dg
algebra and right modules; H^0-Hom homotopy quotient; signed unchanged-action
shifts and cones; genuine cohomology-isomorphism predicate; full MS1--MS6 rather
than only two-out-of-three; both fraction calculi; exact strict localization;
localized cone triangles and exact acyclic kernel; both specified unsigned
opposite triangulations, opposite MS1--MS6 and strict opposite localization.
All have explicit counterparts listed above. In particular, triangulations are
existential conclusions, so the result does not silently assume their existence.
The source functor is fixed by its composition with the quotient, and D(A,d)
is the existing `Derived A`, rather than a second definition or an arbitrary
category. Target universes remain independent. No added or missing mathematical
hypothesis or conclusion was found. Only the source morphism universe typo was
changed during compilation. Every theorem remains sorry-only.

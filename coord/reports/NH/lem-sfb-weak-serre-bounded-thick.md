## Worker report

The module `Sheaf.CategoryTheory.WeakSerreBoundedThick` states
`CategoryTheory.weakSerre_bounded_homology_thick`, with its whole proof `sorry`.
It adds no definitions, auxiliary theorems, or nodes. The original node is unchanged
except for `lean`. No statement correction or STATEMENT-DISPUTED issue is needed.

Source read: `literature/stacks-project/derived.tex`, lines 5909–5965, especially
`lemma-cohomology-in-serre-subcategory` (Tag 06UQ), and `homology.tex`,
`lemma-characterize-weak-serre-subcategory` (Tag 0754). The kernel argument is the
explicit universal-property expansion in steps 3–4 of this node.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Abelian category A | `{A : Type u} [Category.{v} A] [Abelian A]` |
| Ordinary unbounded derived category, cohomology H^n | `[HasDerivedCategory.{w} A]`, `DerivedCategory A`, `DerivedCategory.homologyFunctor A n` |
| Strictly full subcategory B | `P : ObjectProperty A` specifies a full subcategory; `[P.IsClosedUnderIsomorphisms]` expresses strict fullness |
| Contains zero | `[P.ContainsZero]` (with isomorphism closure, contains every zero object) |
| Kernels of morphisms between objects in B | `[P.IsClosedUnderKernels]` |
| Cokernels of morphisms between objects in B | `[P.IsClosedUnderCokernels]` |
| Extension closure for short exact sequences with endpoints in B | `[P.IsClosedUnderExtensions]` |
| Every H^n(K) belongs to B | `DerivedCategory.homologyProperty P K`, whose actual upstream definition is `∀ n : ℤ, P ((homologyFunctor A n).obj K)` |
| Cohomology vanishes outside a finite integer interval | `DerivedCategory.TStructure.t.bounded K`; `isGE_iff` and `isLE_iff` identify its two existential bounds with vanishing below/above them |
| The specified full subcategory | `DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded` |
| Contains zero; closed under all integer shifts and distinguished triangles | The first conjunct, the property's `.IsTriangulated`, includes zero, shifts by all integers and triangle middle-vertex closure; its other two triangle closure instances follow by rotation |
| Closed under isomorphisms | The second conjunct `.IsStableUnderRetracts` supplies `.IsClosedUnderIsomorphisms` by Mathlib's existing instance, so triangle closure is actual membership, not membership only up to isomorphism |
| Closed under all ambient retracts (hence direct summands) | The second conjunct `.IsStableUnderRetracts` ranges over arbitrary ambient `Retract` data, with no splitting or completeness hypothesis |
| L → K → L with ri = 1 and K in the class | `∀ (L K : DerivedCategory A) (i : L ⟶ K) (r : K ⟶ L), i ≫ r = 𝟙 L → (...) K → ...`; Lean composition is left-to-right |
| H^n(i) identifies H^n(L) with ker(1 − H^n(i)H^n(r)) | For every integer `n`, an isomorphism `e : H^n(L) ≅ kernel (𝟙 (H^n(K)) - H^n(r) ≫ H^n(i))` with `e.hom ≫ kernel.ι (...) = H^n(i)`; this is the stated inclusion, not just existence of an unrelated object isomorphism |
| Any cohomological interval bound for K also bounds L | For every `a b : ℤ`, vanishing of H^n(K) whenever `n < a ∨ b < n` implies the same vanishing of H^n(L) for exactly those `a,b` |

Universes `u`, `v`, and `w` are explicitly declared and independent. All variables are
explicitly bound. `HasDerivedCategory` selects the localization's morphism size;
it is the dependency's size convention, not an additional mathematical hypothesis.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; includes the preadditive structure, kernels,
  cokernels and zero objects needed here.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and
  `DerivedCategory.homologyFunctor`, `.homologyFunctorFactors` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `pur9-def-thick`: the recorded combination
  `CategoryTheory.ObjectProperty.IsTriangulated`,
  `Mathlib.CategoryTheory.Triangulated.Subcategory`, and
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `Mathlib.CategoryTheory.ObjectProperty.Retract`.
- Proof dependency `lem-sbc-cohomology-in-weak-serre-subcategory`:
  `CategoryTheory.cohomology_in_weak_serre_subcategory`,
  `Sheaf.Paper.CohomologyInWeakSerreSubcategory` (imported without `public`).
  Its actual declaration gives exactly the weak-Serre hypotheses and the bounded
  intersection's triangulated structure. It is already proved in the read clone.
- `DerivedCategory.homologyProperty` in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`
  is the existing cohomology condition; no private replacement is introduced.
- Proof dependency `def-weil-pbc-bounded-derived-subcategories`:
  `DerivedCategory.Bounded`, `DerivedCategory.TStructure.t.bounded`,
  `DerivedCategory.isGE_iff`, `.isLE_iff`,
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure` and
  `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`.
  The upstream `DerivedCategory.exists_homologyConcentratedIn_iff_bounded` was
  also read and confirms finite interval equivalence.
- Proof dependency `def-weil-triangulated-subcategory` uses the same Mathlib
  `ObjectProperty.IsTriangulated`. Proof dependency
  `def-weil-preadditive-category` is `CategoryTheory.Preadditive` in
  `Mathlib.CategoryTheory.Preadditive.Basic`, inherited from `[Abelian A]`.
  These Mathlib proof dependencies are already reached by the public imports.

Edge cases checked before writing and again against the final signature:

- Zero K or zero L: every cohomology object is zero, and the split relation
  forces H^n(L) to be zero if H^n(K) is zero.
- Identity retract: q = 0 and H^n(i) identifies H^n(K) with the kernel of zero.
- A genuine proper retract: q = 1 − IR and its kernel is precisely the image
  of the inclusion. The compatibility equation fixes that specific inclusion.
- Empty cohomological support is bounded by [0,0]. The statement also allows
  `a > b` in the sharper bound clause, in which case all cohomology vanishes.
- Singleton interval `a = b`, negative endpoints and arbitrary integer shifts
  are all admitted. No ordered-endpoint or nonempty-support assumption appears.
- The class consisting only of zero objects, and the entire abelian category,
  meet the hypotheses and give the expected thick subcategories.
- No Serre-class assumption of closure under every subobject or quotient is
  imposed: only kernels/cokernels of maps with both endpoints in P are required.
- No ambient idempotent-completeness assumption and no equality of universes
  are added.

Searches (2026-10-21):

- `msearch.py ... leanfinder`: "Bounded derived objects whose cohomology lies in
  a weak Serre class form a thick subcategory; retract cohomology is the kernel
  of one minus the split idempotent". Eight results on the derived t-structure,
  `DerivedCategory.IsGE`, `.IsLE`, and bounded representatives; none is this theorem.
- `msearch.py ... loogle`: `DerivedCategory.homologyFunctor, CategoryTheory.Retract`.
  No hits.
- `msearch.py ... grep`:
  `(homologyProperty|weakSerre|WeakSerre).*(Retract|Thick)|(Retract|Thick).*(homologyProperty|weakSerre|WeakSerre)`.
  No Mathlib hits.
- `msearch.py ... leansearch`: "Bounded cohomology in a weak Serre subcategory
  is closed under ambient retracts and forms a thick derived subcategory".
  Eight results including stronger `IsSerreClass` APIs, generic retract closure,
  short-complex quasi-isomorphisms, and bounded representatives; no exact match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for weak-Serre names and
  bounded/thick combinations found the existing upstream `homologyProperty`,
  the triangulated weak-Serre theorem and a **private** `bounded_homology_thick`
  in `Sheaf.Paper.CoefficientHeartTriangulated`. The private lemma lacks the
  kernel-identification and interval clauses and is not a reusable public
  declaration of this node. Its proof was read as a further interface check.
- `grep -rn 'lem-sfb-weak-serre-bounded-thick' lean/WeilConjectures`: no hits.
- `rg` for `weakSerre_bounded_homology_thick` in `dag/lean_names_upstream.json`,
  Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no name collision.

Validation: `scompile.py NH lem-sfb-weak-serre-bounded-thick` checked the complete
module both as a sandbox module (9.6 seconds) and as the actual library module
(4.9 seconds), with no errors or unexpected warnings. The node signature was
copied verbatim from the declaration. Every Lean line has at most 100 characters.

## Second reading by NH

I reopened the node and final file for a separate clause-by-clause pass, represented
in the table above. This is a self-check by the dispatched worker; the independent
review is the maintainer's, as required by this dispatch (no other agents started).
The weak-Serre assumptions match exactly, with no stronger arbitrary-subobject
closure. The bounded predicate is the existing standard derived one, and the
explicit interval clause quantifies over all endpoints. Checking composition
orientation is essential: `i ≫ r = 𝟙 L` renders ri = 1, whereas the endomorphism
of H^n(K) is `map r ≫ map i`, which renders IR. The kernel isomorphism is required
to recover `map i` after its kernel inclusion. Both thickness conjuncts use the
same object property as the retract premise. No mismatch or node fault was found;
no correction or added dependency is necessary.

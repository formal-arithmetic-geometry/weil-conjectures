## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.RingDerivedCompactPerfect` states
`DerivedCategory.isPerfectRingComplex_of_isCompactObject` with a single `sorry`.
It introduces no definitions and changes only the item's `lean` field. There are
no new nodes, dependency repairs, statement corrections, or disputed statements.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 07LT,
`proposition-perfect-is-compact`, implication (2) to (1), including all of its
converse proof, and Tag 0656, `definition-perfect`. The finite-projective
retraction formulation is the elementary finite-generator and projective-lifting
argument (Algebra Tag 00NX); Mathlib's `Module.Projective.iff_split_of_projective`
and `Module.Projective.of_split` confirm the orientation of the maps.

The node and Lean match as follows:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| The chosen universes | Explicit `universe u w`; module universe `u` and independent localization Hom universe `w`. |
| A commutative ring A | `{A : Type u} [CommRing A]`. |
| The unbounded derived category of A-modules | `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` and `DerivedCategory (ModuleCat.{u} A)`. No boundedness assumption on E. |
| Small coproducts represented by termwise direct sums | The imported `DerivedCategory.Coproducts` supplies the coproduct instance and preservation by Q. Module colimits and K-injective resolutions are supplied by the existing imports. No additional coproduct hypothesis is imposed. |
| E is compact, with the canonical Hom direct-sum map bijective for every small family | `(hE : IsCompactObject.{u} E)`, using the recorded definition, which quantifies over `I : Type u` and precisely that bijective map. |
| E is perfect | First conjunct `IsPerfectRingComplex E`, using the recorded dependency definition verbatim. |
| A bounded cochain model with finite projective terms and an isomorphism | Unfolding that first conjunct gives P, integer lower and upper strict support bounds, `Module.Projective A (P.X r)` and `Module.Finite A (P.X r)` for every r, and `Nonempty (E ≅ Q.obj P)`. |
| Equivalent model with terms direct summands of finite free modules | The second conjunct gives a bounded F and `∀ r : ℤ, ∃ (n : ℕ) (i : F.X r →ₗ[A] (Fin n → A)) (p : (Fin n → A) →ₗ[A] F.X r), p.comp i = LinearMap.id`. This existential is under the same compactness assumption, and its model has `Nonempty (E ≅ Q.obj F)`. |
| Every degree, rank at least zero, including zero | `∀ r : ℤ` and `n : ℕ`; `Fin 0 → A` is allowed. |
| No Noetherian hypothesis | The only ring assumption is `CommRing A`; no nonzero-ring, Noetherian, finite-dimensional, field, or finiteness assumption is present. |

Statement dependencies read and used:

- `def-weil-size-convention`: its record is a metatheoretic convention with no
  declaration or module; the two explicit universe levels implement it.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  Read the declarations, their size documentation, and the localization interface.
- `def-pc-compact-object`: `CategoryTheory.IsCompactObject` in
  `WeilConjectures.CategoryTheory.CompactObject`; read its full quantified
  `DirectSum.toAddMonoid` definition and docstring. The example's old Sheaf file
  is withdrawn; its node now correctly records this upstream definition.
- `def-pc-perfect-ring-complex`: `DerivedCategory.IsPerfectRingComplex` in
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`; read its
  full bounded finite-projective witness definition. It permits arbitrary w.

The proof imports follow the node's seven-step proof:

- `CategoryTheory.derivedModuleDirectSums`,
  `WeilConjectures.CategoryTheory.DerivedModuleDirectSums`.
- `CochainComplex.exists_subcategory_left_resolution`,
  `Sheaf.Algebra.Homology.SubcategoryLeftResolution`.
- `DerivedCategory.triangleOfSESδ`, `DerivedCategory.triangleOfSES`, and
  `DerivedCategory.triangleOfSES_distinguished`,
  `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `CategoryTheory.compact_hom_hocolim`,
  `WeilConjectures.CategoryTheory.CompactHomHocolim`.
- The Mathlib matches for the two dependencies with no Lean record:
  `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`, the zero-composite
  clauses, and `exists_iso_binaryBiproduct_of_distTriang`, all in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Module.Projective`, `Mathlib.Algebra.Module.Projective`.
- `DerivedCategory.isPerfectRingComplex_summand`,
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingSummand`.

The full proof is in the theorem docstring: good truncations bound cohomology
above; a free resolution is retracted onto a stupid truncation using its
countable telescope; finite-basis induction and exactness of Hom in triangles
produce a bounded finite free complex retracting onto E; a split triangle and
perfect summand stability give a finite-projective model; generator lifting
provides the termwise finite free retractions and their converse.

Edge cases checked before writing:

- The zero ring is allowed and all its modules are zero; no `Nontrivial A` binder
  excludes it. The zero derived object has the zero bounded model.
- An empty coproduct index is included in the existing compactness definition.
- Degrees are all integers, so shifted models and negative support bounds are
  included. No nonnegative-degree or upper bound on E is assumed.
- Outside the support, the zero module can have rank-zero retraction. Rank zero
  is permitted also in the support. No positive-rank requirement appears.
- Strict lower/upper support predicates mean vanishing below a and above b;
  they impose no condition on a and b. In particular zero models with a > b
  remain allowed, exactly as in the recorded perfectness definition.
- No ring characteristic or Noetherian property is needed.
- `ModuleCat.{u} A` and coproducts indexed by `Type u` use the same small
  universe, while the Hom universe w is independent. No unsupported equality
  of localization and coefficient universes is imposed.

Searches actually run with the prescribed wrapper:

1. LeanFinder: "A compact object in the unbounded derived category of modules
   over a ring is represented by a bounded complex of finitely generated
   projective modules". Eight hits, including `instHasExtModuleCatOfSmall`,
   derived-category bounded-representative lemmas, and K-projectivity lemmas.
   None states the compact-to-perfect theorem.
2. Loogle: `"IsCompactObject"`. Zero hits.
3. Mathlib grep: `IsCompactObject|compact.*projective|projective.*compact|[Pp]erfect`
   under `Algebra/Homology`. Zero hits.
4. LeanSearch: "A compact object of the derived category of modules over a ring
   is perfect". Eight hits: derived-category definitions, HasExt, and unrelated
   topological/perfect-pairing declarations; no matching theorem.
5. Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for compact/perfect
   combinations and `IsPerfectRingComplex`, and `grep -rn` for the exact item id
   in `lean/WeilConjectures`. The latter had no hits. The former found the
   recorded perfectness definition and a private helper `compact_perfect` in
   `Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect.lean`.
   That helper is private, cannot serve as a public dependency declaration,
   and does not include the item's explicit finite free retraction-model clause.
   No publicly usable exact match was found.
6. Local `rg` in `dag/lean_names_upstream.json`, upstream CategoryTheory, and
   project CategoryTheory for the proposed theorem name and compact/perfect
   combinations: the proposed full declaration name is unused.

Validation: the delivered module passed `scompile.py N7
lem-sfb-ring-derived-compact-perfect <file>` in both sandbox and library mode
(5.1 s and 6.6 s); there were no compiler errors or unexpected warnings.
Every variable and universe is explicit, and `autoImplicit` is disabled.
All lines in the module are at most 100 characters.

## Second reading by N7

I reread the node statement against the finished signature and expanded both
recorded predicates in their source files. This is a worker self-check; the
maintainer supplies the independent review, as specified in the assignment.
The compactness binder is exactly the canonical direct-sum Hom bijectivity
condition, and the perfectness predicate gives the required bounded finite
projective model in the same D(A). The extra model existential retains the
second formulation rather than silently dropping it: i goes from F.X r to A^n,
p goes back, and `p.comp i = LinearMap.id` is p after i. The bounds and iso refer
to this F. The ranks may be zero, degrees may be negative, and the zero ring
is included. The localization universe is independent. No hypothesis or clause
needed correction on this reading, and no dependency definition was duplicated.

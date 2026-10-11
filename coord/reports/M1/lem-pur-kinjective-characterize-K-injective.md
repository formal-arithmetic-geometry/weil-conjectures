## Worker report

The module `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveCriterion` states
`CochainComplex.isKInjective_of_small_acyclic`. Its only proof is `sorry`; it introduces
no definitions. The item node changes only in `lean`.

The node's source was read online because `literature/stacks-project/injectives.tex`
is absent from this machine: [Stacks source, injectives.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex),
labels `lemma-characterize-K-injective` and `lemma-acyclic-quotient-complexes-bounded-size`.
The first uses a cardinal supplied by the second; its two properties are precisely the
node's explicit clauses (a) and (b). No statement correction is needed.

Hypotheses and clauses, matched individually:

- The category `𝒜` is `{C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C]`. The Grothendieck declaration supplies small colimits,
  a separator (generator), and exact filtered colimits, as the dependency requires.
- The cardinal is `(κ : Cardinal.{v})`. Object size is rendered directly by
  `Cardinal.mk (Shrink.{v} (Subobject (X)))`. `Subobject X` is the set of subobjects,
  not the underlying elements of `X`. Grothendieck well-poweredness makes this set
  small in `v`; `equivShrink` preserves its cardinality. No new notion is needed.
- Every acyclic cochain complex in (a) is quantified in `h_sub` as
  `∀ (M : CochainComplex C ℤ), M.Acyclic → ...`.
- The qualification `M ≠ 0` is `¬ IsZero M`, expressing nonzero categorically,
  independently of a chosen representative of the zero object.
- A subcomplex is `∃ (N : CochainComplex C ℤ) (ι : N ⟶ M), Mono ι ∧ ...`.
  A monomorphism of complexes is exactly a degreewise monomorphism in the abelian
  category, so this represents an actual subcomplex up to the usual isomorphism.
- Nonzero is `¬ IsZero N`. Bounded above is `∃ b : ℤ, N.IsStrictlyLE b`;
  this is vanishing of terms above `b`, not merely of cohomology. Acyclic is `N.Acyclic`.
  Every degree size bound is `∀ n : ℤ, Cardinal.mk
  (Shrink.{v} (Subobject (N.X n))) ≤ κ`.
- In (b), `h_quot` again quantifies every acyclic `M`. The set and family are
  `∃ (α : Type v) (F : α → CochainComplex C ℤ)`; the surjection is
  `(π : ∐ F ⟶ M), Epi π`. The complex coproduct is calculated degreewise, and
  epimorphisms of complexes are degreewise epimorphisms.
- Each member's three conditions are under `∀ a : α`: its own upper bound
  `∃ b : ℤ, (F a).IsStrictlyLE b`, acyclicity `(F a).Acyclic`, and
  `∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject ((F a).X n))) ≤ κ`.
  There is no uniform upper bound imposed on the family.
- The target complex is `(I : CochainComplex C ℤ)`. Hypothesis (1) is
  `h_inj : ∀ j : ℤ, Injective (I.X j)`.
- Hypothesis (2) is `h_small`: for every bounded-above, acyclic, termwise-small
  complex `M`, `∀ f : M ⟶ I, Nonempty (Homotopy f 0)` says every complex morphism
  is homotopic to zero. The conclusion is exactly `I.IsKInjective`.

All universes and variables are explicitly bound. `v` is the small-set universe of
this Grothendieck category, used consistently for cardinalities and small coproducts;
`u` is independent and permits a large category of objects. No additional regularity,
infinite-cardinal hypothesis, lower bound, or enough-injectives assumption is added.

Dependency declarations read and used:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `def-pc-cochain-complex-modules`: `CochainComplex`,
  `Mathlib.Algebra.Homology.HomologicalComplex`, here specialized to `C` as the node asks.
- `def-pc-acyclic-complex-modules`: `HomologicalComplex.Acyclic`,
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, likewise for `C`.
- `def-sp-injective-resolutions`: the injectivity clause is `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, explicitly identified in the
  dependency's `mathlib_match.how`; no injective resolution is needed in this statement.
- `def-pur-kinjective-complex`: `CochainComplex.IsKInjective`,
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, again for `C`.

The imported `Mathlib.Algebra.Homology.HomologicalComplexLimits` supplies coproducts
of complexes from the category's colimits. All other listed dependency declarations
are available through the K-injective import. The theorem docstring contains all four
proof steps from the node, including their named dependencies and all-shifts induction.

Edge cases checked: (a) applies only to nonzero complexes; zero complexes remain
allowed in (b) and in the small-test hypothesis. The index set in (b) can be empty.
Upper bounds vary with the family member, and complexes may be unbounded below.
The target has no boundedness assumption. Finite cardinals and `κ = 0` are retained;
since even the zero object has a subobject, smallness hypotheses can become impossible,
which is consistent with the conditional statement. No edge case is excluded.
No statement is disputed, and no dependency record is unusable.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "criterion for K injectivity in Grothendieck abelian
  category using bounded above small acyclic complexes"`: eight hits, including
  enough injectives and the bounded-below injective criterion, none with these hypotheses.
- `msearch.py ... loogle "CochainComplex.IsKInjective"`: twelve hits, including the
  definition, bounded-below criterion, shifts and orthogonality; no bounded-size criterion.
- `msearch.py ... grep "characterize.*[Kk].*[Ii]njective|isKInjective" Algebra/Homology`:
  24 hits, K-injective definition and related derived-category lemmas; no exact match.
- `msearch.py ... leansearch "K-injective criterion small bounded above acyclic complexes
  Grothendieck category"`: unavailable, Internal Server Error; no verdict from this service.
- `rg` in `WeilConjectures` and `lean/Sheaf` for K-injective criteria and subobject
  cardinalities: the source has a lifting-property criterion and Serpé cardinal
  constructions, neither the node's statement. Read the lifting criterion's full file
  and the Serpé cardinal module to check this distinction.
- `rg` for the item id in `WeilConjectures` and `dag/lean_names_upstream.json`:
  no matches. `rg` for `isKInjective_of_small_acyclic` in Mathlib, `WeilConjectures`,
  `lean/Sheaf`, and the upstream-name index: no matches.

Validation: `scompile.py M1 lem-pur-kinjective-characterize-K-injective` on the module
completed successfully in 1.5 seconds, with no errors or warnings. The delivery dry run
is the final worker check; the independent second reading is left to the second reader.

## Second reading by M1

The node introduces a Grothendieck abelian category `𝒜`, a cardinal `κ`, an
object-size convention, two hypotheses on every acyclic cochain complex, and a
complex `I`. The Lean renders these as follows.

- `𝒜` is `{C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C]`; this is the same general category as the node.
- `κ` is `(κ : Cardinal.{v})`. The size `|X|` is rendered by
  `Cardinal.mk (Shrink.{v} (Subobject X))`, exactly the cardinality of the set
  of subobjects, with the shrink only expressing the small hom-universe.
- Clause (a) is `h_sub`: for every `M`, `M.Acyclic → ¬ IsZero M`, there are
  `N` and a monomorphism `ι : N ⟶ M`, with `¬ IsZero N`, a bound
  `∃ b : ℤ, N.IsStrictlyLE b`, `N.Acyclic`, and the termwise size bound.
  This is precisely a nonzero bounded-above acyclic subcomplex; no strictness
  of the inclusion beyond the node's subcomplex requirement is added.
- Clause (b) is `h_quot`: for every acyclic `M`, there are a small index type
  `α : Type v`, a family `F`, and an epimorphism `π : ∐ F ⟶ M`; each member is
  bounded above, acyclic, and termwise of size at most `κ`. This is the stated
  coproduct surjection, with no uniform bound imposed on the family.
- The target is `I : CochainComplex C ℤ`; (1) is
  `h_inj : ∀ j : ℤ, Injective (I.X j)` and (2) is `h_small`, which gives
  `Nonempty (Homotopy f 0)` for every map from every bounded-above acyclic
  termwise-small complex. The conclusion is exactly `I.IsKInjective`.

I checked the source lemma `lemma-characterize-K-injective` in
`injectives.tex`: it assumes only the Grothendieck category, the cardinal
criterion, termwise injectivity, and vanishing of maps from the bounded-above
small acyclic complexes. Its Homotopy-category-zero formulation is equivalent
 to the Lean `Nonempty (Homotopy f 0)` formulation used by the node. The
transfinite filtration, successor exactness, limit inverse-system argument,
and final specialization to shift zero are documented in the declaration
docstring and match the node proof steps.

Edge cases are retained: the index type `α` may be empty; zero complexes are
handled by the hypotheses (and excluded only where clause (a) explicitly says
`M ≠ 0`); `κ` may be finite or zero; bounds may vary by family member; and
complexes may be unbounded below. Universes `u` and `v` are explicit and no
extra finiteness, regularity, characteristic, or enough-injectives hypothesis
appears.

Searches were independently repeated with `msearch.py` (LeanFinder, Loogle,
and grep), and `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`; only the
general `CochainComplex.IsKInjective` and related bounded-below criteria were
found. No declaration matching this bounded-size Grothendieck criterion
exists. No mismatch was found, so no source, node, or Lean change was needed.

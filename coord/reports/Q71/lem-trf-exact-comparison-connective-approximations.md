## Worker report

The module `Sheaf.CategoryTheory.Triangulated.ExactComparisonConnectiveApproximations`
states `CategoryTheory.isIso_comparison_of_connective_approximations`, with its proof
left `sorry`. No definitions, dependency repairs, new nodes, or statement corrections
are needed. The source was read in `literature/stacks-project/more-algebra.tex`,
label `lemma-internal-hom-evaluate-isomorphism-technical` (Tag 0A69), especially the
sentence immediately following the truncation triangle. The node abstracts exactly
that reduction; the module docstring contains all three recorded proof steps.

Hypothesis and conclusion correspondence:

- The triangulated category is `{T : Type uT} [Category.{vT} T] [Preadditive T]`
  with `[HasZeroObject T] [HasShift T ℤ]`, additive shifts, `[Pretriangulated T]`
  and `[IsTriangulated T]`. These are precisely the recorded Mathlib interface.
- The abelian category is `{A : Type uA} [Category.{vA} A] [Abelian A]`.
  `[HasDerivedCategory.{w} A]` fixes the chosen unbounded derived category and
  morphism universe. The five universes are explicit and independent.
- `F G : T ⥤ DerivedCategory A`, their `[F.CommShift ℤ] [G.CommShift ℤ]`, and
  `[F.IsTriangulated] [G.IsTriangulated]` give the two exact functors with specified
  shift isomorphisms. `e : F ⟶ G` and `[NatTrans.CommShift e ℤ]` give the stated
  shift-compatible natural transformation.
- `K : T` is the fixed object. `P E : ℤ → T` are the node's A_n and E_n (the name
  P avoids confusing the approximation with the coefficient category A).
  `i`, `p`, and `q` are all three arrows of every triangle; `hTriangle` asserts
  `Triangle.mk (i n) (p n) (q n) ∈ distTriang T` for every integer n.
- `hApprox : ∀ n : ℤ, IsIso (e.app (P n))` is invertibility on every approximation.
- A single integer `c : ℤ` is fixed before `hTail`; for every integer n and r with
  `r ≤ n - c`, that hypothesis states `IsZero` of both image cohomology objects.
  An arbitrary supplied witness c of the node's existential bound is used, since
  the quantitative conclusion refers to that same c. No choice of c is built in.
- The first conclusion is `IsIso (e.app K)` in the derived category itself.
- For every `d n : ℤ` with `d + c ≤ n`, the remaining conclusion supplies proofs
  `hF` and `_hG` of invertibility of both maps on degree-d cohomology, and states
  `H^d(e_K) = inv(H^d(F(i_n))) ≫ H^d(e_(P_n)) ≫ H^d(G(i_n))`.
  Lean's composition order is left to right, so this is exactly the displayed
  formula in the node. Existentially binding the two `IsIso` proof witnesses lets
  `@inv ... hF` mention the inverse in the same conclusion, without hidden lets
  or additional hypotheses. The proof witness is irrelevant, and inverses are unique.
- There is no boundedness hypothesis, no maps between distinct P_n, and no
  preservation of infinite limits or colimits.

Dependency declarations read and used:

- `def-weil-triangulated-category`: `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `CategoryTheory.Pretriangulated`; `Mathlib.CategoryTheory.Triangulated.Triangulated`,
  `CategoryTheory.IsTriangulated`; `Mathlib.CategoryTheory.Triangulated.Functor`,
  `CategoryTheory.Functor.IsTriangulated` and its shift-commutation interface.
  The first two modules are publicly imported by the last module.
- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory` and `HasDerivedCategory`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`.
- The proof dependencies `lem-sf-derived-homology-long-exact` and
  `lem-weil-pbc-unbounded-derived-iso-cohomology` use the already imported
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, respectively
  `DerivedCategory.HomologySequence.exact₁/exact₂/exact₃` and
  `DerivedCategory.isIso_iff`. Their full statements and the connecting map were read.
  This import is public because the statement itself uses its cohomology functor.
- Also read `CategoryTheory.NatTrans.CommShift` in
  `Mathlib.CategoryTheory.Shift.CommShift` and `CategoryTheory.inv` in
  `Mathlib.CategoryTheory.Iso`, to check compatibility and the explicit inverse witness.

Edge cases checked before writing: at n=d+c the bound gives vanishing in both
r=d and r=d-1, exactly the segment needed for invertibility. Negative d, n and c
are allowed with integer arithmetic. The zero category and zero objects cause no
extra restrictions. The index set is all integers and carries no compatibility
data. Unbounded K is allowed. Object and morphism universes of T and A, and the
chosen localization morphism universe, remain independent. No statement dispute
or node fault was found.

Searches for an existing statement (all through the prescribed wrapper where applicable):

- `msearch.py ... leanfinder`: "A natural comparison of exact functors into a derived
  category is invertible on an object if it is invertible on approximations and both
  cone images have cohomology vanishing through n minus a fixed constant".
  Eight hits, including `DerivedCategory.exists_iso_Q_obj_of_isLE`, its isGE and
  bounded variants, and localization infrastructure. None states this criterion.
- `msearch.py ... loogle`: `DerivedCategory, CategoryTheory.NatTrans, CategoryTheory.IsIso`.
  Zero hits.
- `msearch.py ... grep` in `Algebra/Homology`:
  `isIso.*(approx|cone)|approx.*[Ii]sIso|connective`. Two hits in
  `HomotopyCategory/ShortExact.lean`, concerning composition of homology-factor maps;
  neither matches.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the proposed declaration and connective-approximation phrases: no match.
  Broader `exactComparison` and `comparison.*approximation` searches found unrelated
  comparison-factorization and geometric approximation declarations. The existing
  t-exact truncation comparison was inspected and requires different hypotheses
  and gives a different conclusion.
- `grep -rn` for the item id in `lean/WeilConjectures`: no match.

Validation: the prescribed `scompile.py Q71
lem-trf-exact-comparison-connective-approximations <module>` succeeded for both
sandbox and library module visibility, without errors or unexpected warnings.
All variables and universes are explicit, with `set_option autoImplicit false`.

## Second reading by Q71

The dispatcher explicitly prohibits starting another agent; the maintainer supplies
an independent review of this delivery. This section records a second consistency
pass by the same worker, not an independent review. Reopened the node and module:
the T/A universe binders, exact and shift-compatible functor hypotheses, all three
triangle arrows and distinguishedness, approximation isomorphisms, single uniform
integer c, both tail vanishings, derived isomorphism, both quantitative cohomology
isomorphisms and inverse formula each have the counterparts listed above. The
composition orientation was checked against naturality
`F(i_n) ≫ e_K = e_(P_n) ≫ G(i_n)`. The explicit inverse uses the concluded hF,
not an assumed inverse or an arbitrary map. The lower threshold is inclusive.
No mismatch was found and no statement change was made.

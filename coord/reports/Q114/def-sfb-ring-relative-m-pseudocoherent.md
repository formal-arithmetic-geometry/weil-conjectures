## Worker report

Defines `DerivedCategory.IsMPseudoCoherentRelativeTo` in
`Sheaf.RingTheory.RelativeMPseudoCoherent`. There are no theorems, proof obligations,
new nodes, dependency repairs, statement corrections, or sorry declarations in this delivery.
The only change to the original node is its `lean` record.

Read Stacks `literature/stacks-project/more-algebra.tex`,
`definition-relatively-pseudo-coherent` (Tag 065I), clause (1), and
`lemma-relatively-pseudo-coherent` (Tag 065H), condition (1), at lines 21291–21347.
The definition uses the existential condition; presentation independence is a separate lemma.
Also read the latest blueprint's `sk-thm-sf-ctf-stability/_section.md` and
`sk-thm-sf-ctf-stability-direct-images.proof.md`, especially part (3). This algebraic
supporting definition does not change that unit's statement or proof route.
There is no repair note for this item.

Clause-by-clause correspondence:

- Commutative rings R and A: `(R : Type u) {A : Type u}` with `[CommRing R]`
  and `[CommRing A]`. The map R → A is the structure map of `[Algebra R A]`.
- Finite type means finitely many algebra generators: `[Algebra.FiniteType R A]`,
  whose Mathlib definition is finite generation of the top R-subalgebra.
- The arbitrary integer m is `(m : ℤ)`; no sign or bound is imposed.
- The arbitrary derived object is `(M : DerivedCategory (ModuleCat.{u} A))`,
  under `[HasDerivedCategory.{wA} (ModuleCat.{u} A)]`.
- A nonnegative finite number of variables is `∃ (n : ℕ)`; zero is allowed.
- The polynomial presentation is `α : MvPolynomial (Fin n) R →ₐ[R] A`.
  This is an R-algebra homomorphism, so its composite with the polynomial coefficient
  map is exactly the original structure map R → A.
- The presentation is surjective precisely by `Function.Surjective α`.
- The restricted object is
  `(RingDerivedScalarExtension.moduleDerivedRestriction α.toRingHom).obj M`.
  Its result is required to satisfy `IsMPseudoCoherent m`. No all-presentations condition,
  flatness, Noetherianity, finite presentation, or boundedness of M is added.
- The final sentences explaining restriction are realized by the existing derived
  restriction construction, not by a replacement map or an additional hypothesis.
  Its underlying definition is `(ModuleCat.restrictScalars f).mapDerivedCategory`.
  Mathlib `ModuleCat.restrictScalars` leaves the underlying additive group and maps
  unchanged and uses the action `p • x = α(p) • x`. Its exactness instances in
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` preserve finite limits
  and colimits; `Functor.mapDerivedCategory` localizes the termwise complex functor.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q`, in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`. Read also `MvPolynomial.algHom_ext` there
  and `MvPolynomial.aeval` and `aeval_X` in `Mathlib.Algebra.MvPolynomial.Eval`.
- `def-pc-ring-m-pseudo-coherent`: `DerivedCategory.IsMPseudoCoherent` in
  `WeilConjectures.RingTheory.MPseudoCoherent`. Its full definition uses a bounded
  complex of finite free modules, a map to the given derived object, isomorphisms
  on homology above m and an epimorphism in degree m.
- `def-zl-ring-derived-scalar-extension`:
  `CategoryTheory.RingDerivedScalarExtension.moduleDerivedRestriction` in
  `Sheaf.AlgebraicGeometry.RingDerivedScalarExtension`. Read its abbreviation and
  the underlying `CategoryTheory.ConstantScalarRealization.moduleDerivedRestriction`
  in `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`.
- `lem-sf-exact-functor-derived-triangulated`: the recorded Mathlib match is
  `CategoryTheory.Functor.mapDerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. Read its signature,
  `mapDerivedCategoryFactors`, the triangulated/shift instances, and
  `mapDerivedCategorySingleFunctor`.

Universes: u is the common ambient universe for the two rings, their polynomial rings,
and ordinary modules. It is arbitrary, so one can choose an ambient universe containing
all the rings and module carriers under consideration. Localization morphism universes
wA and wP are independent. The family of `HasDerivedCategory` instances for all natural
n simply chooses D(R[t₁,…,tₙ]) before the existential presentation is selected; it makes
no mathematical assumption on the rings. No equality between localization sizes is used.
All variables and universes are explicit, with `autoImplicit false`.

Edge cases checked before writing: n = 0 gives the polynomial algebra on the empty
variable set; R = A with the identity structure map is permitted. The zero ring and
M = 0 are permitted; there is no nontriviality or nonzero assumption. Positive, negative
and zero m all use the same existing degreewise predicate. Arbitrarily unbounded M
and non-Noetherian R are permitted; only the approximating complex in the dependency
predicate is bounded. Empty generators are not excluded.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- leanfinder: `Relative m pseudo coherence of a derived module over a finite type algebra
  by restriction along a surjective finite polynomial presentation` — eight hits,
  including cotangent presentations, finite presentation, and a finite-free module cover;
  no relative derived pseudo-coherence definition.
- loogle: `"PseudoCoherent"` — zero hits.
- grep: `Relative.*PseudoCoherent|relative.*pseudo.?coher` — zero Mathlib hits.
- leansearch: `A derived module over a finite type algebra is relatively m pseudo coherent
  if restriction along a surjective polynomial presentation is m pseudo coherent` —
  eight hits on sheaf/module finite presentation and module presentations, no exact match.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf` with
  `Relative.*PseudoCoherent|relative.*pseudo.?coher`: the existing polynomial-presentation
  invariance theorem and scheme/duality discussions, but no definition of this predicate.
  Read `Sheaf.RingTheory.PolynomialPresentationPseudoCoherence`: it is the theorem for
  the absolute pseudo-coherent predicate, not this relative degreewise definition.
- `grep -rn 'def-sfb-ring-relative-m-pseudocoherent' lean/WeilConjectures` — no hit.
  `rg 'relative.*[Pp]seudo|Relative.*Pseudo' dag/lean_names_upstream.json` — no hit.
  Exact-name rg for `IsMPseudoCoherentRelativeTo` in Mathlib and both source trees — no hit.

Validation: scompile.py compiled the module in both sandbox and library module mode,
with no errors or warnings. After replacing an overly broad finiteness import with
`Mathlib.RingTheory.FiniteType`, the delivery dry run recompiles the final source.

## Second reading by Q114

Author's second pass, with the full node and final module open; the maintainer supplies
independent review as required by the dispatcher brief. Matched commutative rings,
R-algebra structure, finite-type assumption, integer degree, arbitrary derived object,
natural number of variables, polynomial algebra map, surjectivity, and m-pseudo-coherence
of the actual derived restriction individually against the node. Read the definition body
of the scalar restriction abbreviation to check that it is termwise restriction rather
than scalar extension. Checked that only the existential presentation occurs, that n = 0
is admitted, and that no derived or ring nontriviality assumption was introduced.
The full absolute degreewise predicate was read to verify the direction of the
cohomology inequalities and the surjection at m. The final module has no local notation,
auto-bound implicit, new axiom, or sorry data. One import was tightened from
`Mathlib.RingTheory.Finiteness.Basic` to the actual finite-type definition module;
no mathematical mismatch was found, and no statement correction was made.

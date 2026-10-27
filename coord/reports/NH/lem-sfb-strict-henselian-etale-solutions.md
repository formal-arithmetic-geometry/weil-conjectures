## Worker report

The module `Sheaf.RingTheory.StrictHenselianEtaleSolutions` states
`MvPolynomial.bijOn_solutions_of_isStrictlyHenselianLocalRing`, with its entire
proof postponed as `sorry`. No definition or helper theorem is introduced.
The source is Stacks Project, Algebra, Tag 04GX,
`literature/stacks-project/algebra.tex`, label
`lemma-strictly-henselian-solutions`. Its statement, displayed solution sets,
and proof were read. The node's statement agrees with that source; no correction
or statement dispute is needed. Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings R and S are `(R : Type u) (S : Type v) [CommRing R]
  [CommRing S]`. The universes are independent; neither ring is assumed finite,
  Noetherian, a domain, or a field.
- Strictly henselian local rings are `[IsStrictlyHenselianLocalRing R]` and
  `[IsStrictlyHenselianLocalRing S]`. The recorded upstream class extends
  `HenselianLocalRing`, which supplies locality, and has a separably closed
  residue field. No separate redundant locality assumption is added.
- The local ring homomorphism is `(θ : R →+* S) [IsLocalHom θ]`.
  `IsLocalHom` reflects units; ring homomorphisms preserve units, so
  `isUnit_map_iff θ` gives precisely the stated iff.
- The integer n >= 0 is `(n : ℕ)`, including zero. The n equations in n variables
  are `(P : Fin n → MvPolynomial (Fin n) R)`. Indexing by `Fin n` merely changes
  labels from 1,...,n to 0,...,n-1.
- The ring D is written explicitly as
  `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)`.
  Its structural ring map is `algebraMap R` into this quotient, namely constants
  followed by the quotient map. No arbitrary presented algebra is substituted.
- The exact geometric étaleness assumption is `(hEtale :
  AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
  (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))))))`.
  This is the structural morphism Spec D -> Spec R, using the recorded
  `AlgebraicGeometry.Spec.map` and `AlgebraicGeometry.Etale` declarations.
- Coefficientwise images are exactly `MvPolynomial.map θ (P i)`.
- The source solution set is
  `{r : Fin n → R | ∀ i : Fin n, MvPolynomial.eval r (P i) = 0}`.
- The target solution set is
  `{s : Fin n → S | ∀ i : Fin n,
  MvPolynomial.eval s (MvPolynomial.map θ (P i)) = 0}`.
- The specified coordinatewise map is
  `fun r : Fin n → R ↦ fun j ↦ θ (r j)`.
- `Set.BijOn` applied to this map and these exact sets asserts that it maps
  solutions to solutions, is injective there, and is surjective onto the target
  solution set. This is exactly a bijection induced by that coordinate map,
  without any chosen inverse or extra conclusion. The definition of `BijOn`
  in `Mathlib.Data.Set.Operations` was read.

Dependency declarations used and source signatures/docstrings read:

- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian`,
  `IsStrictlyHenselianLocalRing` (extends `HenselianLocalRing` and supplies
  `IsSepClosed (IsLocalRing.ResidueField R)`). Public import.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` (finitely supported monomials), and the recorded universal
  property `MvPolynomial.algHom_ext`; `Mathlib.Algebra.MvPolynomial.Eval`,
  `MvPolynomial.aeval`. The latter module publicly imports Basic and supplies
  `MvPolynomial.eval` and `MvPolynomial.map`, used directly in the statement.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; exposed through the
  public import of `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`, the recorded affine-local class. Public import.
- Quotient algebra infrastructure is publicly imported from
  `Mathlib.RingTheory.Ideal.Quotient.Operations`.

The stated proof-dependency declarations are imported privately for stage 3:

- `lem-weil-pbc-etale-ring-base-change`: Mathlib match
  `Algebra.Etale.baseChange`, `Mathlib.RingTheory.Etale.Basic`.
- `lem-weil-pbc-henselian-local-target-etale-maps`:
  `Algebra.bijective_residueField_tensor_map_of_henselian_target`,
  `Sheaf.RingTheory.HenselianLocalTargetEtaleMaps`. The complete signature and
  proof docstring were read, including the module-finite, formally unramified
  henselian target and the tensor reduction map.
- `lem-weil-pbc-etale-algebra-over-field-product`: Mathlib match
  `Algebra.Etale.iff_exists_algEquiv_prod`, `Mathlib.RingTheory.Etale.Field`.
- `def-kun-separably-closed`: `IsSepClosed` and `IsSepClosure`,
  `Mathlib.FieldTheory.IsSepClosed` (only the former is needed in the proof).
- The other proof dependencies are already publicly imported statement
  dependencies. The docstring carries all five proof steps of the node,
  including tensor adjunction, empty products, and the natural residue square.

Edge cases checked before writing:

- n = 0: `Fin 0` is empty, the span of the empty equation family is zero,
  D is canonically R, and each set of empty tuples is a singleton. The map
  between them is bijective. No positive-n assumption appears.
- Empty solution sets, including the zero quotient D: étale algebras are
  allowed to be zero. With an equation 1 = 0 both solution sets are empty,
  since strictly henselian local rings are nonzero. `BijOn` handles this.
- Identity θ: the induced coordinate map is identity, with identical equations.
- θ need not be injective or surjective on the rings. The theorem asserts
  injectivity only on the étale solution set. No field, residue-field
  isomorphism, or finiteness assumption was added.
- Different ring universes are permitted. The quotient and its spectrum are
  formed only over R; no equality between u and v is imposed.
- Arbitrary residue characteristic and nonreduced strictly henselian local
  rings remain covered.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "A local homomorphism of strictly henselian local
  rings induces a bijection on solutions of an etale polynomial system"`:
  8 hits: `StandardEtalePresentation.lift_bijective`,
  `StandardEtalePair.homEquiv`, `HenselianLocalRing.TFAE`,
  `StandardEtalePair.homEquiv_symm_apply`,
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`,
  `StandardEtalePair.hasMap_X`,
  `StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot`,
  `StandardEtalePair.homEquiv_apply_coe`. The standard-etale parametrization and
  presentation signatures/docstrings were opened. None compares arbitrary
  étale systems over two strictly henselian local rings.
- `msearch.py ... loogle "HenselianLocalRing, RingHom.Etale"`: 0 hits.
- `msearch.py ... grep "StrictlyHenselian|homEquiv|lift_bijective"
  RingTheory/Etale`: 6 hits in StandardEtale.lean and Finite.lean, concerning
  standard presentations and the parametrization of split finite algebras.
  None is the requested statement.
- `msearch.py ... leansearch "Local homomorphism of strictly henselian rings
  induces bijection of etale polynomial solution sets"`: 8 hits,
  `HenselianLocalRing`, `HenselianLocalRing.TFAE`, `RingHom.Etale`,
  `RingHom.FormallyEtale`, `IsLocalRing.ResidueField.map`,
  `IsLocalRing.local_hom_TFAE`, `RingHom.Etale.propertyIsLocal`, and
  `AlgebraicGeometry.SpecToEquivOfLocalRing`. No exact match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `04GX|strictly.henselian.*solutions|etale.*polynomial.*solutions|[Bb]ijOn.*[Hh]enselian`
  returned no hits. Searching the exact node id in `lean/WeilConjectures`
  also returned no hits. Broader StrictlyHenselian searches found root lifting,
  étale sections, and unrelated stalk comparisons, not this solution theorem.
- Exact proposed declaration-name searches in Mathlib and both project roots
  returned no hits. All four statement dependencies already have usable
  declarations, so no new node or dependency repair is required.

## Second reading by NH

The dispatcher explicitly forbids starting other agents; this section records a
second pass by the same worker, not an independent review. The maintainer's
independent delivery review remains separate.

Reopened the node and the module together and matched the two CommRing binders,
strict henselian instances, local θ, arbitrary natural n, indexed polynomial
family, explicit quotient, geometric étaleness, coefficient map, both solution
predicates, and coordinate map. `Set.BijOn` contains all three required clauses
(maps-to, injectivity, surjectivity), not an existential bijection unrelated to θ.
Checked that the étaleness assumption concerns the quotient's structure map,
that no Jacobian-invertibility condition replaces étaleness, and that n = 0 is
retained. No mathematical mismatch was found. The direct private import of
`Mathlib.RingTheory.Etale.Basic` was added to make the base-change proof
 dependency explicit. Every variable and universe is explicitly bound.

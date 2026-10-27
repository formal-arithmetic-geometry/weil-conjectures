## Worker report

The module `Sheaf.RingTheory.PerfectAffinoidLocalJacobianChart` states
`RestrictedSeries.perfect_affinoid_local_jacobian_chart`. Its only declaration is this
named theorem, whose entire proof is `sorry`. No definitions, axioms, helper theorems,
new nodes, dependency repairs, or statement corrections are supplied. The original
node is changed only in `lean`.

Hypothesis and clause matching:

- The field with a real-valued absolute value is `(F : Type u) [NormedField F]`.
  `[IsUltrametricDist F]` expresses nonarchimedeanness; `[CompleteSpace F]` is
  completeness; `hF : ∃ c : F, c ≠ 0 ∧ ‖c‖ ≠ 1` excludes the trivial absolute value.
  No discrete valuation or characteristic-zero hypothesis is added.
- `[PerfectField F]` is Mathlib's perfect-field predicate. Its defining irreducible
  polynomial separability condition is equivalent to every finite algebraic extension
  being separable; `Algebra.IsAlgebraic.isSeparable` supplies the forward implication.
- `(r s : ℕ)` allows all the nonnegative integers in the node. The zero-based `Fin r`
  and `Fin s` are the order-preserving relabellings of its one-based finite sets.
- The ring T is exactly the subtype of
  `MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))`.
  In Mathlib's definition, the weight factor is one, so its cofinite convergence
  condition is exactly the stated finiteness of coefficients of norm at least ε.
  Its inherited addition and multiplication are coefficientwise addition and Cauchy
  multiplication, respectively. The defining file and operations were read.
- `(f : Fin s → T)` is the arbitrary finite family of relations. Every occurrence of
  `Ideal.span (Set.range f)` is the fixed ideal I, and the quotient type `T ⧸ ...`
  is B. Neither ring nor ideal is replaced by an arbitrary ring or ideal.
- `[IsRegularRing (T ⧸ Ideal.span (Set.range f))]` expresses exactly the regular
  Noetherian hypothesis. `IsRegularRing` extends `IsNoetherianRing` and requires
  `IsRegularLocalRing (Localization.AtPrime p)` for every prime p.
- `(m : Ideal B) [m.IsMaximal]` universally quantifies over every maximal ideal of
  B. There is no hypothesis that B is nonzero.
- The witnesses `E : Finset (Fin s)` and `U : Finset (Fin r)`, with
  `h : U.card = E.card`, are precisely the subsets of equal cardinality.
  `U.orderEmbOfFin h` and `E.orderEmbOfFin rfl` enumerate both increasingly with
  the same index type `Fin E.card`.
- `a : T` satisfies
  `∀ b ∈ Ideal.span (Set.range f), a * b ∈ Ideal.span (f '' (E : Set (Fin s)))`.
  This is exactly aI ⊆ I_E, hence the node's definition of colon membership. It
  quantifies over all of I, not merely over some chosen local generators.
- `D : T` is pinned by equality of its underlying formal series with
  `Matrix.det (fun i j : Fin E.card ↦ MvPowerSeries.pderiv F
    (U.orderEmbOfFin h i) (f (E.orderEmbOfFin rfl j)).val)`.
  Mathlib's `pderiv` is the termwise derivative: its ν coefficient is the
  coefficient at ν+e_i multiplied by ν_i+1. Rows are U and columns are E, exactly
  as in the node. This equality renders the node's definition of D as a uniquely
  constrained witness. The actual inclusion `D.val` is injective, so this is not an
  arbitrary map or an existentially chosen substitute for a canonical minor.
  In a nonarchimedean field, natural-number multipliers have norm at most one;
  derivatives therefore preserve the restricted condition, and finite determinants
  also lie in the subring. Thus this way of spelling out D adds no mathematical
  hypothesis or independent conclusion. It avoids inventing a second derivative
  construction or introducing a separate untracked closure theorem.
- The final clause
  `Ideal.Quotient.mk I a * Ideal.Quotient.mk I D ∉ m` is exactly the product of
  the two barred elements outside the maximal ideal.
- The witness sizes are allowed to vary with m; no dimension or equidimensionality
  condition is present. For empty E and U, `Matrix.det` is one, and the image of
  the empty set spans the zero ideal. These are inherited conventions, not extra
  assertions added to the theorem.

Dependency declarations read and used:

- `def-weil-regular-scheme`: its recorded module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` and full definition were read and are
  publicly imported. The node's ring clauses are supplied by its retained
  `mathlib_match`: `IsRegularLocalRing` and `IsRegularRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs`. The latter, rather than the scheme
  predicate, is the exact clause used here. No repair is required.
- `def-weil-pbc-matrix-determinant`: `Matrix.det` in
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, publicly imported. Its Leibniz
  formula `Matrix.det_apply` and empty-matrix convention were read.
- The other public imports provide exactly the existing restricted-series subring,
  termwise derivative, increasing enumeration, and perfect-field predicate. No private
  notation, private abbreviation, implicit universe, or auto-bound variable is used.

All currently recorded proof-dependency modules are imported without `public`:
`Mathlib.RingTheory.Localization.AtPrime.Basic` (`Localization.AtPrime`),
`Mathlib.Algebra.Module.LocalizedModule.Basic` (`LocalizedModule`),
`Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison`
(`RestrictedSeries.affinoid_polynomial_closed_point_comparison`),
`WeilConjectures.LinearAlgebra.NonzeroMaximalMinorOfInjective`
(`Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective`),
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`Mathlib.RingTheory.AdicCompletion.LocalRing`
(`AdicCompletion.residueField_map_bijective`),
`Mathlib.RingTheory.Localization.Submodule` (`IsLocalization.isNoetherianRing`),
`Mathlib.RingTheory.LocalRing.Module` (`IsLocalRing.map_mkQ_eq_top`),
`Mathlib.RingTheory.Jacobson.Ring` (`finite_of_finite_type_of_isJacobsonRing`), and
`Mathlib.LinearAlgebra.LinearIndependent.Lemmas` (`exists_linearIndependent'`).
The regular-ring and determinant proof dependencies are already public statement
imports. `lem-per-separable-regular-affinoid-residual-conormal` has no Lean record
in the read repository, so it has no import; it is a proof-only dependency, absent
from this theorem's signature. Its role is explicitly retained in the proof docstring.
No statement dependency is missing, and no proof-only node is restated here.

Edge cases checked before writing:

- B = 0: the zero ring has no maximal ideals; the universal maximal-ideal assertion
  is vacuous. There is no nontriviality assumption on the quotient.
- s = 0 or I = 0: take E = U = ∅, a = D = 1. Colon membership then says a0 ⊆ 0.
- r = 0: T is the field of constant series. A nonzero quotient is F, the ideal is
  zero, and the empty minor works. A zero quotient is covered as above.
- Empty determinant: its indexing type is `Fin 0`, so it is one, not zero.
- Redundant equations or more equations than variables are permitted. Only the
  selected subsets must have equal cardinalities.
- Perfect fields of positive characteristic and complete fields with nondiscrete
  value group remain allowed. No invertibility of any natural-number coefficient
  was assumed.
- Arbitrary universe u is retained, with finite index types independent of u.

Searches (all through the prescribed wrappers or read-only source searches):

- `msearch.py ... leanfinder`: query “Every regular affinoid algebra over a perfect
  complete nonarchimedean field admits at each maximal ideal a nonvanishing Jacobian
  minor and colon ideal certificate”. Eight hits, led by
  `Algebra.SubmersivePresentation.jacobian_isUnit` and
  `Algebra.PreSubmersivePresentation.isUnit_jacobian_of_linearIndependent_of_span_eq_top`.
  These concern polynomial algebraic presentations, not restricted series.
- `msearch.py ... loogle`: query `"jacobian", "IsRegularRing"`; zero hits.
- `msearch.py ... grep`: query `IsRestricted|TateAlgebra|affinoid`, subdirectory
  `RingTheory`; ten hits, including the existing restricted-series subring. No theorem
  matching the requested analytic criterion.
- `msearch.py ... leansearch`: query “A regular affinoid algebra over a perfect
  complete nonarchimedean field has nonvanishing local Jacobian minors”. Eight hits,
  again polynomial submersive presentations or ordinary formal smoothness, not this
  statement.
- Read-only `rg` on `lean/WeilConjectures` for `IsRestricted|TateAlgebra|affinoid`
  and the item's ID found no existing analytic chart theorem. Searches for
  `local.*jacobian.*chart|perfect.*affinoid` in `lean/Sheaf` and
  `dag/lean_names_upstream.json` found no equivalent declaration.
- Read-only `rg` on `lean/Sheaf/RingTheory` for `RestrictedSeries|IsRestricted.subring`
  found `RestrictedSeriesPresentation` and `AffinoidPolynomialClosedPointComparison`;
  their full declarations were read and the latter is imported as a proof input.
- Read-only source search for `pderiv` in Mathlib's restricted-series and derivative
  files found the existing formal derivative and no subring derivative interface.
  The displayed equality uses that existing derivative directly.

Source check: opened the current blueprint's
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`;
this supporting analytic branch is not a separate sentence of that ancestor.
Read the actual sources at
[Temkin, pp. 19--21](https://math.huji.ac.il/~temkin/papers/Excellent_Desingularization.pdf)
and [Conrad, p. 510](https://www.numdam.org/article/AIF_1999__49_2_473_0.pdf).
They support the regularity/smoothness input and the displayed minor-and-colon
criterion. The node already spells out its general nontrivial real-valued field
hypotheses; no discreteness or characteristic restriction was imported from Temkin's
formal-model setting. No statement dispute or node fault was found.

Validation: `scompile.py Q133 lem-per-perfect-affinoid-local-jacobian-chart <module>`
compiled both the sandbox and actual library module (11.7 s and 8.0 s), without errors
or unexpected warnings. Every binder and universe is explicit, with both automatic
implicit options disabled. The proof is postponed, as required for stage 2.

## Second reading by Q133

Reread the original node together with the final theorem. This is an in-session
second pass, not a claim of an independent worker review: the dispatcher brief
explicitly forbids starting other agents, and the maintainer reviews the delivery
independently. The check matched the field/norm/completeness/nontriviality/perfectness
binders; the literal restricted subring and quotient by the given equations;
Noetherian regularity; the arbitrary maximal ideal; both finite subsets, increasing
orders and common size; full colon membership; the termwise minor; and the product
outside m. In particular, `D.val = ...` uniquely specifies the minor and does not
ask for an arbitrary Jacobian-like map. Zero relations and variables use `Fin 0`
and the determinant of the empty matrix. The proof docstring retains all seven DAG
steps and explains the restrictedness needed for the explicit determinant witness.
No mathematical mismatch was found and no node statement was changed. A cosmetic
leading space in the final proof-docstring paragraph was removed.

## Worker report

The module `Sheaf.AlgebraicGeometry.GradedCoordinatePolynomialDegreeEmptiness`
states `AlgebraicGeometry.coordinateQuotient_polynomial_degree_emptiness`.
Its only theorem has proof `sorry`; no definitions or auxiliary theorems are added.
The original node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- A field k: `{k : Type u} [Field k]`, with arbitrary explicitly declared universe u.
- n >= 0: `(n : ℕ)`. The n+1 variables are `ULift.{u} (Fin (n + 1))`,
  exactly the indexing type of the recorded coordinate quotient interface.
  ULift only changes universe, preserving all n+1 coordinates.
- J homogeneous for total degree with degree-one variables: the binder is
  `@HomogeneousIdeal _ _ _ _ _ _ (MvPolynomial.homogeneousSubmodule
  (ULift.{u} (Fin (n + 1))) k) _ _ MvPolynomial.gradedAlgebra`.
  The explicit final argument supplies Mathlib's canonical total-degree grading;
  it is not an additional structure or hypothesis. Underscores are inferred
  parameters/instances, not auto-bound variables or postponed data.
- A = B/J and A_d its induced quotient pieces: `coordinateQuotientPiece J d`
  is the recorded actual image submodule inside `MvPolynomial ... k ⧸ J.toIdeal`.
  Its recorded `coordinateQuotientGrading` supplies the unique induced grading.
- X = Proj(A): `Proj (coordinateQuotientPiece J)`, using the actual quotient,
  not a saturation, reduced ring, or arbitrary isomorphic scheme.
- Rational Q and nonnegative d0: `(Q : Polynomial ℚ) (d₀ : ℕ)`.
- Eventual equality: `hQ : ∀ d : ℕ, d₀ ≤ d → Q.eval (d : ℚ) =
  (Module.finrank k (coordinateQuotientPiece J d) : ℚ)`.
  The node's integers d >= d0 >= 0 are exactly these natural indices.
  Each piece is finite dimensional because it is the image of the finite-dimensional
  degree-d homogeneous polynomial submodule; this requires no extra hypothesis.
- Both bounds for every d >= d0: first conjunction, with `0 ≤ Q.eval (d : ℚ)`
  and `Q.eval (d : ℚ) ≤ (Nat.choose (d + n) n : ℚ)`.
- Conditional positivity and degree bound: `Q ≠ 0 →
  0 < Q.leadingCoeff ∧ Q.natDegree ≤ n`. For nonzero Q, natDegree is its degree.
- Q=0 iff a zero tail: the third conjunct is `Q = 0 ↔ ∃ D : ℕ,
  ∀ d : ℕ, D ≤ d → coordinateQuotientPiece J d = ⊥`.
  A submodule equals bottom exactly when its vector space is zero.
- Zero tail iff X empty: the final conjunct identifies the same existential
  condition with `IsEmpty (Proj (coordinateQuotientPiece J))`.
  Together the two iff clauses state equivalence of all three conditions.
- No reducedness, saturation, proper-ideal, or quotient nontriviality assumption.
  There is no new conclusion beyond the original node.

Dependency declarations read and used:

- `Field` from `Mathlib.Algebra.Field.Defs` (def-weil-field).
- `AlgebraicGeometry.coordinateQuotientPiece` and the instance
  `AlgebraicGeometry.coordinateQuotientGrading`, module
  `Sheaf.RingTheory.CoordinateQuotientGrading`
  (def-sfb-coordinate-quotient-grading). Its image construction and the
  uniqueness/compatibility declarations were read in full.
- `AlgebraicGeometry.Proj` and `AlgebraicGeometry.projIsoSpec` in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`, and
  `ProjectiveSpectrum.basicOpen` in `.Topology` (def-pc-proj).
  The recorded upstream `Proj.isAffineOpen_basicOpen_and_nonempty_iso` was
  also read; the node's exact Mathlib Proj interface suffices here.
- `MvPolynomial`, `.aeval`, `.algHom_ext` from
  `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`
  (def-weil-pbc-mv-polynomial-ring), available through the grading import.
- `Module.finrank`, `Mathlib.LinearAlgebra.Dimension.Finrank`
  (def-weil-vector-space-dimension), used for the dimension hypothesis.
- `Polynomial`, `.natDegree`, `.leadingCoeff`, `.eval` from
  `Mathlib.Algebra.Polynomial.Basic`, `.Degree.Defs`, `.Eval.Defs`
  (def-weil-polynomial-ring).
- Proof input `Polynomial.isEquivalent_atTop_lead`,
  `Mathlib.Analysis.Polynomial.Basic`
  (lem-sfb-polynomial-leading-term-asymptotic).
- Proof inputs `PrimeSpectrum.zeroLocus_eq_iff`,
  `Mathlib.RingTheory.Spectrum.Prime.Topology`, and `Ideal.radical_eq_sInf`,
  `Mathlib.RingTheory.Ideal.Operations`
  (lem-weil-pbc-zero-locus-eq-iff-radical-eq).
- Proof input `HomogeneousLocalization.Away`,
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`
  (def-nagata-homogeneous-localization-degree-zero).
- Proof input `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`
  (def-weil-ring-localization-away).

All stated proof dependencies are imported, directly or through the public
statement imports. Imports used only for the future proof are non-public.
The theorem docstring includes all six proof steps and their dependency IDs.

Sources read: `literature/stacks-project/varieties.tex`, the Hilbert polynomial
lemma (08AC), definition (08AD), and ensuing monomial count; the standard Proj
chart declaration and localization interfaces cited above. The node explicitly
identifies its growth/nilpotence proof as agent-written, rather than attributing
the full assertion to the Stacks Hilbert polynomial lemma.

Edge cases checked before writing:

- n=0: B=k[z], the monomial upper bound is 1. For J=0, Q=1; for J=(z^e),
  e>0, Q=0 and the tail vanishes at e, while Proj is empty.
- J=B: all image pieces are bottom, Q must be zero, and Proj of the zero
  ring is empty. No Field or Nontrivial instance is requested on the quotient.
- J=0: Q(d)=choose (d+n) n, with positive leading coefficient and degree n.
- d=0 and d0=0: the upper bound is 1 and the actual degree-zero piece is
  retained, without shifting the eventual equality.
- Q=0: positivity/degree is conditional, while both vanishing equivalences
  remain meaningful. Nonzero constant Q has natDegree 0.
- Nilpotent/nonsaturated ideals: k[z]/(z^e) shows that a zero tail need not
  start at degree zero. The existential D accommodates this.
- Arbitrary field characteristic: rational values represent integer dimensions;
  no map ℚ → k, algebraic closedness, or characteristic-zero hypothesis occurs.

Searches for an existing exact statement:

- msearch leanfinder: "An eventual Hilbert polynomial of a homogeneous polynomial
  quotient over a field has degree at most n, positive leading coefficient when
  nonzero, and is zero exactly when Proj is empty". Eight hits: basic Proj,
  homogeneous localization, Polynomial.hilbertPoly and its degree formula,
  unrelated Chevalley degree bounds. None states the quotient/Proj equivalence
  together with every numerical clause.
- msearch loogle: `"ProjectiveSpectrum", "IsEmpty"`. No hits; service reported
  "Loogle is currently under load, please try again later." Semantic and local
  searches succeeded independently.
- msearch leansearch: "An eventual dimension polynomial for a homogeneous quotient
  of k in n plus one variables has positive leading coefficient, degree at most n,
  and is zero if and only if its Proj is empty". Eight hits on AdjoinRoot dimension,
  homogenization and elementary degree facts; no exact match.
- msearch grep: `hilbertPoly|natDegree|isEmpty`, directory
  `RingTheory/GradedAlgebra`: zero hits.
- rg over `lean/WeilConjectures` and `lean/Sheaf`:
  `lem-sfb-graded-coordinate-polynomial-degree-emptiness|hilbertPoly|hilbertPolynomial|coordinateQuotient|polynomial_degree_emptiness`.
  The quotient pieces already exist. ProjectiveCoordinateRingEulerPolynomial
  proves eventual equality with an Euler polynomial and one empty-Proj
  implication; FlatProjectiveHilbertPolynomialLocality concerns scheme families;
  StandardGradedHilbertFunction gives polynomial existence. None is this full
  statement. No upstream occurrence of the item's ID or chosen declaration name.
- rg in `dag/lean_names_upstream.json`: the chosen declaration name and item ID
  are absent. No duplicate definition is introduced.

No statement dispute, dependency repair, or new node is needed.

Validation: scompile.py compiled both its sandbox and actual library-module
contexts without errors or warnings (5.5 s and 5.9 s respectively).

## Second reading by Q76

A second pass reopened the node and the complete module, comparing all binders
and all four conjuncts with the original statement. It checked that n indexes
n+1 variables, that the original quotient pieces and quotient grading are used,
that hQ is an equality in ℚ at every natural d>=d0, and that the first bounds
retain that same d0. The positivity and natDegree conclusion is guarded by Q≠0.
The zero-tail existential appears identically on both sides of the two adjacent
iff clauses, so these give all three equivalences. Bottom is used for a zero
submodule, and IsEmpty for the point type of the actual scheme. No unit-ideal
case or nilpotent case is lost. The explicit canonical grading argument avoids
file-local instances and adds no assumption. No mathematical mismatch was found;
a leading space in the proof docstring was removed. This is a same-worker
second pass; the maintainer's independent delivery review remains separate,
as required by the dispatcher workflow that forbids starting other agents.

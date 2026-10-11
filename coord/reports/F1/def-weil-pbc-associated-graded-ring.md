## Worker report

The module defines `Ideal.associatedGradedPiece J n` as the quotient module
`J^n / J^(n+1)` and `Ideal.associatedGraded J` as its direct sum over `n : ℕ`.
The commutative ring and `A/J`-algebra structures are chosen from the named
existence theorems `exists_associatedGraded_commRing` and
`exists_associatedGraded_algebra`. Their proofs alone are `sorry`; the structure
definitions themselves contain no `sorry`. The node's pointer
`lem-weil-pbc-associated-graded-ring-structure` covers the postponed proofs.

Statement correspondence:

- `A : Type u` with `[CommRing A]` and `J : Ideal A` are precisely the ambient
  commutative ring and ideal. Mathlib's ideal powers give `J^0`, `J^(n+1)`.
- `associatedGradedPiece` uses `Submodule.comap (J^n).subtype (J^(n+1))` as the
  submodule of `J^n` represented by `J^(n+1)`. Its elements are quotient classes
  of representatives `a : J^n`, with `Submodule.Quotient.mk a` the class.
- `associatedGraded` is `⨁ n : ℕ, associatedGradedPiece J n`. `DirectSum.of`
  gives the canonical inclusion, `x n` the degree `n` component, and finite
  support is intrinsic to Mathlib's `DirectSum`.
- The ring existence theorem specifies the unit as the degree-zero class of
  `1` and specifies homogeneous multiplication as the degree-`n+m` class of
  `a*b`. The `CommRing` laws imply biadditivity and the finite convolution
  formula for arbitrary sums.
- The algebra existence theorem specifies `(a mod J) • (x mod J^(n+1))` as
  `a*x mod J^(n+1)`. Its `Algebra` structure is through the degree-zero map;
  the injectivity and ring-hom assertion is postponed to the pointer node.
- `IsHomogeneousAssociatedGraded J b` requires every `DirectSum.of ... n (x n)`
  to belong to `b` whenever `x ∈ b`, exactly the homogeneous-component clause.

Dependency declarations: `Ideal` and ideal powers, `Ideal.Quotient.mk`, and the
quotient algebra from Mathlib's `RingTheory.Ideal.Quotient.Operations`
(`def-weil-pbc-algebra-hom-quotient`); `Submodule.hasQuotient`,
`Submodule.Quotient.mk`, and `Submodule.comap` from Mathlib's
`LinearAlgebra.Quotient.Defs` and submodule API
(`def-weil-pbc-quotient-module`); `DirectSum`, `DirectSum.of`, and the direct
sum additive structure from Mathlib's `Algebra.DirectSum.Basic` and `Ring`
(`def-weil-pbc-direct-sum-modules`).

Edge cases checked: `n = 0` gives `A/J`; `J = 0` leaves only degree zero;
`J = ⊤` gives the zero ring with `1 = 0`; no index truncation is imposed, and
`ℕ` includes zero. `A = 0` is admitted by `[CommRing A]`. The construction does
not assume a field or a characteristic.

Searches: `msearch leanfinder "associated graded ring of a commutative ring
with respect to an ideal, direct sum of ideal powers quotients"` found only
general filtrations, internal gradings, and homogeneous ideals; no exact
definition. `msearch loogle "associatedGraded, AssociatedGraded, gr"` returned
no hit for `associatedGraded`. `msearch grep
"AssociatedGraded|associatedGraded|GradedPiece|gradedPiece" RingTheory`
returned no hit. `rg` of the source `WeilConjectures` and this repository's
`lean/Sheaf` found only prose references, no declaration. `grep -rn` for the
node ID in source Lean found none. The Stacks `.tex` files are absent from this
machine's literature checkout; the node's recorded excerpts and references
to Algebra 05GH/00JM and Artin 07XA supplied the source text.

Server compilation: clean, no warning.

## Second reading by F1

I read the node and the proposed Lean independently, then Stacks Algebra 05GH
(the proof's paragraph beginning with the polynomial surjection), Algebra 00JM
(the homogeneous-ideal criterion), and Artin approximation 07XA. The ambient
Noetherian and finite-generation assumptions in 05GH serve its completion
lemma; the construction of its associated graded ring uses any commutative
ring and ideal. The node correctly carries neither assumption.

Object and clause correspondence:

- Ambient commutative ring and ideal: `{A : Type u} [CommRing A]` and
  `J : Ideal A`. Verdict: exact; no field, characteristic, finiteness, or
  Noetherian condition.
- Powers and quotient pieces: `J ^ n`, `J ^ (n + 1)` and
  `associatedGradedPiece J n`, a `Submodule.Quotient` of `J ^ n` by the
  pullback of `J ^ (n + 1)` under its subtype map. `Submodule.Quotient.mk`
  gives the specified representative classes. Verdict: exact, using the
  Mathlib quotient-module and ideal-power dependencies; at degree zero this
  is canonically `A/J` as an additive group (not a definitional equality of
  Lean types).
- Direct sum, inclusions, components, finite support: `associatedGraded J`
  is `⨁ n : ℕ, associatedGradedPiece J n`; `DirectSum.of` is the inclusion,
  and `x n` is the component. Mathlib's `DirectSum` is finitely supported.
  Verdict: exact, using the recorded direct-sum dependency.
- Multiplication, biadditivity, and unit: the witness in
  `exists_associatedGraded_commRing` is required to preserve the direct sum's
  addition and zero, to have the specified degree-zero unit, and to multiply
  every pair of homogeneous representative classes by the stated product
  class. Ring distributivity and finite support then give exactly the node's
  convolution formula for arbitrary elements and biadditivity. Verdict:
  exact after the repair below; the proof remains `sorry`, as required here.
- Degree-zero algebra: `associatedGradedAlgebra J` is an `Algebra (A ⧸ J)`
  on the graded ring. `exists_associatedGraded_algebra` fixes scalar action
  on every homogeneous representative. At `n = 0`, its action on the unit,
  together with `Algebra.smul_def'`, fixes the algebra map as the inclusion
  of the degree-zero quotient; `associatedGraded_one` and
  `associatedGraded_smul` state the same facts separately. The injectivity
  claim belongs to pointer `lem-weil-pbc-associated-graded-ring-structure`.
  Verdict: exact, using Mathlib's quotient-algebra dependency.
- Homogeneous ideal: `IsHomogeneousAssociatedGraded J b` requires the
  inclusion of `x n` to lie in `b` for every `x ∈ b` and every `n`.
  Verdict: exact match to Algebra 00JM and to the node.

Edge cases: `ℕ` includes `n = 0`; `J = ⊥` has only degree zero, `J = ⊤`
gives the zero ring, and the zero ring `A` is admitted. No index set other
than `ℕ`, scheme, or characteristic condition occurs. `A : Type u` with a
bound universe admits rings in every universe. The ideal, quotient, and
direct-sum dependency nodes have the recorded Mathlib signatures; none
adds a hypothesis here.

Independent searches: `msearch leanfinder "associated graded algebra ideal
filtration quotient direct sum ring"` found filtration and graded-ring APIs,
but no ideal-power quotient construction; `msearch loogle "associatedGraded,
associated graded, gr"` returned no declaration; `msearch grep
"associated.graded|AssociatedGraded|gradedPiece"` found only an unrelated
bicomplex comment. `rg -i` over source `WeilConjectures`, the repository's
`lean/Sheaf`, and Mathlib's filtration files found only prose mentions and
no definition. The existing Mathlib `Ideal.IsHomogeneous` concerns a given
internal grading, not this newly constructed ring.

Mismatch repaired: the first version of `exists_associatedGraded_commRing`
fixed the unit and homogeneous multiplication but allowed its chosen
`CommRing` witness to have a different addition or zero. That did not say
that the ring was built on the node's direct-sum abelian group. I added
equalities for `s.add` and `s.zero` against the existing `DirectSum`
operations and updated its docstring. No other mismatch was found. The
main `associatedGraded` signature recorded in the node is unchanged.

## Reviewer fix by R-agr0615

The delivered `associatedGradedCommRing` and `associatedGradedAlgebra` were
`Classical.choose` of sorry'd existence theorems. Since `associatedGraded` is an
`abbrev` for the direct sum, this created an instance diamond: `x + y` on
`associatedGraded J` elaborated with the chosen ring's addition, which is only
propositionally equal to the direct sum's (`DirectSum.add_apply` failed to
typecheck against it). The multiplication was also not real data. Rewritten:
`μ_{n,m}` is `associatedGradedMul`, the bilinear map `ab mod J^(n+m+1)`
descended with `LinearMap.liftQ₂` (the two kernel inclusions are named sorry
theorems); `associatedGradedGCommRing` is a `DirectSum.GCommRing` instance whose
unit-, associativity- and commutativity-laws are named sorry theorems (the
additivity laws come from bilinearity, the cast laws are proved inline); the
ring is Mathlib's `DirectSum.commRing`, so addition, zero and unit are the
direct sum's by definition. The `A/J`-algebra is `RingHom.toAlgebra` of
`Ideal.Quotient.lift` of the real ring map `a ↦ ι_0(a mod J)`
(`associatedGradedRingHom`, its multiplicativity and its vanishing on `J` named
sorry theorems). `associatedGraded_one`, `associatedGraded_mul`,
`associatedGraded_smul` and `IsHomogeneousAssociatedGraded` are unchanged.
Mathlib (this version) has no associated graded ring: only `Ideal.Filtration`
and `IsRingFiltration` classes.

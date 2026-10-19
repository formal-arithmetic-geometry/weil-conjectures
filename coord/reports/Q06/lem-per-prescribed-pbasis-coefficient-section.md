## Worker report

This delivery states `IsLocalRing.existsUnique_coefficientSection_prescribed_pBasis`
in `Sheaf.RingTheory.PrescribedPBasisCoefficientSection`. Its sole proof is `sorry`.
No definition, helper theorem, new node or dependency repair is needed. The node is
changed only in `lean`.

The former worker's stale-assignment diagnosis confused stages: Q23's PASS is the
stage-1 split review. The current node has status `split`, with no `lean` record and
no `reviewed_lean`. Writing its first Lean statement is the assigned stage-2 work;
this delivery preserves its statement, split, proof, and stage-1 review verbatim.
The retained sandbox initially held only dispatcher markers, with no delivery to repeat.

Source read: Illusie–Laszlo–Orgogozo, Travaux de Gabber, arXiv 1207.3648, Expose IV
2.1.4, printed p.50 (PDF page 56). It states uniqueness of the coefficient field
containing arbitrary lifts of the residue p-basis. A coefficient field determines
one section by the inverse of its residue isomorphism; conversely a section's image
is such a coefficient field. Thus the node's section formulation is equivalent.
The theorem docstring contains all six steps of the node's Frobenius-expansion proof,
including carry calculations, arbitrary-lift compatibility and uniqueness by separatedness.

Hypotheses and clauses, matched to Lean:

- A prime number p: `(p : ℕ) [Fact p.Prime]`. Positive characteristic is `[CharP A p]`;
  primality excludes p = 0, p = 1 and composite p.
- A nonzero local commutative ring: `(A : Type u) [CommRing A] [IsLocalRing A]`.
  Mathlib's `IsLocalRing` extends `Nontrivial`, so nonzero is included without a
  redundant binder (the compiler's overlapping-instance warning confirmed this).
- Noetherian: `[IsNoetherianRing A]`, exactly the recorded dependency declaration.
- Complete for its maximal ideal: `[IsAdicComplete (maximalIdeal A) A]`, including
  separatedness, exactly the recorded completeness dependency declaration.
- The residue field k = A/m: `IsLocalRing.ResidueField A`, whose definition is that
  literal quotient, with its canonical field instance; the residue map is `residue A`.
- Any index set and p-basis `(b_i)`: `(E : Type v) (b : E → ResidueField A)` and `hpb`.
  The exponent subtype `{e : E →₀ ℕ // ∀ i : E, e i < p}` imposes finite support and
  every exponent bound. `Module.Basis` gives linear independence and spanning.
  Its scalar field is `Subfield.closure (Set.range (fun x : ResidueField A ↦ x ^ p))`.
  In the residue field of a characteristic-p local ring, pth powers are already a
  subfield: additivity is Frobenius, multiplication and inverses commute with pth
  powers. Therefore this closure is exactly the node's k^p, not a larger field.
  `∀ e, mon e = e.val.prod (fun i n ↦ b i ^ n)` identifies each basis vector with
  the stated bounded monomial. The existential basis supplies no extra mathematical
  assumption beyond the node's inline definition of p-basis.
- Arbitrarily chosen lifts: `(beta : E → A)` with
  `hlift : ∀ i : E, residue A (beta i) = b i`. There is no assumption that they
  lie in any pre-existing coefficient field.
- A unique field homomorphism: `∃! s : ResidueField A →+* A` with both properties
  in the same predicate, so uniqueness ranges over all sections with prescribed values.
  Mathlib uses unital ring homomorphisms for a field embedding into a ring; each is
  injective here since the target is nonzero, also directly because it is a section.
- Residue composite is the identity:
  `(residue A).comp s = RingHom.id (ResidueField A)`.
- All prescribed values: `∀ i : E, s (b i) = beta i`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, abbreviation for
  `IsNoetherian A A`; its docstring says every ideal is finitely generated.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, extending
  `IsHausdorff` and `IsPrecomplete`; `AdicCompletion.of_bijective_iff` identifies
  this with the node's bijective canonical map to the inverse limit.
- Proof dependency `def-weil-ring-frobenius`: imported privately through
  `Mathlib.Algebra.CharP.Frobenius`; this gives the Frobenius identities named
  in the proof plan, not an extra hypothesis or a postponed helper theorem.
- `Mathlib.RingTheory.LocalRing.ResidueField.Defs`: `ResidueField` and `residue`.
  `Mathlib.LinearAlgebra.Basis.Defs`, `Mathlib.Algebra.BigOperators.Finsupp.Basic`
  and `Mathlib.Algebra.Field.Subfield.Basic` provide the inline monomial condition.

Edge cases checked before writing:

- Empty E: the only finitely supported exponent is zero, with monomial 1. The
  p-basis assumption then says k = k^p. Prescribed values are vacuous and the
  theorem asserts the expected unique coefficient section for a perfect residue field.
- Infinite E: no `Finite`, `Fintype` or `Nonempty` binder; all monomials have finite
  support. Independent universes u and v impose no size restriction on indexing.
- A itself a field: maximal ideal is zero and completeness is automatic. The
  residue map is an isomorphism and the section is its inverse; every lift is forced.
- Nilpotents are allowed: for F_p(u)[epsilon]/epsilon², a lift u + epsilon is
  permitted and determines its own coefficient field. No reduced/domain assumption.
- F_p(u)[[t]] with lift u + t: arbitrary lifts are retained. Perfect residue fields
  and the prime field are included; mixed characteristic and the zero ring are
  excluded exactly by the given hypotheses.

Searches for an existing statement (all msearch searches are retained in searches.jsonl):

- LeanFinder, `complete Noetherian local ring unique coefficient field prescribed
  p-basis lifts`: eight hits on PreTilt, perfection and henselian rings, none states
  this prescribed section theorem.
- Loogle, `CoefficientField, pBasis, IsAdicComplete`: no hits, unknown
  `CoefficientField` identifier.
- msearch grep, `pBasis|p_basis|p-basis|CoefficientField` in Mathlib/FieldTheory:
  nine unrelated galGroupBasis and linear-disjointness hits.
- LeanSearch, `unique coefficient section of complete local ring with prescribed
  residue p-basis lifts`: eight hits, including residue-field lifts, lifted module
  bases and p-adic universal maps; none lifts a residue field into A with prescribed
  p-basis values. `IsLocalRing.ResidueField.lift` goes from a quotient to another
  field from a supplied map; it does not construct this section.
- rg on Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `existsUnique_coefficientSection_prescribed_pBasis` found no existing declaration.
- rg on upstream WeilConjectures and project lean/Sheaf for the item id found no
  existing statement. Searches for pBasis/p-basis inspected ExistsPBasis,
  PBasisDifferentialsBasis and PBasisComplementMonomialBasis: they state existence,
  differential bases or complementary monomial bases, not a coefficient section.
  Their p-basis conditions likewise use an inline bounded-monomial basis, so this
  delivery introduces no second definition of p-basis.

No disputed statement or source-based correction is needed. The first compilation
exposed module visibility for CharP and Nat.Prime; a public CharP import fixes it.
The next compilation identified a redundant Nontrivial binder, which was removed.
Final validation is through scompile.py and the prescribed deliver2.py preflight.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

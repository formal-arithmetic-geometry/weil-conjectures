## Worker report

The module `Sheaf.TraceFormula.SeparableResidueCoefficientSection` states
`Algebra.exists_separable_residueField_section`, the coefficient-field section in
Stacks Tag 0C34. It uses Mathlib's canonical local-ring residue field
`IsLocalRing.ResidueField R` and residue map `IsLocalRing.residue R`; no private
notion is introduced. The declaration has the following direct rendering of the
node's hypotheses and conclusion:

- `k : Type u` with `[Field k]` is the base field.
- `R : Type v` with `[CommRing R]` and `[Algebra k R]` is the commutative local
  `k`-algebra.
- `[IsLocalRing R]` supplies the maximal ideal and local-ring structure.
- `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]` is completeness for the
  maximal-ideal adic topology.
- `[Algebra.IsSeparable k (IsLocalRing.ResidueField R)]` renders the separable
  algebraic residue-field hypothesis, using Mathlib's `Algebra.IsSeparable`.
- The conclusion `∃ σ : IsLocalRing.ResidueField R →ₐ[k] R` is a `k`-algebra
  map from the residue field to `R`, and
  `(IsLocalRing.residue R).comp σ.toRingHom =
  RingHom.id (IsLocalRing.ResidueField R)` says its composite with the canonical
  quotient map is the identity on the residue field.

The proof is deliberately `sorry`, as required for stage 2. The module imports
`Mathlib.FieldTheory.Separable`, `Mathlib.RingTheory.AdicCompletion.Basic`, and
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`; these provide
`Algebra.IsSeparable`, `IsAdicComplete`, `IsLocalRing.ResidueField`, and
`IsLocalRing.residue`, respectively. The statement uses the two recorded
statement dependencies: `def-weil-pbc-adically-complete-ring` via Mathlib
`IsAdicComplete`, and `def-weil-pbc-separable-algebraic-extension` via Mathlib
`Algebra.IsSeparable`.

I checked the edge cases `R = k` (the identity section), a power-series example
`R = k[[t]]` (constant-coefficient section), and the inseparable-residue case,
where the separability hypothesis correctly does not apply. The empty and zero
ring cases are excluded exactly as Mathlib's `Field` and `IsLocalRing` require;
no extra finiteness hypothesis is introduced.

Searches for an existing declaration were made before writing the module:

- `msearch.py ... leanfinder "A complete local k-algebra with separable residue
  field has a k-algebra section"`: found formal-unramified residue-field
  declarations but no coefficient-section theorem.
- `msearch.py ... loogle "IsSeparable, IsAdicComplete, IsLocalRing, Algebra"`:
  no matching lifting theorem.
- `msearch.py ... grep "lift-residue-field|coefficient.*section"` in
  Mathlib: no match.
- `rg` over `WeilConjectures/` and the side `lean/Sheaf/` tree for residue
  coefficient sections: no declaration of this node.
- The DAG search for `lem-trf-separable-residue-coefficient-section` found only
  this node; the prior Q90 stage-1 delivery had no Lean module and therefore did
  not provide a declaration to reuse.

The module compiles cleanly with `scompile.py`; the only expected diagnostic is
none beyond the postponed `sorry` declaration.

## Second reading by N2

Maintainer independent second reading of the immutable delivery, 2026-10-18.
The original delivery explicitly disclaimed a second reading; this replacement
records the independent reading performed in the maintainer review.

I read Stacks More on Algebra Tag 0C34, `lemma-lift-residue-field`, including its
proof, and both statement-dependency records and their exact Mathlib declarations.
The node specifies the separable algebraic specialization of the source through
its cited separability definition; the Lean does exactly that.

- The field `k : Type u` is `[Field k]`.
- The local commutative `k`-algebra is `R : Type v`, `[CommRing R]`,
  `[Algebra k R]`, `[IsLocalRing R]`.
- Maximal-ideal completeness is
  `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`, including separatedness.
- The canonical quotient field is `IsLocalRing.ResidueField R`, with its
  induced `k`-algebra structure. `Algebra.IsSeparable` includes algebraicity;
  neither finiteness nor a Noetherian hypothesis is added.
- The existential algebra homomorphism has exactly domain the residue field
  and codomain `R`. Equality of its composite with `IsLocalRing.residue R`
  to `RingHom.id` is precisely the required identity composite.

The universes `u v` are independent and explicitly bound. The identity case
`R = k`, zero maximal ideal, arbitrary characteristic, and infinite separable
algebraic residue extensions are covered. The zero ring is excluded by the
source's local-ring convention and by Mathlib's `IsLocalRing`; there is no
index-set or scheme edge case in this ring statement.

I read the formal-smooth-adic definition and the complete-target lifting theorem
in the group clone, and the Mathlib square-zero lifting declarations
`Algebra.FormallyEtale.of_isSeparable` and `Algebra.FormallyEtale.comp_bijective`.
The first node step takes source ideal zero, so every positive power is zero.
The second takes both target ideals to be the maximal ideal, with exponents
one, closedness by `m + m^r = m`, and the identity quotient map; the required
image containment is of the zero source ideal. These give the stated section.

Independent `rg` searches in Mathlib, upstream `WeilConjectures`, and side
`lean/Sheaf` for coefficient fields, residue sections, residue lifts, the node
id, and declaration name found no duplicate theorem. The worker report also
records LeanSearch, LeanFinder, and Loogle searches. No new definition or
unusable statement dependency was found; no helper or universe repair is needed.

Findings repaired in the complete replacement module: H8, expand the proof
into its two steps with node citations; H9, import the already available proof
dependency modules, including the Mathlib field lifting interface. H11 is
repaired by this actual reading record. Both source/blueprint docstrings are
present. The sole theorem proof remains `sorry`, and there is no definition.
The signature and node record are unchanged, and the recorded statement is
verbatim equal to the declaration before `:= by`.

Compiler evidence: the immutable module compiled via `scompile.py N2
lem-trf-separable-residue-coefficient-section` with exit status zero, no
diagnostics (sandbox 1.6 s, library 1.5 s). The complete replacement module
was also compiled successfully through the same wrapper; see review.md for
the final output. No global build, direct SSH, live Lean write, or repository
edit was performed. No pro-etale or dropped route-pivot machinery occurs.

## Worker report

The module `Sheaf.RingTheory.PrimeFieldCompleteCoordinateModel` states
`IsLocalRing.exists_prime_field_complete_coordinate_model`, with `sorry` as its whole proof.
No definitions, helper nodes, dependency replacements or statement corrections are needed.
The source is Stacks Project, Algebra, Tag 0C0S (the complete regular local coefficient-field
lemma), read in `literature/stacks-project/algebra.tex`, together with the node's explicit
coefficientwise polynomial-completion formulation. The previous worker's stage-1 stale
assignment diagnosis does not apply to this stage-2 task: Q29's reviewed split has no `lean`
record. Its statement, proof and all other fields are preserved.

Hypotheses and clauses, with their exact Lean renderings:

- B is a commutative Noetherian regular local ring: `(B : Type u) [CommRing B]
  [IsRegularLocalRing B]`. Mathlib's regular-local class extends both `IsLocalRing B`
  and `IsNoetherianRing B`; separate redundant binders were removed after the compiler's
  overlapping-instance warning.
- Completeness for m: `[IsAdicComplete (maximalIdeal B) B]`, with the same ring's maximal
  ideal. No ambient topology, coefficient embedding, excellence, or smoothness is assumed.
- Contains Q or F_p for prime p: `hchar : (∃ p : ℕ, Nat.Prime p ∧ CharP B p) ∨
  ∃ ι : ℚ →+* B, Function.Injective ι`. For prime p and nontrivial B, `CharP B p`
  is equivalent to the existence of the canonical embedding F_p into B. The rational
  alternative explicitly supplies the ring embedding; it is not weakened to `CharZero B`
  (which would incorrectly include mixed-characteristic rings such as the p-adic integers).
- F = B/m is `IsLocalRing.ResidueField B`, defined in Mathlib as precisely this quotient;
  `residue B` is the quotient homomorphism. This is the local-ring construction used
  literally inside the recorded scheme-residue-field declaration, rather than a copy.
- d = dim B is `∃ (d : ℕ), ringKrullDim B = (d : WithBot ℕ∞) ∧ ...`. Existence of this
  finite d is part of the conclusion; no finite-dimension hypothesis has been added.
- The section is `σ : ResidueField B →+* B`, with
  `(residue B).comp σ = RingHom.id (ResidueField B)`. This is the right composition order:
  F goes first to B, then back to F.
- The d parameters are `t : Fin d → B`; membership in m is `∀ i, t i ∈ maximalIdeal B`.
  The explicit generation conclusion is `Ideal.span (Set.range t) = maximalIdeal B`.
- The series isomorphism is `e : MvPowerSeries (Fin d) (ResidueField B) ≃+* B`, with
  `e (MvPowerSeries.C a) = σ a` for all coefficients and `e (MvPowerSeries.X i) = t i`
  for all coordinates. Continuity is stated with `@Continuous` and the explicitly supplied
  variables-adic topology on the source and maximal-ideal-adic topology on B.
- C is `MvPolynomial (Fin d) (ResidueField B)` and I is `MvPolynomial.idealOfVars ...`,
  Mathlib's existing abbreviation for the span of its variables. The polynomial map is
  the existing `MvPolynomial.eval₂ σ t`, not an arbitrary homomorphism.
- The completion isomorphism is `ec : AdicCompletion I C ≃+* B`. Its equality to
  `(MvPowerSeries.toAdicCompletionAlgEquiv ...).toRingEquiv.symm.trans e` specifies the
  canonical coefficientwise identification followed by the same series isomorphism.
  The additional equation `ec (AdicCompletion.of I C c) = MvPolynomial.eval₂ σ t c`
  explicitly identifies its restriction to C with the prescribed polynomial map.
  Thus this clause concerns the induced map, rather than merely an abstract isomorphism.
- Coordinate preservation follows by taking c = X i in that restriction equation; taking
  c = C a gives coefficient preservation. The quotient identity is stated for every
  completion element z and polynomial representative c of `AdicCompletion.evalOneₐ I z`:
  `residue B (ec z) = MvPolynomial.constantCoeff c`. Since constant coefficient is the
  canonical identification C/I = F, this says exactly that the induced map to B/m = F
  is the identity; it is independent of the chosen representative.
- d = 0 is included: `Fin 0` is empty, `Set.range t` is empty, hence m = 0. Mathlib's
  zero-variable polynomial and series rings are canonically F and `AdicCompletion 0 F`
  is canonically F. None of the binders requires positive dimension or nonempty indices.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (inherited by regularity).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the recorded
  mathlib_match for the ring clauses of `def-weil-regular-scheme`. Its scheme module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is also imported as required; no scheme
  notion is substituted for the ring hypothesis.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `IsAdicComplete`,
  `AdicCompletion`, `AdicCompletion.of`, `AdicCompletion.evalOneₐ`.
- `Mathlib.AlgebraicGeometry.ResidueField`: the recorded `Scheme.residueField` is
  `CommRingCat.of (IsLocalRing.ResidueField (X.presheaf.stalk x))`; the underlying
  local-ring definition and quotient map come from
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs` (`ResidueField`, `residue`).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.MvPowerSeries.Basic` and `.Equiv`: `MvPowerSeries`, `C`, `X`,
  and the canonical `toAdicCompletionAlgEquiv`, read with its coefficientwise inverse.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `aeval`, `algHom_ext`,
  and `eval₂`; `.RingTheory.MvPolynomial.Ideal` supplies `idealOfVars`.

The available proof-dependency modules are imported without `public`: coefficient-subring
existence, power-series field/Cohen regular completeness, power-series universal property,
and `Mathlib.RingTheory.AdicCompletion.Functoriality` for surjectivity. Dimension bounds are
already supplied by the imported regular-local-ring API. The proof docstring describes all
six node steps, including the prime-chain injectivity argument and zero-dimensional case.

Edge cases checked by reading the mathematical statement and its types: zero-variable
field case; imperfect residue field in characteristic p; arbitrary finite d; characteristic
zero with a rational embedding; mixed characteristic excluded by the actual prime-field
hypothesis; zero ring excluded by the existing local-ring class. No universe restriction:
B is in an arbitrary explicit universe u and its residue quotient and polynomial/completion
constructions use that same universe. No hidden auto-implicit variables are enabled.

Searches (all read before selecting the statement):

- `msearch.py ... leanfinder "A complete regular local ring containing a prime field has a
  residue field section and is a power series ring and completed polynomial ring"`: eight
  hits (univariate residue-field equivalence, henselian fields, and Weierstrass results),
  none states this result for an arbitrary complete regular local ring.
- `msearch.py ... loogle '"IsRegularLocalRing", "AdicCompletion"'`: zero hits.
- `msearch.py ... grep 'Cohen|coefficient.?field|regular.*power.?series|power.?series.*regular'
  RingTheory`: only the unrelated citation in Noetherian/OfPrime.lean.
- `msearch.py ... leansearch "A complete regular local ring containing a field is isomorphic
  to a power series ring over its residue field"`: eight hits, including existing
  univariate-series local/residue lemmas and Weierstrass preparation; no arbitrary-ring
  coefficient-field isomorphism theorem.
- `rg` for the same Cohen/coefficient/regular-power-series patterns in the upstream
  `WeilConjectures` source and the side `lean/Sheaf` source: no upstream attachment to
  this node. Read side `CohenPowerSeriesPresentation` (a surjective presentation of a
  general complete local ring, allowing Cohen coefficients) and `PowerSeriesFullCoordinatesField`
  (coordinates on an already given power-series ring). Neither states the node's theorem.
  The Mathlib grep found `MvPowerSeries.toAdicCompletionAlgEquiv`; reused it rather than
  constructing a second polynomial-completion equivalence.
- Exact node-id search in upstream `WeilConjectures`: no hits.

No STATEMENT-DISPUTED flag or source discrepancy remains. Compilation via the prescribed
`scompile.py Q36 lem-per-prime-field-complete-coordinate-model <module>` passed for both
the sandbox and library-path checks, with no errors or non-sorry warnings.

## Second reading by Q36

Author's second reading against the current node and source: checked every binder and every
conjunction against the clause list above. The initial draft was repaired before delivery:
the section composition now has the correct F-to-B-to-F order; characteristic zero alone was
replaced by a rational embedding; prime p is explicit; parameter generation and actual adic
continuity are present; the completed equivalence is tied to Mathlib's canonical coefficient
map and polynomial evaluation; and the residue identity applies to every completion class.
The regular-local class already contains Noetherianity and locality, avoiding redundant
instance parameters without losing hypotheses. Read the d=0 case again: all indexed
conditions are vacuous, generation forces m=0, and the constant-coefficient equations remain.
No remaining mismatch was found. Independent review is performed by the maintainer's reader.

## Worker report

The module `Sheaf.AlgebraicGeometry.FixedResidueLiftsTruncatedSection` states
`Algebra.fixed_residue_lifts_truncated_section`, with its sole theorem proof `sorry`.
It introduces no definitions. The accepted split, statement, and all dependencies
are preserved; the only node change is its `lean` record.

The source read is Stacks Project, `literature/stacks-project/algebra.tex`,
Tag 02HT, condition (4) and the proof of (4) implies (1), particularly the
paragraphs “Let N” and “Applying condition (4)”. Condition (4) fixes the residue
field via the isomorphism induced by A. The displayed construction filters the
kernel into length-one extensions, lifts successively, extends to the localization,
and descends modulo the Nth power of its maximal ideal. The module docstring
records all five accepted proof steps, including the structural R-map and the
specified residue-field identifications throughout the downward induction.

Each hypothesis and clause has the following rendering:

- Commutative rings R and A with an R-algebra structure: `{R : Type u}`,
  `{A : Type v}`, `[CommRing R]`, `[CommRing A]`, `[Algebra R A]`.
- A prime ideal q: `(q : Ideal A) [q.IsPrime]`.
- S = A_q: `Localization.AtPrime q`; k = S/qS: `q.ResidueField`.
  Mathlib defines this as the quotient of `Localization.AtPrime q` by its
  maximal ideal, which equals qS. Its `algebraMap A q.ResidueField` is the
  composite A → S → k, with its canonical localization and quotient maps.
- A Noetherian local commutative R-algebra C: `{C : Type w}`,
  `[CommRing C]`, `[Algebra R C]`, `[IsNoetherianRing C]`, `[IsLocalRing C]`.
  The local-ring class extends `Nontrivial`, as required by unique maximality.
- The surjective R-algebra map to S: `(p : C →ₐ[R] Localization.AtPrime q)`
  and `(hp : Function.Surjective p)`.
- J = ker p and the unique maximal ideal m are rendered directly as
  `RingHom.ker p.toRingHom` and `IsLocalRing.maximalIdeal C`.
- “For every surjection of nonzero Artinian local commutative rings”: the
  `hlift` quantifier binds B', B, their `CommRing`, `IsArtinianRing`, and
  `IsLocalRing` instances, `(φ : B' →+* B)`, and `Function.Surjective φ`.
  `IsArtinianRing` is the descending-chain condition on ideals. Both local
  instances already include nontriviality; no zero-ring test is introduced.
- Kernel length one: `Module.length B' (RingHom.ker φ) = 1`, using the
  ideal as its canonical B'-submodule, with no change of scalars.
- Specified residue isomorphisms: the universally bound
  `e' : IsLocalRing.ResidueField B' ≃+* q.ResidueField` and
  `e : IsLocalRing.ResidueField B ≃+* q.ResidueField`.
- Identity of the induced residue map under those isomorphisms: the equation
  `e'.toRingHom.comp (IsLocalRing.residue B') =
  (e.toRingHom.comp (IsLocalRing.residue B)).comp φ`.
  Since both residue quotient maps are surjective, this is precisely that
  induced-map identity, expressed before passage to the quotient. A surjective
  ring map of these local rings is local, so no additional locality hypothesis
  or choice of residue map is needed.
- The arbitrary maps rho and a are `ρ : R →+* B'` and `a : A →+* B`.
- Their R-compatibility: `a.comp (algebraMap R A) = φ.comp ρ`.
- Their canonical residue composite: `(e.toRingHom.comp
  (IsLocalRing.residue B)).comp a = algebraMap A q.ResidueField`.
  This retains the actual specified residue map, rather than merely its kernel.
- Existence of the ring lift and both required equalities:
  `∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ`.
- Every positive integer N: `∀ (N : ℕ), 1 ≤ N →`; natural positive exponents
  cover exactly the integers N ≥ 1 from the statement.
- Both quotient rings and their induced R-algebra structures appear literally
  in the type of `σ`. Ideal addition is the lattice join `⊔`. The source of σ
  is C/(J + m^N); the target is C/(J² + m^N).
- The canonical quotient map is `Ideal.Quotient.factorₐ R` for the inclusion
  `sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl`.
  The conclusion `(Ideal.Quotient.factorₐ R ...).comp σ = AlgHom.id R _`
  is exactly an R-algebra section. No arbitrary comparison map is substituted.

Universes are explicitly bound, with `set_option autoImplicit false`.
R, A, and C have independent universes. The test rings range over
`Type (max u v w t)`, with t arbitrary; the intermediate C-quotients can
always be lifted to this universe. Transport by the ULift ring equivalence
preserves the residue identifications, module length, and all map equations.
Thus the test universe cannot lie below the objects needed in the proof.
There are no file-local notations, instances, auxiliary definitions, or axioms.

Dependency declarations read and used:

- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs`, `IsLocalRing.ResidueField`
  and `IsLocalRing.residue`. These are the localization and residue-field
  interfaces recorded by `def-weil-pbc-localization-at-prime`. The fibre-ring
  clause of that node is not used by this item.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` (the recorded
  declaration for `def-weil-pbc-noetherian-ring`).
- `Mathlib.RingTheory.Length`, `Module.length` (the `mathlib_match` of
  `def-weil-pbc-module-length`, which correctly has no `lean` record).
- `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Ideal.Quotient.factorₐ`;
  its domain and codomain carry exactly the quotient algebra structures.
- Proof imports: `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`;
  `WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration`,
  `RingTheory.exists_ideal_filtration_length_one`;
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`,
  `IsLocalRing.notMem_maximalIdeal`. These are precisely the recorded modules
  of the three remaining proof dependencies. Their full declarations and
  docstrings were read; none needs a repaired interface to state this item.

Edge cases checked before writing:

- N = 1: J ≤ m and J² ≤ m, so both defining ideals are m; the canonical
  quotient is the identity and admits the identity section.
- J = 0: both defining ideals are m^N; again the quotient map is the identity.
- C a field: surjectivity to the nonzero localization forces J = 0, so this
  case is included. No assumption that m or J be nonzero occurs.
- The filtration can have length zero, including K = 0. The starting map
  then gives the lift with no induction steps; this appears in the docstring.
- A zero test ring is excluded by `IsLocalRing`; a zero A cannot have a prime
  q; a zero C cannot surject onto the nonzero localization. These are exactly
  the degeneracies excluded by the mathematical hypotheses.
- Neither a residue characteristic nor finite type of A or R-Noetherianness
  is assumed or needed in this truncated-section implication.

Searches made for an existing declaration (2026-10-23):

- `msearch.py`, leanfinder, “Fixed residue field Artinian local length one
  lifting implies sections of truncated square zero quotient”: eight hits,
  including `Algebra.FormallySmooth.exists_lift`,
  `Algebra.FormallyEtale.comp_bijective`,
  `Algebra.FormallyEtale.iff_comp_bijective`,
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`,
  `Algebra.FormallySmooth.iff_comp_surjective`,
  `Algebra.Extension.toInfinitesimal`,
  `Algebra.FormallyUnramified.iff_comp_injective_of_small`, and
  `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`.
  None states the fixed-residue implication. In particular formal-smoothness
  lifting results assume formal smoothness rather than these testing hypotheses.
- `msearch.py`, loogle, `Algebra.FormallySmooth`: twelve hits, including
  formal-smoothness definitions, constructors, localization and equivalence
  invariance. None states this implication.
- `msearch.py`, grep, `fixed.residue|truncated.section`, subdirectory
  `RingTheory`: zero Mathlib hits.
- `rg -n 'fixed.residue|fixedResidue|fixed_residue|truncated.section|truncated_section'`
  in `lean/WeilConjectures` and `lean/Sheaf`: the relevant hit is
  `Algebra.artinian_lifting_truncated_section` in
  `WeilConjectures.AlgebraicGeometry.ArtinianLiftingTruncatedSection`.
  Reading its full signature shows it assumes lifts for arbitrary residue-field
  extensions, expressed by `Ideal.comap a (maximalIdeal B) = q`, without any
  required residue-field isomorphism. That hypothesis is stronger than this
  item's fixed-residue hypothesis. It cannot attach this node or be applied
  directly here. The other hits concern conormal comparisons or unrelated
  fixed residue embeddings, not this statement.
- `grep -rn 'lem-sfb-fixed-residue-lifts-truncated-section' lean/WeilConjectures`:
  no hit. A full Mathlib/project grep for the new declaration name gave no hit.

No new nodes or dependency modules are needed. No statement correction or
STATEMENT-DISPUTED flag is warranted. The stage-1 rejection inherited in the
brief does not apply: the current item is an accepted split, is queued at stage 2,
and has no Lean record; this delivery adds its missing statement only.

Validation: the module compiled cleanly with the prescribed `scompile.py` wrapper,
including both sandbox and library-name compilation. Dry-run preflight and
final delivery are performed with `deliver2.py`.

## Second reading by Q131

No second worker was started, as the dispatch brief forbids starting other
agents and directs this worker to deliver. The maintainer's independent review
reads this packet. The clause mapping above is the author's audit, not a claim
of an independent second reading.

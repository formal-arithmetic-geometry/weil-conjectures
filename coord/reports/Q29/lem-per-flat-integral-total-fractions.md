## Worker report

The module `Sheaf.RingTheory.FlatIntegralTotalFractions` states the single theorem
`flat_integral_totalFractions`, with `sorry` as its only proof. It defines no new
notion or map. The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- Reduced commutative rings A and R are `(A : Type u) (R : Type v)` with
  `[CommRing A] [CommRing R] [IsReduced A] [IsReduced R]`.
- The given ring map f is encoded by `[Algebra A R]` and its `algebraMap A R`.
  Every ring homomorphism supplies precisely such an algebra structure via
  `RingHom.toAlgebra`; this does not assume f injective or faithfully flat.
  Its flatness is the explicit hypothesis `hf : (algebraMap A R).Flat`.
- The intermediate algebra A ⊆ B ⊆ Q(A) is
  `B : Subalgebra A (FractionRing A)`. This includes the actual embedding into
  the specified total-fraction ring. Integrality is `[Algebra.IsIntegral A B]`,
  without a finite-module assumption. The inclusion of A into Q(A) is injective
  for every commutative ring by regularity of the localized denominators.
- For each D, `FractionRing D` is Mathlib's exact
  `Localization (nonZeroDivisors D)`. Its source explicitly permits zero divisors
  and the zero ring. `Localization S` and `LocalizedModule S D` are reducibly
  the same construction when S is a submonoid of D. The module does not confuse
  total fractions with a domain-only fraction field.
- C is the actual `R ⊗[A] B`, with its canonical R-algebra structure.
- The conclusion's first witness is
  `hregular : nonZeroDivisors A ≤ (nonZeroDivisors R).comap (algebraMap A R)`.
  This states exactly f(S_A) ⊆ S_R as a conclusion, rather than assuming it.
  Q(f) is the existing `IsLocalization.map (FractionRing R)
  (algebraMap A R) hregular`, so it is the canonical induced map, not an
  unconstrained ring homomorphism.
- The next witness `j : R ⊗[A] B →ₐ[R] FractionRing R` is required to satisfy
  the stated pure-tensor formula for every r and b. Pure tensors generate C,
  so the formula uniquely specifies j. Its injectivity is `Function.Injective j`.
- Injectivity and integrality of R → C are respectively
  `Function.Injective (algebraMap R (R ⊗[A] B))` and
  `Algebra.IsIntegral R (R ⊗[A] B)` in the conclusion.
- The total-fraction comparison is a ring equivalence
  `e : FractionRing (R ⊗[A] B) ≃+* FractionRing R`, required to send c/1 to
  `j c` for every c. Localization uniqueness identifies its forward map with
  the canonical map; this is not an unrelated abstract isomorphism.
- Normality of C is the dependency record's exact inline predicate:
  `∀ (p : Ideal (R ⊗[A] B)) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  It is an implication hypothesis for the last clause, not a hypothesis on the
  preceding conclusions. Its conclusion is the equality of R-subalgebras
  `j.range = integralClosure R (FractionRing R)`.
- There are no Noetherian, domain, nontriviality, finite type, or module-finite
  binders. Both universes are explicit and independent; B is a genuine
  subalgebra of Q(A), so its carrier has A's universe.

Dependency declarations used, with their recorded source signatures and
docstrings read:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; its module-flatness content
  and injection characterization are `Module.Flat` and
  `Module.Flat.lTensor_preserves_injective_linearMap` in
  `Mathlib.RingTheory.Flat.Basic`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, with
  the ring specialization `Localization` and `FractionRing` in
  `Mathlib.RingTheory.Localization.FractionRing`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `IsIntegral`,
  `integralClosure`, and the proof input `Algebra.IsIntegral.tensorProduct`.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`:
  `Algebra.TensorProduct.instCommRing`, `includeLeft`, `includeRight`,
  `productMap`, its pure-tensor formula, and `Algebra.TensorProduct.ext`.
  C uses their existing ring and algebra instances.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and
  `Mathlib.RingTheory.Localization.AtPrime.Basic`: `IsIntegrallyClosed`,
  `IsDomain`, and `Localization.AtPrime`, assembled in the recorded inline
  normal-ring predicate without inventing a new predicate.
- Proof imports also explicitly include
  `Mathlib.LinearAlgebra.TensorProduct.Defs` (`TensorProduct`) and
  `Mathlib.RingTheory.Localization.Defs` (`IsLocalization.lift`, `ringHom_ext`).
- `WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal`:
  `integral_totalFraction_mem_range_of_normal`, the recorded proof dependency
  for the final normality clause. Its full statement accepts arbitrary
  commutative rings and exactly the same prime-local normality predicate.

Sources checked: local `literature/stacks-project/algebra.tex`,
`lemma-base-change-integral` (02JK), `lemma-normal-ring-integrally-closed`
(034M), and the node's seven-step proof. This is the node's stated agent
algebra generalization underlying ILO VIII Lemma 2.2.9; no statement correction
or extra hypothesis was required. The full seven-step proof is in the theorem
docstring, including the per-element denominator argument for nonfinite B.

Edge cases checked mathematically:

- B = A gives C ≅ R and the identity total-fraction comparison; the last
  clause reduces to normal R being integrally closed in Q(R).
- R is the zero ring: C and both total-fraction rings are zero, regularity means
  injective multiplication even on a singleton, and the normality predicate
  is vacuous because there are no primes. The claimed ranges are singleton.
- A is the zero ring: an A-algebra R must also be zero, already covered.
- Noninjective flat f, for example projection k × k → k: the statement does not
  assume injectivity of f or of Q(f); the regular-element image condition
  holds and the injection claimed is the tensor map j.
- Reduced rings with zero divisors use all nonzerodivisors, rather than all
  nonzero elements. No field instance is used for their total fractions.
- Infinitely generated integral B is allowed. A tensor element is a finite
  sum even if B is not finite, which is why Step 3 can clear its denominators.

Searches made with the prescribed `msearch.py Q29
lem-per-flat-integral-total-fractions` wrapper:

- LeanFinder: "flat base change of an integral subalgebra of total fractions
  embeds in the total quotient ring, with the same total fractions and
  normality identifying integral closure". Eight hits, including
  `TensorProduct.toIntegralClosure_injective_of_flat`,
  `Algebra.IsAlgebraic.isBaseChange_of_isFractionRing`, and
  `IsLocalization.integralClosure`. The first compares integral closures in
  a tensor product, the second imposes domain-related hypotheses, and the
  last is a localization comparison. None states the whole item.
- Loogle: `TensorProduct, IsFractionRing`. The sole hit is
  `Ideal.eq_top_of_mk_tensor_eq_one`, about inverse ideals in a Picard group,
  and is unrelated to this statement.
- Grep: `toIntegralClosure|isBaseChange_of_isFractionRing|IsFractionRing.*[Tt]ensor`
  in Mathlib/RingTheory. Seven hits in Smooth/IntegralClosure and
  Algebraic/Integral, the component results above rather than an exact match.
- `rg` of the project's `lean/Sheaf` and upstream `lean/WeilConjectures`
  for total-fraction and integral-closure language found existing normal-ring,
  finite-component, and localization results, but no theorem with these
  hypotheses and clauses. The exact node-id grep in WeilConjectures found no
  declaration. Searches for the proposed module/declaration names in Mathlib,
  both project roots, and `dag/lean_names_upstream.json` found no collision.

The inherited refusal concerned an unchanged stage-1 split already reviewed by
Q39. The current queue lists this node at stage 2 with no `lean` record, and
brief-stage2 §0 explicitly permits this stage handoff. No repair note for the
item was present. No upstream source, git state, or tool was edited.

## Second reading by Q29

A second pass by this sole dispatched worker re-read the node and module side
by side; this is a self-check, not a claim of another agent's independent
review. The maintainer's independent review remains the delivery review.
Checked each binder and every conclusion against the correspondence above.
The algebra structure encodes the given arbitrary ring map, and the Subalgebra
binder encodes the actual intermediate ring. The regularity condition is an
existential conclusion; j is fixed by its formula; and the ring equivalence
is required to commute with j on C, ensuring the canonical comparison. The
last implication uses prime-local normality, not the generally weaker global
integral-closedness predicate. In particular normality was not moved into the
main hypotheses. There are no extra tautological clauses or hidden choices.
No mismatch was found, and no node statement was changed.

Validation: `scompile.py Q29 lem-per-flat-integral-total-fractions` compiled the
statement in both its sandbox and library module contexts, cleanly. The final
module is compiled again by the prescribed delivery dry run.

## Worker report

The module `Sheaf.RingTheory.SplitPrincipalQuotientNormality` states
`RingHom.split_principal_quotient_normality`. Its only theorem has proof `sorry`;
there are no definitions or auxiliary postponed theorems. The node's statement,
statement dependencies, and proof plan are unchanged.

I read the assigned node, its normal-ring dependency and its complete Mathlib
record, its fraction-field proof dependency, the stage-2 brief and conventions,
and Stacks algebra.tex at `definition-domain-normal` (Tag 0309, lines 7979ff)
and `lemma-descent-normal` (Tag 033G, lines 46684ff). The node correctly identifies
its argument as agent-formulated: 0309 supplies the meaning of normal domain;
033G supplies the fractional-ideal descent argument being adapted, rather than
asserting the present module-splitting theorem. No faithful flatness is imposed.

Hypothesis and clause correspondence:

- `R : Type u`, `A : Type v`, `[CommRing R]`, `[CommRing A]` are the two
  commutative rings with identity. Independent explicit universes retain all
  sizes. There is no nontriviality or domain hypothesis on these original rings.
- `ι : R →+* A` is the identity-preserving ring homomorphism, and
  `hι : Function.Injective ι` is its stated injectivity assumption.
- `ρ : A →+ R` bundles exactly additivity. It is not a ring homomorphism.
  `hlinear : ∀ (r : R) (a : A), ρ (ι r * a) = r * ρ a` is the specified
  linearity for the module structure induced by ι, written without selecting
  an extra algebra instance. `hretract : ∀ r : R, ρ (ι r) = r` is retraction.
- `(θ : R)` is arbitrary; the theorem therefore applies to every θ.
- `Ideal.comap ι (Ideal.span ({ι θ} : Set A)) =
  Ideal.span ({θ} : Set R)` is exactly the asserted principal-ideal contraction.
- The existentially quantified `j : R/(θ) →+* A/(ι θ)` is a unital ring map.
  Its formula on every `r : R`, using `Ideal.Quotient.mk`, specifies precisely
  the induced map `[r] ↦ [ι r]`. `Function.Injective j` gives its injectivity.
- The map `p : A/(ι θ) →+ R/(θ)` is bundled additive. Its formula on every
  `a : A` specifies `[a] ↦ [ρ a]` and asserts existence of a well-defined
  additive map on the actual quotient rings. These formulas uniquely determine
  both quotient maps because each quotient map `Ideal.Quotient.mk` is surjective;
  no arbitrary map is substituted for a canonical one, nor is data chosen from
  a theorem. The existential is the assertion of the induced maps' existence.
- `Function.LeftInverse p j` says exactly that p retracts j, on every quotient
  element. `∀ b c, p (j b * c) = b * p c` is the asserted R/(θ)-linearity:
  scalar multiplication on the larger quotient is multiplication by j b.
- The implication from `IsDomain (A/(ι θ)) ∧ IsIntegrallyClosed (A/(ι θ))`
  to the same conjunction for `R/(θ)` is normal-domain descent. In particular,
  `IsDomain` includes nontriviality; normality is not weakened to local normality
  or integral closedness alone.
- The final implication `(IsDomain A ∧ IsIntegrallyClosed A) →
  IsDomain R ∧ IsIntegrallyClosed R` explicitly records the node's final
  θ=0 assertion. The general quotient claims also include θ=0 unchanged.

Dependency declarations and imports:

- `def-weil-pbc-normal-ring` records Mathlib's `IsIntegrallyClosed`, `IsDomain`,
  and the inline normal-domain conjunction. Public import
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` supplies these notions.
  Read `IsIntegrallyClosedIn`, `IsIntegrallyClosed`, and
  `isIntegrallyClosed_iff` at lines 66–127; `IsDomain` and its docstring in
  `Mathlib.Algebra.Ring.Defs` at lines 431–439. The localization-at-prime
  normal-ring clause of that dependency is not used: this item says domain.
- `lem-weil-pbc-fraction-field-lift` is a Mathlib leaf with no Lean record.
  Read `IsFractionRing.lift`, `lift_unique`, and `lift_algebraMap`, with their
  signatures, docstrings and surrounding variables in
  `Mathlib.RingTheory.Localization.FractionRing` at lines 321–390, and
  `RingHom.injective` in `Mathlib.RingTheory.SimpleRing.Basic` at lines 60–71.
  Both modules are ordinary, nonpublic proof imports as required.
- `Mathlib.RingTheory.Ideal.Quotient.Operations` supplies the actual ideal
  quotients and quotient maps. Its `Ideal.quotientMap` API was also inspected;
  no second quotient construction is introduced.

Edge cases checked mathematically before writing:

- θ=0: the principal ideals are zero, the quotient maps identify with ι and ρ,
  and normality descends by the same fractional-ideal argument.
- θ a unit: both quotient rings are zero. All map, contraction, and retraction
  assertions still hold; the normal-domain antecedent is false, as required.
- Zero-divisor θ: with `R = ℤ/6`, `A = R[X]`, and θ=2, contraction and the
  coefficient splitting give the quotient inclusion `𝔽₂ → 𝔽₂[X]`; normality
  descends. No regular-element or domain assumption is silently introduced.
- Nonmultiplicative retraction: for `ℤ → ℤ[X]`, take ρ(f)=coeff₀(f)+coeff₁(f).
  This is additive, ℤ-linear and retracts constants, but ρ(X²)=0 while
  ρ(X)²=1. It satisfies the theorem's hypotheses and descends modulo θ=2.
- Zero rings are admitted by the initial binders. Since ι is unital and has a
  retraction, the zero-ring cases cause no obstruction to quotient splitting;
  none can satisfy a normal-domain antecedent.

Searches made (actual results):

- `msearch.py`, LeanFinder: “If a commutative subring is a module direct summand
  of a normal domain, its quotient by a principal ideal embeds as a module
  direct summand of the corresponding quotient, and normality descends.”
  Eight hits concerned PID normal forms, quotient decompositions,
  Kummer–Dedekind quotients, or normal field extensions; none states this result.
- `msearch.py`, Loogle: `IsIntegrallyClosed, LinearMap`. Twelve hits concern
  integral traces, trace quotients, and different ideals; none gives the split
  principal quotient theorem.
- `msearch.py`, grep: `retract|split|[Pp]ure|of_injective` in
  `RingTheory/IntegralClosure`. Five hits concern injective integral maps or
  incidental occurrences; none is this theorem.
- `msearch.py`, LeanSearch: “A subring which is a module direct summand of an
  integrally closed domain is integrally closed; the splitting descends modulo
  a principal ideal.” Eight hits include `IsIntegrallyClosed`, integral closure
  instances, and `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`.
  Reading the latter's full signature at IntegrallyClosed.lean:308 shows the
  additional assumption `IsIntegrallyClosedIn R S`, which the present splitting
  does not imply (e.g. a proper algebraic field extension has a vector-space
  splitting). It also gives no principal quotient splitting.
- `rg` in both project roots for split/normal/retract combinations found
  unrelated normal-form, conormal, and field-splitting declarations, with no
  matching result. An exact `rg` for `split_principal_quotient_normality` in
  Mathlib, `WeilConjectures`, and `Sheaf` found no declaration. The required
  node-id grep in `WeilConjectures` also found no occurrence. Broader normal-ring
  module inspection found normality/localization results, not this statement.

There are no missing notions, dependency interface repairs, statement changes,
or disputed statements. The current CompactObject example is withdrawn; its
node's recorded upstream module was read for the active module/header style.

Validation: scompile.py compiled both its sandbox view and the library module
successfully (1.3 s and 1.5 s). No errors or unexpected warnings. All binders and
universes are explicit; all lines are at most 100 characters. The delivery dry
run and push are performed through deliver2.py.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

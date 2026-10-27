## Worker report

The module `Sheaf.RingTheory.SquareZeroAdicThickening` states
`IsAdicComplete.of_square_zero_quotient`, with its entire proof `sorry`.
It defines no new notion. The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- A commutative ring C: `(C : Type u) [CommRing C]`, with explicit universe `u`.
- C is Noetherian: `[IsNoetherianRing C]`, exactly the recorded Mathlib definition.
- Ideals Q and H of C: `(Q H : Ideal C)`, with no extra restrictions on H.
- Q squared is zero: `(hQ : Q ^ 2 = ⊥)`; bottom is the zero ideal.
- The ring C/Q: Mathlib's quotient ring `C ⧸ Q`.
- Its ideal (H+Q)/Q: `(H ⊔ Q).map (Ideal.Quotient.mk Q)`. Supremum is ideal
  addition, and map along the surjective quotient homomorphism is its ideal image.
- Quotient completeness: `hcomplete : IsAdicComplete
  ((H ⊔ Q).map (Ideal.Quotient.mk Q)) (C ⧸ Q)`.
- Conclusion: `IsAdicComplete H C`.
- The final sentence imposes no additional hypothesis: there is no section, coefficient
  ring or flatness datum, or locality assumption in the signature.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with
  `isNoetherianRing_iff` and `isNoetherianRing_iff_ideal_fg` confirming the exact meaning.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, a class extending
  `IsHausdorff` and `IsPrecomplete`. Read also `AdicCompletion`, `AdicCompletion.of`,
  and `AdicCompletion.of_bijective_iff`: the class is exactly bijectivity of the
  canonical map, including separatedness, as required by the node.
- Mathlib's `Ideal.Quotient.mk` and `Ideal.map` are used directly; their definitions
  and quotient ring instances were read. Both are available through the public imports.

The proof docstring reproduces both reviewed DAG steps: the eventually constant
Q-power quotient system makes C Q-complete, then the two-ideal lemma with I=Q, J=H
applies. The proof dependency `lem-sfb-two-ideal-adic-completeness` currently has no
Lean record or Mathlib match; it is not needed to type the statement and no module
exists to import. Its application remains explicitly documented for stage 3.
Read the source in `literature/stacks-project/algebra.tex`,
`lemma-complete-modulo-nilpotent` (Tag 0DYC), including its hypotheses and proof.

Edge cases checked before writing:

- Q=0: the quotient is C and the hypothesis recovers exactly H-completeness.
- H=0: the conclusion is automatic zero-adic completeness; nothing is excluded.
- H=top: completeness of C/Q for its unit ideal forces C/Q=0, hence Q=top;
  Q squared zero then forces C=0, whose conclusion holds.
- The zero ring is permitted (no `Nontrivial` binder); Q=top is covered by that case.
- Dual numbers over k[[t]], Q=(epsilon), H=(t): the usual complete thickening is covered.
  Over k[t] the analogous quotient is not (t)-complete, so the hypothesis correctly fails.
- No locality is inferred or required: products of complete examples are included.

Searches for existing statements, on 2026-10-24:

- `msearch.py ... leanfinder` query: "A Noetherian commutative ring is H-adically
  complete if its quotient by a square-zero ideal Q is complete for the image of H".
  Eight hits: `IsAdicComplete`, `AdicCompletion.flat_of_isNoetherian`,
  `IsAdicComplete.henselianRing`, `IsAdic`, `isAdicComplete_iff`,
  `IsAdic.isAdicComplete_iff`, `IsAdicComplete.toIsPrecomplete`,
  `IsAdic.isPrecomplete_iff`. None is this theorem.
- `msearch.py ... loogle` query: `"IsAdicComplete", "Ideal.Quotient"`.
  Result: zero hits.
- `msearch.py ... grep` query: `IsAdicComplete|complete.*nilpotent|square.zero`,
  restricted to `RingTheory/AdicCompletion`: 25 hits, definitions and results on
  completeness of completions, local rings, topology and functoriality; no lifting theorem.
- `rg -n 'IsAdicComplete|complete.*nilpotent|adic.*square|square.*adic'` in
  `lean/WeilConjectures` and `lean/Sheaf`, followed by focused RingTheory searches for
  square-zero, nilpotent, quotient and two-ideal completeness: no identical statement.
  Nilpotent-ideal completeness helpers concern completeness for the nilpotent ideal
  itself, not the independent H in this theorem. Related local-quotient results impose
  locality and concern the other direction. The adic deformation functor cites the same
  still-unstated two-ideal lemma but does not expose the present statement.
- `grep -rn 'lem-sfb-finite-square-zero-adic-thickening' lean/WeilConjectures`:
  no matches. A name search for `of_square_zero_quotient` in Mathlib, WeilConjectures,
  and Sheaf has no match; focused upstream name-index searches also found no duplicate.

No statement correction, missing notion, new node, dependency interface repair,
or STATEMENT-DISPUTED issue was found.

## Second reading by Q142

Reread the node and final Lean signature against one another after writing the file.
This is a separate self-review pass; the dispatcher explicitly forbids starting other
agents, and the maintainer supplies the independent delivery review.

The binders cover exactly a commutative Noetherian C, two ideals, square-zero Q,
and completeness of the literal image of H+Q in C/Q. The conclusion is completeness
of the same C for the same H. In particular `IsAdicComplete` includes Hausdorffness;
there is no weakening to mere precompleteness. All variables and the sole universe
are explicitly bound. The quotient ideal matches the node literally, and the zero
ring and improper H are included. The proof docstring contains both DAG steps.
No mismatch was found and no statement change was made.

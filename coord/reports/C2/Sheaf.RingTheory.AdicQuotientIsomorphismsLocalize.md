## What changed

Proved `Localization.adic_quotient_isomorphisms_localize` in
`Sheaf.RingTheory.AdicQuotientIsomorphismsLocalize`, preserving its statement and public imports.
Added one private, fully proved helper `Localization.localized_quotient_bijective` and the private
proof import `Mathlib.RingTheory.LocalRing.RingHom.Basic`.

The exponent-one quotient surjectivity proves `Q = p.map f`. Ideal extension commutes with
powers. Locality of the canonical local homomorphism proves the contraction assertion. The
quotient-localization instance and `IsLocalization.ringEquivOfRingEquiv` prove bijectivity on
each local quotient; extensionality identifies that isomorphism with the canonical quotient
map. Its fraction formula follows from `localRingHom_mk'`, and transition compatibility follows
by choosing a quotient representative. The node proof and proof origin now record this route.

Validation: the complete proof compiled remotely with exit code 0 in 5.0 seconds and no
warnings. The theorem signature and all public imports are byte-for-byte unchanged; no
existing consumer needs adaptation.

## Proved and sorry left

Closed 1 of 1 original holes: `Localization.adic_quotient_isomorphisms_localize`
(node `lem-trf-adic-quotient-isomorphisms-localize`). Added 0 holes; 0 remain.
The private helper is completely proved. No decomposition or split-off statements.

## No longer needed

None. All three declared proof dependencies remain used: the localization definition,
`Ideal.map_pow`, and the quotient-localization Mathlib leaf. No imports removed and no
nodes or modules pruned. The explicit zero-fraction kernel calculation is replaced by
Mathlib's proved localization-of-a-ring-isomorphism construction.

## Where the brief, the DAG or earlier work was wrong

No statement errors found. The DAG's fraction argument can be shortened using the existing
Mathlib quotient-localization instance and `ringEquivOfRingEquiv`; its statements and the unit
route are unchanged. The argument does not require maximality of p, injectivity of f,
Noetherian hypotheses, or reducedness. Positivity is used only for the power ideal to lie in Q;
the denominator-lifting argument uses J contained in Q. Equal transition exponents are included.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

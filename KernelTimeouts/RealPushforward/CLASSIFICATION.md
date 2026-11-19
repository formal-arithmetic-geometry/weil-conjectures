# RealPushforward: exact Kernel site

**Declaration:** `AlgebraicGeometry.WeilSheaf` example with the statement of
`isReal_higherLowerShriek_one`, from `ed3d39ddb5d`.

## Phase gate

The master build tree is Lean/Mathlib 4.35.0. Every command below was run
with `LEAN_NUM_THREADS=1`, `-DElab.async=false`, and `/usr/bin/time -v`.
The original Before file took 54.73 s with Kernel checking and reported
`(kernel) deterministic timeout` (4,686,328 KB RSS); the same file with
`-Ddebug.skipKernelTC=true` took 3.00 s (3,125,404 KB). The type-only probe
`probes/TypeOnly.lean` took 2.80 s with Kernel on. Thus the declared type and
the prefix are cheap; the expensive work is in the value check.

## Top-down bisect

1. `probes/TypeOnly.lean` replaces the whole value by a typed `sorry`: 2.80 s.
2. `probes/BeforeFinalSorry.lean` retains the old `rwa` prefix but replaces
   the final consumer with `sorry`: 3.00 s.
3. `probes/FinalExact.lean` retains the same prefix, binds its local equality
   as `this`, and checks `exact this` against the declaration goal: 54.54 s,
   deterministic timeout (4,686,316 KB RSS).

The first expensive operation is therefore the final Kernel conversion
`type(this) == declared goal`, not `h₁`, `hc`, or the preceding rewrite
tactics. `probes/PrintConversion.lean` uses `pp.explicit`, `pp.proofs`, and
`pp.universes` to print both sides immediately before that conversion.

## Exact expressions and diagnosis

The left side has head
`Polynomial.coeff (LinearMap.charpolyRev (stalk ((higherLowerShriek ... 1).obj K) ξ))`;
the goal has the same coefficient expression with
`FrobeniusModule.localPolynomial` as its polynomial head. The visible
`rw [FrobeniusModule.localPolynomial, ← hc, Polynomial.coeff_expand_mul ...]`
does not make the stored equality's inferred type syntactically identical to
the theorem statement: the implicit `PadicAlgCl`, stalk, `WeilSheaf`, and
finite-point instances remain in different unfolded paths. The proof is an
ordinary equality, so the conversion must reduce the concrete polynomial
representation before accepting it.

With `-Ddiagnostics=true -Ddiagnostics.threshold=1` on `FinalExact.lean`,
Kernel diagnostics report a deterministic timeout and deep reduction chains;
the compact successful fixed proof avoids this conversion. The exact
diagnostic command is recorded by the probe name and is reproducible with:

```text
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean \
  -DElab.async=false -Ddiagnostics=true -Ddiagnostics.threshold=1 probes/FinalExact.lean
```

## Classification

Primary mechanism: **A (reduction/definitional equality heavy)**. Contributing
mechanism: **E (representation/instance mismatch)**. The phase gate and the
typed-sorry/final-`exact` bisect confirm the conversion site; the printed
`charpolyRev` versus `localPolynomial` heads and the fixed abstract theorem
application explain why reduction is required. Evidence: **confirmed** for the
cost site, **strongly supported** for A/E. The fixed form takes 2.80 s and
uses `isReal_higherLowerShriek_one`, which keeps the polynomial identity behind
a generic lemma.

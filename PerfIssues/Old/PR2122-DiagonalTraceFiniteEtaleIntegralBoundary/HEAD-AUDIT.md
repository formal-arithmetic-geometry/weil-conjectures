# Head audit: PR #2122 finite-etale integral boundary

Case ID: `PR2122-integralBoundary`. Conversion ID: `P2122-value`.
Declaration:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteEtale_integralBoundary`.
Lean 4.35.0; master revision `1ef1fddac73e`. The baseline source is
[Before.lean](Before.lean) restored at its original module path and compiled
with the generated Lake setup, one Lean thread, synchronous elaboration,
ordinary Kernel checking, `nice -n 10`, and `timeout 3600`. The historical
and fixed modules both compile without diagnostic axioms or `sorry`.

## Expensive conversion and Head Audit

The old module takes 350.32 s wall, 347.37 s user CPU, and 16,321,824 KB
peak RSS; the current module takes 30.69 s wall, 29.87 s user CPU, and
5,285,748 KB. Old Kernel checks include 15.6, 64.3, and 176 seconds; the
final theorem is the largest. [HeadAudit.lean](probes/HeadAudit.lean)
replays `Kernel.check` on the final theorem's original stored value in
172.014 s. Its inferred and declared types both have 14 outer Pi binders.
The declared result is an `Eq.{u+2}` with three arguments: an `Ext` carrier,
an `Ext.mk₀CompMk₀` left side, and an `evaluatedIntegralKummerClass` right
side. The first raw positional difference from the inferred type is an
`Expr.mdata` wrapper versus the declared `Eq` application. This is a
printer/metadata boundary, not evidence that metadata caused 172 seconds
of checking. The final inferred/declared conversion is 1 ms; the inner
conversion that dominates `Kernel.check(value)`
has not been extracted.

[ValueFrames.lean](probes/ValueFrames.lean) preserves the raw value before
normalization. Its first 14 frames are lambdas, followed by 12 `Expr.letE`
bindings named `T`, `E`, `A`, `S`, `M`, `L`, `y`, `f`, `β`, `hb'`, `hE`, and
`hd`. The terminal outer body is an `Exists.casesOn` application with five
arguments; the final proof is nested in its branch lambda. The `Exists`
recursor is observed as an expression head, but no timed subcomparison has
implicated its iota reduction. The full original pair remains executable
in the probe through the environment's stored value and declared type;
the **expensive inner pair is not yet identified**. Thus this is a bounded
Head Audit, not a claim of complete inner conversion attribution.

## Source-guided prediction and hypothesis tests

The historical PR described concrete `DiagonalAb T` versus sheaf-category
representations, `(F ⋙ G).obj` versus `G.obj (F.obj)`, and `ULift.ring`
versus `CommRing.toRing` beneath derived-category/`Quiver.Hom` types. If
such a pair occurs in the checked value, the installed Kernel may need to
unfold a concrete category or functor representation before comparing a
common head. This remains a source-guided prediction; neither side of
that historical inner pair was re-extracted from the 4.35.0 value.

| Hypothesis | Status and measured experiment |
|---|---|
| H1 reducibility hints | No pair of differing constant heads with recorded hints is isolated at the expensive site. Not applicable to a claim about this value check. |
| H2 same-head argument | The declared result has `Eq` head, but the first inferred diff is metadata; no valid per-argument `Eq` timing was obtained. Unresolved. |
| H3 projection exposure | Historical source names `.obj` differences; no elaborated `Expr.proj` at the expensive inner pair was dumped. Unresolved. |
| H4 dependent binder | The theorem has 14 Pi binders and the value replay takes 173.437 s, but no particular application domain was reconstructed. Unresolved. |
| H5 instance paths | Historical structural differences include `ULift.ring`/`CommRing.toRing`; the current head probe did not inspect those stored leaves. Plausible only. |
| H6 proof arguments | No timed proof-proposition pair was isolated. Unresolved. |
| H7 non-delta reduction | Tested H7.1: raw value contains 12 lets and an outer `Exists.casesOn`. No shallow reduction or size control tied them to the 173.437-second value check. Plausible alternative, not supported as cause. |
| H8 context/order | Old/new whole modules were measured (347.37/29.87 CPU s), but the fix also moves helpers into imported modules. The old value replay alone costs 172.014 s, and the final conversion 1 ms. This confirms persistence of a slow Kernel value check, not a single-factor source explanation. |

## Causal record and confidence

Initial checked object: the final theorem's stored value against its
declared `Eq` type. A potential high-level `Eq` comparison is visible at
the result, but the check spends 173 seconds inside the value before a
specific expected-domain pair has been identified. The first raw type
diff is metadata, not a demonstrated failure of high-level comparison.
No first reduction candidate or one-step exposure at the expensive inner
site can be assigned from current evidence. The real after module is
faster, but its module split and helper factoring change several factors.
**Necessary versus unfavorable: unresolved.**

Confirmed: the Kernel phase, final theorem value cost, raw outer shape,
and whole-module before/after measurements. Plausible: the concrete
category/functor/instance differences described in the historical PR
contribute. Overall evidence level for why the Kernel unfolds:
**unclassified**. The next useful experiment is to isolate one application
argument inside the `Exists.casesOn` branch and dump its exact inferred
type and instantiated expected domain.

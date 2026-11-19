# F66Adj workplan experiments

Source snapshot: `imageHomIso_naturality`, module
`AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomComp`,
commit `f66ad18a9ed`; Lean and Mathlib 4.35.0. The expensive site
is proof argument 39 (`hR`) of `homIso_naturality_of_counit`, after
the preceding 38 actual arguments instantiate its dependent binder.
`probes/HeadAudit.lean` retains the original local context and exact
proposition pair. Both propositions have outer `Eq` and
`Quiver.Hom` heads; the first stored difference is a
`DerivedCategoryModule` scheme argument: an
`Over.left (Over.mk f.left)` expression in the actual
`imageRestriction_counit` proposition versus the helper's local
scheme variable in the expected proposition. The difference recurs
in the two equality sides. The `Over.left` head is an abbrev whose
immediate body is `Comma.left`; this is an application in the
elaborated pair, not an initial `Expr.proj`.

All workplan timings used one Lean thread, `timeout 3600`,
`/usr/bin/time -v`, and normal Kernel checking. The theorem uses
400,000 heartbeats. Kernel-only time and heartbeat consumption are
not separately available. Application probes end in diagnostic
`sorry` only after the helper application; the full `After.lean`
theorem is normally checked.

## B3-L: Accessor result in isolation

EXPERIMENT: B3-L; group: G2-A/G3-B. Hypothesis: the stored
`Over.left` term can reduce to the local scheme object. BASELINE:
the exact argument-39 proposition pair above; original checked
application costs 34.72 s wall, 34.03 + 1.01 s CPU,
5,667,344 KB RSS. CONTROL: `probes/wp/OverLeftShape.lean`
checks `(Over.mk f.left).left = T.left` by `rfl` under the
same toolchain. It succeeds in 2.30 s wall, 1.48 + 0.76 s CPU,
2,779,128 KB RSS. This is an independently checked accessor
equality, not a replacement of the original argument-39 pair, so
the expensive conversion is not measured by this control.
Theorem obligation and original elaborated pair remain as in the
baseline. Supports: a direct reduction route from the concrete
over-object to its underlying scheme. Weakens: an irreconcilable
scheme mismatch. Unresolved: whether that reduction alone removes
the full proof-proposition cost. Classification: necessary accessor
exposure in the original representation; confidence: strongly
supported for the equality, inconclusive for its isolated cost.

## B3-R: Replace only argument 39

EXPERIMENT: B3-R; group: G2-B/G2-C. Hypothesis: the argument's
stored proposition representation causes the 39th-binder cost.
BASELINE: `probes/ApplicationOnly.lean`, 34.72 s wall,
34.03 + 1.01 s CPU, 5,667,344 KB RSS, Kernel success but
expensive. CONTROL: `probes/ReplaceHR.lean` changes only
argument 39 from `imageRestriction_counit A _ _ (Over.mk f.left)`
to the direct `restriction_counit A f.left _ _`. All preceding
arguments and the same square obligation are preserved, with Kernel
checking enabled. `probes/ReplaceHRHead.lean` confirms that the
elaborated proposition changes: the `Over.left`/local-scheme first
difference is gone. The next first difference is
`DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`
versus `ExternalRHom.siteDerivedMonoidal` in the equality's
functor structure. That remaining difference is cheap in this
application. RESULT: 3.40 s wall, 2.79 + 0.92 s CPU,
2,854,984 KB RSS; the same argument-domain hotspot is removed.
Supports: the proof argument's proposition representation is causal.
Weakens: the remaining monoidal-instance difference suffices to
cause the old cost. Unresolved: the replacement also changes the
proof-producing interface, so the specific `Over.left` leaf alone
has not been changed independently. Classification: unfavorable
dependent proposition path; confidence: confirmed for the
one-argument replacement, strongly supported for the accessor
representation as the trigger.

## B3-Q: Preceding tensor-isomorphism negative control

EXPERIMENT: B3-Q; group: G2-C. Hypothesis: the earlier tensor
isomorphism rather than the proof proposition drives the jump.
BASELINE: the same argument-39 application, measured above. CONTROL:
`probes/ReplaceTauQ.lean` changes only the preceding
tensor-isomorphism argument. The proof argument and its original
first `Over.left` divergence remain. Theorem obligation is
preserved and Kernel checking is enabled. RESULT: 35.12 s wall,
34.08 + 0.99 s CPU, 5,631,848 KB RSS, still expensive. This
weakens the preceding-argument hypothesis and supports the
argument-39 localization. The exact inner reduction remains
unresolved. Classification: negative control; confidence:
strongly supported.

## Mechanism

The proof supplied at argument 39 stores the restriction counit
through a concrete over-object, while the helper's instantiated
domain uses its local scheme. The accessor can reduce to the same
scheme, but in the original equality it is embedded in concrete
derived-category and functor data. A direct restriction proof
changes that stored proposition and makes the same application
cheap. The full `After.lean` proof has additional final-handoff
edits, so the local control is not attributed with every part of
the full theorem's speedup.

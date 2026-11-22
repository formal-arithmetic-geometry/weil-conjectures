# Intrinsic vs mismatch-induced DefEq: PerfIssues

Current-case revision: a2ec460045b. Kernel: READY2-4.35.0.

| Case | Family | M / O / A evidence | Verdict |
|---|---|---|---|
| PR1556 | NatTrans.app | M 2.074 s diagnostic; O 73.190 s / 6.670M; A 0 ms; R 70.107 s | H3 + H2 |
| PR1625 | nested NatTrans.app | M 0 ms exact; O 114.240 s / 11.758M; A 0 ms; R 109.892 s | H3 + H2 |
| NativePullTensor | Functor.obj | M 1 ms regular; O 22.805 s / 2.686M; A 0 ms; abbrev M 14.134 s | H2 + residual H1 |
| PR1563 | CategoryStruct.comp | M invalid; O 23.415 s / 2.574M; A 20.699 s broad | H1/H3 |
| PR1627 | generated fields | M invalid; O 29.454 s / 10.905M; A no root >100 ms | H1/H3 |
| PR1624 | dependent Functor.comp | M invalid; O 53.521 s / 6.599M; A 5.256 s / 456k | H1/H3 |
| PR2122 | Exists.casesOn | M invalid; O historical 25.836 s; A historical 5.142 s | H1/H3 limited |

NatTrans.app, CategoryStruct.comp, and Functor.obj are generally path markers:
projection, dependent proposition, and nested composition descendants own most
exclusive time. Functor.obj is the clearest mismatch-sensitive case: a
non-identical regular-provider match is 1 ms, while the original and abbrev
provider pairs are about 14 seconds. PR1556 and PR1625 show the same reversible
major-premise effect at application level, amplified by dependent work.

unif_hint was applicable to none of these cases: no relevant inferred provider
assignment changed the critical expressions. Shared-provider three-way controls
were invalid for every dependent telescope touched. Context controls support
interaction: isolated PR1563/PR1624 endpoint checks are expensive but their
dependent parents are larger. PR2122 was not freshly replayable because of the
missing imported olean.

## What changed

The item module proves integrationInput_existsUnique and
rankZeroOrdinarySource_existsUnique using the actual specified arrows, reflexive
heterogeneous equality and uniqueness via eq_of_heq.
It also proves ordinaryPlus, with a proved private helper establishing
boundedness of the ordered Tate coefficient. Proof imports supply flatness of finite
Tate lines, tensor symmetry, bounded tensor stability, shifted Tor amplitude and the
comparison between the two existing Tor-amplitude predicates. No public signature,
definition, attribute or public import changes.

The DAG retains the original geometric plan and records the auxiliary proofs and
additional dependencies.

## Proved and sorry left

Three of the four original holes are closed:
WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.integrationInput_existsUnique;
WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.rankZeroOrdinarySource_existsUnique;
WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.ordinaryPlus.
The private helper baseCoefficient_bounded is also proved.
The resumed delivery passed the server compile and preflight on 2026-10-25,
including the corrected Etale.DerivedCategory.torAmplitudeIn.shift application.

One textual sorry remains:
WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.diagonalAffineTraceSiteComparison
(lem-pur-diagonal-affine-trace-site-comparison).
No holes added or split off. This is a partial delivery of the auxiliary proofs;
the main geometric comparison is unchanged.

## No longer needed

None. All original public imports and geometric proof dependencies are retained
because the main theorem remains open. All added private imports are used by
ordinaryPlus or its proved helper. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The two endpoint-transport statements are indeed definitionally compatible,
including rank zero; no definition repair was necessary. Boundedness follows from
the existing finite-Tor tensor API after proving the Tate coefficient bounded.
The previous attempt stopped at a server temporary-directory disk-space error.
The resumed delivery passed compilation and preflight; that tool failure is resolved.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Completed the zero-hole retirement of Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
(coord/retire-items.tsv, row 2802). The copy is withdrawn in deleted.txt and its node attaches to
the unchanged official WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison.

All six current direct importers switch to the official twin. The additional transitive user
StrictHenselizationModuleFibreFactorization is adapted too. The three comparison-isomorphism
consumers transport the official comparison along the base change of the canonical small/full
ring-colimit isomorphism. Their target schemes stay the original small presentation.

Added Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction, containing an actual graph construction,
the general unit restriction along an arbitrary étale lift, and its fully proved composition
formula. Four consumer signatures express their former specialized restrictions by this general
construction; the exchange predicate is expanded as the same germ equations. This preserves their
mathematical statements, with no new hypotheses. No adopted source module or target is edited.

The complete eight-file sandbox compiles cleanly through lcompile.py --all, each file independently
in 3.3–12.7 seconds. The general composition proof uses only the existing adjunction/composition
API, naturality, terminal evaluation and pullback extensionality. No global build was run.

Change record: coord/changes/H2-qcqs-strict-local-module-comparison-retirement.md, including verbatim
old/new declarations and every downstream importer with its holder and effect.

## Proved and sorry left

The assigned module has zero textual holes before withdrawal: 0 closed, 0 added, 0 left.
No proof is replaced by sorry and no statement is split off with an unfinished proof.
The new AlgebraicGeometry.Etale.unitSectionRestriction_comp is fully proved.
Every adapted theorem remains fully proved:
- AlgebraicGeometry.Etale.constant_strict_fibre_stalk_comparison;
- AlgebraicGeometry.Etale.exists_integralStrictLocalFibreComparison;
- AlgebraicGeometry.Etale.qcqs_geometricExchange_factorization;
- AlgebraicGeometry.Etale.strictHenselizationModuleFibre_factorization;
- AlgebraicGeometry.Etale.strictLocal_exchange_compatibility;
- AlgebraicGeometry.Etale.strictLocalFibreRestriction_compatibility;
- AlgebraicGeometry.Etale.strictLocal_section_pullback.

There are no sorry declarations in the delivery. The assigned node now names the existing,
fully proved AlgebraicGeometry.Etale.exists_qcqsStrictLocalModuleComparison in the adopted module.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/QcqsStrictLocalModuleComparison.lean. Remove all six imports
of it; none remain. The official twin supplies its canonical comparison, rather than rebuilding
the stalk cocone and invertibility argument in the small presentation.

The assigned node no longer directly needs the old inlined small-model proof dependencies
lem-weil-pbc-strict-henselization-base-change-cone,
def-weil-pbc-small-strict-local-section-maps,
lem-weil-pbc-module-sections-iso-transport, or
lem-weil-pbc-sets-pushforward-stalk-strict-henselization. Its official proof instead uses the
existing refinement-naturality and restriction-isomorphism nodes. The small section maps remain
needed by the consumer transports; this does not claim their global withdrawal. ModuleSectionsIsoTransport
and the set-valued continuity theorem may still have other users, including dependencies of the
official restriction-isomorphism theorem, so they are not deleted. No unit statement or unit step
is bypassed and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed module, but the current item is the zero-hole retirement
listed in coord/retire-items.tsv. The current return contains no numbered repair requests.
No quarantine row applies. The retired and official module signatures differ because of the two
canonical strict-henselization presentations, so an import-only edit is insufficient.

The new general restriction lemma was checked on the identity/composite-map equations and has no
nonemptiness requirement. Empty schemes and the zero coefficient ring are included. The old small
restriction expressions are definitionally the same general graph/unit expressions; the comparison
isomorphisms are explicitly transported, never treated as definitionally equal across the two bases.

## New nodes

lem-weil-pbc-etale-unit-section-restriction-comp: the graph/unit restriction for any étale lift and
its pullback composition formula, fully proved in Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction.
It is strictly general functoriality, independent of strict henselization, stalk continuity and qcqs.
LeanFinder, Loogle, LeanSearch and grep found no exact general formula. The blueprint searches for
unitSectionRestriction and inverse-image unit found no duplicate blueprint statement.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Retired Sheaf.AlgebraicGeometry.LocallyClosedStratification, a zero-hole alias module listed
in coord/retire-items.tsv. Its only declaration was
AlgebraicGeometry.Scheme.LocallyClosedStratification, an abbreviation of Scheme.Stratification.
All 27 current consumers now use that upstream type directly; direct imports switch to
WeilConjectures.AlgebraicGeometry.LocallyClosedStratification with unchanged visibility.
The change is definitionally equal in every signature and definition. Twelve DAG lean
records receive the corresponding spelling update. No proof bodies otherwise change.
The shared repository received newer work in
AdicFiniteStratificationPullback (including its completed theorem) and new imports in
NormalizedTowerCommonLisseStrata during delivery; both are preserved in full.
The new FiniteStratificationWidePullback consumer is
adapted in the same way, and its existing DAG Lean record is updated.
The completed adic theorem is not counted as this delivery’s proof progress.

Return repair: added `WeilConjectures` to the change record's `## Users` table. The
downstream scan matches its existing upstream-twin import by the last name segment;
it does not use the withdrawn alias and needs no source edit. Compared all 27 retained
Lean files against current shared sources: their only differences remain the intended
alias expansion and import replacement. All twelve retained node edits affect only `lean`.

Fresh validation: all 27 adapted modules compile through lcompile.py without errors or
warnings. The repaired packet's dry run passed compilation and server preflight at
f8f3af4d0b4, with review class CODEX. The retired module is represented by the delivery
tool as an empty module; the consumer and change-record checks accept this withdrawal.

Change record: coord/changes/F9-retire-locally-closed-stratification.md.

## Proved and sorry left

Item: zero original sorries, zero closed, zero added, zero split off, zero remaining.
This delivery retires a duplicate; it does not claim proof progress.
Existing sorries in adapted consumer modules remain unchanged:

- AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_constructible_abelian
  (lem-weil-pbc-constructible-abelian-zn-module-constructible).
- AlgebraicGeometry.Scheme.normalizedTower_common_lisse_strata
  (lem-weil-pbc-normalized-tower-common-lisse-strata).

## No longer needed

Sheaf.AlgebraicGeometry.LocallyClosedStratification and its alias are withdrawn.
Every direct import switches to its upstream twin. No other module or node is pruned.
The weaker FiniteLocallyClosedStratification is distinct and remains needed.
The alias imposed exactly the same constructibility field as upstream Stratification;
this delivery preserves that condition, including for non-Noetherian schemes.
Empty schemes and empty strata are also unchanged because the old type was an abbreviation.
The change record additionally lists the 31 unaffected users returned by the downstream scan.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief does not name the retirement operation, but the current retirement
hand-off and retire-items.tsv explicitly assign it to workers. There is no sorry to prove.
The old module docstring said no constructibility condition was imposed, but its abbreviation
already imposed upstream Stratification.isConstructible_stratum. Removing the misleading alias
and naming the actual upstream type preserves the elaborated statements.
The DAG definition node already points to FiniteLocallyClosedStratification; it must not be
repointed to the stronger upstream Stratification.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

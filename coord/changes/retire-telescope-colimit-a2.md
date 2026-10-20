# Retire the Sheaf telescope-colimit wrapper

## Reason

The human's 2026-10-20 retirement hand-off in
coord/changes/retire-sheaf-twins-20261020.md and this item's row of
coord/retire-items.tsv authorize replacing the copy by its upstream twin.
The M4 consolidation already removed duplicate constructions and proofs; its
remaining abbreviation has no active user. Retiring this wrapper removes an
unnecessary module while preserving the original theorem upstream.

## Old

Old item: public import WeilConjectures.Algebra.Homology.TelescopeColimit and
noncomputable abbrev CochainComplex.telescopeShiftColimit R E :=
CochainComplex.telescopeColimitShift R E.

## New

Item withdrawn through deleted.txt, leaving the delivery tool's empty module
stub. Active consumers directly import the source module. The definition's source
formula is the same Sigma.desc of inclusion minus transition then next inclusion.
The source theorem retains its comparison morphism, unshifted restriction,
vanishing shifted cochain restriction, and quasi-isomorphism conclusion.

The comparison node's Lean attachment already names the source theorem. Only its
Lean note changes. No dependency is removed and no unit route is bypassed.

## Users

- Sheaf.CategoryTheory.RingedCechKoszulHomLimitComparison: no holder in current
  local claim records; change only private import line 12 to the source module.
- Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor: no holder in current
  local claim records; change only private import line 33 to the source module.
- Sheaf.Algebra.Homology.TruncationTelescope: absent from active sources; its
  upstream twin already uses the source telescope directly. No edit needed.
- Sheaf.CategoryTheory.RingedCechKoszulDualLimit: archived in
  quarantine/Sheaf/CategoryTheory/RingedCechKoszulDualLimit.lean, with the current
  coord/rework.tsv entry citing its separate quarantined dependency chain.
  Preserve its archive, Lean attachment and mathematical dependencies. Do not
  restore that unrelated rework cluster just to migrate a dormant import.

For restoration of the archived consumer, the exact two textual substitutions are:

```diff
-public import Sheaf.Algebra.Homology.TelescopeColimit
+public import WeilConjectures.Algebra.Homology.TelescopeColimit
```

```diff
-          (CochainComplex.telescopeShiftColimit O (ringedKoszulDiagram O r b)) ⟶
+          (CochainComplex.telescopeColimitShift O (ringedKoszulDiagram O r b)) ⟶
```

The corresponding node lem-weil-pbc-ringed-cech-koszul-dual-limit must then record
the second spelling in lean.statement. Its mathematical statement and dependency
on lem-pc-complex-hocolim-colimit remain unchanged. The archived statement's old
abbreviation expands to the source expression definitionally, so this future
spelling change has no mathematical effect. The archive itself is not an active
Lean module and this packet does not change or claim to compile it.

## Validation

The two active adapted consumers compile cleanly, in 2.7 and 30.4 seconds.
A separate scratch probe checks the direct-sum formula by rfl and closes the
complete existential comparison using the upstream theorem. No assumptions,
universes or canonicality clauses change, including for zero complexes or zero
and identity transition maps: the construction is the identical expression.
The probe completes in 1.8 seconds. #print axioms for
CochainComplex.quasiIso_telescopeColimit reports exactly propext,
Classical.choice and Quot.sound.
No source-library signature, public import, definition or theorem proof changes.

## Status

landed 20261020T152946-L-2855501 2026-10-20 (merge of deliver/A2/Sheaf.Algebra.Homology.TelescopeColimit)
the item already had zero holes. Quarantined consumer migration remains part of
that consumer's separately assigned rework and is documented above.

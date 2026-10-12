## What changed

Proved `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback` using the
Mathlib effective-epimorphism API. The pullback projection `qV` is flat, surjective
and quasi-compact. Compatibility with descent transport supplies the coequalizer
condition; `EffectiveEpi.desc`, `fac`, and epi cancellation give existence, the
`Over` condition, and uniqueness. All existing signatures and definitions remain
byte for byte unchanged. Changed the proof-only fpqc import to plain `import`,
removed the unused `Mathlib.CategoryTheory.Sites.Over` import, and updated
`lem-pd-morphisms-descend`'s proof and proof_origin to describe the actual argument.

## Proved and sorry left

Proved `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback`
(node `lem-pd-morphisms-descend`), one of four originally open theorems.
The original sorries remain unchanged:

- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite`
  (`thm-pd-effective-descent`).
- `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`
  (`lem-pd-group-scheme-descent`).
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`
  (`thm-pd-fpqc-local-properties`).

No new declarations, nodes, or split-off sorries.

## No longer needed

Removed unused import `Mathlib.CategoryTheory.Sites.Over`.
`Mathlib.AlgebraicGeometry.Sites.Fpqc` is needed only by the proof and now uses
plain `import`. No old proof-dependency nodes are pruned: `def-pd-descent-datum`
and `def-pc-base-change` are both used. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old DAG proof described full faithfulness abstractly; it now describes the
actual effective-epimorphism proof. The node already records that its prose
statement omits fpqc hypotheses; this pre-existing issue is not repaired by
silently changing either the node statement or the Lean signature. The Lean
proof uses exactly the original Flat, Surjective and QuasiCompact hypotheses.
The first report omitted the nodes of the remaining original sorries.

## Second reading by T1

1. Compared the whole sandbox module against the repository: the only declaration
   change is the body of `existsUnique_hom_of_isPullback`. Existing signatures,
   definitions and docstrings are unchanged; the public import cleanup has its own change record.
2. Compiled the module locally and a scratch copy with `#print axioms` for the
   proved theorem and `descendPoint`: both report only `propext`, `Classical.choice`,
   and `Quot.sound`. No prohibited constructs or hollow definitions occur.
   Exactly the three listed original theorem sorries remain.
3. No statement was split off, so no new statement, edge-case or duplication
   obligations arise. Searched upstream, lean/Sheaf, lean/WeilConjectures and
   Mathlib through msearch and rg. The upstream theorem is still sorry; the
   existing EffectiveEpi API already gives the shortest underlying-map descent.
4. Read the proof top downward: `hqV.flip` base-changes p; the equality of
   qV-composites yields equality over Y; `hDV` and pullback uniqueness identify
   the transported point with b. `hψ` and `hEW` then give the descent condition.
   `fac` and cancellation prove the base condition and uniqueness. This works
   also for identity covers and empty schemes under the given surjectivity
   hypothesis. The unit `sk-prop-jacobian-descent` has empty realized entries;
   none are changed or bypassed. The no-longer-needed list is complete.
5. Read `lem-pd-morphisms-descend` and the unit record: retained both old
   proof_deps, which the actual argument uses, and repaired proof/proof_origin.
   Other nodes and all unit records are unchanged.

Second reading changed the import visibility of Fpqc, removed Sites.Over,
removed an accidental extra blank line, corrected the DAG proof route, and
completed this report. The compiled proof itself needed no repair.

Change record: `coord/changes/effective-descent-proof-imports.md`.

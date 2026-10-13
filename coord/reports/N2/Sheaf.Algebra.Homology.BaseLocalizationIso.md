## What changed

Replaced `RingTensorCohomology.exists_baseLocalization_iso` with a complete Lean reduction.
The target proof constructs the tensor-algebra-linear map by induction on pure tensors,
proves its invertibility from B-linear invertibility, and verifies equality of the two
coefficient maps to D using the four scalar towers. A new generic scalar-extension lemma
is proved completely: `ModuleCat.exists_extendScalars_iso_of_ringEquiv`. Its proof uses
the extension/restriction adjunction counit for a ring equivalence, extends the resulting
isomorphism to D, and checks the generator formula by tensor associativity.

The two derived steps have separate statement modules and nodes. The A-action step is proved. Only
proof imports were added to the existing target. No existing signature or definition changed.

## Proved and sorry left

Closed the original hole `RingTensorCohomology.exists_baseLocalization_iso` by a reduction,
not a complete foundational proof. Also proved the new generic theorem
`ModuleCat.exists_extendScalars_iso_of_ringEquiv`, without any new hole in that module.

One new named hole remains:

- `RingTensorCohomology.baseLocalizationCohomologyMap_isIso`
  (`lem-pc-base-localization-cohomology-is-iso`): invertibility on B-linear cohomology.

`RingTensorCohomology.baseLocalizationCohomologyMap_smul` is proved completely:
input-isomorphism naturality and derived-lift naturality yield the derived square;
cohomology and the two action equations yield the scalar formula.

Thus one original hole is closed and one strictly smaller hole is added; this is a decomposition.
Every hole has its source and full proof plan in its docstring and node. The assembly proof,
A-action proof and generic scalar-extension proof compile. No arbitrary existence witness supplies data.

## No longer needed

No original public imports removed. No mathematical dependency of the original route is
pruned: localization exactness and the K-flat counit theorem are needed by the new
B-linear invertibility node. The private hom-ext helper from the earlier sandbox attempt
is unused and removed. No other library module is adapted.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt abandoned after looking for a direct proof and left the target unchanged.
The reduction here follows the planned K-flat comparison and action-compatibility route,
with the tensor extension to D now proved explicitly. Identity localization, zero complexes,
zero coefficient rings, a = 0 and a = 1 were checked mathematically against the new
statements. None of them assumes flatness of D or boundedness of Q.

The first dry run required the second-reader section during worker preflight. The launcher
now explicitly exempts that section on a no-push dry run, which prints OK; the independent
second reader retains responsibility for writing it.

## New nodes

`lem-pc-base-localization-cohomology-is-iso` records the canonical B-linear map's
invertibility; its proof uses a K-flat Rp-resolution whose restriction is K-flat by exact
localization, the two counits, and naturality for the augmentation.

`lem-pc-base-localization-cohomology-action` records compatibility with multiplication
by A. It uses naturality of the input isomorphism and derived lift, followed by the two
`cohomologyIso_smul` equations; it is independent of invertibility.

`lem-pc-base-localization-dlinear-glue` records the proved generic scalar-extension
isomorphism for a ring equivalence and two equal coefficient maps. It contains no derived
category or localization assumptions and has no sorry. No change records are required.

## Second reading by N2

1. Compared `BaseLocalizationIso.lean` with the repository version. The existing target
statement is byte-for-byte unchanged; the three auxiliary modules are new declarations.
Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py`. The only remaining `sorry` is
the named split theorem `baseLocalizationCohomologyMap_isIso`; no definitions contain
`sorry`, and no forbidden declarations occur. The proofs use only the permitted imported
axioms apart from that open theorem. Verdict: pass.
3. Checked the three new statements against their docstrings, node records, and existing
library declarations. The action theorem is the exact scalar compatibility formula, the
invertibility theorem is the strictly smaller B-linear subgoal, and the D-linear glue is
the generic ring-equivalence extension lemma. No duplicate library statement was found.
Verdict: pass.
4. Read the proof from the target downward. It uses the B-linear invertibility and action
nodes, then the proved scalar-extension glue; tensor induction supplies the generator
calculation. The target's public imports are unchanged and the proof-only imports are
private. No unused original dependency was removed. Verdict: pass.
5. The DAG proof steps and `proof_deps` match the declarations and imports, and the unit
route remains realized through the three auxiliary nodes. Verdict: pass.

Changed only this second-reading report section; no Lean statements or definitions were
changed during review.

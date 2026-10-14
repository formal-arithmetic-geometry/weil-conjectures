## What changed

Replaced the hole in `RingTheory.dvr_abhyankar_local_residue_isSeparable` by a complete
Lean reduction following the unit-root claim of Stacks 0BRM. The original signature
and all original public imports are unchanged. Added proof-only imports of
`Mathlib.FieldTheory.SeparableDegree`,
`Sheaf.RingTheory.DvrEtaleUnitRootDiagram`, and
`Sheaf.RingTheory.DvrUniformizerRootCompositumResidue`.

The Lean proof chooses uniformizers, obtains their unit relation from equality of
principal ideals, passes to the unit-root diagram, constructs the root of the base
uniformizer explicitly, proves generation and all compatibility equations after
composition, applies the root-case theorem, and descends residue separability through
the commuting residue-field towers. No data definitions are introduced or chosen
from an unproved existence statement.

## Proved and sorry left

Closed the original hole in `RingTheory.dvr_abhyankar_local_residue_isSeparable`
(node `lem-sbc-dvr-abhyankar-local-residue`). Its module has no remaining sorry.
Added exactly two holes, both public theorems with whole proofs `:= by sorry`:

- `RingTheory.dvr_etale_unit_root_diagram`
  (`lem-sbc-dvr-etale-unit-root-diagram`). This is the simultaneous local cover
  construction, independent of the tame compositum assumptions.
- `RingTheory.dvr_uniformizer_root_compositum_residue_isSeparable`
  (`lem-sbc-dvr-uniformizer-root-compositum-residue`). This is the case where a root
  of the base uniformizer is already present. The unknown ramification divisibility
  and unit factor of the original theorem are absent.

This is a decomposition: one hole closed, two added, net minus one. It is not a
sorry-free proof of Abhyankar's lemma. All three modules compile cleanly locally.

## No longer needed

Removed the first worker's redundant proof-only import
`Mathlib.Algebra.Algebra.Subalgebra.Tower` (already available through
`Mathlib.FieldTheory.SeparableDegree`). No original imports removed and no existing
modules pruned. The original DAG had no
proof-dependency nodes to prune. The proof no longer needs a separate identification
of A with its normalization or identification of the original T with a normalized
tensor factor: these are bypassed by the unit-root cover and root-case argument.
The latter retains the local normalization comparison within its own proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG's non-elementary steps had empty `uses` lists. There were no stated
proof-dependency lemmas to assemble. The two new modules expose the actual geometric
inputs, and the updated original node records their Lean assembly.

The source's 09EQ argument also applies to the arbitrary further DVR base used in
the root-case statement: its tensor special fibre is a product of separable fields,
and the resulting one-dimensional local rings are already normal. This avoids an
unnecessary finiteness hypothesis on the unit-root cover A' over B. Local factors
of finite etale algebras need not themselves be finite over a nonhenselian base;
the new statements do not assert such finiteness.

Edge cases checked mathematically: e=1 uses the identity unit-root diagram and
weakly unramified base change; e=0 is excluded in the cover lemma by positivity
and in the root lemma by invertibility in the nontrivial DVR B. The original
positivity gives e>0 from e dividing n. Nonhenselian DVRs are allowed by localizing
at selected primes, without claiming the localized cover is finite. A=T and F=Frac(T)
are allowed. The new results define no arbitrarily chosen witness objects.

Searches: LeanSearch was unavailable (HTTP 500); LeanFinder returned the standard
etale and unramified residue APIs; Loogle returned separability tower lemmas and
formal unramified base change; grep located their source files. No full root
cancellation or local cover diagram theorem was found. Blueprint searches for
`unit root` and `Abhyankar` returned no duplicate. The spreading unit's realized
statement and steps are untouched.

## New nodes

`lem-sbc-dvr-etale-unit-root-diagram`, module `Sheaf.RingTheory.DvrEtaleUnitRootDiagram`:
the first unit-root claim in Stacks 0BRM, stated as a compatible local DVR and
fraction-field diagram, with a complete construction proof in its docstring.

`lem-sbc-dvr-uniformizer-root-compositum-residue`, module
`Sheaf.RingTheory.DvrUniformizerRootCompositumResidue`: the last two paragraphs of
0BRM and 09EQ, restricted to a base already containing an e-th root of a uniformizer.
Its docstring describes the unit-root calculation over U and further base change.
No change records or forced adaptations are required.

## Second reading by D2

1. Compared `DvrAbhyankarLocalResidue.lean` with the repository version. The
existing theorem signature is byte-for-byte unchanged; only proof-only imports and
the proof body changed. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`; the target theorem
is sorry-free and the only remaining sorries are the two named split-off theorems.
The scratch-copy `#print axioms` probes for all three declarations returned only
`propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
No forbidden declarations or hollow definitions occur. Verdict: pass.
3. Read both split-off statements and their docstrings and checked the edge cases
described above. They are strict reductions of the original argument and have
matching DAG nodes. Independently read Stacks Tags 0BRM, 09EV and 09EQ:
https://stacks.math.columbia.edu/tag/0BRM ,
https://stacks.math.columbia.edu/tag/09EV ,
https://stacks.math.columbia.edu/tag/09EQ . The latter's special-fibre argument
applies to the arbitrary further DVR base stated here. Independently searched
LeanFinder for residue separability after cancellation by a radical of a parameter,
Loogle for etale DVRs, and grep for `X_pow_sub_C`, `IsStandardEtale`, and residue
separability. These found polynomial separability, formal-unramified residue, and
tower APIs, but no duplicate of either geometric lemma. Verdict: pass.
4. Checked the proof route against the unit record: the unit-root diagram and the
uniformizer-root residue theorem are used explicitly, and the original node's
`proof_deps` matches the imports and applications. The unit record has empty
`realized.statement` and `realized.steps` entries, so there is no realized unit node
bypassed. Removed the redundant added `Subalgebra.Tower` import after a successful
single-file compile without it. Retained `SeparableDegree`: omitting it makes
`Algebra.IsSeparable.trans` unavailable. No original dependency node can be pruned.
Verdict: pass.
5. Checked all three DAG records against the Lean declarations, including
`proof`, `proof_deps`, `proof_origin`, and the new-node metadata. Verdict: pass.

Second-reading changes: removed the redundant proof-only
`Mathlib.Algebra.Algebra.Subalgebra.Tower` import and expanded this report with
independent search, source, unit-route, and axiom checks. No statements or
definitions were changed; neither geometric split can be closed by the elementary
APIs found in a few minutes.

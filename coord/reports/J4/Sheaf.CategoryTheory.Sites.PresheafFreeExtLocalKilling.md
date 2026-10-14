## What changed

Verified the already-landed proof of
`Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling`. The sandbox module is
unchanged in every signature, definition and import. Relative to the current
checkout, the wrapper proof uses `exact` instead of `simpa only [] using`; this
is a proof-only simplification. Both public theorems already have complete proofs. The
requested upstream-review #1428 repair is already present: the witness concludes
the vanishing equation directly, without an existential proof witness or True.
The report records this stale assignment for the independent second reader.

The local single-file compile passed in 20.6 seconds. The delivery dry run also
checks every declaration's axioms with the maintainer's probe.

## Proved and sorry left

Holes closed by this worker: none (0 of 0 starting sorries).
Holes added: none. Sorries remaining in the delivered module: none.

Already proved, with signatures preserved:
- `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness`
  (node `lem-sc-presheaf-free-ext-local-killing-witness`).
- `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`
  (node `lem-sc-presheaf-free-ext-local-killing`).

The two private helpers `epi_locally_surjective` and
`exists_presheaf_cover_lift` are also proved. The imported theorem
`CategoryTheory.Abelian.Ext.exists_epi_comp_eq_zero` in
`Sheaf.CategoryTheory.Abelian.ExtEpiEffacement` has a complete proof in the
checkout. No decomposition or net hole reduction is claimed.

## No longer needed

None. No import or DAG node was removed. The existing witness proof genuinely
uses `lem-sc-ext-epi-effacement` through the proof-only import
`Sheaf.CategoryTheory.Abelian.ExtEpiEffacement`; the wrapper uses the witness.
The existing unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says this module still contains sorry. It does not.
The repair list still names upstream review #1428's padded witness conclusion,
but the padding was already removed in landing 20261013T190156-L-3221515.
The landed change record
`coord/changes/presheaf-ext-local-killing-witness-padding.md` documents the
subsequent explicit Ext type annotation, landed as
20261013T222416-L-1227531. Both node copies agree with the current unpadded
statements and the proof route. Neither a new theorem nor another padding repair
is needed. The maintainer should retire the stale repair-list entry.


## Second reading by J4

1. Compared the entire sandbox module with the repository using `diff -u`.
   The sole difference is the wrapper's `exact` in place of `simpa only [] using`.
   All existing signatures, visibility, definitions and imports are byte-for-byte
   unchanged. No interface change record is needed. Verdict: pass.
2. Independently compiled the delivered file (18.5 seconds, no warnings or
   errors). Compiled a scratch copy with `#print axioms` for both public theorems
   and both private helpers (19.8 seconds). Every result contains exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the delivered source: no `sorry`, forbidden declaration, hollow
   definition, or arbitrary data chosen from an unproved existence theorem.
   The lift presheaf is explicitly constructed as pairs satisfying an equation;
   the effacement witnesses are local to a theorem and come from a proved lemma.
   Verdict: pass.
3. There are no new or unproved split statements to validate or search for.
   Read the actual constructions: empty generator sets cause no obstruction,
   q=1 uses the same positive-degree effacement, and q=0 is deliberately excluded.
   The existing witness duplicates the wrapper's proposition but is fully proved,
   rather than moving a hole. No decomposition or hole reduction is claimed.
   Verdict: pass.
4. Read the imported effacement proof, searched both library roots for local
   killing/lift lemmas, and inspected Mathlib's Sites/EpiMono and LeftExact APIs.
   The generic epi/local-surjectivity route requires additional instances such as
   WEqualsLocallyBijective; the explicit small-valued image construction here
   avoids adding such hypotheses. Both public imports support the signatures;
   ExtEpiEffacement is correctly proof-only. No old proof dependency is unused.
   Read dag/units/sk-prop-cd.json: this edit changes no realized node or unit step
   and keeps the existing route. No import or module is pruned. Verdict: pass.
5. Read both node files and their recorded Lean statements, proof steps,
   proof_deps and proof_origin. The wrapper uses the witness; the witness uses
   lem-sc-ext-epi-effacement and the two explicit private constructions exactly
   as recorded. No node changes are required. Verdict: pass.

Second reading changed the report's inaccurate claim of an identical module,
recorded the actual proof-only wrapper simplification, and added this independent
review. No Lean repair was needed. Holes closed: none (0 of 0); holes added: none;
split off: none. The stale repair assignment remains a maintainer follow-up.

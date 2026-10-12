## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_integral_dim_one`
with a complete Lean proof from the three existing planned declarations.
For each point, Mathlib's `exists_isAffineOpen_mem_and_subset` supplies an
inhabited affine neighbourhood. Its complement is finite by
`IsAffineOpen.finite_compl_of_integral_dim_one`. The theorem
`exists_globallyGenerated_invertible_nonvanishing_eq` then supplies an invertible,
globally generated module and a section whose nonvanishing locus is that neighbourhood.
These witnesses satisfy `exists_isAmple_of_enough_globallyGenerated`.
The finite-subcover argument is already encapsulated in this last criterion.

No signatures, definitions, imports, or docstrings changed. The DAG's three proof
steps and all three proof dependencies are retained; no node update is needed.
The unit route is unchanged.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_integral_dim_one`
(blueprint: `lem-sc-integral-dim-one-ample`). Added 0 holes, split off 0 statements.
No sorry remains in the delivered module.

This is a proof from existing statements, not an unconditional closure of all
transitive proof dependencies. The existing dependencies remain separate work items:
`AlgebraicGeometry.IsAffineOpen.finite_compl_of_integral_dim_one`
(`lem-sc-affine-complement-finite-on-integral-curve`),
`AlgebraicGeometry.Scheme.Modules.exists_globallyGenerated_invertible_nonvanishing_eq`
(`lem-sc-find-globally-generated`), and
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_enough_globallyGenerated`
(`lem-sc-enough-globally-generated-ample`). This delivery changes none of them.

Validation: the authorized single-file compiler succeeds without errors or warnings.
The result handles a neighbourhood equal to the whole affine scheme: its complement
is empty, and the existing construction permits that finite complement. Nonemptiness
of every chosen neighbourhood is witnessed by the point itself.

## No longer needed

None. All three proof imports and all three planned dependency nodes are used.
No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The pointwise interface of the ampleness
criterion already performs the finite-cover selection, so the caller need not
construct a finite index type. This is the same argument as the existing DAG plan.
LeanFinder returned generic integrality facts, not a shorter ampleness theorem;
Loogle and grep searches likewise supplied no replacement route.

## Second reading by T1

1. PASS: compared the entire delivered module with the repository using `diff -u`.
   Only the sole theorem's proof body changes; its signature, all definitions,
   imports and docstrings are byte-for-byte unchanged. No change record is needed.
2. PASS: independently compiled the module with `lcompile.py`, without errors or
   warnings. Inspected the whole file: no remaining sorry, new declaration, hollow
   definition or prohibited mechanism. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_integral_dim_one`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected
   from the existing, unchanged proof dependencies; this is one local hole closed,
   not an unconditional proof of the transitive closure.
3. PASS: no statements were split off and no holes were added. Read the interfaces
   and docstring arguments of all three existing dependency modules. The chosen
   point proves nonemptiness of its affine neighbourhood, the finite-complement
   theorem supplies precisely the construction's remaining hypothesis, and
   `hs.symm` has precisely the equality orientation the criterion asks for.
   The case U = Y has empty finite complement and is permitted. No arbitrary data
   witness is made into a definition.
4. PASS: repeated library searches by ampleness and global generation, and fresh
   msearch LeanFinder, Loogle and Mathlib grep searches. LeanFinder returned generic
   affine-section/function-field facts; Loogle did not recognize IsAmple; exact-name
   Mathlib grep found no ampleness/global-generation theorem. No shorter applicable
   route was found. All three proof imports are used and already plain imports;
   public imports supply signature notions. No old proof dependency is unused, so
   `No longer needed` is complete. Read `dag/units/sk-thm-curveestimate.json`:
   its realized statement and steps are unchanged. The existing node's affine-cover,
   section-construction, ampleness route is retained; finite-cover selection is
   encapsulated by the pointwise criterion.
5. PASS: read `lem-sc-integral-dim-one-ample.json` and compared its statement,
   three proof steps, proof_deps and document proof_origin against the Lean proof.
   They agree; the finite-subcover step remains inside the cited criterion. There
   are no new nodes requiring metadata, and no existing node update is necessary.

Second reading changed only this report, adding the independent checks above.
No Lean repair was needed. Closed 1 of 1 local holes; added 0 holes; split off 0.

## What changed

`Sheaf.AlgebraicGeometry.AffineFormalMapPresentation`: replaced the original
`affine_formal_map_presentation` hole by a complete proof from existing results and
one new, torsion-free affine dictionary. The statement and public imports are unchanged.
Added four proof-only imports. The tensor-unit comparison is constructed as `asIso`
using `affine_completion_baseChange_unit`, so its specified hom is definitionally equal.
The fixed-exponent affine-limit implication of Remark 0888 is applied directly to
the actual section-limit map on the top affine open, giving exponent 2 * t.
A proved private linear-square lemma transfers its kernel and cokernel annihilators:
kernel membership is preserved by the source equivalence; for cokernels, quotient
annihilation gives a range witness, which is lifted back by source surjectivity and
reflected by target injectivity.

`Sheaf.AlgebraicGeometry.AffineCoherentTildePresentation`: new proved public theorem
`AlgebraicGeometry.affine_coherent_tilde_presentation`. It uses the quasi-coherent
counit on the inverse affine chart, restriction composition, and the restriction/pullback
comparison. This proves the coherent-sheaf part of the old node's first step.

`Sheaf.AlgebraicGeometry.AffineFormalMapLimitDictionary`: new public theorem
`AlgebraicGeometry.affine_formal_map_limit_dictionary`, containing the representation
and naturality work before the torsion argument. It supplies linear equivalences to the
actual categorical section limits with an elementwise commuting square. It has neither
a torsion hypothesis nor an annihilator conclusion, and accepts the already chosen
coherent presentation and tensor-system isomorphism as inputs.

All three modules compile together through lcompile.py. No definition, existing signature,
visibility, or target was changed. New modules follow the module-system header convention.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.affine_formal_map_presentation`
(node `lem-weil-pbc-affine-formal-map-presentation`). This is a decomposition, not a
sorry-free proof: one hole closed and one new hole added, net zero.

Also proved `AlgebraicGeometry.affine_coherent_tilde_presentation`
(node `lem-weil-pbc-affine-coherent-tilde-presentation`) and the private
`AlgebraicGeometry.annihilators_of_linear_square` helper. The coherent presentation
uses the library's existing coherence criterion; no new assumptions are added.

The only sorry left in the delivered files is
`AlgebraicGeometry.affine_formal_map_limit_dictionary`
(node `lem-weil-pbc-affine-formal-map-limit-dictionary`). Its docstring records the
construction via Tag 087W, finite-module completion as tensor, inverse comparison,
and naturality of the specified limit cones. It is strictly the representation/naturality
part; the ideal annihilation argument is proved in the assigned module.

Existing dependencies can still contain holes, including
`AlgebraicGeometry.affine_completion_baseChange_unit`; these were reused and not
copied, changed, or newly introduced by this delivery.

## No longer needed

The second reading replaced the proof-only import
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated` by the smaller
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimit`. The old direct node
`lem-weil-pbc-formal-systems-annihilated-by-power` is no longer used; only its
fixed-exponent affine-limit implication
`lem-weil-pbc-formal-annihilation-affine-limit` is needed. The full four-way
equivalence, formal cover criterion and reverse implications are bypassed on this
proof route. No claim is made that their modules leave the whole target closure.

The other four old direct proof dependencies are retained transitively:
`lem-weil-pbc-coherent-formal-modules-affine`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-completion-finite-module-tensor`. They now support the two comparison
nodes instead of being direct dependencies of the assigned theorem. No original
public import is removed: all three describe its unchanged statement.
No algebraization or affine candidate result is imported, avoiding a cycle through
a consumer. No unit realization or chapter route is pruned.

## Where the brief, the DAG or earlier work was wrong

The plan's first two steps supply only a Spec-level formal equivalence, whereas this
statement uses a general affine X, its ideal sheaf, the chart pullback, and categorical
limits of ordinary sections. The missing bridge is now stated with the exact
commuting square needed downstream. The completion-finite-module-tensor node has
no `lean` record, but has an established Mathlib match in
`Mathlib.RingTheory.AdicCompletion.AsTensorProduct`; the dictionary imports that
module instead of duplicating its theorem.

The compiled mirror initially lacked AffineCompletionBaseChangeUnit; it refreshed
before final compilation. The temporary diagnostic placeholder was removed. LeanSearch
returned Internal Server Error; the other search kinds and local source searches worked.
The cited Stacks sources were read online because literature/stacks-project is absent
in this read-only checkout. Tags 087W, 0888 and 0889 support the stated construction.

The item and both new nodes are below the unit's realized nodes. The unit route is
unchanged. Edge cases checked mathematically: I=0 gives constant systems, I=A gives
zero formal systems and limits, and the zero ring/empty spectrum uses those same
comparisons. Zero modules and zero morphisms are covered; the dictionary imposes no
annihilation on a general morphism, so it does not smuggle in the conclusion.

## New nodes

`lem-weil-pbc-affine-coherent-tilde-presentation`, module
`Sheaf.AlgebraicGeometry.AffineCoherentTildePresentation`: proved affine-chart transport
of the quasi-coherent tilde counit. This needs coherence only to obtain quasi-coherence.

`lem-weil-pbc-affine-formal-map-limit-dictionary`, module
`Sheaf.AlgebraicGeometry.AffineFormalMapLimitDictionary`: the remaining representation
and limit-naturality comparison, without torsion. Its source is the affine construction
in Stacks 0889(1), using 087W and 00MA. One new hole. No change records are required.


## Second reading by G2

1. **Interfaces: pass.** Read the diff of the assigned module against the repository.
   Its complete existing theorem signature is byte for byte identical, as verified by
   extracting the signature through the final `:= by` delimiter; all three original
   public imports remain. The other two modules are new. No existing definition,
   visibility or target changes, and no forced adaptation or change record is needed.

2. **Proof and axioms: pass as a decomposition.** All three delivered files compile
   together through `lcompile.py`, without errors or warnings. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound` for
   `affine_coherent_tilde_presentation` and `annihilators_of_linear_square`.
   The assigned theorem and the new dictionary additionally show `sorryAx`, as
   expected from the reported open comparison and existing dependencies. The only
   delivered hole is the named dictionary theorem; no data definition, arbitrary
   data witness, forbidden declaration, or hidden hole is introduced. The completed
   transfer proof uses source surjectivity and target injectivity correctly.

3. **New statements: pass.** Read both new signatures and docstrings against Stacks
   [087W](https://stacks.math.columbia.edu/tag/087W),
   [00MA](https://stacks.math.columbia.edu/tag/00MA), and the affine construction in
   [0889](https://stacks.math.columbia.edu/tag/0889).
   Coherence plus the affine tilde presentation implies P is finite, so B=S tensor P
   is finite and complete over S. Fullness gives phi between the finite S-modules,
   and natural cones give the exact section-limit square. An arbitrary supplied eta
   is allowed because b incorporates its inverse limit map; clarified this explicitly
   in the dictionary docstring and node. I=0 gives constant quotient systems; I=A
   gives S=0 and zero systems; the zero ring, empty spectrum, zero modules and zero
   maps obey the same comparisons. The dictionary drops the entire torsion estimate,
   takes the presentation and eta as inputs, and is a strictly separate part of the
   argument, not a restatement of the item. Repeated searches with different words
   using LeanFinder, Loogle, msearch grep, and local lean/ found building blocks but
   no duplicate theorem. The existing affine-limit equivalence is only the cone
   part on an open subscheme; it does not supply this inverse comparison and tensor
   factorization. The internal-Hom dictionary concerns a different map.
   No split-off hole could be closed in a few minutes; it requires chart and ideal
   transport plus natural quotient-system comparisons.

4. **Route and pruning: pass after repair.** Replaced the full TFAE with the direct
   affine-limit lemma and explicit positive exponent 2*t, then compiled the result.
   The four other original proof dependencies survive through the comparison nodes;
   the removed direct annihilation criterion is listed above. All four proof-only
   imports in the assigned module supply declarations it calls. The dictionary's
   two plain imports carry the building blocks of its still-open documented proof.
   Read `dag/units/sk-thm-p1.json`: none of these three nodes realizes the unit
   statement or its fixed steps; its `realized` entries and route remain intact.
   This closes one original hole and adds one hole, net zero; it is a decomposition,
   not a completed target or a net proof gain.

5. **DAG: pass after repair.** All three `lean.statement` signatures agree exactly
   with their Lean declarations; all `proof_deps` equal the union of step uses.
   The existing node now records the direct affine-limit invocation. The dictionary
   node records the precise directions of rho, eta, and the limit comparisons.
   New nodes have the required source, complete proof steps, searches, creation,
   blueprint, chapter, unit and Lean records. Existing-node edits stay within the
   owned proof fields; its statement and statement dependencies do not change.

Second reading changed the torsion proof and its import/dependency to the direct
fixed-exponent affine-limit lemma; clarified the dictionary's natural comparison
construction and updated its node/searches; corrected the pruning report. It added
no holes and changed no signatures.

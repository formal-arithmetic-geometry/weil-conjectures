## What changed

Replaced the proof hole in
`TopCat.Sheaf.isZero_secondCohomology_of_noetherian_dim_le_one` with an application of
`TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound` at `d = 1`
and `q = 2`, proving `1 < 2` by `decide`. The signatures match directly, including
Lean's dimension-bound coercion. No statement, definition, import, or DAG route changed.
The existing node already records exactly this specialization of Stacks Proposition 02UZ.
The curve-estimate unit's statement and realized route are preserved.

## Proved and sorry left

Closed the only hole:
`TopCat.Sheaf.isZero_secondCohomology_of_noetherian_dim_le_one`
(node `lem-sc-noetherian-cohomology-vanishing-abelian-dim-one`).
There are no sorries left in the delivered module and no holes added or split off.
This is a proof from the existing general vanishing theorem; its underlying component
and irreducible vanishing obligations remain separate existing work, not new holes.
Single-file compilation through `lcompile.py` succeeded without warnings.

## No longer needed

None. The sole proof import
`Sheaf.Topology.NoetherianTopologicalCohomologyVanishing` is used. The Mathlib public
imports continue to supply the statement's topology, cohomology, and category instances.
No nodes or modules of the stated plan were bypassed.

## Where the brief, the DAG or earlier work was wrong

No discrepancy found. The general vanishing theorem has precisely the required
Noetherian-space, dimension-bound, and abelian-sheaf hypotheses. Its specialization
retains empty spaces and spaces of dimension zero; no nonemptiness or separation
hypothesis was introduced. Repository and Mathlib searches found no shorter direct
vanishing theorem for arbitrary abelian sheaves. Lean Finder returned cohomology
primitives and unrelated group-cohomology results, so the existing DAG route was used.

## Second reading by N3

1. Compared the only delivered module with the repository using `diff -u`.
   The only change is the theorem's proof body, from `sorry` to the two-line
   application. Its signature, docstring, imports, universes, namespace, and
   module exposure are byte-for-byte unchanged. No change record is required.
2. Compiled the delivered file independently through `lcompile.py`: exit 0,
   no warnings. Scanned it for forbidden declarations and proof escapes: none;
   there are no definitions or remaining sorries in this module. Compiled a
   scratch copy with `#print axioms` for
   `TopCat.Sheaf.isZero_secondCohomology_of_noetherian_dim_le_one`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes
   from existing lower vanishing obligations, not a new hole in this delivery.
   Thus the local hole is closed, but this is not yet an axiom-clean target proof.
3. No statements were split off, no nodes were added, and no data are chosen.
   Read the general theorem's actual signature: `d : ℕ`, the dimension bound
   in `WithBot ℕ∞`, arbitrary abelian sheaf, and `d < q`. Substitution with
   `d = 1`, `q = 2` needs only the closed arithmetic fact proved by `decide`.
   The empty space and dimension-zero spaces remain included; no nonemptiness,
   sobriety, or separation hypothesis is introduced.
4. Searched `lean/Sheaf`, `lean/WeilConjectures`, and Mathlib's sheaf-cohomology
   directory with dimension/vanishing terminology, and made an independent
   Lean Finder search for Grothendieck vanishing/cohomological dimension.
   Its hits were injective/projective-dimension criteria, which do not supply
   the needed topological bound. The upstream scheme-module result is not a
   theorem for arbitrary abelian sheaves on arbitrary topological spaces.
   The existing general theorem is the shortest direct route. Its sole private
   proof import is used; the public Mathlib imports supply statement notions
   and the sheaf/Ext/category instances. No old proof dependency is unused.
   Read `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`, with no recorded steps; this local specialization
   does not bypass or alter that unit route.
5. Read both the item's node and its general-vanishing dependency's node and
   Lean module. The item's one proof step, sole `proof_deps` entry, and
   source-based `proof_origin` already describe exactly this application.
   Checked Stacks Proposition 02UZ at
   https://stacks.math.columbia.edu/tag/02UZ (the local literature copies are
   absent on this machine): Noetherian X, dimension at most d, every abelian
   sheaf, vanishing for p greater than d. Every hypothesis and the conclusion
   match the specialization. No DAG edits are needed.

Verdict: pass. Changed only this report by adding the independent second
reading and explicitly recording the inherited `sorryAx`; no Lean repair was
needed. Holes closed: the one named above. Holes added: none. Split off: none.

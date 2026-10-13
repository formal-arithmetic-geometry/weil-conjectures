## What changed

Replaced the sole hole in `PerfectHomMayerVietorisLocalRows` by a complete Lean
reduction to `perfect_hom_mayerVietoris_stage_rows` in the new module
`Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows`.
The new theorem isolates geometric construction and local recognition; it has no
supplied `H`, `d`, `ident`, or transition hypothesis and asserts no exactness of
the filtered-colimit row. The original module proves that remaining argument:
it forms `A = S ⋙ colim`, proves exactness at every spot by
`ShortComplex.Exact.map`, constructs the morphism using `colimit.desc`, and
checks naturality using `colimit.hom_ext`. It builds the natural isomorphism
from `H` to the underlying middle diagram, uses preservation of filtered
colimits and uniqueness of colimits to construct `a`, and proves the
representative pinning equation by `colimit.ι_desc`. Universe shrinking for
AB5 and the forgetful functor is explicit. All existing signatures and
visibility are unchanged; no definition or consumer module is changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.perfect_hom_mayerVietoris_local_rows`
(node `lem-pc-perfect-hom-mayer-vietoris-local-rows`), from a named intermediate.
Added and left: `AlgebraicGeometry.perfect_hom_mayerVietoris_stage_rows`
(node `lem-pc-perfect-hom-mayer-vietoris-stage-rows`), the only remaining hole
in the delivered files. This is a decomposition: one hole closed, one added,
net zero. The categorical colimit argument itself is fully proved.
The intermediate is strictly the geometric portion of the argument: it
supplies exactness in the diagram category, not in its group colimit, and
neither supplies nor identifies the externally specified set colimit.

## No longer needed

Removed the original direct proof imports `PerfectThickClosure`,
`LocalizedPullbackPerfectModel`, `PerfectImpliesQCoh`,
`AffineDerivedPullbackTensorTilde`, `DerivedAdjoint`,
`DerivedMayerVietorisFunctorial`, and `PerfectHomStageColimit`.
Their nodes remain needed by the geometric intermediate, where their imports
and proof plan now live; none of these modules is claimed globally pruned.
Removed the redundant direct import `Mathlib.Algebra.Category.Grp.FilteredColimits`;
`Mathlib.Algebra.Category.Grp.AB` already publicly imports it.
In the new stage-row module, replaced the public import of
`Mathlib.Algebra.Category.Grp.AB` by
`Mathlib.Algebra.Category.Grp.Colimits`: the statement needs group colimits
and the preadditive structure, while AB5 is used only in the original module
and remains a plain proof import there.
No mathematical dependency node is globally pruned. The original node's
`proof_deps` now names the stage-row intermediate and the filtered exactness
node; the detailed geometric dependencies are on the new node.

## Where the brief, the DAG or earlier work was wrong

The old plan is mathematically the intended route, but its declarations do
not directly supply a tail-indexed exact row diagram, coherent transition
morphisms, and four local recognition witnesses. These are now a precise
geometric intermediate, leaving the generic colimit step proved here.
`DerivedMayerVietorisFunctorial` currently marks its direct-image theorem
as an interface dispute concerning arbitrarily chosen comparison isomorphisms.
The new statement does not prescribe those choices: its proof must construct
compatible comparisons from adjunction units/counits and the functorial
K-injective presentation. The unresolved coherence work stays visible in
this intermediate; this delivery does not resolve that interface dispute.
Edge cases: the tail contains i, so its nonemptiness is explicit; empty opens
are allowed and give zero local Hom groups; no affine-intersection or local
continuity hypothesis is introduced. The unit's `realized` arrays are empty,
and no unit statement or route is changed.
Searches: LeanFinder found generic exact-colimit lemmas, Loogle found
`ShortComplex.Exact.map`, msearch grep found no geometric Hom-row theorem.
LeanSearch returned Internal Server Error (recorded unavailable).
Blueprint searches for Mayer Vietoris Hom, filtered exact rows, and stage
rows found no matching node.

## New nodes

`lem-pc-perfect-hom-mayer-vietoris-stage-rows`, in the item's chapter and unit,
records the simultaneous exact stage rows, comparison to the exact limit
row, transition and limit pinning, and neighboring locality. Its Lean module
is `lean/Sheaf/AlgebraicGeometry/PerfectHomMayerVietorisStageRows.lean`.
Its source and numbered proof dependencies follow the geometric part of
Stacks Tags 09RE and 08BW. The local literature files are absent on this
machine; the source was read at https://stacks.math.columbia.edu/tag/09RE
and https://stacks.math.columbia.edu/tag/08BW. No change record is needed: no existing interface
has changed. Both the original node and the new node follow the implemented
reduction.


## Second reading by R1

1. Compared the sole existing module with the repository by `diff`, and
   compared its theorem signature as bytes: identical. Existing node changes
   are exactly `proof`, `proof_deps`, and `proof_origin`. No existing
   definition, visibility, statement, or hypothesis changes; no change record
   is required. Verdict: pass.
2. Read the complete categorical proof: tail nonemptiness and directedness,
   universe shrinking, exactness under colim, naturality of the descended
   row morphism, transport of the supplied set colimit, and representative
   pinning. There is one named theorem hole in StageRows and none in
   LocalRows. No forbidden declaration or hollow definition appears. The
   existential rows are eliminated inside a theorem proving an existential
   proposition; no arbitrary existence witness defines public data.
   Compilation and axiom-probe verdict is recorded below.
3. Read the new statement, its full docstring proof, its node, the local
   recognition predicates, and the existing geometric and transport
   interfaces. Checked Stacks [09RE](https://stacks.math.columbia.edu/tag/09RE)
   and [08BW](https://stacks.math.columbia.edu/tag/08BW). The exact stage
   diagram is the geometric portion; the supplied H,d,ident, its colimit
   equivalence, exactness after taking colimits, and the final pinning proof
   are genuinely discharged in LocalRows. This is a valid decomposition,
   not a renamed restatement, and not a net hole reduction. Small cases:
   the tail always contains i (including a one-stage system); empty opens
   and zero perfect objects give zero local terms, with no nonemptiness
   hypothesis on Hom introduced. Boundary and comparison coherence must
   be constructed compatibly, as the docstring specifies; the existing
   disputed arbitrary direct-image comparisons are not asserted valid.
   New LeanFinder search on open-cover derived-morphism exact sequences
   found only the sheaf MayerVietorisSquare short complex; Loogle confirmed
   ShortComplex.Exact.map. Additional msearch grep and local rg found no
   existing theorem supplying the pinned geometric stage rows. Closing
   that geometric theorem is substantial work, not a few-minute repair.
   Verdict: pass, with one explicit geometric hole.
4. The generic colimit proof uses the direct Mathlib exact-map lemma and
   colimit universal properties. Its geometric dependencies are relocated,
   not globally pruned. Checked the old proof dependencies against the
   report: every removed direct dependency remains named in the stage-row
   plan, and no global pruning is claimed. The unit sk-thm-picard-semicon
   has empty realized statement and step arrays; its record and route are
   unchanged. Verdict: pass after the import correction below.
5. Checked both nodes against Lean: the new node's signature is byte-identical
   to the declaration, all required fields are present, chapter and unit
   agree, and proof_deps equals the union of step uses. The original node
   records the implemented stage-row reduction and Mathlib filtered
   exactness; its colimit-transport step is elementary category theory.
   The new node records the remaining geometric proof plan and source.
   Verdict: pass.

Changed only the new module's public Mathlib import, from Grp.AB to
Grp.Colimits, to expose what its statement actually needs. The original
categorical proof is retained without rewriting. Updated No longer needed
above to record this correction. No hole was closed or added by this reading.


Validation: `lcompile.py --all` compiled both delivered modules without errors
or warnings after the import correction. Scratch copies with `#print axioms`
compiled and reported exactly propext, Classical.choice, Quot.sound, and
sorryAx for both declarations. sorryAx is expected from the named geometric
stage-row theorem and existing open dependencies. No further axioms occur.
Scratch probe sources were removed before delivery.

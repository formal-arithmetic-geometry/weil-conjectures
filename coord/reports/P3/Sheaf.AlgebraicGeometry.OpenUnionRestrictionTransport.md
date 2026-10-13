## What changed

Reduced `AlgebraicGeometry.Scheme.open_union_restriction_transport` to the canonical
comparison diagram and proved the remaining categorical transport calculation with
private helpers `comparison_conjugation`, `comparison_pair`, and
`comparison_diagram_pair`. Existing signatures and public imports stay
unchanged. Added the proof-only import `OpenUnionRestrictionComparisonDiagram`.
Removed local generic exactness-instance overrides in favor of the dedicated instances
already provided by `DerivedOpenRestrictionMaps`.

The new statement supplies derived equivalences, natural comparison isomorphisms and
two pasting identities. It does not quantify over local morphisms or their compatibility.
The main proof applies naturality, `Functor.map_preimage`, inverse cancellation and
faithfulness to deduce the required compatibility from the ambient hypothesis.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.open_union_restriction_transport`
by decomposition. No sorry remains in the item module. The private categorical helpers
`comparison_conjugation`, `comparison_pair`, and `comparison_diagram_pair`
are proved directly.

Added one hole: `AlgebraicGeometry.Scheme.open_union_restriction_comparison_diagram`,
node `lem-sc-open-union-restriction-comparison-diagram`, in the new module
`Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram`. This is a decomposition,
not a net reduction in holes. The geometric comparison construction remains to be proved.

## No longer needed

Removed the item's direct proof imports `Sheaf.AlgebraicGeometry.DerivedOpenLocalization`
and `Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`. Their nodes
`lem-pc-derived-open-localization-universe` and
`lem-pc-open-derived-localization-adjunction` remain planned dependencies of the new
comparison diagram and its proof-only imports. No module or node is claimed pruned
from the targets' transitive closure. The old proof dependency
`def-pc-derived-open-restriction-maps` remains a statement dependency and its public
import remains: the proof uses its functors and canonical comparison isomorphisms.
It is not a pruned node.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's new node incorrectly repeated the original transport statement
in prose and recorded only the theorem name as its Lean signature. Both are corrected:
the node now describes exactly the comparison diagram and records the full Lean statement.
Its copied review records were removed, its blueprint ancestor was corrected, and the
original node's proof route now records the new dependency and the categorical calculation.
The generic simplification uses `Category.comp_id` inside mapped composites.
The previous attempt did not compile: its pointwise-isomorphism components and
composite inverse maps were not normalized before comparing them with the natural
isomorphism components. Explicit `Iso.app_hom`, `Iso.app_inv`, `Iso.trans_hom`,
`Iso.trans_inv`, and associativity rewrites now close these conversions. The final
transport calculation is normalized in an abstract categorical helper. Locally
marking `Functor.mapDerivedCategory` and `schemeDerivedOpenRestrictionCompIso`
irreducible prevents unnecessary unfolding of their localization constructions;
this affects elaboration only. The dependent existential witnesses are preserved
with `Exists.imp` rather than unpacking and rebuilding their whole diagram, which
the profiler identified as the main elaboration bottleneck. Category arguments
in the final application are explicit. No definitions or interfaces were changed. Preflight conservatively classifies the
local attribute changes as an interface change; the required change record explains
that these commands are local and lists the unchanged declaration users.

The source Tag 08BW gives the restriction-based Mayer–Vietoris sequence; the explicit
comparison and coherence construction is an agent-written expansion using Mathlib's
canonical restriction comparisons. Empty opens, disjoint opens, equal opens and the
empty union require no additional hypotheses: every identification used remains an
isomorphism, and the categorical calculation applies unchanged. The unit's realized
statement and steps are unchanged.

## New nodes

`lem-sc-open-union-restriction-comparison-diagram`: isolates the geometric construction
of the three derived equivalences, the restriction comparisons and their two pasting
identities. The remaining transport of compatible morphisms is proved in the item.
LeanSearch was unavailable; Loogle and the Mathlib source search found the underived
comparison ingredients, but no complete derived comparison diagram theorem.

Change record: `coord/changes/open-union-restriction-local-elaboration.md`.


## Second reading by P3

1. Compared the complete item against the repository with `diff`, and independently
   compared the theorem signature byte for byte: unchanged. Its existing docstring
   and public import are unchanged. The only attribute changes are local elaboration
   settings, documented in the change record; no definition or target changes.
2. Read all three categorical helper proofs and the dependent existential reduction.
   Naturality moves the transported morphism across cW/cV; map_preimage removes the
   fully faithful lift; inverse cancellation gives conjugation by qI; faithfulness
   reflects the ambient compatibility equality. There are no new definitions or
   extracted arbitrary data. The sole new sorry is the reported named comparison
   theorem. Compilation and axiom checks are recorded below.
3. Read the comparison theorem and its node against their geometric construction.
   Its conclusions are comparison isomorphisms and coherence, with no local maps or
   compatibility assertion: a genuine geometric part of the original argument.
   Empty opens, empty intersection, equal opens, and top opens still have the same
   canonical scheme isomorphisms and equivalences; no nonemptiness or separation
   hypothesis is needed. Its source and natural-language proof describe constructing
   and deriving these comparisons, rather than postulating a gluing result. Checked
   Stacks Tag 08BW: it supplies the restriction-based Mayer–Vietoris context; the
   explicit comparison construction is correctly identified as an expansion.
   Fresh LeanFinder search for scheme-isomorphism/restriction coherence, Loogle for
   restrictRestrictComm, and source searches for overFunctorEquiv and comparison
   transport found ingredients, not this full derived diagram. The remaining hole
   requires the geometric construction and coherence, not a few-minute tactic repair.
4. Checked the old proof dependencies and all imports: the two localization imports
   move to the comparison theorem's planned proof; DerivedOpenRestrictionMaps stays
   public because signatures use it; ComparisonDiagram is proof-only. No transitive
   module pruning is claimed. The unit record sk-thm-picard-duality and its realized
   fields are untouched; this is a reduction below the unit's route. One hole is
   closed and one is added, so this is decomposition with zero net hole reduction.
5. Both nodes' recorded Lean signatures match the delivered text. The existing node
   changes only proof, proof_deps, and proof_origin, accurately recording comparison
   construction followed by categorical conjugation. The new node has source,
   searches, creation/blueprint metadata, proof steps and dependencies, and matches
   the sole remaining named sorry.

Second-reading changes: clarified that the old derived restriction definition node
is retained as a statement dependency, not pruned; added this independent review and
verification results. No Lean proof, signature, or new statement needed repair.

Verification: both delivered modules compiled locally without errors or warnings.
A scratch copy with `#print axioms` for all three private helpers reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The transport theorem and comparison
theorem reported only those plus `sorryAx`, as expected from the one open geometric
comparison theorem (and any still-open upstream statements). No forbidden axiom,
unsafe/opaque declaration, external implementation, or sorry in data occurs.

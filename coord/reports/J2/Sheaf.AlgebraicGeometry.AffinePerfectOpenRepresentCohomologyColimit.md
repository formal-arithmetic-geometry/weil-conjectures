## What changed

Replaced the original hole in `AlgebraicGeometry.affine_perfect_open_represent_cohomology_colimit`
with an explicit construction. The proof transports the principal-open augmentation
isomorphisms through the derived equivalence, takes their canonical inverses, proves
compatibility with power transitions, and constructs the natural cocone by restriction.
It then uses Mathlib's filtered-colimit criterion: finite-stage surjectivity and eventual
vanishing of restriction-zero morphisms supply its two conditions, the latter applied
to the difference of two morphisms.

Added `Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionSurjective` and
`Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionEventuallyZero` for these two strict
parts of the H^0 comparison argument. Both have complete source proofs and DAG nodes.
No existing signature, definition or declaration visibility changes. The unused
public PerfectComplex import removal is documented in
`coord/changes/Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit.imports.md`. The original node now records
the actual construction and these dependencies. The unit route is retained.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.affine_perfect_open_represent_cohomology_colimit`
(node `lem-sc-affine-perfect-open-represent-cohomology-colimit`). No sorry remains in
its module. This is a decomposition, not a proof free of sorry dependencies: one
original hole closed and two new, strictly smaller holes added.

The only new sorries are:

- `AlgebraicGeometry.koszulOpenHom_restriction_surjective`
  (`lem-sc-koszul-open-hom-restriction-surjective`).
- `AlgebraicGeometry.koszulOpenHom_restriction_eventually_zero`
  (`lem-sc-koszul-open-hom-restriction-eventually-zero`).

Existing dependencies `affine_perfect_koszul_principal_unit` and the compatibility
clause of `affine_perfect_open_represent_cohomology_core` are used as stated. The
repository core lemma now has a complete proof; this delivery does not change it
or any existing dependency holes. The inverse and cocone construction and the categorical
assembly are proved in this delivery. No data is chosen from an arbitrary existence
statement: each inverse is the uniquely determined categorical inverse.

## No longer needed

Removed the unused public import `Sheaf.AlgebraicGeometry.PerfectComplex`: no
existing signature or definition in the module uses it.

Removed the original module's unused direct proof imports:
`Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison`,
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`, and
`Sheaf.Paper.KoszulComplex`. The first two nodes are now proof dependencies of the
new H^0 assertions, rather than direct steps of the assembly. The KoszulComplex module
remains reachable via KoszulOpenSystem and the principal-unit lemma. No globally
unreachable module is claimed. The comparison and affine-equivalence modules remain
imported by both new finite-stage assertions, along with
`Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology` and Mathlib
KProjective, matching the proof plans in their nodes.

Removed the earlier, unsubmitted sandbox modules and nodes for ExistsV and ExistsCocone
and the unregistered IsColimit helper. Their proved inverse/naturality parts are inlined
in the original module; the remaining colimit assertion is replaced by the two strict
finite-stage assertions above. They are not part of this delivery and need no work.

## Where the brief, the DAG or earlier work was wrong

The inherited report claimed that ExistsV and ExistsCocone were still sorry although
both had been developed further, and it supplied a second-reading heading prematurely.
Its cocone proof did not compile: reassociation was required before rewriting functorial
composition, and TypeCat morphism equality required `ext` rather than `funext`.
Its last IsColimit hole lacked a node and a complete proof docstring. The delivery
replaces it by surjectivity and eventual-zero assertions, each separately needed and
strictly weaker than representability.

The LeanSearch service returned Internal Server Error on both attempts. This is
recorded as unavailable without claiming a no-match result. LeanFinder, Loogle and
local source searches found no direct derived Koszul representability theorem.
The local source packet is absent; the mathematical proof was checked against the
online Stacks Tag 08DD (https://stacks.math.columbia.edu/tag/08DD).
WANTED: literature/stacks-project/perfect.tex, Proposition 36.9.5 and its referenced
Koszul comparison equations, for the two new nodes. The proof origin records an agent
translation of that online argument.

Edge checks: the empty sequence has empty open and zero tails; E=0 admits only zero
morphisms; a zero morphism vanishes already at its own stage. For nilpotent generators
with empty open, a sufficiently late diagonal power transition is zero. No boundedness
hypothesis on E is imposed; K-projectivity applies to the source tails.

## New nodes

`lem-sc-koszul-open-hom-restriction-surjective` states finite-stage representation of
an arbitrary derived section, with supplied inverse augmentations. It supplies only
the surjectivity condition in Mathlib's colimit criterion.

`lem-sc-koszul-open-hom-restriction-eventually-zero` states that a restriction-zero
morphism is killed by a later power transition. It supplies the injectivity condition
by applying it to the difference of morphisms. It assumes no chosen inverse or cocone.

## Second reading by J2

1. Compared the existing module with the repository using diff and extracted its
   theorem signature: byte-for-byte identical. There are no new definitions,
   changed declaration visibilities or changed target statements. The public-import
   removal has its own import change record and downstream analysis.
   The two additional files contain only new named theorem statements. Verdict: pass.
2. Compiled the three files in import order through lcompile.py; all passed without
   warnings. Scanned all delivered Lean for forbidden declarations and holes: exactly
   the two reported named theorem sorries remain. Checked #print axioms for each
   delivered theorem: only propext, Classical.choice, Quot.sound, and sorryAx
   from the acknowledged open dependencies. The inverse is categorical inv of the
   specified augmentation; the cocone is written explicitly, with no arbitrary
   existence witness used to supply data. Verdict: pass as a decomposition.
3. Read both new statements and their complete proof docstrings against Stacks
   https://stacks.math.columbia.edu/tag/08DD and its comparison in Tag 08D1.
   Surjectivity and eventual-zero injectivity are separate, strictly smaller parts
   of representability; neither is the original conjunction under another name.
   Checked r=0, the zero ring, E=0, zero morphisms, nilpotent generators (empty U),
   and r=1 with f a unit (the augmentation and transitions are invertible). For
   arbitrary r the bounded finite free source allows E to be unbounded. Repeated
   LeanFinder, Loogle, and Mathlib grep searches with different queries; inspected
   local uses of koszulOpenObject and koszulOpenHomDiagram, and upstream sources.
   No replacement theorem found. The generic filtered-colimit criterion is already
   used. Closing either remaining hole requires the derived-Hom/H^0 comparison
   identifications, rather than a short direct application of an existing result.
   Verdict: both statements true, needed, sourced, and not duplicates.
4. Read the proof from inverse augmentations through naturality to both conditions
   of Types.FilteredColimit.isColimitOf'. Its same-stage equality criterion is
   correctly discharged by applying eventual-zero to phi minus psi. Checked the
   old proof_deps: principal-unit remains used, and derived-comparison is moved to
   the two new nodes, not discarded. No node realizing a unit step is bypassed;
   dag/units/sk-thm-picard-duality.json is unchanged (its existing realized arrays
   are empty). No globally unreachable module is claimed. Verdict: pass.
5. Checked that each node's proof_deps is the union of its proof-step uses, that
   the main node describes the actual Lean assembly, and that both new nodes have
   all required provenance/source/search/created/blueprint/lean fields. Compared
   each new node's verbatim Lean statement with its file. Verdict: pass after
   repairing missing planned imports and recording independent searches.

Changes made by the second reader: added plain proof-dependency imports to both
new lemma modules; removed unused PerfectComplex import from the original module;
updated the new-node searches; corrected the report's obsolete assertion that the
core lemma still contains a hole and clarified the retained comparison imports.
The first dry run required a change record for the removed public import. Added
that record, checked the sole direct importer retains its own public PerfectComplex
import, and compiled it unchanged against the delivered overlay. Thus all transitive
downstream exports remain available. No proof body or theorem statement needed repair. One original hole is closed and
two new holes are added (local net -1); this is a decomposition, not a claim of
sorry-free target progress.

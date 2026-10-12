## What changed

Replaced the sole sorry in `AlgebraicGeometry.etaleSetSectionContinuity` by a complete
Lean proof from three strictly smaller statements: coherence of the section comparisons,
lifting one limit section to a stage, and detecting equality at a common later stage.
The proof constructs the actual functor `E`, takes identity identifications `e`, constructs
the canonical natural transformation, and proves injectivity and surjectivity of
`colimit.desc` with Mathlib's stage representatives and `Types.colimit_sound'`.

The restriction clause is proved, rather than split: a private, fully proved helper
uses `etaleSetInverseImageRestriction`, naturality at the diagonal, and
`pullback.diagonal_fst`. The evaluated restriction isomorphism composed with the
unit/diagonal map is the identity, so that map is an isomorphism and hence bijective.

Moved the existing, unchanged `etaleSetSectionComparison` definition into
`Sheaf.AlgebraicGeometry.EtaleSetSectionComparison`. The original module publicly imports
it. This avoids cycles when the new statements refer to this concrete map, preserves
its name/type/body and downstream access, and avoids costly elaboration of repeated
expanded adjunction expressions. No existing statement or definition's meaning changes.

All five modules compile without warnings with `lcompile.py --all`. The original
continuity theorem's signature and restriction-unit definition are unchanged.

## Proved and sorry left

Proved/reduced: `AlgebraicGeometry.etaleSetSectionContinuity` (1 of 1 original sorries).
The private `etaleSetRestrictionUnit_bijective` is fully proved from the existing
restriction theorem. The relocated `etaleSetSectionComparison` is a real definition,
with its original data, and contains no sorry.

Three named public statements remain `:= by sorry`, each in its own new module:

- `AlgebraicGeometry.etaleSetSectionComparisonLaws`:
  `lem-weil-pbc-sets-section-comparison-laws`.
- `AlgebraicGeometry.etaleSetSectionLift`: `lem-weil-pbc-sets-section-lift`.
- `AlgebraicGeometry.etaleSetSectionEventualEquality`:
  `lem-weil-pbc-sets-section-eventual-equality`.

Each has its source, complete proof in words, and DAG node. They independently isolate
coherence, existence of a representative, and equality of representatives. None restates
the original existential functor/cocone/bijection/restriction package. Existing dependency
sorries are used as authorized by stage 3, and are not claimed closed.

Edge cases were checked in the mathematical statements: coherence needs no limit or
qcqs assumptions; the inverse system may be constant or have a one-element index; a
preorder need not be antisymmetric; the two stages in eventual equality may differ;
and the empty etale object is covered by the empty family and has a unique section.
Directedness moves all finitely many restrictions/equalities to a single later stage.

## No longer needed

Removed from the main module the five direct proof imports:
`Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison`,
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`,
`Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`,
`Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`, and
`Sheaf.CategoryTheory.ColimitSiteSections`.
Their nodes remain needed below the new lifting/eventual-equality statements, so these
are moved dependencies, not claims that the affine-site argument is unnecessary.

The original twelve direct proof dependencies are replaced by the three new statement
nodes and `lem-weil-pbc-sets-etale-inverse-image-restriction`. Specifically, affine-site
colimit, affine projections, affine-site topos, affine inverse-image comparison,
colimit-of-sites sections, site-equivalence transport, constant connected colimit,
finite affine coverings, and the pretopology sheaf condition move into the two descent
nodes. Composition units move below the comparison definition and its coherence node.

`lem-weil-pbc-filtered-colimits-commute-finite-limits` is no longer needed on this route:
the new proofs use stage representatives, eventual equality, finite choices of stages,
and direct sheaf gluing/separatedness, instead of a separate finite-limit commutation
argument. No unit statement or realized unit step is bypassed (`sk-thm-iff` is unchanged).
No entire library module is asserted globally unreachable.

Second reading removed the unused public import
`Mathlib.CategoryTheory.Limits.Types.Colimits` from each of
`EtaleSetSectionComparisonLaws`, `EtaleSetSectionLift`, and
`EtaleSetSectionEventualEquality`. Their signatures mention no colimits; the main
continuity module retains its public colimit import because its signature uses `colimit.desc`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The existing abstract site declarations
are useful inputs but do not directly instantiate the concrete upper-tail section
comparison: site transport, comparison coherence, and finite-cover descent still
require substantial glue. Those gaps are the three new named statements.
The source checkout's `SectionContinuity` theorem is for abelian sheaves, so it is not
a proof of this set-valued statement.

The repository copy does not contain its referenced Stacks TeX files on this machine.
The sources were read from the Stacks pages and their upstream TeX was downloaded only
into this item's scratchpad. LeanSearch returned an Internal Server Error; its searches
are recorded as unavailable without a mathematical verdict. LeanFinder, Loogle, source
grep, and blueprint searches did not find the required concrete set-valued statements.

The comparison definition's relocation is recorded in
`coord/changes/etale-set-section-comparison-location.md`. No downstream source adjustment
is required because the original module publicly reexports the unchanged declaration.

## New nodes

`def-weil-pbc-sets-section-comparison` records the existing comparison map in its new
standalone module, without introducing a second notion or changing its definition.

`lem-weil-pbc-sets-section-comparison-laws` isolates identity, composition, and cone-leg
compatibility. Its hypotheses omit all continuity assumptions and its proof uses the
existing inverse-image composition/unit theorem and pullback pasting.

`lem-weil-pbc-sets-section-lift` isolates existence of a stage representative of one
limit section, following affine-site continuity and finite affine-cover gluing.

`lem-weil-pbc-sets-section-eventual-equality` isolates equality detection for two
representatives, allowing distinct stages, following affine-site continuity and finite
cover separatedness. It is also used to synchronize overlap equalities in the lift node.

The change record is `coord/changes/etale-set-section-comparison-location.md`.

## Second reading by T1

1. **Existing declarations unchanged: pass.** Compared the original module with the
   repository by `diff`, then checked the declaration substrings directly. The continuity
   theorem signature is byte for byte identical. Both existing definition signatures and
   bodies are byte for byte identical, including the relocated section comparison.
   The relocation has its change record and public reexport; the only direct external
   importer is `SetsPushforwardStalkStrictHenselization`, which retains access. No
   hypothesis, conclusion, target, or mathematical definition changed.
2. **Proof and trust: pass.** Read the complete functor/cocone construction, representative
   argument for injectivity, lifting argument for surjectivity, and diagonal/naturality
   argument for restriction. All five files compile with no errors or warnings using
   `lcompile.py --all`. There are exactly three sorries, only in the reported named public
   helper theorems; no definition contains sorry and no forbidden declaration is present.
   A scratch copy prints the axioms of both definitions, the restriction helper, the main
   theorem, and all three open helpers; only the permitted standard axioms and `sorryAx`
   from the explicitly open statements occur. The main theorem is a reduction, not a
   claim that its transitive dependencies are already proved.
3. **Split statements: pass.** Each helper isolates a strict part of the argument:
   coherence requires no limit, lifting gives a single representative, and eventual
   equality detects equality of two representatives. All have complete mathematical
   proof docstrings and matching nodes. Checked identity and constant systems, a singleton
   index, non-antisymmetric preorders, distinct initial stages, and the empty etale object.
   Directedness synchronizes finite choices; finite affine refinements of overlaps are
   needed for gluing. Read Stacks [0EYL](https://stacks.math.columbia.edu/tag/0EYL) and
   [09YN](https://stacks.math.columbia.edu/tag/09YN): the latter states the set-valued section
   comparison, so the argument does not assume that the abelian theorem 09YQ itself
   applies to sets. Independent LeanFinder queries for coherent adjunction comparisons
   and descent/equality of set-valued inverse-image sections, Loogle for adjunction units,
   and `rg` on both Lean roots found no existing concrete theorem closing these helpers.
   Structure-sheaf eventual equality and module-valued filtered-colimit results are
   different statements. None of the open helpers can be closed in a few minutes from
   these generic facts without the documented transport and descent argument.
4. **Route and pruning: pass after import repair.** The categorical combination already
   uses Mathlib stage representatives and colimit equality directly. Removed the unused
   public Types.Colimits import from all three new helper modules. Kept the planned
   affine-site, transport, and finite-cover inputs under the two descent nodes. The
   report accounts for all eleven removed old direct dependency edges, distinguishing
   moved dependencies from the one pruned finite-limit-commutation node. The unit
   `sk-thm-iff` and its `realized` statement/step are untouched; no unit route is bypassed.
5. **DAG agreement: pass.** The existing node changes only `lean`, `proof`, `proof_deps`,
   and `proof_origin`. Its steps match the checked Lean argument. Checked the new
   nodes' sources, statements, signatures, creation/blueprint/chapter/unit fields,
   dependency unions, and search records. The comparison definition has its own node;
   eventual equality does not depend on lifting, so the finite-cover proof is not circular.

Changed only the three unused public imports and this review/pruning documentation.
The mathematical proof, existing signatures, helper statements, definitions, and node
records were retained.

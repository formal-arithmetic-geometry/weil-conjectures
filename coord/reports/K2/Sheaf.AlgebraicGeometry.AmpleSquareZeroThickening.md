## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.Modules.isAmple_of_isAmple_tensorPullback_of_square_zero`
in `Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening` now has a complete Lean proof from a
strictly smaller single-section lifting statement and existing library declarations.

Two private helpers are proved: `surjective_of_square_zero` uses Mathlib
`IdealSheafData.support_pow_succ`, `support_bot`, `Hom.support_ker` and closedness of the
immersion image; `affine_of_affine_preimage` restricts the immersion, constructs its
surjectivity instance, proves the target open Noetherian, and applies the recorded
finite-surjective affine descent theorem. The main proof unpacks ampleness downstairs,
uses the section-power lifting lemma, obtains openness from the existing
`nonvanishing_section_trivializes`, proves equality of the inverse image open, and builds
all witnesses of ampleness upstairs. Tensor-power invertibility is the proved source
instance `IsInvertible.tensorPow` from `ProjectionFormula`.

Added `Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus`, containing one public theorem
with its source and complete natural-language proof. Its conclusion is only the equality
of the nonvanishing set of one upstairs section, pulled back to Z, with a given affine
nonvanishing open downstairs. It assumes no ampleness, makes no affineness assertion
upstairs, and does not choose a point. It is the cohomological part of 09MS, before the
finite-surjective affine descent and the covering argument. Both node proof routes were
updated to match this reduction. Existing public imports and all existing signatures are
unchanged; new proof imports are non-public.

Both sandbox modules compile without errors or warnings through lcompile.py. The source
was read at https://stacks.math.columbia.edu/tag/09MS; the repository does not contain the
untracked Stacks TeX checkout on this machine. No repository file was edited directly.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.isAmple_of_isAmple_tensorPullback_of_square_zero`
(node `lem-sc-ample-square-zero-thickening`). No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_section_power_locus_of_square_zero`
(node `lem-sc-square-zero-section-power-locus`), in the new module
`Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus`.

This is a decomposition, not a net decrease in holes: one upper hole closed and one
strictly smaller lower hole added. The two private helpers and the assembly are proved.
The existing dependencies, including `nonvanishing_section_trivializes` and
`isAffine_of_isFinite_surjective_of_isNoetherian`, still have their pre-existing holes;
this delivery does not change them. The section-power node retains the needed
cohomology, boundary derivation, and annihilated-module proof dependencies for its worker.

## No longer needed

Pruned node `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine` and its direct import
`Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`: the surjectivity needed here is
proved from Mathlib's support-of-power and kernel-support formulas. No target-wide
unreachability claim is made: other modules can still need this node.

Removed these direct proof imports from the item's module, because the cohomological
argument is isolated in the new section-power node:

- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`
- `Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology`
- `Sheaf.Paper.BoundaryDerivationSquareZero`

Their nodes (`lem-weil-pbc-affine-morphism-cohomology-edge`,
`lem-weil-pbc-closed-immersion-pushforward-annihilated`,
`lem-weil-pbc-closed-immersion-unit-quotient`,
`lem-sc-section-affine-open-kills-cohomology`, and
`lem-sc-boundary-derivation-square-zero`) remain needed by the new section-power node;
they are not globally pruned. The local-Noetherian quasi-separatedness node is likewise
needed there, rather than directly in the parent's proof. The ideal definitions and
Mathlib closed-immersion permanence/finiteness remain needed. No public import removed.

The old proof dependency `lem-weil-pbc-invertible-pullback-invertible` is also no longer
used: the retained `lem-weil-pbc-invertible-pullback-tensor` supplies the pullback
invertibility instance, including in the new section-power argument. This replaces a
proof dependency, rather than asserting that its module is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or signature correction. The planned cohomology results have large
interfaces: the boundary lemma produces injective resolutions and actions for a general
commutative algebra-sheaf extension, while the needed application involves a graded sum
of tensor powers and its degreewise connecting maps. Constructing that graded extension
and establishing all degree/action identifications is not supplied by a single existing
declaration. The new node records these steps rather than pretending the general boundary
lemma directly proves the lifting conclusion.

The planned zero-set lemma is unnecessary for surjectivity. Mathlib has a shorter proof
using the support of an ideal power and the kernel support. The unit
`sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and no steps; this local
reduction bypasses no unit statement or realized step.

Searches: LeanFinder returned free-locus/projectivity and Proj basic-open results, with
no section-lifting result; Loogle returned no hits for the kernel/zero-locus query;
LeanSearch was unavailable (HTTP internal server error). Grep of Mathlib, both library
roots, and DAG nodes found the existing cohomology tools and openness lemma but no
single-section lifting declaration. All search evidence is recorded in the new node.

Edge cases checked for the new statement: identity immersion and I=0 allow k=1 and the
section itself after the pullback comparison; empty schemes impose no point condition;
a zero section has empty locus and permits t=0; n=0 is valid: s is then an arbitrary degree-zero global function, not necessarily
the unit. The same boundary and cohomology-killing argument applies to its powers. Positive k is
essential for reflecting nonvanishing and is included explicitly. The new statement
does not require n>0; the parent separately obtains n>0 from ampleness and proves n*k>0.

## New nodes

`lem-sc-square-zero-section-power-locus`, module
`Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus`: the single-section cohomological
lifting/locus part of Stacks 09MS. It retains the exact-sequence, annihilated-kernel,
affine cohomology comparison, graded boundary derivation, and cohomology-killing tools.
The proof explains the degreewise boundary identifications and positive-power residue
calculation. This is strictly below ampleness: it gives neither affineness upstairs nor
sections covering X. No change record is needed because no existing statement,
definition, or public import changes.

## Second reading by K2

1. Compared the item with the repository using diff and an exact signature comparison.
   The existing theorem signature and every public import are byte for byte unchanged.
   There is no definition change, target change, or change requiring a change record.
   The existing node changes only proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled both modules in import order through lcompile.py; no errors or warnings.
   Scanned for forbidden declarations and proof escapes: none. The only delivered sorry
   is the reported public section-power theorem, with a source, full proof docstring and
   node; no definition contains sorry or chooses data from an unproved existence theorem.
   Scratch-copy axiom probes show only propext, Classical.choice and Quot.sound, plus
   sorryAx for the item, affine descent helper and split theorem. The surjectivity helper
   has only the three permitted axioms. Existential witnesses in the item are eliminated
   inside a theorem proof, not used to define objects. Verdict: pass as a decomposition.
3. Read the new statement, its proof and its node against Stacks 09MS, especially the
   degreewise exact sequence, boundary derivation, affine-open killing and fibre test.
   It assumes no ampleness and asserts no affineness upstairs or covering, so it is
   strictly smaller than the item. Identity immersion, zero ideal, empty schemes, zero
   section and arbitrary degree-zero section all satisfy the statement; positive k
   prevents the zero-section power from acquiring nonvanishing points. Independent
   LeanFinder search for extending a section from a nilpotent closed subscheme returned
   basic-open denominator/annihilation lemmas, not this result. Loogle tensorPow/section
   and msearch grep lift/tensorPow/square-zero returned no hits; rg of both source roots
   found the existing separate cohomology ingredients, not a duplicate. Closing this
   cohomological lemma requires substantial graded-algebra and boundary comparison
   constructions, not a short application of the searched results. Verdict: pass.
4. Read the proof from ampleness downward: surjectivity is proved directly from Mathlib,
   the lifting lemma supplies just one section locus, openness uses the existing
   nonvanishing theorem, and the restricted closed immersion supplies finite-surjective
   affine descent. Each proof import is needed for these steps or for the documented
   route of the open lemma. The existing public imports are preserved. Checked every
   old proof dependency against the pruning report and corrected the missing replaced
   pullback-invertibility node. The unit sk-thm-curveestimate realizes only
   thm-sc-proper-cohomology and has no realized steps; this reduction changes neither.
   Verdict: pass; no shorter available route found.
5. Read both nodes against their modules; the union of step uses equals proof_deps in
   each. The existing node records the actual assembly; the new node has its source,
   statement dependencies, proof, search evidence, split status, creation, blueprint,
   chapter, unit and Lean record. Verdict: pass.

Changed only the report's omitted pruning entry and its degree-zero explanation,
and added independent second-reader search evidence to the new node. No Lean proof or
statement needed repair. One original hole is closed and one strictly smaller hole is
added: net zero, a decomposition rather than an axiom-free proof of the item.

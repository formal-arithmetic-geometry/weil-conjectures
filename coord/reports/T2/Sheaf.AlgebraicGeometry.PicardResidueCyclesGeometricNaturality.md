## What changed

Replaced the original cycle-level hole by a proof from a geometric comparison on
explicit homology quotients. The original declaration's signature is unchanged.

Added `Sheaf.AlgebraicGeometry.AffineResidueCycleHomology`, containing actual
constructions of residue terms, differentials, cycles, the subgroup of incoming
boundaries, and their additive quotient. Proved that its cycle-class map is
surjective and has precisely the incoming boundaries as its kernel. Also constructed
the induced quotient map of a chain map: the evaluated and residue-extended
commutation equations show that it preserves cycles and boundaries. Its equation
on cycle classes is proved, including independence of the supplied cycle-membership
proof by proof irrelevance.

Added `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality`, isolating
only the identification of these quotient homology groups with geometric fibre
cohomology and compatibility of the induced homology maps. This homology-level
statement needs no negative-degree vanishing, target degree-zero differential
vanishing, or independently supplied target trivialization: its target fibre
trivializations are the pullbacks of tau. The original proof explicitly clears
these unnecessary assumptions, retaining its original signature. The original proof
composes those equivalences with the already constructed quotient projections,
transfers surjectivity and the kernel formula, and applies the proved chain-map
formula to obtain the cycle-level equation. No definition chooses data from an
unproved existence theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_residue_cycles_geometric_naturality` by a
complete Lean reduction. Added one hole:
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality`, node
`lem-sc-picard-residue-homology-geometric-naturality`.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
It is not a claim that geometric naturality is now proved without dependencies.
The new hole is strictly the geometric part of the argument: it contains no
cycle-map surjectivity or boundary-kernel conclusion, and acts on the actual
quotient homology groups with their already constructed induced maps. Those
algebraic assertions are independently proved in the delivery.

The new declarations
`AlgebraicGeometry.Scheme.affineResidueCycleClass_surjective_kernel` and
`AlgebraicGeometry.Scheme.affineResidueCycleHomologyMap_class` are proved.
All helper definitions and the commutation lemma are free of holes.
There are no holes left in the original module or the algebraic helper module.

## No longer needed

Removed these direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`,
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.
Their nodes `lem-pc-module-pullback-adjunction`,
`lem-pc-rf-perfect-base-change`, and `lem-pc-cohomology-sections-affine-base`
are retained in the geometric subproblem's proof plan and imports. Therefore
none of these modules is claimed to be pruned from the targets' import closure.
No unit statement or realized unit step is bypassed; the unit record has empty
realized arrays for this local comparison.

The original node's proof dependencies now name only the geometric homology
comparison and the two proved algebraic steps. The old direct dependencies
`def-sc-structure-sheaf-cohomology-pullback` and `def-weil-residue-field` also
leave its proof_deps: their definitions remain in its unchanged statement
imports and in the geometric subproblem. No globally pruned module.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped after finding no short geometric proof. That does
not obstruct this stage: the algebraic quotient and its map can be constructed
and proved, and the residual geometric comparison can be stated separately.
The DAG's source cycle-quotient step is now proved rather than postponed.
The 60-second compiler limit was kept. The original theorem scopes its
heartbeat budget to account for specializing the large derived-localization
interface. Its unchanged but now unnecessary hypotheses require a scoped
unused-variable linter setting. The new geometric interface takes the residue
prime p and its equality to the evaluation kernel explicitly; this avoids
normalizing nested residue-field instances when unpacking its existential
conclusion. The final proof uses explicit Exists.elim calls rather than tuple
unpacking, avoiding expensive reconstruction of a case-elimination motive in
the original dependent letI goal. The complete original module then compiled
in 33.9 seconds. No check of mathematical correctness is disabled.

Checked the remaining geometric statement against Stacks Tags 0B91 (arbitrary
base change), 0BF2 (the derived arrows and compatible fibre trivializations in
its proof), and 01XK (cohomology over an affine base). Checked the quotient and
induced-map construction against Section 12.13, Tag 010V, and Mathlib's additive
quotient and scalar-extension API. LeanSearch returned Internal Server Error;
LeanFinder, Loogle and local searches supplied the algebraic API but no exact
geometric comparison. The source pages were read online because this machine
has the literature lists but not the downloaded Stacks or blueprint texts.

Edge cases: for n=0 the target family is empty; the source quotient is still
needed. A zero complex gives the zero quotient. Nonzero source boundaries
are retained in the subgroup and killed by the class map. Target incoming
boundaries vanish under the supplied hCzero, but the algebraic construction
and proof do not depend on this special case. No source differential vanishing
or minimality hypothesis was introduced.

## New nodes

`lem-sc-affine-residue-cycle-class-quotient` records the explicit quotient and
its proved surjectivity and kernel formula, in
`Sheaf.AlgebraicGeometry.AffineResidueCycleHomology`.

`lem-sc-affine-residue-cycle-homology-map` records the constructed map induced
by a chain map and its proved formula on cycle classes in the same module.

`lem-sc-picard-residue-homology-geometric-naturality` records the remaining
geometric comparison and naturality on quotient homology, with one named hole
in its own module, a source and a complete proof in words.

The original node's proof, proof_deps and proof_origin are updated to the Lean
reduction. No existing statement, definition, public import or visibility was
changed. No change record or forced adaptation is needed.

## Second reading by T2

1. Interface: compared all three delivered modules with the repository. Only
   PicardResidueCyclesGeometricNaturality exists there. Its theorem signature,
   including the dependent prime-instance lets, is byte-for-byte unchanged;
   its docstring and public imports are unchanged. The existing node changes
   only proof, proof_deps and proof_origin. No definition or target is changed.
2. Proof: read the complete quotient construction, the evaluated chain-map
   square, the quotient lift and the original theorem's reduction. The subgroup
   is the comap of incoming range along the cycle inclusion, not a zero subgroup.
   The 0,1 square sends boundaries to boundaries and the 1,2 square sends cycles
   to cycles. The original proof transfers surjectivity and the kernel formula
   through eK, then evaluates homology naturality on the source class. Proof
   irrelevance identifies the supplied target membership proof. Definitions
   construct their data; none chooses a witness of the open geometric theorem.
   The only remaining hole is picard_residue_homology_geometric_naturality.
3. Split statement: read Stacks Tags 0B91, 0BF2 (the derived-arrow and common
   fibre-trivialization paragraphs), 01XK and Section 12.13 (010V). Properness
   and local finite presentation give the finite-presentation hypothesis;
   flatness and invertibility give relative flatness of each coefficient after
   base change. Strict perfectness gives bounded finite projective section
   complexes on affine U, hence termwise residue tensor computes derived
   restriction. hp identifies the affine prime, and immersion identifies the
   point residue fields. tau and its pullbacks trivialize the fibre coefficients
   compatibly. Thus negative terms, target d01=0 and separate trivializations
   are unnecessary for this comparison. Checked n=0, the zero complex, a
   contractible 0-to-1 summand with nonzero incoming boundaries, and a shifted
   strictly perfect model: none requires an omitted vanishing assumption.
   The hole is the geometric comparison on actual homology quotients; it does
   not assume the cycle quotient's surjectivity or kernel formula. This is a
   genuine decomposition with net zero holes, not a completed geometric proof.
   Independent msearch LeanFinder query about affine perfect-complex restriction
   returned pullback/tensor constructions, not this comparison. Loogle returned QuotientAddGroup.lift, lift_comp_mk' and lift_mk;
   these generic APIs are already used directly by the concrete construction. Independent grep
   for residue homology and cycles/boundaries found specialized group homology.
   Also searched lean/Sheaf, lean/WeilConjectures and upstream WeilConjectures:
   LocalizedStrictPerfectResidueHomology is a degree-zero stalk comparison,
   not this degree-one affine-sections/geometric comparison. No short closure
   of the remaining geometric hole was found.
4. Route and pruning: checked dag/units/sk-prop-av-cube.json. Its statement
   realization and sole step realization are empty, and this local reduction
   bypasses no realized unit step. All five old proof dependencies are accounted
   for in No longer needed; the three geometric proof modules remain imported
   by the geometric subproblem. No globally pruned module is claimed. Reduced
   the algebraic helper's imports so it no longer depends on PerfectComplex;
   imported PerfectComplex explicitly where IsStrictlyPerfect occurs in the
   new geometric statement. Kept the original theorem's public imports.
5. Nodes: read each node against its declarations. The existing node's three
   steps match the Lean reduction. Each new node has its source, self-contained
   statement, recorded searches, creation and blueprint provenance, unit,
   chapter and Lean record. Verified proof_deps equals the union of step uses
   for all four nodes. Added the omitted affineResidueComponent to the map
   node's declaration inventory. The two algebraic nodes are proved; the
   geometric node has the one documented named hole.

Second-reading changes: minimized the new algebraic module's imports, made
PerfectComplex an explicit signature dependency of the geometric module, added
source/blueprint references to both new module docstrings, completed the map
node's declaration inventory, and accounted for the two old definition nodes
in No longer needed. No theorem signature or proof body was changed.

Validation: all three delivered modules compiled together without diagnostics
(10.5 s, 22.3 s and 52.5 s respectively). Explicit #print axioms scratch
copies checked every declaration of the algebraic helper: only propext,
Classical.choice and Quot.sound occur, with no sorryAx. The geometric hole's
axioms are precisely those three plus sorryAx, as expected.
The original theorem's explicit #print axioms also reports exactly propext,
Classical.choice, Quot.sound and sorryAx, reflecting the one split-off geometric
hole. Scratch copies were moved outside lean/ before delivery.

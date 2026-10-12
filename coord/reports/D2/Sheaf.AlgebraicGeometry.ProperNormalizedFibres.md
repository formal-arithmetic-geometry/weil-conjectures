## What changed

Proved `AlgebraicGeometry.Scheme.Hom.connectedSpace_fiber_of_isProper_of_globalSections_iso`
in `Sheaf.AlgebraicGeometry.ProperNormalizedFibres`, with its existing signature and public
imports unchanged. Updated its proof docstring and DAG proof to match the Lean argument.
The Stein factorization lemma provides surjectivity and invertible section maps. The proper
fibre lifting lemma and clopen correspondence reduce connectedness to an elementary field
argument. The fibre square proves the required section-map compatibility explicitly.

The argument follows the last paragraph of Stacks Tag 03H2:
https://stacks.math.columbia.edu/tag/03H2, using the input of Tag 0G7X:
https://stacks.math.columbia.edu/tag/0G7X. The local Stacks source files are absent on this
machine, so these official pages were read directly. No new literature is required.

Validation: single-file `lcompile.py` compilation succeeds. The zero base ring has no base
points, so the universally quantified fibre conclusion is vacuous. For any actual base
point, surjectivity produces a fibre point. Empty and full clopens are both handled by the
zero/one characteristic-section calculation. The lifted section is never assumed
idempotent. All chosen sections and points are local proof witnesses, not new definitions.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Hom.connectedSpace_fiber_of_isProper_of_globalSections_iso`
(node `lem-weil-pbc-stein-normalized-fibre-idempotent`).

No `sorry` remains in the item, and no holes or new declarations were added.
The proof still uses the existing unproved dependencies
`AlgebraicGeometry.stein_universally_closed_factor` and
`AlgebraicGeometry.Scheme.Hom.exists_section_restricting_to_fiber_idempotent`;
these were not proved or modified here. This is a complete stage-3 proof from existing
named statements, not an unconditional axiom-free proof of the entire import closure.

## No longer needed

Removed these direct proof imports and direct DAG proof dependencies:

- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`, node
  `lem-weil-pbc-affine-morphism-relative-spec`.
- `Sheaf.AlgebraicGeometry.ProperBasic`, node `pqf-lem-proper-basic`.
- `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`, node
  `pqf-lem-pushforward-qcoh`.

The direct dependency `lem-weil-pbc-affine-tilde-gamma-adjunction` is also unnecessary:
the structure-sheaf isomorphism is already a conclusion of the Stein factorization input.
Properness consequences needed for that input are Mathlib instances. No separate stalk
identification, local-ring unit/maximal-ideal dichotomy, or quasi-coherence argument is
required in this item. These nodes may still be needed transitively by retained inputs;
this report does not claim they leave the entire targets' import closure.

The retained direct project imports are `ProperFibreIdempotentImage`,
`SchemeClopenIdempotent`, and `SteinUniversallyClosedFactor`. No unit statement or
realized unit step is bypassed (`dag/units/sk-thm-p1.json`).

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical dispute was found. The DAG's extra
quasi-coherence and affine-equivalence inputs repeat work already exposed by the sharp-map
isomorphism in `stein_universally_closed_factor`. Its stalk argument can be implemented
more directly on neighbourhood sections and the Cartesian fibre square, followed by the
field zero-or-unit dichotomy. The rewritten DAG and docstring record this shorter glue.

## Second reading by D2

1. **Interface: pass.** Read the full module and its diff against the repository.
   The existing theorem signature is byte for byte unchanged: arbitrary commutative
   `R`, proper `f`, invertibility of the canonical ring map, and every base point `s`.
   No declaration, definition, public import, or universe changed. The only source
   changes are its proof, its explanatory proof docstring, and three plain imports.
2. **Proof: pass.** Independently compiled the delivered file with `lcompile.py`
   (3.9 seconds, exit 0, no warnings). A scratch copy with `#print axioms` compiled
   (2.7 seconds) and reports exactly `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`. The last comes from the two existing open inputs named above;
   the delivered module contains no `sorry` or forbidden declaration mechanism.
   Checked the conjunction projections of the Stein input, the isomorphism of
   every section map, the direction of the fibre homeomorphism, and the explicit
   `appLE` equality from the Cartesian fibre square. The field argument only
   requires the image to be idempotent, never its neighbourhood lift. The local
   existential witnesses are used in a proof; no data definition chooses one.
3. **Split statements: pass, none added.** There are no new declarations, nodes,
   or holes to validate or close. Read the retained lifting and clopen statements
   and checked that their exact conclusions supply the sections used. Independently
   read Stacks [03H2](https://stacks.math.columbia.edu/tag/03H2) and
   [0G7X](https://stacks.math.columbia.edu/tag/0G7X); the argument matches their
   normalized-affine reduction. Checked the zero base ring (no base points),
   nonemptiness for an actual base point, and both constant idempotents. The
   clopen-one calculation uses nontrivial scheme stalks, not a nontriviality
   assumption on an arbitrary ring of sections.
4. **Route and pruning: pass.** Repeated a LeanFinder search with the alternative
   pushforward-structure-sheaf formulation and searched project and Mathlib
   sources for connected fibres and Stein factorization. No shorter applicable
   independent theorem was found. The upstream henselian connectedness proof
   imports `SteinFactorizationAffine`, which itself depends on this item, so it
   is not an alternative input. Both Mathlib public imports occur in the signature;
   all three retained project imports occur in the proof and remain plain imports.
   Compared the old and new `proof_deps`: all four removed nodes are named in
   `No longer needed`, including the affine tilde/global-sections node. Read
   `dag/units/sk-thm-p1.json`: none of those removed nodes is a realized unit
   statement or step, and its `realized` record is unchanged. Pruning claimed here
   is direct dependency pruning, not removal from the entire target closure.
5. **DAG agreement: pass.** The node changes only `proof`, `proof_deps`, and
   `proof_origin`. Verified that `proof_deps` is exactly the union of step `uses`
   and checked each retained dependency's recorded Lean declaration. The three
   steps describe, respectively, surjectivity and section-map invertibility,
   characteristic-section lifting, and the residue-field/fibre-square argument.
   The node's statement and Lean statement record remain unchanged. No new-node
   fields or change records are required.

Second reading changed only this report by recording the independent review and
axiom check. No proof or metadata repair was needed. Net local holes closed: one;
holes added: zero. This does not certify the existing open inputs as proved.

## What changed

Replaced the sorry in
`AlgebraicGeometry.gradedModule_quasicoherent_realization` by a complete Lean proof
from `AlgebraicGeometry.balancedAction_quasicoherent_realization`, a new geometric
intermediate statement in `Sheaf.Paper.BalancedActionQuasicoherentRealization`.
The original signature, visibility, hypotheses, conclusion and docstrings are unchanged.
No definitions or existing intermediate interfaces were changed.

The proof forms the sheaf coproduct, proves quasi-coherence using the existing
`Scheme.Modules.isQuasicoherent_sigma`, and constructs its B-action explicitly:
`Sigma.desc` extends each homogeneous map, `DirectSum.toAddMonoid` extends in the
scalar, and the internal-grading additive equivalence identifies the scalar domain
with B. Coproduct extensionality proves additivity, the unit and scalar equations,
and the homogeneous multiplication equation. Induction on both finite homogeneous
sums proves the full multiplication law. After applying the geometric intermediate,
the proof constructs and verifies the colimit descent maps and transports the
homogeneous compatibility equation through the resulting isomorphism.

The algebraic finite-sum argument adapts the proof pattern in
`Sheaf.Paper.GradedCohomologyModuleStructure`; that module is not imported, since
this proof works directly with sheaf morphisms and categorical coproducts.
Added proof imports of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
and the new geometric module to the item. The new module keeps the existing
`RelativeSpecBaseChange`, `AffineModuleCorrespondence` and Mathlib tilde interfaces
as proof imports for its outstanding geometric argument.

Validation: both sandbox modules compile in import order with lcompile.py, without
errors or warnings. All Lean lines are at most 100 characters. No axiom, hollow
definition, or anonymous/private sorry was introduced. The unit record sk-thm-p1
was read; neither this helper nor its parent realizes one of that unit's fixed
statement/step nodes. The unit and chapter routes are unchanged.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.gradedModule_quasicoherent_realization`
(node `lem-weil-pbc-graded-module-quasicoherent-realization`). No sorry remains in
the item's module.

Added exactly one hole:
`AlgebraicGeometry.balancedAction_quasicoherent_realization`
(node `lem-weil-pbc-balanced-action-quasicoherent-realization`), with the entire
proof `:= by sorry` in its own module, its source, and the complete local-to-global
argument in its docstring and DAG node.

This is a decomposition, not an unconditional proof: one hole closed, one added,
net zero from the delivered declarations. The algebraic construction and
coproduct/isomorphism transport are proved; the geometric action-extension,
localization/gluing and affine correspondence remain. The new statement has no
grading, homogeneous action family, coproduct data or coproduct conclusion, and
its scalar compatibility is for a pre-existing B-action. It isolates steps 2--3
of the old plan after proving step 1, rather than renaming the original statement.

Edge cases checked mathematically for the new statement: M = 0 gives F = 0;
empty X gives empty Y and unique modules/maps; B the zero ring forces id_M = 0
by the unital ring map rho and thus M = 0, consistent with empty Y; B = A with
the structure action recovers M across the identity base change. No finite-type,
Noetherian, nonzero-ring or nonempty-scheme condition is needed. On each affine,
balancing and O_X-linearity give the actual C tensor_A B-action. Non-affine
overlap intersections are refined by basic affine opens, never assumed affine.

## No longer needed

No existing imports were removed. No existing dependency module is claimed
pruned from the targets' closure.

The parent's direct geometric dependencies
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-relative-spec-base-change`,
`lem-weil-pbc-affine-morphism-relative-spec`, and
`lem-weil-pbc-affine-module-correspondence`
are replaced at the parent by the new balanced-action node. The first, second,
third and fifth remain dependencies of the new node's proof; affine-morphism
relative Spec remains underneath relative-spec base change and affine module
correspondence. This relocation is not pruning.

No direct use of affine section calculations or localization is needed for the
proved homogeneous-action construction: its entire argument is in the sheaf
category, using the coproduct universal property. Neither
`Sheaf.Paper.GradedCohomologyModuleStructure` nor its cohomology dependencies are
needed by this proof and none was imported.

## Where the brief, the DAG or earlier work was wrong

No false statement or target mismatch was found. The existing graded-action
assumptions imply the unital action and the required A-balancing equation.

There are two interface details to retain for subsequent workers. First,
`Scheme.Modules.isQuasicoherent_sigma` takes its index type in Type u, whereas
this item uses N in Type 0. The proof reindexes with ULift and transports
quasi-coherence along `Sigma.reindex`; it does not restrict the theorem's universe.
Second, affine module correspondence consumes a sheaf of modules over the
pushforward algebra, while the graded data initially provide only O_X-linear
homogeneous maps. Constructing the B-action is now complete, but extending that
balanced action on affine sections and gluing it into the required algebra-module
sheaf is precisely the outstanding geometric bridge.

The pinned Stacks tex files are absent on this machine. Read the actual sources
online: Tags 0897 (relative-spectrum paragraph), 01LX (base-change and algebra
identification), and 01SB (affine quasi-coherent module equivalence). The new
node records this and marks the explication as written by an agent. Search:
Lean Finder returned tilde/module/sheaf infrastructure but no balanced-action
realization; grep found the existing affine correspondence and relative-spec
interfaces but no bridge from End(M)-valued ring maps. LeanSearch returned an
Internal Server Error and is recorded as unavailable, not as evidence of absence.
Blueprint searches for 01SB and algebra action found no imported blueprint node
stating this bridge.

## New nodes

`lem-weil-pbc-balanced-action-quasicoherent-realization`, in
`dag/nodes/sec-proper-base-change/`, states the geometric realization of a
balanced action on a single quasi-coherent sheaf. Its module is
`Sheaf.Paper.BalancedActionQuasicoherentRealization`, and its declaration is
`AlgebraicGeometry.balancedAction_quasicoherent_realization`. It inherits the
parent's chapter, unit and blueprint ancestor. It groups the local extension and
gluing step with affine realization; the parent proves the algebraic graded
construction and the categorical transport. No change record is necessary:
all existing signatures and visibility are unchanged, and the parent's new
imports are proof-only.

## Second reading by U4

1. Compared the delivered parent module with the read-only repository using diff,
   and compared its entire theorem signature byte for byte: identical. Only two
   proof imports and the proof body were added. No existing definition, statement,
   visibility or target was changed, and no change record is needed. Verdict: pass.
2. Compiled both modules locally in import order. Independently compiled scratch
   copies with #print axioms for both public declarations: exactly propext,
   Classical.choice, Quot.sound and sorryAx. The parent has no sorry; the sole new
   sorry is the named balancedAction_quasicoherent_realization theorem. Checked
   the delivered files for forbidden declarations and hollow definitions: none.
   The coproduct, homogeneous endomorphisms, finite-sum action and ring map are
   explicit constructions. Existential elimination occurs only inside the proof;
   no definition chooses arbitrary data from an unproved existence. Verdict: pass
   as a decomposition, not an unconditional proof.
3. Read the new theorem and its complete affine-local proof against Stacks
   [0897](https://stacks.math.columbia.edu/tag/0897),
   [01LX](https://stacks.math.columbia.edu/tag/01LX), and
   [01SB](https://stacks.math.columbia.edu/tag/01SB). Checked zero M, zero B,
   empty X, B = A, and arbitrary non-affine overlap intersections. The statement
   is true without extra finiteness assumptions. It isolates geometric extension
   and realization, with no grading, homogeneous action or coproduct; the parent
   actually proves the finite-sum action and colimit transport, so this is not a
   restatement. Repeated Lean Finder with endomorphism/affine-projection terminology,
   and searched repository and Mathlib sources for balanced actions and End-valued
   ring maps. No replacement theorem found. Loogle could not resolve ModuleCat.tilde
   and is not evidence of absence. Existing affine correspondence requires the
   algebra-module sheaf that this helper still must construct. This geometric
   bridge cannot be closed by a short application of the existing interfaces.
   Verdict: pass; one strictly simpler geometric hole remains.
4. Read the parent proof from coproduct construction through HEq degree transport,
   finite-sum induction and the explicit colimit descent maps. All existing public
   imports serve the signature (including moduleRings and smulHom); added parent
   imports are proof-only. The helper retains the proof-plan imports for its open
   theorem. Compared all old proof_deps with the report: all five removed direct
   geometric dependencies are named, and their relocation is explicitly not counted
   as pruning. Read sk-thm-p1 and its realized fields: neither delivered node is a
   fixed statement/step realization, and no unit route is bypassed. Verdict: pass.
5. Compared both node lean.statement records verbatim with the Lean signatures and
   checked proof_deps equals the union of proof-step uses. The parent steps describe
   the actual coproduct/action construction and geometric application; proof_origin
   records the new route. The new node has source, full proof, search records,
   creation metadata, blueprint ancestry, chapter, unit and Lean record. Verdict: pass.

Second reading changed only the new helper's docstring and matching node proof:
made explicit that the scalar-restriction clause of 01SB proves quasi-coherence
of the constructed algebra module before applying the equivalence. Added the
independent search record and this review. No Lean proof or signature repair was
needed. One original hole is closed and one geometric hole is added: net zero.

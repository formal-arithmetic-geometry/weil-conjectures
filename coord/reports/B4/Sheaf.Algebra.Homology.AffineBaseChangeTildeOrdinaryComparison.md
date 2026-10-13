## What changed

Replaced the single sorry in
`AlgebraicGeometry.exists_affineBaseChangeTildeOrdinaryComparison` with a complete
Lean assembly proof. Its signature and existing public imports are unchanged.
Added the proof-only import
`Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization`.

Added two modules, one remaining theorem per module:
`AffineTildePushforwardCohomologyNormalization` and
`AffineBaseChangeTildeMateFactorization`. The first constructs the ordinary
pushforward comparison as an actual natural isomorphism using the tilde unit,
sections restriction and the tilde counit. It also constructs the actual map to
derived pushforward cohomology using the right-derived unit, and the cohomology
coordinates for an arbitrary representative. The second constructs the actual
representative of derived affine pullback using the existing unit-normalized
tensor-pullback comparison, the supplied invertible derived counit and e.
None of these definitions contains a sorry or selects an arbitrary witness from
a mere existence assertion. The existing tensor-pullback isomorphism is pinned
by its unit compatibility.

The proof specializes the natural normalization to the extended module complex
and its pullback representative. Its cohomology-coordinate isomorphism is
judgmentally the original b. Substituting the mate factorization and normalization,
then reassociating and applying functoriality, gives precisely the original c
followed by d. Updated the original node's proof route and added matching nodes
for the two remaining steps. No existing definition or statement was changed;
there are no forced adaptations or change records.

Scoped `linter.unusedVariables false` to the original theorem because its existing
signature contains the unused let V. This avoids the new warning after filling
its proof while retaining that signature verbatim.

Second-reader cleanup makes the displayed-functor zero-map instance reuse
`affineBaseChangeTilde_preservesZero` instead of rebuilding its proof. The named
instance bridge is necessary: ordinary instance search does not match the
imported instance's explicitly typed id with this abbreviation in signatures.
The original theorem signature is byte-for-byte identical to the repository,
including the whitespace before its proof.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_affineBaseChangeTildeOrdinaryComparison`
(node `lem-pc-affine-base-change-tilde-ordinary-comparison`). No sorry remains in
the assigned module.

Added two holes, each exactly a public theorem with `:= by sorry` and a source,
complete proof in words and blueprint identifier:

- `AlgebraicGeometry.exists_affineTildePushforwardCohomologyNormalization`
  (`lem-pc-affine-tilde-pushforward-cohomology-normalization`): the natural affine
  cohomology presentation must agree with the explicitly constructed right-unit
  comparison on every representative. This concerns only affine pushforward and
  does not mention derived base change, a coefficient map or a source tensor model.
- `AlgebraicGeometry.exists_affineBaseChangeTildeMateFactorization`
  (`lem-pc-affine-base-change-tilde-mate-factorization`): the source tensor model
  factors the derived mate through the explicit ordinary-to-derived cohomology map.
  It has no natural target-cohomology isomorphism d and no sections-coordinate b.

This is a decomposition, not a sorry-free proof: one upper hole closed and two
strictly smaller holes added (local net -1). The Lean proof combining these parts
is complete. The ordinary pushforward natural isomorphism and all representative
and comparison-map constructions are proved without new holes.

The remaining statements permit zero rings, zero complexes, unbounded complexes
and commuting non-cartesian squares. The normalization makes no K-flat assumption;
the mate factorization retains the supplied K-flat and invertible-counit hypotheses.
The coefficient map is not assumed invertible.

## No longer needed

No existing import was removed, and no module is claimed pruned. The following
old direct proof dependencies are no longer used directly by the assembly proof:

- `def-pc-base-derived-tensor-cohomology-model`
- `def-pc-derived-base-change-map`
- `lem-pc-affine-derived-cohomology-presentation`
- `lem-pc-affine-derived-pullback-tensor-tilde`
- `lem-pc-affine-morphism-hi`
- `lem-pc-derived-base-change-unit-compatibility`
- `lem-pc-source-module-kflat-resolution`
- `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`
- `lem-weil-pbc-tilde-pullback-base-change`

These prerequisites remain in the routes of the two split statements (or their
constructions), so this is a reorganization of direct dependencies, not transitive
pruning. The original node directly uses the two new statements and the existing
coordinate construction. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The original plan correctly describes the argument,
but existence-only affine cohomology presentation/acyclicity isomorphisms do not
state the normalization with the right-derived unit needed for the displayed
square. Applying an arbitrary such isomorphism would not prove that equality.
The normalization theorem makes this missing compatibility explicit. The second
step isolates the genuine common-resolution mate calculation instead of silently
assuming that the coefficient comparison is the canonical derived mate.

Mathlib and the existing source library provide the ordinary tilde counits,
sections restriction, derived units and homology transports used in the explicit
constructions. Searches found no matching normalized affine mate theorem. The
leansearch service returned Internal Server Error; those failures and the actual
leanfinder/grep results are recorded in the new nodes.

## New nodes

`lem-pc-affine-tilde-pushforward-cohomology-normalization`, in
`dag/nodes/sec-picard-framework/`, follows the affine unbounded acyclic-pushforward
calculation (Stacks 0AVW, 08D4), with tilde-unit/counit compatibility and naturality
on representatives. Its Lean module contains the ordinary natural isomorphism,
explicit cohomology comparison and representative cohomology coordinates.

`lem-pc-affine-base-change-tilde-mate-factorization`, in the same chapter, follows
the common K-flat resolution and derived mate calculation (Stacks 0DJ8, 06Y6,
08HY). Its Lean module constructs the pullback representative and states only
the source factorization through the explicit ordinary-to-derived map. Both
nodes inherit the item's chapter/unit and record the target ancestor and route.

## Second reading by B4

1. Compared the original module with the repository using `diff -u`, then compared
   the complete declaration signature byte for byte. The signature, original
   docstring, definitions and existing public imports are unchanged. The only
   original-module edits are the proof-only mate-factorization import, scoped
   unused-variable lint suppression for the existing unused V, and the assembly
   proof. The two other modules and nodes are new. No change record or forced
   adaptation is needed. Verdict: the existing interface is preserved.

2. Read all three modules and checked their module headers, visibility, all
   constructions and every `sorry`. Exactly the two named split theorems remain;
   there is no hole in a definition, forbidden declaration or kernel bypass.
   The ordinary comparison is the explicit tilde unit, identity-on-sections
   restriction comparison and counit; the representative is the explicit inverse
   tensor comparison, inverse supplied derived counit and image of e. The tensor
   comparison comes from the existing proved unit-normalized theorem, not an
   arbitrary unproved existence witness. Compilation and the scratch axiom audit
   are recorded below. Verdict: a genuine assembly proof with two declared holes.

3. Read both split signatures, their docstring arguments and their complete nodes.
   Normalization quantifies over arbitrary representatives C and t and concerns
   only affine pushforward; it does not restate the base-change calculation.
   Factorization retains hK, the A-K-flat hM, hc and the commuting-square hypotheses,
   and ends in the actual right-derived pushforward unit rather than choosing d or
   target sections coordinates. It is the source-mate part of the argument.
   Checked zero rings and zero complexes (all maps between zero objects), identity
   maps (unit/counit triangles), arbitrary degree and unbounded C (bound-one affine
   vanishing and truncation), and a noninvertible coefficient map (only a map is
   asserted, not an isomorphism). The general commuting-square calculation never
   uses cartesianness. Read the 0AVW cohomology display and the 0DJ8 affine tensor
   calculation in perfect.tex. Independent leanfinder searches used exact-functor
   right-derived comparison and Beck-Chevalley augmentation wording, and grep used
   homology/unit and counit/base-change wording. Read the library's acyclic
   pushforward theorem, affine tensor comparisons, sections/pushforward
   normalization and affine derived-unit lemmas. These supply portions of the
   argument but do not assert either new normalization/factorization equation.
   Neither remaining hole closes in a few minutes by applying them. Verdict:
   true, necessary, strictly partial reductions, not a renamed upper hole.

4. Read the assembly from the top: specialize normalization at A', R', phi_f',
   then use source factorization; `rfl` identifies representative cohomology
   coordinates with the existing b; substitution and functoriality give exactly
   z and c of the original statement. No unnecessary logical step was found.
   The zero-map instance now reuses the imported coordinate theorem. Its
   displayed-functor bridge is necessary because type-class search does not match
   the upstream instance in the new public signatures; removing the bridge was
   tested and failed with synthInstanceFailed at the cohomology declarations.
   Public PullbackTilde is justified by data in the exposed
   ordinary-comparison definition; the assembly's new import is proof-only.
   Expanded No longer needed to list every removed old direct proof dependency,
   distinguishing their continued use in the split plans from module pruning.
   Read dag/units/sk-thm-picard-semicon.json: its realized statement and steps are
   empty, and this item is below the unit; no fixed route entry is bypassed or
   altered. Verdict: route preserved; no modules claimed pruned.

5. Compared the original node against the repository: only proof, proof_deps and
   proof_origin differ. The three assembly steps match the actual Lean proof.
   For all three delivered nodes, proof_deps equals the union of proof-step uses.
   Both new nodes carry source/place, self-contained statements, statement
   dependencies, docstring-matching proof plans, searches, created/item/group,
   blueprint ancestry, inherited chapter/unit and Lean records. Checked the
   normalization node's declaration list against the module, and added
   the cited 06Y6 URL to the mate node's source.document. Verdict: nodes agree with
   the delivered code and remaining proof obligations.

Second reading changed: reused the existing zero-map proof in the necessary
abbreviation-instance bridge; restored exact signature whitespace; completed the
direct-dependency removal list; completed the mate source URL list. No mathematical
statement or definition changed.

Validation: `lcompile.py --all` compiled all three final modules cleanly in import
order (45.7 s, 30.3 s and 57.0 s). A scratch module printed the axioms of every
new data construction, the two split theorems, the assembled original theorem,
and the reused upstream tensor comparison. All data constructions and the
upstream comparison use only propext, Classical.choice and Quot.sound. The two
split theorems and the original assembly additionally use sorryAx, exactly as
expected from the two listed open obligations; no other axiom occurs. The scratch
module was removed before delivery. Static scans found exactly two sorry tokens,
no forbidden declarations and no Lean line over 100 characters.

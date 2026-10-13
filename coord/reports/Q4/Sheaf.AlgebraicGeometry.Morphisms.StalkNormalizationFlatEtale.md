## What changed

Repaired the landing refusal for four duplicate private helper statements in
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale` by the return's
explicit alternative, generalizing the helpers in place. All helpers are private
and completely proved; the original public theorem signature is unchanged.

- Removed `maximal_smul_top_ne_top`; properness of the maximal ideal is proved
  locally inside the depth argument using `Ideal.smul_top_eq_map` and maximality.
- Removed the depth-transport helper altogether during second reading: the
  imported flat local depth formula, applied to the canonical stalk ring
  isomorphism (flat by bijectivity, local by surjectivity), gives the needed
  depth inequality. This avoids an equality statement already present privately
  in `FlatLocalDepthReduction` and `FlatFiberLocalDepth`.
- Replaced `normalization_etale_restrict` by
  `morphismProperty_normalization_restrict_iff`: for every morphism property
  respecting isomorphisms, the normalization restricted to the original open
  has the property if and only if the original finite map does. No etale
  assumption is needed in this generalization.
- Replaced `etale_pullback_restrict` by `morphismProperty_pullback_restrict`:
  every morphism property stable under base change passes to the pullback of
  the restriction. The target specializes both property helpers to Etale.

The suggested existing helpers are private. Importing `StalkNormalizationEtale`
also creates a cycle, as confirmed by `tools/import_direction.py may`.
The two generalized morphism-property statements are useful independently of
Etale; the depth and maximal-ideal helpers have been eliminated. No existing sibling
module is changed or adapted. No public import or interface changes.

The assembly still proves the punctured etale restriction, identifies the missing
locus with the closed fibre, and derives source boundary depth from the existing
flat local depth formula. It applies the previously delivered general purity
criterion in `Sheaf.AlgebraicGeometry.Morphisms.FlatQuasiFiniteDepthPurity`.
The item node's proof and proof_origin now describe the generalized helpers.
The new purity module and its node are unchanged by this repair.

## Proved and sorry left

Closed the original direct hole
`AlgebraicGeometry.Scheme.finiteEtale_stalk_normalization_etale_of_flat`
(node `lem-sbc-stalk-normalization-flat-etale`). Its complete assembly has no
sorry. Both remaining private generalized helpers are proved without sorry.

One split-off public hole remains:
`AlgebraicGeometry.Scheme.etale_of_flat_quasiFinite_depth_two_boundary`
(node `lem-sbc-flat-quasi-finite-depth-purity`). Its entire proof is `by sorry`,
with its source and natural-language proof in its docstring and node.
There are no other direct sorries in the delivered files. This is a decomposition:
one original hole closed, one new hole added, net zero before pruning. The assembly
also inherits any remaining holes in the existing flat local depth formula.

Both delivered modules compile with `lcompile.py --all` without errors or warnings.
The import-pruning checker passes separately (exit code 0), verifying that the
specific landing refusal is fixed. The delivery dry run printed OK after compilation,
axiom probes and preflight; only the independent second reading remains, as expected.
Nothing was pushed. Byte-for-byte comparison confirms the public signature is
unchanged; all Lean lines meet the 100-character limit and each node dependency set
is the union of its proof-step uses. The second reading below covers the repaired delivery.

## No longer needed

The original proof-only import `Sheaf.RingTheory.NormalLocalDepthTwo` and node
`lem-weil-pbc-normal-local-depth-two` are not needed by this flat source-open route.
Normality/going-down dimension comparison and uniqueness of the finite depth-two
extension are unnecessary here: the assumed flatness propagates base depth directly.
The flat local depth formula and the new purity criterion remain needed.

All four duplicate private declarations listed by the return are removed. Neither
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale`,
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity`, nor
`Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension` is imported;
the more general helpers supply their special cases without those dependency trees.
No claim is made that these modules are globally unreachable from other targets.

The earlier rejected sibling `StalkNormalizationFormallyUnramified` and its node
remain absent. No normalization-dimension node or module is added.

## Where the brief, the DAG or earlier work was wrong

The returned version repeated four private theorem statements from other modules.
Merely renaming them would preserve the duplication. This repair follows the
return's instruction to generalize in place: arbitrary morphism properties replace
the Etale-specific statements, the existing flat local depth formula replaces the private depth helper,
and the separate maximal-ideal theorem is eliminated. The import-pruning refusal
is addressed by changes to the Lean proofs and statements of private helpers,
not by a rebase or an unchanged re-push.

The obsolete second-reading section is removed because it describes the returned
helper proofs. The second reading below inspects the remaining generalized helpers.

The earlier equivalent formally-unramified restatement remains withdrawn. The
retained purity criterion is strictly part of the argument: it assumes none of the
normalization, smooth local base, minimality or depth propagation setup, and the
item supplies its etale-open and depth-bound premises in Lean. The original node's
normality/dimension detour is unnecessary. The unit's depth-two purity route stays
through the branch-locus criterion used in 0EY6(3); no target or unit is altered.

The unchanged purity statement includes empty sources and W=X. For W empty its
all-stalk depth bound excludes nonempty locally Noetherian sources by considering
a component generic point. Dimension-one points cannot be in the boundary since
depth is at most dimension. Disconnected and nonnormal schemes are allowed. The
new property generalizations require only the explicit stability classes used by
their proofs and also include empty opens. No definitions or arbitrary witnesses
from unproved existence statements are introduced.

## New nodes

The previously delivered node `lem-sbc-flat-quasi-finite-depth-purity`, at
`dag/nodes/sec-smooth-base-change/lem-sbc-flat-quasi-finite-depth-purity.json`, states
`AlgebraicGeometry.Scheme.etale_of_flat_quasiFinite_depth_two_boundary` in
`Sheaf.AlgebraicGeometry.Morphisms.FlatQuasiFiniteDepthPurity`.
Its source is Stacks Tag 0BJH, used in Tag 0EY6(3). Its docstring and node contain
its full argument and the earlier recorded searches. It is unchanged in this repair.
No additional nodes, change records or forced adaptations are introduced.

## Second reading by Q4

1. **Interfaces unchanged — pass.** Read the complete diff against the repository
   module and compared the original public theorem signature byte for byte,
   including all typeclass assumptions, normality, generic-point membership,
   minimality, depth bound, the finite pullback premise, and arbitrary source V.
   No definition, existing declaration signature or public import changed. The
   only additional public declaration is the separately reported purity theorem.

2. **Proof and kernel checks — pass as a decomposition.** Compiled both files
   in import order with `lcompile.py --all`, and compiled scratch copies with
   `#print axioms` for the public declarations and both private helpers. The
   helpers use only propext, Classical.choice and Quot.sound. The assembly also
   uses sorryAx from open dependencies; the purity theorem has exactly its one
   named `by sorry`. There are no new definitions, arbitrary chosen objects,
   forbidden declarations, or hidden proof holes. The closed original hole is
   `AlgebraicGeometry.Scheme.finiteEtale_stalk_normalization_etale_of_flat`; the
   added hole is `AlgebraicGeometry.Scheme.etale_of_flat_quasiFinite_depth_two_boundary`.
   This is one hole closed and one added, net zero before pruning, not a fully
   axiom-free proof of the original item.

3. **Split theorem and sources — pass.** Read Stacks Tag 0BJH, all four
   hypotheses and its discriminant proof, and Tag 0EY6(3), which uses precisely
   this depth-versus-dimension argument. The new theorem is the source-open
   version of that argument: depth >= 2 excludes generic boundary points and
   all dimension-one generalizations belong to W. Flatness and local
   quasi-finiteness supply the remaining hypotheses. The docstring gives both
   the application and the underlying finite locally free discriminant argument.
   Checked empty X, W=X, W empty, zero-dimensional and dimension-one components,
   and disconnected sources: generic or dimension-one points cannot be outside
   W under the depth premise. No normality or dominance is used.
   Repeated semantic search with "ramification confined to points of depth at
   least two", Loogle's Etale/Flat query, and grep for ramification, branch locus,
   purity and depth, plus direct searches of the repository, upstream checkout
   and Mathlib geometry/etale files. No matching general source-open criterion
   is available. `formallyUnramified_of_flat_depth_two_finite_extension` requires
   the whole map finite and its open pulled back from the target; V -> L in this
   item is only locally quasi-finite. The smooth-local purity statements need
   additional fibre density. The new criterion isolates the branch-locus step;
   the item separately proves normalization restriction, boundary identification
   and boundary depth, so it is a genuine reduction rather than a restatement.

4. **Top-down route and pruning — pass.** Read the two morphism-property helper
   proofs: normalization commutes with the smooth open immersion, the finite
   restriction normalizes to itself, and the restriction pullback square transfers
   a base-change-stable property. Their empty-open cases are included. Read
   `hboundary`, which uses minimality and hs, and `hrx`, which uses injectivity of
   fromSpecStalk and the pullback equation. The existing flat local depth formula
   applies to Noetherian local stalks and the composite flat map. This establishes
   every premise of the new criterion. The only old proof dependency removed is
   `lem-weil-pbc-normal-local-depth-two`, with its proof-only import, both recorded
   under No longer needed. The flat local depth formula remains used. Read
   `dag/units/sk-prop-input-spreading.json`: its extension/depth-two local
   computation step uses 0EY6 and is retained through its 0BJH branch-locus
   argument. Its realized arrays are currently empty; this delivery changes none
   of them and bypasses no named realization.

5. **DAG agrees with Lean — pass.** Read both delivered node files. The original
   node's three steps describe the etale restriction, depth propagation, and
   purity application actually written in Lean. Its proof_deps are exactly the
   flat local depth formula and new purity criterion. The new node's Lean
   statement is verbatim, has its source, complete proof, statement dependencies,
   searches, creation record, blueprint ancestry, chapter/unit and Lean record.
   Checked that each proof_deps set is the union of step uses. The new node
   retains the depth-le-support-dimension dependency needed for its pending proof.

**Changes made by the second reader.** Found that depth equality already exists
privately in FlatLocalDepthReduction and FlatFiberLocalDepth, so removed the
remaining duplicate private depth theorem. Applied the imported flat local depth
formula directly to the canonical stalk isomorphism instead. Updated the affected
proof docstring, original node proof/proof_origin and report to describe this
shorter argument. Added the new node's blueprint identifier to its module docstring.
The two generalized morphism-property helpers and the split purity statement
remain unchanged. No new holes, nodes, definition changes or forced adaptations
were introduced by this reading.

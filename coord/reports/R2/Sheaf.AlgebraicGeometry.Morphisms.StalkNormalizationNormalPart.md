## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`
with a complete proof from the named intermediate theorem
`AlgebraicGeometry.Scheme.relativeNormalization_normal_stalks`.
The existing statement and all its public imports are preserved verbatim.

The two proved private helpers are `normal_stalks_of_smooth_integral_base` and
`normal_stalks_of_flat_preimmersion`. The first applies `RingHom.Smooth.isNormalRing`
on affine charts, uses normal section rings of the integral base, and transports prime
localization normality to the source stalks. It applies directly to P -> S, combining the
original smooth and etale ascent steps. The second proves normality transport for any flat
preimmersion by constructing a ring equivalence from injective and surjective stalk maps.
Its use after both pullbacks proves the original localization step entirely.

Added proof imports of `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat`, and the new relative-normalization
module. No definition, public interface or other held module was changed. A theorem-local
unused-variable linter setting preserves the original signature's unused let-bound projection
`n`; there are no compiler warnings. Updated the parent node's proof and proof dependencies.
Both modules compile through `lcompile.py --all`.

## Proved and sorry left

Closed the direct hole in `AlgebraicGeometry.Scheme.stalk_normalization_normal_part`
(node `lem-sbc-stalk-normalization-normal-part`). Its proof is complete from the declared
intermediate theorem. Both private helpers have complete proofs with no direct holes.

Added one direct hole, `AlgebraicGeometry.Scheme.relativeNormalization_normal_stalks`
(node `lem-sbc-relative-normalization-normal-stalks`), in its own new module. Its proof is
exactly `by sorry`. This is only the unlocalized middle step, with locally Noetherian normal
source hypotheses; it contains neither smooth ascent from S nor the pullback-to-stalk step.
It is a decomposition: one upper hole closed and one strictly lower hole added, net zero
direct holes. Existing holes reached through `SmoothNormalRing` remain existing dependencies.
No direct sorry remains in the assigned module. No other hole is added.

## No longer needed

Removed the proof import `Sheaf.RingTheory.EtaleNormalRing`, and removed the parent's direct
proof dependency `lem-weil-pbc-etale-over-normal-ring-normal`. Etale maps are smooth, so direct
smooth ascent along P -> S suffices. Its module and node are unnecessary for this proof;
other target paths may still reach them. `Sheaf.RingTheory.SmoothNormalRing` is retained.

No additional original imports are removed. `lem-weil-pbc-relative-normalization` is needed
for the statement and for the new middle theorem's affine-chart argument, rather than as an
extra direct proof dependency of the parent. The original chart-localization proof and any
potential separate new localization lemma are unnecessary: the proof uses actual stalk ring
equivalences of flat preimmersions. Unit and chapter statements and routes are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the assigned statement was found. The planned first and third steps
have shorter routes described above. Mathlib has relative-normalization construction and
integrality, but no general normal-stalk theorem for a nonintegral normal source. The source
library's `Scheme.Hom.isIntegrallyClosed_stalk_normalization` requires an integral source and
cannot be applied directly to an arbitrary finite etale cover P, which may be disconnected
or empty. The new intermediate theorem supplies exactly this missing generalization.

Read Stacks Tags 035L, 0357, 0358, 034L, 033C and 0307 on the official Stacks pages. The
remaining intermediate theorem follows Tag 035L, with local Noetherianness providing its
finite-component assumption. Checked empty X (empty normalization charts), disconnected
normal components (a finite product of normal domains), and non-dominant or noninjective
maps to Y (the base ring A need not be a domain and the integral closure is in the source
section ring). No connectedness, dominance, or finiteness of normalization is assumed.

Mathlib searches are logged in `searches.jsonl`: LeanFinder supplies construction/integrality
results, Loogle supplies localization of normal domains, and grep finds no normal-stalk result
in Mathlib's normalization module. LeanSearch returned Internal Server Error; it is recorded
as unavailable, not as evidence of absence. Searches of the full DAG and blueprint found the
integral-source theorem but no copy of the new general theorem.

## New nodes

`lem-sbc-relative-normalization-normal-stalks` in
`dag/nodes/sec-smooth-base-change/lem-sbc-relative-normalization-normal-stalks.json` states
normality of unlocalized relative normalization in a locally Noetherian normal source.
Its module is `Sheaf.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks`.
The source is Stacks 035L. Its proof describes finite clopen integral components on each
quasi-compact inverse-image chart, integral closure commuting with the finite product, and
normality of each component normalization using the existing integral-source theorem. The
existing parent invokes it between the two proved helpers. No change record is necessary.

## Second reading by R2

1. Compared the assigned module against the repository with `diff -u` and the
   declaration parser in `stage3_delivery.py`: `statement_changed` is empty.
   The complete signature of `stalk_normalization_normal_part`, including its
   unused let-bound `n`, is byte for byte unchanged. All five public imports
   are unchanged. There are no changed definitions or forced adaptations.
   Verdict: the public statement is preserved.

2. Independently compiled both delivered modules in import order with
   `lcompile.py --all`, including after the repair below: no errors or warnings.
   Searched both modules for forbidden declarations and holes. The only direct
   hole is the reported named `relativeNormalization_normal_stalks`, whose
   body is exactly `by sorry`; neither private helper has a hole. A scratch
   copy with `#print axioms` checked both helpers, the parent and the new
   theorem. The flat-preimmersion helper uses only `propext`, `Classical.choice`
   and `Quot.sound`; the other three also use `sorryAx`, as expected from the
   existing smooth-normal-ring dependency and/or the new middle theorem.
   No other axiom occurs. Removed the scratch copy. Verdict: a valid conditional
   proof, with one upper hole closed and one lower hole added, net zero.

3. Read Stacks 035L, 0357 and 0358 on their official pages, and opened the new
   Lean theorem and its node. Its qcqs assumptions are precisely those of the
   relative-normalization construction. Local Noetherianness gives finite
   components on each quasi-compact inverse-image chart; normal stalks make
   these components disjoint and clopen. Each nonempty component is integral.
   The finite-product integral-closure assertion is justified by projecting
   monic equations in one direction and multiplying their monic polynomials
   in the other. The node's final step uses the actual statement of the
   existing integral-source normalization theorem, not its proof. Checked
   X empty (zero section ring and empty normalization), X a finite disjoint
   union of normal domains (coordinate idempotents separate the charts),
   and a noninjective A -> B (none of the argument requires A a domain).
   This theorem is strictly the middle step: it contains neither smooth ascent
   from S nor localization/pullback transport. It does not restate the item.
   Independently searched with LeanFinder for relative integral closure in
   multiple normal components, with grep for normalization/normality in
   Mathlib, and with `rg` throughout lean/Sheaf, lean/WeilConjectures, the
   upstream source and DAG. The only applicable upstream normal-stalk result
   requires `IsIntegral X`; the dense-open normalization and reduced-curve
   nodes have different hypotheses and conclusions. Loogle's separate
   `IsIntegrallyClosed, RingEquiv` search was unavailable, not a negative result.
   No existing general theorem was found. Verdict: true, necessary and sourced;
   formalizing the component decomposition is substantial, so the hole remains.

4. Read both helpers from top to bottom. Smoothness of the composite P -> S
   incorporates the finite-etale ascent and permits pruning EtaleNormalRing.
   Nonemptiness of the chosen base chart is supplied by the image of x, so
   normal integral section rings and their prime localizations apply without
   an empty-ring error. The second helper uses flatness of the local stalk
   map for faithful flatness/injectivity and preimmersion for surjectivity;
   its ring equivalence then transports both asserted properties. Two base
   changes of fromSpecStalk provide those hypotheses in the parent. No
   arbitrary-flat-base-change normality assertion is used. The old direct
   dependency on relative normalization is now a statement dependency of the
   parent and a proof dependency of the middle theorem; the old etale-normal
   dependency alone is discarded. All removed original proof dependencies
   are accounted for in `No longer needed`. Read the unit's `realized` record
   (empty at baseline) and the boundary-extension blueprint ancestry: no
   unit or chapter route or realization is removed. Verdict: the genuine
   reduction and pruning are sound.

5. Compared the parent node's three proof steps and `proof_deps` to the Lean:
   smooth ascent, the new unlocalized theorem, and stalk equivalences match
   exactly. Checked the new node's statement, verbatim Lean record, source,
   creation record, blueprint ancestry, chapter/unit and recorded searches.
   Opened its cited finite-components Mathlib leaf, relative-normalization
   chart node, and upstream integral-source normal-stalk node; their statements
   give exactly what each prose step takes. Verdict: nodes agree with Lean.
   Found that the new module omitted the proof import of the upstream
   normal-stalk theorem used in its pending plan; repaired that omission.

Changed only the new module: added plain (proof-only) import
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, and expanded its
new docstring to state the finite-product monic-polynomial argument explicitly.
The proved parent and its signatures were left untouched. No additional hole
or node was created, and no existing public interface was changed.

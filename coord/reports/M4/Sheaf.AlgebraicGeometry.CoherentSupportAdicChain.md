## What changed

Repaired every duplicate named in the maintainer's return in
`Sheaf.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence`.
The item and both public theorem signatures remain unchanged.

Removed `product_qc`, `product_range`, `powers_qc`, and `powers_range`.
The new private, proved `powers_affine_sections` treats an arbitrary
quasi-coherent module map to the structure sheaf, without monicity or
IdealSheafData assumptions, and proves quasi-coherence and the section-range
formula together for every exponent, including zero. It uses the existing
`quasiCoherent_cokernel_image` and tensor-section comparison declarations.
Generalized `multiplication_range`: its source need not be quasi-coherent;
it assumes only a quasi-coherent tensor object and target and surjectivity
of the tensor-section comparison. This includes non-quasi-coherent sources
when the target is zero.

Replaced `affine_zero_of_sections` by `affine_source_zero_of_sections`, valid
for any open immersion from an affine scheme. Replaced the ideal-sheaf-specific
`idealPowerProduct_isZero_iff_affine_cover` by
`powerProduct_isZero_iff_affine_cover`, for arbitrary quasi-coherent maps to
the unit and their section-range ideals. This covers zero maps and nonmonic
maps as well as ideal inclusions. Specialization uses the existing
`IdealSheafData.range_toModulesι_app` theorem. Removed the unused direct
QuasicoherentCokernel import and its direct DAG dependency.

Updated the nilpotence node's proof and proof dependencies. No existing library
module other than the item is adapted. Removed the stale second reading from
the earlier delivery; this repair needs a fresh independent reading.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_support_adic_chain`.
Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.coherent_support_vanishingIdeal_nilpotence`
(node `lem-pc-s3-coherent-support-vanishing-ideal-nilpotence`).
Holes added: none. Holes left in delivered modules: none. No split-off holes.
All private helpers are proved. The chain uses existing open dependencies,
including `isCoherent_kernel_cokernel_biprod_and_submodule`; this delivery does
not claim to remove their holes. Net local holes closed: one.

## No longer needed

Removed nilpotence-module proof import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel` and the
corresponding direct node dependency
`lem-weil-pbc-quasi-coherent-module-cokernel-closure`; the image theorem still
has its own transitive dependencies.
Removed duplicate local helpers `product_qc`, `product_range`, `powers_qc`,
`powers_range`, `affine_zero_of_sections`, and
`idealPowerProduct_isZero_iff_affine_cover`; `multiplication_range` is generalized.
The earlier repair also removed `ideal_quasiCoherent` and `stalk_injective`
from the item. No original public statement import is removed.

All three removed original direct proof dependencies of the item:
`lem-weil-pbc-coherent-support-power-ideal-kills`
(`Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills`) is replaced by the
proved vanishing-ideal nilpotence module;
`lem-weil-pbc-formal-module-ideal-power-factor`
(`Sheaf.AlgebraicGeometry.CoherentFormalModule`) is replaced by the generalized
local factorization proofs;
`lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`
(`Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`) is still needed
transitively by the new nilpotence theorem and is not pruned from the closure.

`Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover`,
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`, and
`Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationAdicReduction` are not
imported by this proof. No claim that these leave the whole target closure:
other consumers may still need them. No unit realization is removed.

## Where the brief, the DAG or earlier work was wrong

The returned nilpotence module duplicated seven existing statements.
Import-direction checks for both cited affine-product packages report that
those modules already reach `CoherentSupportAdicChain`; importing either from
this item closes a cycle. Several cited helpers are private as well. The
repair generalizes the local results and removes the specialized duplicate
statements, while reusing the acyclic public tensor/image interfaces.
Checked the generalized arguments for zero maps, exponent zero, zero targets,
nonmonic maps, and empty affine covers: none require positivity or monicity.
The old second reading does not cover this repair and has been removed.

## New nodes

`lem-pc-s3-coherent-support-vanishing-ideal-nilpotence` is stated and proved in
`lean/Sheaf/AlgebraicGeometry/CoherentSupportVanishingIdealNilpotence.lean`.
It supplies the nilpotence step of Stacks 01Y9, strictly below the chain.
No further new node or change record is added by this repair: only private
proved helpers and proof imports in the delivery's new module change.

## Second reading by M4

1. Interface: compared the delivered chain module with the repository using diff,
   and checked the full existing theorem signature byte for byte. It is identical:
   Noetherian X, closed T, generic point, coherent F, exact support equality,
   literal P(0)=F, terminal zero, coherent terms, short exact successive sequences,
   support containment and maximal-ideal annihilation are all retained. The four
   original public imports remain. The nilpotence module and its public theorem
   are new; no existing definition or other module is adapted. Verdict: pass.
2. Proof: compiled both modules in import order with lcompile.py, with no errors
   or warnings. No delivered theorem or definition contains sorry, and there is
   no axiom, unsafe, opaque, implemented_by or extern declaration. Scratch-copy
   #print axioms shows only propext, Classical.choice and Quot.sound for
   coherent_support_vanishingIdeal_nilpotence. The chain additionally uses sorryAx
   through existing open dependencies (in particular coherent closure); this is
   explicitly not an axiom-free closure of the target. The objects are actual
   vanishing ideals, recursive powers, images and cokernels. Chosen exponents
   are indices, and chosen factorization maps are uniquely determined by their
   composites with monic inclusions; no arbitrary unproved existence witness
   supplies data. Verdict: pass with the reported upstream holes.
3. New statements: no split-off sorry remains. Read the new nilpotence statement
   against [Stacks 01Y9](https://stacks.math.columbia.edu/tag/01Y9): it is the
   forward support-to-nilpotence implication specialized to the actual vanishing
   ideal, without a generic-point assumption. Read the ideal-power paragraph of
   [01YF](https://stacks.math.columbia.edu/tag/01YF) and the generic ideal equality
   in [01YE](https://stacks.math.columbia.edu/tag/01YE). Checked zero F, empty X
   and its empty affine cover, exponent zero, zero/nonmonic unit-valued maps in
   powers_affine_sections and powerProduct_isZero_iff_affine_cover, and arbitrary
   affine-source open immersions in affine_source_zero_of_sections. The power-one
   case is the original source module, while higher powers are actual images;
   none of these proofs assumes the initial map is monic. multiplication_range
   uses exactly tensor quasi-coherence, target quasi-coherence and surjective
   comparison, so a non-quasi-coherent source with zero target is permitted.
   Searched lean/Sheaf and the source checkout with range, factor and powers
   names, and ran fresh leanfinder, loogle and grep searches through msearch.py.
   LeanFinder returned ideal-sheaf/basic-open ingredients, not the sheaf result;
   Loogle reported unknown identifier IsZero, so that query supplied no evidence;
   grep returned unrelated module-support and annihilator occurrences. Read the
   existing CoherentSupportPowerIdealKills, IdealPowerProductZeroAffineCover,
   IdealTimesQuasiCoherentAffineSections, CoherentMapReductionTorsionKernel and
   CoherentFormalModule interfaces. Their specialized duplicate helpers are
   removed; their modules reach this item, preventing import reuse here. The
   new helpers have genuinely more general explicit hypotheses. Verdict: pass.
4. Route and pruning: the proof follows 01YF downward: nilpotence, coherent image
   powers, monic factorization, coherent cokernels and generic annihilation.
   generic_ideal_range uses the pointwise vanishing characterization and the
   specialization direction correctly. In the quotient argument, lifting along
   the stalk cokernel projection, multiplying into the next range, and using
   injectivity of b(t) prove the stated annihilation. Q(0)=F, Q(k+1)=P(k) gives
   terminal Q(n+1)=P(n); its initial isomorphism has zero cokernel, including
   when n=0. All three former direct dependencies removed from proof_deps are
   named under No longer needed; QuasiCoherentIdealZeroSetAffine remains used
   transitively. Each import is needed by a statement/definition or a named
   proof ingredient; proof-only imports are plain import. The unit record
   sk-thm-picard-coherence has empty realized statement/step entries, and the
   delivery removes none of its realizations. No whole-closure pruning is
   claimed without a ledger computation. Verdict: pass.
5. DAG: checked both nodes with both modules open. The chain's six steps match
   nilpotence, tensor/image and coherent closure, generalized power-factor
   maps, reduced vanishing-ideal generic range, stalk ranges and cokernels,
   and the leading zero quotient. Its proof_deps is exactly the union of uses.
   The nilpotence node matches support/annihilator radical containment, finite
   affine cover and maximum exponent, then affine multiplication and sheaf
   locality. Its cited support, zero-locus, tensor/image, kernel, coherence and
   pushforward declarations supply those facts. Its Lean statement matches
   verbatim; chapter, unit, created, source, searches, blueprint and Lean record
   are present. Both proof_origin records describe the repaired argument.
   Verdict: pass.

Second reading changed only this report: added the independent review and the
explicit axiom distinction. No Lean proof or statement repair was necessary.

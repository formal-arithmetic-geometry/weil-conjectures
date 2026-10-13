## What changed

Completed the earlier sandbox attempt. The assigned theorem
`AlgebraicGeometry.Scheme.exists_powerSeries_punctured_finite_order_approximation`
now handles order zero directly and, at positive order, pulls back the section to
Spec(B/I^(n+1)), lifts its quotient class, and applies the proved stalk-kernel comparison.
Its existing signature and public imports are unchanged.

Proved the new transport helper in PowerSeriesPuncturedFiniteThickeningSections
from the existing `bijective_powerSeries_punctured_thickening_restriction`.
The existing quotient-first-variables kernel theorem identifies the variables
ideal with ker(constantCoeff). Pullback symmetry and `pullbackRestrictIsoRestrict` identify
the pullback thickening with the inverse-image open. Functoriality of `appTop`
identifies the composite section map with canonical restriction.
The helper is indexed by n+1; it does not repeat the Hartogs argument.

Retained the fully proved PowerSeriesPuncturedThickeningKernel module. It computes
quotient stalk kernels using explicit localization fractions, transports germs
through open-subscheme stalk isomorphisms, and uses the inclusion of the variables
ideal in the zero-section kernel. No definition, existing interface, or module
held by another group is changed. Both new nodes and the assigned node have proof
routes matching the Lean proofs.

All three modules compile cleanly with `lcompile.py --all`. The source is
[Stacks Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9), first displayed calculation.
The finite-thickening route of the unit is retained.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.exists_powerSeries_punctured_finite_order_approximation`
(node lem-sbc-power-series-punctured-finite-order-approximation).

Added zero holes. Both new public helper declarations are fully proved:

- `AlgebraicGeometry.Scheme.surjective_powerSeries_punctured_thickening_sections`
  (lem-sbc-power-series-punctured-finite-thickening-sections).
- `AlgebraicGeometry.Scheme.powerSeries_punctured_germs_mem_pow_of_thickening_zero`
  (lem-sbc-power-series-punctured-thickening-kernel).

Every delivered declaration, including the two private localization helpers,
is proved. The existing imported finite-index restriction theorem still has its
own named sorry in the library; it is neither added nor copied by this delivery.
This closes the assigned hole from an existing stated dependency, rather than
proving the whole Hartogs calculation without dependencies.

Edge cases: order zero uses membership in the unit ideal; helper index zero is
the first thickening. The kernel lemma allows d=0 and arbitrary coefficient rings,
including the zero ring. Empty opens cause no issue: all maps and section identities
are canonical. Quotient lifts are witnesses inside theorem proofs, not data chosen
in definitions. The transport helper keeps exactly the existing restriction
theorem's depth, locality, Noetherianity, and positive-dimension hypotheses.

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`.
Its node lem-sbc-depth-two-hartogs-restriction is still needed through the existing
PowerSeriesPuncturedThickeningRestriction module, so it is not globally pruned.
The affine-open and Spec-map stalk-localization nodes formerly used directly by
the assigned node remain used by the proved kernel helper; they are not pruned.
No original node or mathematical module is globally pruned.

The earlier attempt's duplicate finite-thickening sections sorry is eliminated.
The new sections helper uses only the two proof imports
PowerSeriesPuncturedThickeningRestriction and PowerSeriesQuotientVariables;
its former standalone finite-free/Hartogs proof plan is no longer needed.
All delivered proof imports are used.

## Where the brief, the DAG or earlier work was wrong

The previous compiled-baseline blocker has cleared: the existing finite-index
restriction module and its dependencies are available, and the reduction compiles.
The earlier attempt unnecessarily added a second hole for the finite-index
calculation already stated in PowerSeriesPuncturedThickeningRestriction. This
repair replaces it with a complete canonical-map transport proof.
No mathematical error or target-statement change was found.

The existing localization plan suggested equality of the zero-section kernel
with the localized variables ideal. The written kernel proof only needs the
inclusion, which follows directly because constantCoeff kills every variable.
It proves the requested conclusion without that stronger equality.

## New nodes

lem-sbc-power-series-punctured-finite-thickening-sections records the proved
transport of the existing finite-index restriction theorem from the pullback
scheme to its inverse-image open, using the existing quotient-first-variables kernel identity.
It has no sorry and adds no independent geometric calculation.

lem-sbc-power-series-punctured-thickening-kernel records the fully proved
local implication from zero pullback on a quotient-power thickening to
zero-section germ kernel-power membership. It needs only a commutative ring.
No change record or forced adaptation is needed.

## Second reading by T4

1. Compared the assigned module with the repository by diff. The theorem signature,
   its docstring, and all public imports are unchanged; restored the extra space
   before `:=` to make the signature text byte-for-byte identical. The other two
   modules and their nodes are new. No definition or existing interface changes.
2. Compiled all three delivered modules cleanly with lcompile.py --all, then compiled
   scratch copies with #print axioms for all three public theorems and both private
   localization lemmas. The kernel theorem and private lemmas use only propext,
   Classical.choice, and Quot.sound. The sections transport and assigned theorem
   additionally use sorryAx through the existing finite-index restriction theorem.
   No delivered sorry, axiom, unsafe, opaque, extern, implemented_by, or hollow
   definition occurs. All quotient and prime witnesses are chosen in proofs only.
3. No sorry statements are split off. Read both new helper statements against
   Stacks Tag 0EY9's first displayed calculation. Sections surjectivity uses exactly
   the existing restriction theorem's local, Noetherian, depth-two and d>0
   assumptions; it makes no approximation claim. The kernel implication is strictly
   the local algebra part and needs only CommRing A. Checked n=0 (unit ideal), n=1,
   d=0 (no variable generators), empty V and the zero ring (no points). Searched
   LeanFinder for localized quotient kernels, Loogle for constantCoeff kernels,
   and rg in Mathlib, upstream WeilConjectures and lean/Sheaf. Found the proved
   quotient_first_variables_kernels identity and used its second conclusion.
   IsLocalization.ker_map is a general alternative for the private fraction lemma
   but requires identifying the mapped prime-complement submonoid; the present
   direct fraction argument is complete. No existing theorem duplicates either
   geometric helper.
4. Read the proof top down: zero order is immediate; positive order obtains a
   quotient section, lifts it, checks canonical-map naturality, then applies the
   kernel implication. The transport uses the existing finite-index theorem,
   pullback symmetry and pullbackRestrictIsoRestrict, without repeating Hartogs.
   Replaced the coefficient argument for hI by the existing kernel identity and
   changed its proof-only import from PowerSeriesCombinedIdealCoefficients to
   PowerSeriesQuotientVariables. All remaining imports supply statement objects
   or used proof declarations. No longer needed lists all three old proof_deps:
   Hartogs remains through finite-index restriction, and both localization leaves
   remain through the kernel helper. No global module is pruned. Read the unit
   sk-prop-input-spreading realized field (empty statement and seven empty step
   slots) and its local-computation step: this delivery retains the 0EY9
   finite-thickening route and changes no unit realization.
5. Read the three node records against the Lean. The assigned proof_deps are the
   two helpers. The sections helper now cites lem-weil-pbc-power-series-kernels
   and the existing finite-index restriction node. The kernel node's two Mathlib
   localization leaves match arrowStalkMapSpecIso, Spec.algebraMap_stalkIso_inv,
   and the open-stalk identifications actually used. New nodes have the required
   source, searches, created, blueprint, chapter/unit and verbatim lean fields.
   Updated the sections helper proof route and proof_origin to the shorter proof.

Changed only the kernel-identity reduction and its proof import/node/report,
plus the assigned signature's accidental whitespace. One existing hole closed,
zero holes added; both new public helpers are proved. No mathematical correction,
change record, or forced adaptation was necessary.

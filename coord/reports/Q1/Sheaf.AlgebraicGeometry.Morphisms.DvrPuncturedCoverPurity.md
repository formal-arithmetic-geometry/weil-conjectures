## What changed

The original module now proves
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_dvr_neighbourhood`
with its signature and visibility unchanged. Two proof-only imports were added:
`Sheaf.AlgebraicGeometry.Morphisms.FlatDvrSpecialFiberCartier` and
`Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity`.
All original public imports remain: they describe the original statement.

The new flat-DVR module proves that the actual scheme-theoretic special-fibre inclusion
is an effective Cartier centre. It chooses a uniformizer only inside a proof, identifies
the residue-field inclusion's kernel with the closed point's vanishing ideal, transports
regular principality through the Gamma-Spec ring isomorphism, and pulls back its invertible
ideal along the flat map. This theorem has no sorry.

The original proof then establishes local Noetherianity, smoothness and regularity of the
fibre, connectedness from GeometricallyConnected, and integrality from the existing
IsRegular.isIntegral theorem. It identifies the puncture with the complement of the fibre,
lifts x to the fibre, and maps the generic-point specialization to show that W contains
its generic point. Finally it applies the new regular-integral-divisor purity theorem.
The node's proof and proof dependencies now describe these exact steps.

The remaining new theorem isolates the source's classical purity input, with explicit
Cartier, regularity, integrality, and generic-point neighbourhood hypotheses, independent
of DVR families. It follows Stacks 0EYE and the codimension-one argument in 0EYJ.
The unit's trait-case route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_dvr_neighbourhood`
(node `lem-sbc-dvr-punctured-cover-purity`). The original module contains no sorry.
This is a decomposition, not a net reduction in holes: one hole closed, one hole added.

Also proved the new theorem
`AlgebraicGeometry.Scheme.isEffectiveCartierCenter_specialFiber_of_flat`
(node `lem-sbc-flat-dvr-special-fiber-cartier`), with no sorry.

The sole sorry added by this delivery is the complete named public theorem
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_regular_integral_divisor`
(node `lem-sbc-regular-integral-divisor-etale-purity`). Its whole proof is `by sorry`;
its docstring and node give the source and argument. It is the remaining purity step,
not another formulation of the original DVR statement: the Cartier special fibre,
regularity, integrality, complement identification, and generic-point membership are
now established by real Lean proofs before this theorem is applied.

All three modules compile together through lcompile.py without warnings. No existing
signature, definition, visibility, or target statement was changed. No data definition
chooses a witness from an unproved existence theorem.

Edge-case checks: the flat-DVR Cartier theorem allows an empty special fibre (the pulled
back ideal is then the unit ideal). The original theorem's x witnesses a nonempty fibre.
The purity theorem assumes an integral, hence nonempty, divisor and explicitly allows
an empty finite cover. None of the arguments uses global quasi-compactness or
quasi-separatedness. Extra vertical components of N away from W are harmless, since the
conclusion concerns only its restriction to the puncture.

## No longer needed

No imports or modules were pruned. All three geometric steps of the source plan remain.
The original direct proof-dependency entries `def-sc-discrete-valuation-ring`,
`def-weil-finite-integral-morphism`, and `def-weil-etale-morphism` are now represented through
statement dependencies and the two new lemmas; these notions remain needed and are not
claimed as global pruning. The original statement dependencies were left unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node's proof dependencies named definitions rather than the substantial
purity theorem needed in its last step. There is no independent declaration for that
step in Mathlib or the project: project references to 0EYE belong to this item's ancestors
and cannot be imported without a cycle. This delivery makes the missing classical input
an explicit independent item and proves the DVR geometry and assembly.

LeanSearch returned Internal Server Error for both searches. LeanFinder, Loogle, source
grep, and blueprint reference searches were used and recorded; none found an exact purity
extension theorem. The flat-DVR Cartier proof uses existing proved ingredients discovered
by these searches.

## New nodes

`lem-sbc-flat-dvr-special-fiber-cartier`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-flat-dvr-special-fiber-cartier.json`, records the
fully proved theorem for flat DVR families. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.FlatDvrSpecialFiberCartier`. Source: Stacks 0EYJ,
first paragraph, and 02OO, case (6). Its searches found the uniformizer and flat pullback
ingredients but no exact statement. This result supplies the first geometric step.

`lem-sbc-regular-integral-divisor-etale-purity`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-regular-integral-divisor-etale-purity.json`, records
the remaining purity input for a regular integral effective Cartier divisor. Its module
is `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity`. Source: Stacks
0EYE and the generic-point argument of 0EYJ. Its searches found no independent extension
statement. It contains the sole new sorry. No change record is needed, because no existing
interface changed and no other module was adapted.

## Second reading by Q1

1. Unchanged interfaces: diffed the original module against the repository version.
   Only two plain proof imports and the theorem body changed. The existing signature,
   visibility, definition data, and original docstring are byte-for-byte unchanged.
   The other two modules are new, and no forced adaptations or change records are needed.
   Verdict: pass.
2. Proof and axioms: compiled all three modules through lcompile.py in import order.
   Independently printed axioms in scratchpad/lean/SecondReading.lean. The flat-DVR
   Cartier theorem uses only propext, Classical.choice and Quot.sound. The original
   theorem and new purity theorem additionally use sorryAx, as expected for the one
   recorded open purity input. There is exactly one sorry, the entire named public
   purity theorem; no axiom, unsafe, opaque, extern, implemented_by, holed definition,
   or selection of arbitrary data from unproved existence occurs. Verdict: pass as
   a decomposition, not a sorry-free proof or net hole reduction.
3. New statements: read Stacks 0EYE (Lemma 58.31.3), 0EYJ (trait paragraphs), and
   00NU (regularity of a local ring lifting from its Cartier quotient). The actual
   fibre inclusion and flatness hypotheses exactly support the proved Cartier lemma.
   The purity input assumes locally Noetherian L, a regular integral Cartier D,
   the actual open complement, and an etale neighbourhood of its generic point.
   At that point the ambient local ring is a DVR; elsewhere on D its dimension
   is at least two. Thus this neighbourhood supplies precisely the codimension-one
   unramifiedness required by 0EYE. The finite cover need not be normal or flat
   everywhere. Empty covers, empty flat-DVR special fibres, and extra components
   away from D cause no counterexample; the purity lemma's integral D is nonempty.
   Repeated searches with different terms: LeanFinder query "finite etale coverings
   extend across a nonsingular codimension one closed subscheme when unramified"
   returned only locus and etale-composition ingredients; Loogle query
   "IsEffectiveCartierCenter" returned no match. Searched project/Mathlib sources
   for unramified extension and regular-Cartier etale purity. The 0EYE references
   occur in ancestors of this item, not an independently usable theorem. Verdict:
   the open theorem is true and isolates the general classical purity input; it
   does not restate the DVR geometry now proved in the original module.
4. Route and pruning: checked top-down use of flat Cartier pullback, smooth-fibre
   regularity, connected regular integrality, complement identification and mapped
   generic-point specialization. The existing proved IsRegular.of_smooth and
   IsRegular.isIntegral declarations are used rather than copied. All original
   proof dependencies absent from the new proof_deps are listed under No longer
   needed. Tested removing the flat-DVR module's plain IdealSheaf.Basic import;
   compilation then lacked Hom.ker_eq_vanishingIdeal, so restored the required
   proof-only import. The two new imports of the original are likewise plain.
   No module pruning is justified. Read sk-prop-input-spreading's trait and section
   steps: they explicitly quote 0EYE as a classical input, and this decomposition
   preserves that route. Its realized arrays are empty in the repository; no existing
   realization was removed or bypassed. The literature blueprint checkout is absent
   on this machine; the unit JSON contains the full relevant step text. Verdict: pass.
5. DAG alignment: read all three delivered nodes and their Lean records, the original
   dependency records, and the unit. The original proof/proof_deps agree with the Lean
   assembly; new nodes have source, proof, searches, created, blueprint, chapter/unit,
   and lean records. In particular the Cartier theorem is genuinely proved and the
   purity node remains the sole open input. Verdict: pass.

Changes made: expanded the new purity theorem's natural-language proof and its node's
first proof step to explain regularity along all of D, the DVR at its generic point,
and why no other point of D has ambient codimension one (Stacks 00NU). Restored the
required Basic import after the removal test. No Lean statement or proof term changed.
The original hole closed remains exists_finite_etale_extension_of_dvr_neighbourhood;
the sole added hole remains exists_finite_etale_extension_of_regular_integral_divisor.

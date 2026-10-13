## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.isIso_rawRestrictedCohomologyComparisonEvaluation`
without changing its signature. Added two modules for distinct steps: homotopy classes
versus termwise section cohomology, and compatibility of derived evaluation with that
chain-level map. Their auxiliary definitions are explicit functorial constructions.
The assigned module proves the injective-representative, localization, bijectivity,
and transport argument. Its new imports are proof-only.

The whole three-file set compiles through lcompile.py without warnings. Degree zero,
zero complexes, zero maps and empty pullbacks are included. No affine or qcqs
assumption is added. The unit record sk-lem-failure-field has empty realized arrays;
the proof retains the planned injective-resolution and Yoneda route.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.isIso_rawRestrictedCohomologyComparisonEvaluation`
(node lem-sbc-raw-restricted-cohomology-comparison-evaluation-is-iso).
No sorry remains in the assigned module. Its two private helpers are fully proved.

Added and left:
- `AlgebraicGeometry.Etale.RawRestrictedComparison.exists_rawRestrictedHomotopySectionsIso`
  (lem-sbc-raw-restricted-homotopy-sections-iso).
- `AlgebraicGeometry.Etale.RawRestrictedComparison.rawRestricted_resolution_evaluation`
  (lem-sbc-raw-restricted-resolution-evaluation).

This is a decomposition: one hole closed and two strictly different lower holes added,
not a claim of a sorry-free proof. The first has no derived sections or injectivity
hypothesis; the second is an equality on chain maps and asserts no bijectivity. The
upper proof combines them using the independently proved localization and resolution
results. Neither is the assigned statement under a new name.

## No longer needed

No original import or planned dependency is pruned. The original sole public import
RawRestrictedCohomologyComparisonMap remains necessary. New proof imports are
RawRestrictedResolutionEvaluation and TorsionAcyclic. The second reader removed
the redundant proof-only imports DerivabilityStructureInjectives and
ConcreteCategory.EpiMono; their required declarations are already available through
the remaining imports. An exploratory HomComplexCohomology import was removed
from RawRestrictedHomotopySectionsIso because its statement uses no HomComplex data.
No existing DAG node or module is claimed to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

The existing dependency lem-weil-pbc-etale-restriction-injectives records the
module-coefficient theorem, whereas this item uses abelian sheaves. The already proved
`injective_upperStar_obj_of_etale_addCommGrp` in TorsionAcyclic supplies the required
specialization; no interface adaptation was necessary. The single original proof
step omitted both the chain-level Yoneda construction and its compatibility with
zeroIso. These are now separate precise statements with full proof descriptions.

The item's blueprint ancestor tool returns None because its created.item is a module
name. The parent node has the established ancestor sbc-lem-higher-direct-image-limit;
the new nodes record that ancestor and the full intervening chain. Nothing in the
existing blueprint or unit records was changed.

Sources read: https://stacks.math.columbia.edu/tag/03Q8,
https://stacks.math.columbia.edu/tag/072W,
https://stacks.math.columbia.edu/tag/0BKV, and
https://stacks.math.columbia.edu/tag/0D6F. These identify the section-complex computation;
the explicit Lean comparison glue is recorded as supplied by Q1. The exact source
tex is absent from this read-only checkout, so the published tag pages were read.
LeanFinder and grep found generic HomComplex and Yoneda ingredients, not a complete
comparison for this generator. Both LeanSearch queries returned HTTP 500; the new
nodes accurately record the service as unavailable.

## New nodes

lem-sbc-raw-restricted-homotopy-sections-iso: arbitrary complexes, homotopy classes of
maps from the free pulled-back represented single sheaf, and the section complex's
zeroth homology. Its isomorphism is specified on every chain-map representative.

lem-sbc-raw-restricted-resolution-evaluation: the concrete canonical derived-sections
comparison on a bounded-below complex with K-injective restriction, and its equality
with chainEvaluation. resolutionSectionsIso itself is constructed from existing
isomorphisms, not from an unproved existence theorem. No change records are needed.

## Second reading by Q1

1. Interface: compared the assigned module with the repository using diff. The sole
   existing declaration, `isIso_rawRestrictedCohomologyComparisonEvaluation`, retains
   its signature byte for byte, including arbitrary h, every natural degree p,
   abelian sheaf coefficients and every etale U. Only proof imports, private proved
   helpers and its proof changed. The other two modules and nodes are new. No
   existing definition or target statement changed, so no change record is needed.
2. Proof and data: compiled all three files locally through lcompile.py without
   warnings. Read both private helpers: the first uses evaluation naturality to
   transport IsIso; the second combines the two lower statements with injective
   restriction, K-injective localization and cancellation of bijections. The final
   theorem uses a bounded-below injective representative of F[0][p]. There are exactly
   the two reported named theorem sorries, with no forbidden declaration or holed
   definition. Scratch-copy #print axioms checks find only the standard axioms and
   sorryAx, as expected from the open lower statements. All auxiliary data are
   explicit maps or composites of existing isomorphisms; the homotopy isomorphism
   existence theorem fixes its hom on every chain-map representative, which exhaust
   the quotient Hom set, and it is used only inside a proposition proof.
3. Lower statements: matched each node with its Lean signature. The first applies
   to arbitrary complexes and asserts the underived represented Hom/sections
   isomorphism with its evaluation formula; it contains no derived sections or
   injectivity assumption. Termwise additive Yoneda identifies cycles with chain
   maps and boundaries with null-homotopies, proving the claim even for unbounded
   complexes. The second fixes the explicit resolutionSectionsIso and asserts only
   its equality on chain representatives, assuming K-injectivity of the restriction;
   naturality of the derived unit and its degree-zero normalization give exactly
   this equality. Neither asserts the upper theorem again. Checked zero complexes,
   zero maps, complexes concentrated away from zero and empty pullbacks: the first
   gives the appropriate zero groups, and the second gives the same zero element.
   Read Stacks Tags 03Q8, 072W, 0BKV and 0D6F and the definitions of zeroIso and
   rightDerivedFunctorObjQIso. Repeated LeanFinder and Mathlib grep searches with
   different wording, and searched the Sheaf and upstream sources. The hits provide
   HomComplex homAddEquiv and single homology naturality, not this represented
   comparison. Existing RightDerivedCanonicalSingleUnit and
   RightDerivedSingleUnitHomologyComparison concern different bounded-derived
   comparison formulas; they do not directly close the second hole in a few minutes.
4. Route and pruning: the proof follows the original injective-representative and
   Yoneda route. Checked sk-lem-failure-field.realized (empty statement/step arrays);
   no realized unit node is bypassed. Every original proof dependency is still used.
   Removed the two redundant Mathlib proof imports after individual compile checks;
   no library module or original dependency is claimed pruned. The public KInjective
   import in the new resolution module is needed by the public definition body:
   removing it makes rightDerivedFunctorObjQIso unavailable.
5. DAG: checked the new nodes' hypotheses, evaluation clauses, source, proof steps,
   dependencies, origin, searches, creation and Lean records against the files.
   The assigned node describes the actual localization, bijectivity and transport
   argument. Its etale-restriction dependency is used through the existing abelian
   specialization in TorsionAcyclic, as explicitly recorded in the proof and report.
   Both new nodes have full docstring proofs and the same chapter/unit and blueprint
   ancestry as the assigned node. Verdict: valid decomposition, one upper hole
   closed and two strictly different lower holes added; net holes closed minus added
   is -1 for this delivery, not a sorry-free proof or a positive progress claim.

Changed in this reading: removed the redundant Mathlib imports
DerivabilityStructureInjectives and ConcreteCategory.EpiMono, corrected the import
inventory above, and added this review. No theorem statement or mathematical proof
was changed.

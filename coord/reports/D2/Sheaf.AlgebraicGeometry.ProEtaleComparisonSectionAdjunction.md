## What changed

Replaced the first worker's existential `CoreHomEquiv` split with a concrete
reduction. `proEtaleComparisonSectionUnit` constructs the unit section by section:
pull back by the inverse-image unit, restrict along the diagonal, and apply `e.symm`.
Its site naturality is proved by the new, fully proved theorem
`proEtaleComparisonDiagonalSection_naturality`; its coefficient naturality is proved
from `hfun` and the inverse-image unit and coefficient-morphism naturality equations.
The diagonal formula expands through local notation, since an identical named
section-map definition already exists downstream in `ProEtaleComparisonPullbackSections`
and importing that module would create a cycle. No duplicate definition is added.

The target builds the hom-set equivalences for this specified unit from its
unique-extension/bijectivity theorem. It proves both naturality laws, assembles the
adjunction, identifies its unit with the constructed unit, and proves the required
decoded section equation. All existing declaration signatures remain unchanged.

New modules are `ProEtaleComparisonDiagonalSection` and
`ProEtaleComparisonSectionUnitUniversal`. The target imports the latter only for
its proof. The unit module imports diagonal naturality only for its proof and
retains `EtaleSetInverseImageRestriction` as the planned dependency of its open
extension theorem. Removed the undelivered `ProEtaleComparisonSectionHomEquiv`
module and its node. No changes to any other group's module are required.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.proEtaleComparisonSectionAdjunction`.
New hole added: `AlgebraicGeometry.proEtaleComparisonSectionUnit_bijective`, node
`lem-cbc-comparison-section-unit-universal`. It is the only delivered `sorry` and
has a source and a complete transpose/uniqueness proof in its docstring.

Also proved: `AlgebraicGeometry.proEtaleComparisonDiagonalSection_naturality`, node
`lem-cbc-comparison-diagonal-section-naturality`. Constructed with both naturality
proofs: `AlgebraicGeometry.proEtaleComparisonSectionUnit`, node
`def-cbc-comparison-section-diagonal-unit`. No definition contains `sorry` or chooses
arbitrary data from an unproved existence result. The only newly chosen inverse is
that of a specified map asserted bijective, so its values are uniquely determined.

This is a decomposition: one original hole closed and one lower hole added, net
zero hole reduction, plus the proved diagonal coherence and concrete unit construction.
The target therefore still depends on `sorryAx` through the extension theorem.
The diagonal coherence and the constructed unit have only `propext`,
`Classical.choice`, and `Quot.sound` as axioms.

## No longer needed

Removed direct proof imports from the target:
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`,
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`,
`Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`, and
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
The first is available through terminal transport and used by the proved diagonal
coherence; the second remains the extension theorem's dependency. The last two are
unnecessary: the source `Proetale` module already supplies continuity of `toProEt`
and of pro-etale `Over.map`; the proof does not use the separately packaged canonical
comparison adjunction or its left-exactness theorem.

All six old direct proof-dependency nodes leave the target's direct dependency list:
`lem-weil-pbc-fpqc-finer-than-etale`, `def-weil-pbc-site-comparison-morphism`,
`lem-weil-pbc-weakly-etale-composition-base-change`,
`lem-weil-pbc-etale-base-change-finite-limits`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`, and
`lem-weil-pbc-sets-etale-inverse-image-restriction`.
The final four remain in the lower nodes' proof route. The first two are no longer
proof dependencies of this reduction. Whether a module is globally pruned is for
the closure ledger; no global pruning count is claimed here.

## Where the brief, the DAG or earlier work was wrong

The first worker's proposed `proEtaleComparisonSectionHomEquiv` carried essentially
the entire target under an equivalent categorical packaging. Its final construction
with `Adjunction.mkOfHomEquiv` alone was not a sufficient reduction. The second
reading removed that split, constructed the actual unit, proved its naturality,
and isolated only its unique-extension property. No original statement or definition
has been changed to make a proof easier.

The original dependency plan imported the separately packaged site comparison and
fpqc comparison unnecessarily for this step; existing upstream continuity instances
suffice. The unit `sk-prop-sf-comparison` has empty `realized.statement` and
`realized.steps` lists; this work changes neither the unit nor its prescribed route.

## New nodes

`lem-cbc-comparison-diagonal-section-naturality` records the proved compatibility of
diagonal sections with site arrows, directly from inverse-image composition units
and pullback uniqueness. Its module is `ProEtaleComparisonDiagonalSection`.

`def-cbc-comparison-section-diagonal-unit` records the explicit unit and its proved
site and coefficient naturality in `ProEtaleComparisonSectionUnitUniversal`.

`lem-cbc-comparison-section-unit-universal` records bijectivity of the concrete map
`beta ↦ eta_F ≫ restriction(beta)`, the remaining lower theorem in that same module.
Its docstring gives the construction over each Y, the inverse-image adjunction
transpose, and both the extension and uniqueness verifications.

No statement/interface change record is needed.

## Second reading by D2

1. Compared the complete original target signature byte for byte with the repository
   version, including all universes, hypotheses, and the decoded unit formula: pass.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
2. Compiled all three modules in import order using `lcompile.py`, with no warnings.
   Scanned for forbidden declarations and `sorry` in data. The sole `sorry` is the
   named bijectivity theorem. Separate `#print axioms` probes check all delivered
   public declarations: the unit and diagonal theorem use only standard axioms;
   the target and the explicitly open theorem additionally use `sorryAx`.
3. Rejected and removed the equivalent `CoreHomEquiv` split. The replacement fixes
   a concrete unit first and leaves only extension/uniqueness for that fixed map.
   Checked the empty-scheme/empty-section cases and identity arrows: the assertions
   require no section to exist, and the proved diagram identities apply unchanged.
   Repeated leanfinder, loogle, and grep searches via `msearch.py` (LeanSearch
   was also attempted but returned Internal Server Error), and local searches
   under both library roots, with different wording. Found and avoided the duplicate
   downstream section-map definition. `EtaleSetTerminalTransition` is related but
   includes additional section comparisons; the direct composition-unit proof uses
   the existing proved theorem without importing that larger route.
4. Read the target proof from its unit construction through hom-set naturality and
   the decoded unit formula. Removed proof-only imports and public exposure that
   this route does not need. Reported all six former direct proof dependencies and
   distinguished those retained below. The unit's `realized` fields are unchanged.
5. Read all four delivered DAG records against the Lean declarations and their
   source. The new naturality theorem, explicit unit, and remaining extension theorem
   have matching records, sources, search records, and dependency unions. The target
   node follows the implemented reduction.

Second-reading changes: replaced the equivalent split with the explicit diagonal
unit and unique-extension reduction, proved diagonal coherence and both unit
naturality laws, removed duplicate public data and unused imports, rewrote the
node proof routes, and corrected the report format and decomposition accounting.

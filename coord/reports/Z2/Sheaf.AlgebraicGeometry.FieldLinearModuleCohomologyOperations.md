## What changed

Partial definition repair in FieldLinearModuleCohomologyOperations:

- scalarUnitLinear: chosen from exists_scalarUnitLinear → ModuleCat.ofHom with
  toFun r = scalarMap f ⊤ r. Additivity and linearity are proved directly.
  exists_scalarUnitLinear now states the proved formula of the real map,
  retaining its legacy name.
- scalarTensorCoefficient: chosen from exists_scalarTensorCoefficient → the
  sheafification-adjunction extension of scalarTensorPresheafCoefficient, composed
  with the canonical Sheaf.tensorLeftIso. The presheaf map has explicit components
  scalarTensorCoefficientApp, using tensorLift of tmulSection. All four bilinear
  laws and scalarTensorCoefficientApp_naturality are proved.
  exists_scalarTensorCoefficient is restated as the formula for this real map,
  retaining its name and leaving its Prop-valued proof sorry.
- moduleExtEquiv: unchanged, still chosen from exists_moduleExtEquiv. A real
  construction requires the chain-level Hom(unit,-) / global-sections comparison
  and its homology/resolution identifications. No ready construction was found in
  the library search. Replacing it by a cocycle-formula predicate must also replace
  scalarCohomologyExtMap, its equivalence and every cup/pullback operation; this
  broader API repair is left for the next item.
- scalarPullbackCoefficient: unchanged, still chosen from
  exists_scalarPullbackCoefficient. The real map is the mate of the k-linear
  sectionwise tensor-pullback unit. The existing tensorPullbackAdjunction itself
  is chosen from an unproved existence theorem; it must first be constructed or
  supplied as a parameter satisfying its unit formula. Merely taking its mate
  would preserve hollow data.
- externalCupPullbackIso: unchanged, still uses the chosen module_pullback_tensor
  isomorphism and the chosen scalarPullbackAdjunction. A real construction requires
  the tensor-pullback monoidal comparison and normalized composition comparisons.
  A predicate repair must parameterize these comparisons and adapt
  PicardKunnethQcoh's functoriality clause at the same time.

No adapted modules and no imports changed. Change record:
coord/changes/field-linear-explicit-coefficients.md.
The existing node records the additional construction declarations and partial route.

## Proved and sorry left

Proved exists_scalarUnitLinear (replacing the old existence sorry), the four
bilinear laws in scalarTensorCoefficientApp, and scalarTensorCoefficientApp_naturality.
No new sorry is added. The tensor formula remains a Prop-valued obligation,
not a source of data. Every remaining sorry belongs to
 def-sc-field-linear-module-cohomology-operations:

- scalarRestriction_linear
- scalarRestriction_id
- scalarRestriction_comp
- scalarPresheaf_isSheaf
- scalarHom_linear
- scalarHom_naturality
- scalarHom_id
- scalarHom_comp
- scalarFunctor_additive
- scalarFunctor_preservesFiniteLimits
- scalarFunctor_preservesFiniteColimits
- exists_moduleExtEquiv
- scalarCohomologyExtMap_add
- scalarCohomologyExtMap_smul
- scalarCohomologyExtMap_bijective
- scalarInverseImage_additive
- scalarInverseImage_preservesFiniteLimits
- scalarInverseImage_preservesFiniteColimits
- exists_scalarPullbackCoefficient
- scalarTensorLeftLimits
- scalarTensorLeftColimits
- scalarTensorRightLimits
- scalarTensorRightColimits
- exists_scalarTensorCoefficient

## No longer needed

No imports, nodes, or modules pruned. Neither repaired definition uses its former
existence theorem to obtain data. The unit existence declaration now states the reflexive formula of the real map,
retaining its legacy name.

## Where the brief, the DAG or earlier work was wrong

The old definitions chose coefficient data from sorry existence statements,
contrary to the human ruling. The repair leaves three requested comparisons
unrepaired, as detailed above. scalarPullbackAdjunction is an additional hollow
adjunction in this file; scalarPullbackCompIso consequently depends on hollow data.
scalarCohomologyExtEquiv also constructs inverse data using an unproved bijectivity
statement, so the broader Ext-comparison repair must address it as well.
The new explicit maps work on every open, including the empty open; the formulas
use only ring-homomorphism and tensor-section laws and add no nonemptiness assumptions.

The first dry run raised a KeyError when an old sorry declaration was removed.
Both former existence names are therefore retained for their characterization statements.

## Second reading by Z2

1. Compared the entire delivered module with the repository using diff. Only
   scalarUnitLinear, scalarTensorCoefficient, their two declared characterization
   statements, and the three new tensor-construction helpers differ. All other
   existing signatures and all imports are byte-for-byte unchanged. The change
   record contains the old and new text. Repeated all four downstream.py --uses
   checks: only the item directly uses these names; no adapted module is needed.
   Verdict: no accidental interface change and no target signature changed.
2. Read both explicit constructions and their dependencies. scalarUnitLinear has
   the ring-map function as data; tensorLift has tmulSection as data. Naturality
   is proved by tensor extensionality and tmulSection_map. The sheaf morphism is
   the sheafification-adjunction extension, with the existing tensorLeftIso.
   These constructions choose no data from an unproved existence statement.
   Remaining sorry proofs are named and listed above; no prohibited declaration
   or sorry in a data field occurs. The reported unrepaired chosen comparisons
   remain defects, permitted only by this item's explicit partial-repair scope.
   Verdict: the two repairs have real data; the entire module is not fully repaired.
3. No new split-off sorry statement is introduced. Checked the sectionwise laws
   using ring-homomorphism and tensor-section laws, including empty opens and
   zero sections: no nonemptiness or nonzero-section assumption is needed.
   Repeated library searches for tensor coefficient constructions and searched
   Loogle for tensorLift: the existing universal-property implementation is used.
   The characterization statements express precisely the original formulas for
   the explicitly constructed maps. Verdict: no weakening or restatement split.
4. The construction uses the existing shortest sectionwise and sheafification
   route. No imports or old proof dependencies are removed (the old proof_deps
   is empty); No longer needed is complete for this repair. The unit record
   sk-prop-av-cube has pre-existing empty realized.statement and realized.steps
   entries. This delivery neither changes nor bypasses its route; the missing
   realization metadata is an upstream bookkeeping gap. Verdict: route preserved.
5. Read the node and change record alongside Lean. The three new declarations
   are included in lean.declarations; the partial construction is recorded in
   proof and proof_origin. Added the exact changed characterization signatures
   to lean.note, since lean.statement remains the unchanged primary cup signature.
   TeX mathematics is unchanged, so no statement_change is needed. Verdict:
   metadata agrees with the partial repair and names its limitations.

Second-reader changes: recorded both changed characterization signatures in the
node's Lean record and documented the pre-existing unit-realization gap. The
Lean constructions were correct and were not rewritten.

Validation: lcompile.py --all passed in 45.4 s. The explicit module-output
compile passed in 51.2 s including writing the .olean. A scratch copy with
#print axioms for both repaired maps, their characterizations, and all three
new helpers passed in 47.9 s. Only propext, Classical.choice, Quot.sound and
sorryAx occur; scalarTensorCoefficientApp has no sorryAx. The other repaired
constructions still depend on pre-existing Prop-valued obligations, including
the scalar presheaf/sheaf laws, rather than choosing unknown coefficient data.
All Lean lines satisfy the 100-character limit. The second-reader LeanFinder
search found presheaf/module sheafification machinery, not a duplicate of these
field-restriction coefficient maps. No new sorry or split node was introduced.

Delivery validation: deliver3.py Z2
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations --no-push printed
OK: commit 84171cba8 compiles and passes preflight, review class CODEX. Nothing
was pushed. No adapted modules. The launcher owns the final delivery step.

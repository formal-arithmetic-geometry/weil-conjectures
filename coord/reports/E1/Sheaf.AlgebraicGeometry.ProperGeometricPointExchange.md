## What changed

The signature and existing docstring of
`AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isProper_geometricPoint` are unchanged.
Its proof now rewrites the identity geometric stalk of exchange by a qcqs strict-local
factorization, proves that the middle fibre restriction is invertible, and applies the
conservative singleton family of identity geometric points on Spec Ω, with its universe lift.
The categorical combination is complete Lean.

Added `Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections`. Its public theorem
`isIso_globalSectionsUpperStarMap_of_strictLocal_geometricClosedPoint` is proved, without
any new hole, from the existing henselian-pair section comparison and the separably closed
field-extension comparison. The proof factors the geometric point through the residue
field, composes the two restrictions using the actual inverse-image composition maps,
and transports to the specified cartesian model. A private proved helper adapts the
coefficient-forgetting proof already in `AlgClosedExtensionModuleSections` to arbitrary
commutative coefficients and a separably closed base field; its existing theorem has
specialized ZMod coefficients and an algebraically closed base and cannot be applied here.
The helper uses `isIso_upperStar_forget_comparison`, already proved in the library.

Added `Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization`. Its theorem leaves only
the qcqs continuity, coefficient transport and canonical exchange compatibility step open.
It has no properness hypothesis and makes no invertibility assertion about fibre restriction.
It returns a strict-local factorization rather than restating proper exchange.
`geometricPointGlobalGerm` is a real, explicit definition: global-section identification
followed by the identity-object germ. The private helper `isIso_geometricPointGlobalGerm` in the original item is fully proved by
representing each germ on a pointed neighbourhood and pulling back along its marked section.
No definition obtains data from an unproved existence theorem; the factorization witnesses
are eliminated only inside the proposition-valued proof of the original theorem.

Both new modules use public imports for their signatures and plain imports for proof
inputs. The original module retains all public imports and imports only the two new
modules for its proof. Existing interfaces, target statements and other modules were not
changed. All three modules compiled without errors or warnings through lcompile.py --all.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isProper_geometricPoint`
(node `lem-weil-pbc-proper-geometric-point-exchange`): 1 of 1 holes of the item.

Added exactly one hole:
`AlgebraicGeometry.Etale.qcqs_geometricExchange_factorization`, in
`Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization`, node
`lem-weil-pbc-qcqs-geometric-exchange-factorization`. Its whole proof is `by sorry`.
There are no other direct sorries in the delivered modules.

The new proper closed-fibre theorem and the identity global-germ isomorphism have complete
proofs. The henselian-pair theorem and the field-extension theorem they use retain their
existing upstream dependencies. This delivery is a decomposition of the original hole,
not an axiom-free proof of proper base change: holes closed 1, holes added 1, net 0 before
the authoritative pinned-baseline ledger. No new hole is a renamed copy of the item.

## No longer needed

Removed these six direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension`: used through the new proved
  proper strict-local module; node `lem-weil-pbc-sections-base-field-extension` remains needed.
- `Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization`: moved to the qcqs
  factorization item; node `lem-weil-pbc-sets-pushforward-stalk-strict-henselization` remains needed.
- `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`: no longer used by this route.
  Node `lem-weil-pbc-strictly-henselian-sections-stalk` is replaced here by the directly proved
  identity-neighbourhood calculation on Spec Ω. This is the genuinely unnecessary module.
- `Sheaf.Paper.InverseImageStalkGerm`: moved to the qcqs factorization item;
  node `lem-weil-pbc-inverse-image-stalk-germ` remains needed there.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`: its conservative-family API
  is still used and publicly available through the new factorization module's stalk import.
  Node `lemma-weil-pbc-geometric-stalk-conservative` remains needed.
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`: moved to the new proved
  proper restriction module. Its henselian-pair theorem is used. The specific algebraic-closure
  theorem `isIso_globalSectionsUpperStarMap_geometricFibre`, node
  `lemma-weil-pbc-proper-strict-henselian-h0`, is no longer used; its module remains needed.

Of the old node's other proof dependencies, `lem-weil-pbc-proper-base-change` remains needed
for the inferred properness of the structural base change. The scheme conventions,
cartesian-square and exchange definition nodes are still statement dependencies; they need
no separate proof edge in the categorical assembly. All old dependencies are accounted for.
No claim is made that a module leaves the entire targets' closure: other branches may use it.
The unit `sk-thm-iff` and its `realized` route remain unchanged; the proof still computes
strict-local sections, restricts to the proper closed geometric fibre, and uses conservativity.

## Where the brief, the DAG or earlier work was wrong

The existing comparison interfaces are insufficient to combine the original four steps
by direct applications: the sets continuity theorem uses Type coefficients, the germ
compatibility theorem uses AddCommGrpCat, and the degree-zero geometricFibre theorem is
specialized to the algebraic closure of the residue field. The new factorization names the
remaining coefficient and canonical-map glue explicitly; it does not assume proper exchange.

The degree-zero module's explanation that a transcendental geometric point would enlarge
sections of an inverse-image sheaf is misleading. Tag 0A3I applies to arbitrary field
extensions of a separably closed field. Inverse image of the original G_m sheaf is not the
new field's G_m sheaf. The new proved restriction theorem uses the correct arbitrary
extension and does not modify that existing module.

The source was read from Stacks Tags 03Q9, 0A3T, 0A3U and 0A3I, and the source TeX was
obtained in the sandbox scratchpad. Tag 0A3U omits the compatibility verification; the new
factorization docstring explains it on pointed affine representatives. Searches were made
with msearch.py (LeanSearch unavailable with HTTP 500, recorded as unavailable; Loogle,
LeanFinder and grep returned no matching theorem). Blueprint searches for the exact
strict-local/geometric-fibre and qcqs-factorization claims found no existing realization.

The blueprint ancestor script follows created.item, which is a module name on the existing
stage-3 node, and therefore returns None. The new nodes retain the explicit existing
blueprint ancestor `lemma-weil-pbc-proper-underived-exchange` from the item's blueprint field,
with the item in via, rather than losing the source provenance. No project tool was changed.

Edge cases checked: arbitrary and transcendental Ω, a separably closed but imperfect residue
field, zero coefficient ring, empty scheme/fibre, nonstandard cartesian models, and
nonproper qcqs maps. The restriction is only asserted invertible with properness; the qcqs
factorization itself is meaningful without it. Its terminal germ proof works for all module
sheaves without torsion or finiteness assumptions.

## New nodes

`lem-weil-pbc-proper-strict-local-arbitrary-geometric-fibre-sections`, in
`dag/nodes/sec-proper-base-change/`, records the newly proved proper closed-fibre section
comparison. Its proof uses the already named henselian-pair and separably closed
field-extension comparisons plus the already proved module/set inverse-image comparison.
The last is a generic tool from `sec-smooth-base-change`; it is used as a coefficient tool,
not to change the unit's route. The new node has no new sorry.

`lem-weil-pbc-qcqs-geometric-exchange-factorization`, in the same directory, records the one
new sorry, its mathematical proof and its exact Lean statement, together with the explicit
identity global germ. Its isomorphism is a private proved helper in the original item. It isolates continuity and compatibility,
not the proper closed-fibre restriction or the conservative-family argument.

The original node's proof, proof_deps and proof_origin now follow the actual Lean assembly.
No change record is needed: there are no changed existing signatures, definitions, public
imports or forced adaptations.

## Second reading by E1

1. **Interfaces — pass.** Compared the original module with the repository using
   diff and separately checked the existing theorem signature byte for byte. Its
   statement and existing docstring are unchanged. The other two modules are new.
   Existing public imports are unchanged; the six removed imports were plain proof
   imports. No existing definition, target, or other module was changed.
2. **Proof and trust — pass as a decomposition.** Compiled all three modules in
   dependency order through lcompile.py, without errors or warnings. Read both
   private helpers and the complete proper strict-local proof. Scratch copies with
   #print axioms checked all six delivered declarations: only propext,
   Classical.choice, Quot.sound, and sorryAx occur. The identity germ definition
   and its isomorphism helper do not use sorryAx; the field-extension helper,
   proper restriction theorem and original item still depend on open upstream
   results or the new factorization. There is exactly one direct sorry, the whole
   public theorem qcqs_geometricExchange_factorization; no forbidden declaration
   or hollow definition occurs. Existential witnesses are eliminated within Prop,
   not used to define arbitrary data. Closed 1 original hole; added 1 lower hole.
3. **Split statement — pass.** Read the local source TeX at 03Q9, 0A3T, 0A3U
   and 0A3I. The new hole isolates qcqs continuity and canonical-map compatibility,
   omits properness, and does not assert that fibre restriction is invertible.
   It is strictly a part of the original argument, not the original statement
   renamed. Its named theorem, docstring proof and node agree. Checked identity
   base change, empty total space/fibre, zero coefficients, transcendental point
   fields and separably closed imperfect residue fields. For nonproper qcqs maps
   the middle restriction may fail to be invertible, consistently with this
   factorization. Independent searches used LeanFinder with “étale inverse image
   module sheaf global sections closed fibre henselian pair restriction”, Loogle
   with “sheafFiber”, “IsIso”, and grep with “henselian.*sections|sections.*henselian|
   exchange.*stalk”. They returned no replacement. Local rg found the existing
   set-valued identity-stalk theorem, the ZMod/algebraically-closed extension
   theorem, and abelian derived stalk-localization results; their coefficient
   types or conclusions do not supply the required module-valued statement.
4. **Route and pruning — pass.** The assembly separately proves proper closed-fibre
   restriction and identity-germ invertibility, then uses singleton geometric-point
   conservativity. It retains the strict-local/closed-fibre route of sk-thm-iff;
   the unit and its realized fields are untouched. All old proof dependencies
   are accounted for in No longer needed. Imports in the new modules serve their
   signatures/definition or the stated proof plan; proof-only imports are plain.
   No simpler applicable library proof was found. No claim of whole-closure
   pruning or positive net hole reduction is made.
5. **DAG — pass.** The original node changes only proof, proof_deps and
   proof_origin. Its assembly matches the Lean. Both new nodes contain their
   verbatim normalized signatures, source, proof steps, dependency union, search
   records, provenance, chapter/unit and Lean records. The functoriality module
   also contains strictHenselizationResidue, which supplies precisely the residue
   and pointed-factorization facts used in the new plan.

Second reading changed only this report: added the independent review, compilation
and axiom evidence, and confirmed that the result is a net-zero decomposition.
No Lean proof, statement, definition, import, node or change record needed repair.

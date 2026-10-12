## What changed

Replaced the sorry in AlgebraicGeometry.affine_algebra_derived_pullback_preserves_qcoh
with a complete Lean assembly proof. The statement, binders, universes and public imports
are unchanged. Added two modules with underived statements: AffineAlgebraTensorPullbackExact
and RingedSpaceTensorPullbackQCoh. Each has one public theorem, a complete proof in words,
a source and a new node. No definitions, arbitrary witnesses or axioms were added.

The existing RingedSpace.derivedModulePullback_adjunction supplies P, its object and map
formulas, additivity, D with its left-derived comparison, and the adjunction. Affine
exactness makes P.mapDerivedCategory a second left-derived functor. The proof uses
Functor.leftDerivedUnique and Adjunction.leftAdjointUniq to identify the given L with it.
For each degree, the existing source-library mapDerivedCategoryHomologyFunctorIso and
Mathlib ObjectProperty.prop_of_iso transport the underived quasi-coherence assertion.

This is a decomposition, not a sorry-free proof. The two remaining obligations are
independent underived pieces of the argument: affine exactness for all module sheaves,
and quasi-coherence of ordinary tensor pullback on arbitrary ringed spaces. Neither
mentions the given derived left adjoint or repackages the original conclusion.

All three files compile together with lcompile.py. The original module has no sorry.
The natural-language arguments were checked against Stacks 0AVW and 01BG online because
the local literature directory contains the citation lists but not the .tex files.

## Proved and sorry left

Closed: AlgebraicGeometry.affine_algebra_derived_pullback_preserves_qcoh
(node lem-sc-affine-algebra-derived-adjunction-qcoh), by the compiled assembly described
above. There are no remaining sorries in the item module.

Added, still sorry:
- AlgebraicGeometry.affine_algebra_tensorModulePullback_exact
  (lem-sc-affine-algebra-tensor-pullback-exact).
- AlgebraicGeometry.RingedSpace.tensorModulePullback_isQuasicoherent
  (lem-pc-ringed-space-tensor-pullback-qcoh).

One upper hole closed and two underived holes added. This is a decomposition; no net
hole reduction or target closure is claimed. Existing imported declarations may still
rest on sorries; they are not changed by this delivery.

Edge cases were checked mathematically before stating the lemmas: empty X gives a
trivial module category, the identity morphism gives ordinary identity pullback,
non-flat affine f is allowed since flatness is for g over f_*O_X, and no boundedness
or finite presentation is assumed. The generic quasi-coherence statement uses local
presentations and holds for non-flat ringed-space maps as well. Both signatures compile.

## No longer needed

Removed the explicit proof import Sheaf.AlgebraicGeometry.AffineModuleCorrespondence.
The proof no longer uses lem-weil-pbc-affine-module-correspondence or its two-stage
algebra tensor pushout, tensor associativity comparison, counit/unit invertibility,
and full-subcategory equivalence. Their modules
Sheaf.AlgebraicGeometry.AffineModuleTensorConstruction and
Sheaf.AlgebraicGeometry.AffineModuleTensorComparisonIsIso are not needed by this proof.
The original proof-dependency edge to lem-weil-pbc-affine-module-correspondence is removed
in the sandbox node. RingedSpaceDerivedAdjunctionGeneral remains needed.

DirectImageAlgebraDerivedCategory still publicly imports AffineModuleCorrespondence;
this delivery leaves that interface unchanged. Thus this removes the logical proof
edge and the redundant direct import, but does not claim that AffineModuleCorrespondence
leaves the targets' transitive import closure. Its other users still need it.

## Where the brief, the DAG or earlier work was wrong

The existing derived-adjunction signature does not supply affine exactness or the
cohomology comparison by itself. The original first step required unstated underived
geometry. It is now isolated as affine_algebra_tensorModulePullback_exact; the actual
cohomology comparison is supplied by the existing source-library exact-functor theorem.

The original second step used the affine module correspondence, but Stacks 0AVW
explicitly cites Modules 01BG for preservation of quasi-coherence under ringed-space
pullback. That argument works for all ringed spaces and avoids the two-stage tensor
comparison. The source-library isQuasicoherent_pullback applies only to scheme morphisms,
so it cannot directly apply to (Y,f_*O_X). No existing node states the generic version.

No target statement or unit route changes. The unit sk-thm-picard-duality has no realized
node attached to this item in dag/units; the pruning here is below the unit level.
The generic underived adjunction used in the new quasi-coherence proof is a tool for
colimit preservation, not a replacement of the unit's argument.

## New nodes

lem-sc-affine-algebra-tensor-pullback-exact: finite-limit and finite-colimit preservation
of the specified tensor pullback along g, for arbitrary module sheaves. Source: Stacks
0AVW's affine stalk calculation, with filtered-colimit and flat-tensor details written
out. Its docstring and node explain stalk comparison, exactness detection and the
abelian finite-limit/colimit conclusion.

lem-pc-ringed-space-tensor-pullback-qcoh: ordinary tensor pullback preserves locally
presented quasi-coherent modules on arbitrary ringed spaces. Source: Stacks 01BG's
local-presentation proof. This has no derived-category or affine hypotheses.

Both nodes belong to sec-picard-framework/sk-thm-picard-duality and record three kinds
of search (LeanSearch unavailable, LeanFinder completed, source grep completed). No
change record is needed because no existing statement or definition changed.

## Second reading by A2

1. Compared the delivered item with the repository using diff. The complete existing
   theorem signature, universes, binders and public imports are byte-for-byte unchanged;
   only its proof, proof imports and explanatory proof docstring differ. There are no
   existing definitions changed, no added hypotheses, and no change records required.
   The existing node differs only in proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled all three delivered modules in import order with lcompile.py. The item
   contains no sorry; each new module contains exactly its one named public theorem
   with a whole-proof sorry. No definition, axiom, unsafe, opaque, implemented_by or
   extern is added. A scratch import and #print axioms for all three declarations showed
   only propext, Classical.choice, Quot.sound and sorryAx. The proof obtains P locally
   with both its object and morphism formulas, and D with a left-derived universal
   property; it adds no data definition chosen from arbitrary mere existence.
   The isomorphism used at the end goes from P(H^n M) to H^n(L M), the direction required
   by prop_of_iso. Verdict: pass, as a decomposition with two open lower obligations.
3. Read Stacks Tags 0AVW and 01BG and both new docstrings and nodes. Exactness applies to
   every input module because at p over q the algebra stalk is S^-1 A, and A_p is a
   further localization; it does not incorrectly assume the original f flat. The map
   formula hm prevents an arbitrary action on morphisms from satisfying the lemma.
   The quasi-coherence lemma uses local arbitrary free presentations, not finite ones;
   it holds for arbitrary ringed-space maps and needs neither flatness nor boundedness.
   Checked identity maps, empty X, zero modules, and the non-flat affine quotient map
   Spec(B/I) to Spec B: the latter still gives localization at the direct-image-algebra
   stalk, so exactness is consistent. Neither new statement mentions L, Rg_* or derived
   cohomology, hence neither restates the item.
   Fresh LeanFinder search used “locally free presentation pullback preserves
   quasicoherent ringed space”; Loogle searched SheafOfModules.IsQuasicoherent; grep
   searched localization/stalk and isQuasicoherent_pushforward, supplemented by rg over
   lean/Sheaf and the source Tilde module. Found Presentation.map and pullbackObjFreeIso,
   useful tools but no closure of the concrete inverse-image/change-of-rings formula.
   Read Mathlib isQuasicoherent_pushforward and its left-adjoint variant: they concern
   site pushforward with unit and over-site colimit data; they do not directly prove
   this tensor-pullback formula. The source isQuasicoherent_pullback is scheme-specific,
   and FlatModulePullbackExact is for flat scheme maps. Neither supplies this general
   ringed-space case. Closing these geometry comparison obligations is not a short
   assembly proof with the available statements. Verdict: true, strictly underived
   pieces, with source proofs sufficient for a later worker; left open explicitly.
4. Read the top proof and RingedSpaceDerivedAdjunctionGeneral. It correctly uses hP,
   the finite-limit/colimit instances, hD, the invertible exact-functor localization
   comparison, leftDerivedUnique and leftAdjointUniq. It transports quasi-coherence
   degree by degree through mapDerivedCategoryHomologyFunctorIso. No unnecessary
   derived-equivalence construction is introduced. The only old proof_deps edge
   removed is lem-weil-pbc-affine-module-correspondence, already fully named above.
   RingedSpaceDerivedAdjunctionGeneral remains used. The unit sk-thm-picard-duality
   realized fields have no node for this item or step, so no realized route is bypassed.
   AffineModuleCorrespondence remains transitively publicly imported by the unchanged
   DirectImageAlgebraDerivedCategory interface; no closure pruning is claimed.
   Verdict: pass. Narrowed the new QCoh module's public import from Coherent to the
   Mathlib Quasicoherent module that supplies its statement's predicate, plus
   DerivedHomMayerVietoris, which supplies the public moduleRings carrier. The first
   dry run caught that KFlatPullback alone does not publicly expose moduleRings; the
   explicit carrier import repairs that without changing the signature.
5. Matched each Lean signature with its node's lean.statement and mathematical
   statement. The existing proof_deps are precisely derived adjunction, affine tensor
   exactness and underived quasi-coherence. The new exactness node explains stalk
   identification, flat tensor exactness and stalk detection; the new QCoh node uses
   exists_tensorModulePullback for the colimit-preserving underived adjunction and
   describes the restriction/free-presentation comparisons still to formalize.
   Both new nodes carry their source, searches, creation, blueprint, chapter/unit and
   Lean records. Verdict: pass. Converted the two new node statements' formulas to
   TeX without changing their meaning, and added their blueprint markers to the module
   docstrings. No Lean theorem statement or proof was changed in the second reading.

Second-reading changes: narrowed one new public import; added two module-docstring
blueprint markers; formatted the two new node statements in TeX; appended this review.
The hole accounting remains one upper hole closed, two lower holes added (decomposition).

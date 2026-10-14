## What changed

Repair H2 (reviewer X-c05cd, point 6): restored the enclosing node's entire
`lean.statement` field verbatim from the clone, including the original theorem name
and formatting. No Lean source or signature changed in this repair.

Repaired and reduced `AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`.
The core now assumes `hUc : iSup U = ⊤` and `hVc : iSup V = ⊤`, exactly the assumptions
already present on `picardScalarCech_externalCup`. Its sole caller passes those proofs.
The outer theorem and all target signatures stay identical.

The complete Lean proof eliminates p+q=n, uses `homologyπ_naturality` to express the
homology-map image as the class of the mapped cycle, and uses `cyclesMap_i`, the cycle
inclusion hypothesis and `IsPicardExternalCechCupComponent` to calculate its tuple
coordinates. It then applies the new product-cover cocycle comparison.

Added `Sheaf.AlgebraicGeometry.PicardScalarExternalCocycleComparison`, which isolates
the canonical resolution comparison part of the argument. This has no tensor total,
cochain map c, component predicate hc, arbitrary total cycle, or degree cast. It only
compares an actual target cocycle with the prescribed front/back section coordinates.
Thus it is strictly the comparison step, not a renamed copy of the core theorem.
Updated both existing DAG proof routes and added its node. All sandbox Lean files compile
without warnings through lcompile.py --all (about 6 and 10 seconds respectively).

## Proved and sorry left

Replaced the false cover-free helper by the documented corrected statement and
closed that corrected module hole:
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`
(node `lem-sc-picard-scalar-cech-external-cup-core`), after the documented statement repair.
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup` remains proved and its
signature is unchanged. No sorry remains in the item's module.

Added one hole, exactly `:= by sorry` in the new public theorem
`AlgebraicGeometry.Scheme.Modules.picardScalar_externalCocycle_comparison`
(node `lem-sc-picard-scalar-external-cocycle-comparison`). It has a source and a complete
natural-language proof in its docstring. This is a decomposition plus a false-helper
repair, not a net decrease in holes and not a fully axiom-free proof of external cup
compatibility. No definition, axiom or private sorry was added.

## No longer needed

Removed the item's direct proof import `Sheaf.Paper.CechCupPullbackCompat`.
Its node `lem-sc-picard-cech-cup-pullback-compat` remains in the planned proof dependencies
of the new comparison theorem, so this delivery does not claim to prune that module
from the targets' transitive closure.

The core no longer directly uses the planned nodes
`def-sc-field-linear-module-cohomology-operations` and
`lem-sc-picard-cech-cup-pullback-compat`; they belong to the new comparison step.
The outer theorem now directly needs only the repaired core node, rather than directly
using its historical seven-node comparison plan. Those nodes still needed for the new
comparison remain recorded there. Public statement imports
`PicardScalarCechComparison` and `PicardExternalCechCupComponent` are retained.
Removed the new comparison module's redundant public import
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`: it is already publicly available
through FieldLinearModuleCohomologyOperations and ModulePullbackTensor. Its statement
still uses the adjunction declaration, so its statement dependency stays.
No whole node or module is claimed globally unnecessary. The unit record
`sk-prop-av-cube` has no realized statement or step nodes, and its route was not changed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old version, repaired in this delivery): the cover-free core is false.
`IsModuleCechComparison` states c followed by the resolution identification and H(alpha)
equals H(beta). When the opens do not cover, H(alpha) can have a kernel, so this does not
uniquely specify c. The old cover-free helper is false. Take X=Y=P¹ over a field k with two
rational points x₀ and x₁, U=V={P¹ \ {x₁}}, and F=G the direct sum of the two
skyscraper modules k(x₀) and k(x₁). These modules are quasi-coherent. Since
Γ(P¹,O)=k and Γ(P¹×P¹,O)=k, the comparisons in degree zero need only be
k-linear, even though IsModuleCechComparison requires global-ring linearity.
The singleton Cech H⁰ is k and global H⁰ is k². The factor comparisons can
send s to (s,0), and the product comparison can send s to (s,s,s,s) in k⁴.
They satisfy IsModuleCechComparison: the alpha/beta equation is restriction
to the chosen open, which discards the omitted skyscraper summands. More
explicitly, sections on that open are exact on these finite-support modules,
so the resolution total computes the restricted module's H⁰=k; the equation
holds for every resolution. All higher factor and product Cech groups vanish,
so take the zero comparisons in higher degrees. The standard front/back
cochain pairing supplies c and hc. For a=b=1 its product comparison is
(1,1,1,1), while externalCup of the factor comparisons is (1,0,0,0).
The original Spec(k×k) example was invalid: its global-ring idempotents force
an O(X)-linear comparison to vanish on omitted components.

This is precisely why the open-cover hypotheses cannot be dropped.

The helper was corrected to the source: Stacks Tags 01FD and 0FKV explicitly assume
coverings. Its sole source caller has both hypotheses already. The change record includes
old and new signatures verbatim and the user search. The DAG's statement_change records
the old statement and its citers; no base node cites this helper, so that list is empty.
The enclosing node's route is nevertheless updated to name the core it actually applies.

The literature tex files are not present on this machine. Read the official Stacks pages
https://stacks.math.columbia.edu/tag/01FD and https://stacks.math.columbia.edu/tag/0FKV
and the Varieties page https://stacks.math.columbia.edu/tag/0BED instead. Searches used the
launcher leanfinder, loogle and grep wrappers, with the actual results in searches.jsonl;
LeanSearch additionally returned Internal Server Error, recorded as unavailable.

Edge cases: zero factor cycles give zero tensor coordinates; the target cycle is then zero
because its cycle inclusion and the tuple equivalence are injective. In degree zero the
claim is the pulled-back section tensor pairing. An empty family can be a cover only on
an empty scheme; the corresponding scalar complexes have zero classes. No affine cover
or existence of comparison isomorphisms is assumed in the new statement.

## New nodes

`lem-sc-picard-scalar-external-cocycle-comparison` is the resolution-comparison part of
steps 2 and 3 of the enclosing node. Its module states one public theorem comparing a
product-cover cycle with its external front/back section coordinates. The plan uses the
existing refinement comparison, Cech/sheaf cup and scalar Ext characterizations; the
actual core Lean proof supplies its coordinate hypothesis without a further hole.

Change record: `coord/changes/picard-scalar-cech-core-cover-hypotheses.md`.


## Earlier second reading (a previous round; superseded)

1. Interface check: compared the delivered module against the repository with a
   declaration-by-declaration signature extraction. The outer theorem's signature
   is byte-for-byte identical. The core adds only the two cover equalities recorded
   in the change record; no definition changes. Source searches find only the outer
   theorem as a caller. The original and corrected signatures in the change record
   now reproduce the source verbatim. Verdict: pass as a documented intermediate
   statement repair, not a proof of the old false statement.
2. Kernel check: both files compile without errors or warnings through lcompile.py
   --all. Scratch #print axioms checks for the core, outer theorem, and new comparison
   show exactly propext, Classical.choice, Quot.sound and sorryAx. The only local
   sorry is the named new comparison theorem. There are no definitions, axioms,
   unsafe/opaque declarations, extern attributes or implemented_by hooks in this
   delivery. The adjunction used in the signature is the existing proved theorem
   pinned by its explicit unit formula, not an arbitrary existence witness.
   Verdict: pass as a decomposition with a remaining comparison hole.
3. Split statement check: read IsPicardScalarCechComparison, IsModuleCechComparison,
   the scalar Ext and externalCup definitions, and cechCupPullbackCompat. The new
   statement handles a target cocycle with prescribed coordinates; it omits the
   tensor-total map and computes the specific comparison step. The core performs
   the actual homology-naturality and coordinate reduction to it. Zero factors,
   degree zero, empty covering families, and non-affine covers give the expected
   behavior. Cover equalities guarantee uniqueness through moduleCechAlpha_isIso.
   Re-read official Stacks Tags 01FD, 0FKV and 0BED. Independent leanfinder query
   "canonical map from cover cohomology preserves tensor product of cocycles and
   pullback", loogle query HomologicalComplex.homologyπ_naturality and grep query
   externalCup|scalarCohomologyCup returned no exact replacement. Also searched
   the library for external/Cech names. cechCupPullbackCompat provides module
   pullback and cup comparison, but not the scalar Ext identification; closing the
   new lemma is not a few-minute application of it. Its docstring supplies that
   mathematical bridge and its node records the route. Verdict: pass, still open.
4. Route and pruning check: the compiled core uses homologyπ_naturality,
   cyclesMap_i and the component hypothesis before the scalar comparison lemma.
   Public imports in the new module are needed for its signature. Removed the
   redundant TensorPullbackAdjunction public import, available transitively. The
   item retains exactly its two statement imports and one proof import. The old
   core and outer proof dependencies no longer directly used are all listed in
   No longer needed; no whole module is claimed pruned. The unit's realized
   statement and steps are empty and no unit route is changed. Verdict: pass.
5. DAG check: all three Lean records now match their source signatures verbatim.
   The core's proof and dependencies describe its coordinate calculation and the
   new comparison; the outer route describes the call to that core. The new node
   has the required source, statement dependencies, proof steps, searches,
   creation, blueprint, chapter/unit and Lean fields. Verdict: pass.

Second reading changed the invalid Spec(k×k) counterexample to P¹ with two
skyscraper summands (global-ring linearity invalidated the original example),
corrected the change record and DAG justification and verbatim signatures,
removed one redundant public import, and made the hole accounting explicit as
statement repair plus decomposition. No additional hole was closed or added.

## Second reading by G3

1. Compared both delivered modules and all existing-node changes against the repository.
   The outer theorem signature is byte-for-byte unchanged. The only existing signature
   change is the core's two cover equalities, with verbatim old/new signatures and its
   sole caller in the change record. No definition or target changed. All three DAG
   lean.statement strings equal the corresponding source signatures. Verdict: pass
   as the recorded false-helper repair.
2. Independently compiled both modules with lcompile.py --all, cleanly, and compiled
   the scratch axiom probe. Each of the three declarations uses only propext,
   Classical.choice, Quot.sound and sorryAx. The sole local hole is
   picardScalar_externalCocycle_comparison; no forbidden declaration or hollow
   definition occurs. The chosen tensor-pullback adjunction is pinned by its unit
   formula and is already proved. Verdict: pass as a decomposition, not an
   axiom-free proof of the external cup theorem.
3. Read the new statement, its coordinate restrictions, scalar and module comparison
   predicates, and existing cup/pullback constructions. Open covers make alpha
   invertible and comparisons unique; the product family covers by choosing a
   covering index for each projection. Zero factors, degree zero, and empty covering
   families on empty schemes agree with the assertion. The new hole is the actual
   cocycle comparison step, while the core proves the homology/coordinate reduction.
   Independent leanfinder, loogle and grep searches found supporting homology lemmas
   but no exact replacement. Repository searches additionally found the existing
   scalarExternalCup_moduleComparison: this supplies the last bridge, but not the
   Cech cocycle transports and product-cover cup identification. Closing those is
   not a few-minute application. Re-read Stacks 01FD, 0FKV and 0BED. Verdict: true,
   strictly simpler comparison step, still open.
4. Checked homology naturality, cyclesMap_i and use of hc in the core. Statement
   imports are needed and the new comparison is a plain proof import of the item.
   The unit sk-prop-av-cube has empty realized statement/step lists; its route stays.
   For completeness the outer node's old directly unused dependencies are
   def-sc-cech-cup-product, def-sc-cech-refinement-cochain-map,
   def-sc-field-linear-module-cohomology-operations,
   def-sc-module-cohomology-cup-product, lem-sc-picard-cech-cup-pullback-compat,
   lem-sc-picard-external-cech-cup-component, and
   lem-sc-picard-scalar-cech-comparison. The core's unused old dependencies are
   def-sc-field-linear-module-cohomology-operations and
   lem-sc-picard-cech-cup-pullback-compat. These are direct-route changes, with no
   whole module claimed pruned. Verdict: pass.
5. Checked existing node field diffs, signature strings, new-node required metadata,
   proof dependency unions and statement-change record. The outer route invokes
   the repaired core; the core performs the coordinate reduction. Updated the new
   comparison's final planned step to use the existing scalar/module external-cup
   bridge. Verdict: pass.

Second reading changed the new comparison docstring and DAG proof plan to reuse
scalarExternalCup_moduleComparison, and made the old unused dependency list
explicit. No Lean signature or proof was changed in this reading. No extra hole
was closed or added: one corrected core hole closed, one comparison hole added,
net zero; the old false core statement is not counted as proved.

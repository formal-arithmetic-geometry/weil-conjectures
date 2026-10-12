## What changed

The original theorem `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsSheaf_ulift_finiteCech_succ` now has a complete Lean proof without changing its signature or docstring. This is a decomposition, not a sorry-free proof of the underlying mathematical result.

The proof chooses the proved Zariski-to-etale inclusion, derives acyclicity on every affine etale object from the finite affine Cech basis, lifted tensor Cech vanishing and the Cech-vanishing criterion, and applies the proved Ext/right-derived evaluation comparison. A new acyclic-cover edge theorem compares derived evaluation with the open-section Cech homology. A second new theorem identifies tensor sections on opens naturally with the module section presheaf.

The private `liftedModuleCechIso` is completely proved: product-preservation comparisons give the degree maps, and the projection formula for the Cech differential, preservation of sums and integer scalar multiplication prove differential compatibility. Whiskering the section comparison by ULift and applying the Cech functor gives the remaining complex isomorphism. Applying homology and composing the additive equivalences proves the original theorem.

Only sandbox files were edited. All three Lean modules compile cleanly through lcompile.py. The item node's proof, dependencies and proof origin now follow this actual Lean argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsSheaf_ulift_finiteCech_succ` (lem-sc-etale-qcoherent-ulift-finite-cech-comparison), one original hole. The original module has no sorry left, including its private complex comparison.

Added: `AlgebraicGeometry.Scheme.nonempty_rightDerived_etale_affineOpenCech` (lem-sc-etale-affine-open-cech-derived-evaluation), exactly `by sorry` in its own module.

Added: `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensor_openSections_iso` (lem-sc-etale-tensor-open-sections), exactly `by sorry` in its own module.

Net: one original hole closed and two strictly smaller holes added. The first statement concerns arbitrary large additive etale sheaves satisfying explicit affine acyclicity, and never compares module section complexes or Ext-defined H. The second concerns presheaves and has no cohomology, cover, affineness or quasi-coherence hypothesis. The original theorem genuinely combines these parts and the fully proved coefficient-complex comparison.

## No longer needed

Removed proof-only imports: Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift; Sheaf.AlgebraicGeometry.TensorPullback; WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech; WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde.

The item no longer directly needs nodes lem-sc-etale-affine-qcoherent, lem-weil-pbc-module-pullback-quasi-coherent, lem-weil-pbc-open-immersion-module-pullback-restriction, lem-pc-module-pullback-identity-composition, or lem-sc-cech-spectral. The two new nodes still need the pullback/restriction and spectral-sequence steps where specified in their proof dependencies. The affine acyclicity module is replaced by deriving affine-object acyclicity directly from the existing finite affine Cech interfaces. No claim is made that these modules disappear from every other target path. Public imports were retained to preserve the module's public interface.

## Where the brief, the DAG or earlier work was wrong

The old plan called the full lifted complex identification elementary; the delivered Lean proof explicitly proves its product and differential compatibility. The plan also had no usable interface for the acyclic-cover edge comparison; the general spectral-sequence theorem does not directly conclude a homology isomorphism. This missing part is now separately stated with affine derived acyclicity as an explicit hypothesis.

The existing node lem-weil-pbc-open-immersion-module-pullback-restriction has no lean record, although Mathlib's restrictFunctorIsoPullback supplies the abstract restriction comparison; the tensor unit-normalized naturality still requires work. This is contained in the new open-section theorem, not a change to an existing statement.

Blueprint searches for Cech, affine, acyclic and tensor-pullback sections were run. The blueprint's generic Cech spectral sequence is used as a tool by the new edge theorem; the unit sk-prop-cd Step 5 Artin-Schreier/descent route is retained. The item's recorded nearest blueprint ancestor is null; the new records inherit this and explicitly describe the unit sentence they serve, without modifying maintainer-owned ancestry fields.

Edge cases checked mathematically: empty scheme with empty cover, singleton identity cover, repeated or empty opens, and zero module. Both new statements include these cases. No arbitrary existence witness defines data; every chosen isomorphism determines its source and target up to the equality used for transport.

LeanFinder and Loogle found component pullback and Cech definitions but no whole comparison. LeanSearch was unavailable (HTTP 500), recorded as unavailable, never as absence.

## New nodes

lem-sc-etale-affine-open-cech-derived-evaluation, module Sheaf.AlgebraicGeometry.EtaleAffineOpenCechDerivedEvaluation: the acyclic finite-affine open-cover edge comparison with derived evaluation. Source: Stacks 03AZ, specialized as in the separated-case proof of 03P2. A complete proof sketch is in the theorem docstring and node.

lem-sc-etale-tensor-open-sections, module Sheaf.AlgebraicGeometry.EtaleTensorOpenSections: the natural additive presheaf identification of unit-normalized tensor-pullback sections on opens. Source: Stacks 03DR and the adjunction comparisons of 0095/0096. It leaves the finite product and alternating-differential compatibility to the proved private helper in the original module. No change records are needed, since no existing statement or definition changed.

## Second reading by F2

1. **Statements and interfaces.** Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are unchanged byte for byte; only its proof and proof-only imports changed. The two added declarations have matching DAG records and are not duplicate restatements of the target.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; compilation succeeds with no errors. The target proof closes its original `sorry`, and the only remaining `sorry`s are the two named public split-off theorems, each with a source, proof docstring, and node. No hollow definition, axiom, unsafe, opaque, extern, or implemented_by declaration was added. The private lifted complex comparison is fully proved. Explicit `#print axioms` checks in a scratch copy show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the target and both split theorems; the delivery tool also probes all added constants.

3. **Pruning and dependencies.** The target proof uses the recorded derived-evaluation, Cech-vanishing, Zariski-to-etale, affine tensor-vanishing, and open-section interfaces. Removed proof-only imports and obsolete target dependencies are listed above under “No longer needed”; public imports preserve the module interface.

4. **Truth and strength of split statements.** The affine-open derived-evaluation statement has explicit separatedness, finite affine cover, cover, terminal-object, injective-resolution, and affine acyclicity hypotheses and concludes exactly the Cech homology comparison. The tensor-open-sections statement has no unnecessary quasi-coherence, cover, separatedness, or cohomology assumptions and concludes the natural additive presheaf isomorphism. Empty covers on empty schemes, singleton identity covers, empty opens, repeated opens, and zero modules are covered by the statements.

5. **Nodes and unit route.** The existing node changes only its proof, proof dependencies, and proof origin to follow the Lean argument; both new nodes have verbatim Lean statements, source, proof steps, dependency unions, searches, creation metadata, and split status.  The unit record has empty `realized` lists and was left unchanged. The target node retains its recorded ancestry under the finite-affine Cech comparison used in Step 5 of `sk-prop-cd`; its proof keeps the Cech spectral/vanishing route and derives the lifted complex comparison explicitly. The new nodes record the intermediate edge and section-comparison steps used by that route.

Independent LeanFinder search for acyclic covering/derived sections and open-immersion tensor restriction found component restriction, composition, and adjunction lemmas, but no complete new comparison. Repository searches for acyclic, Cech isomorphisms, restriction/pullback, and adjoint uniqueness likewise found component interfaces. A first combined quoted Loogle query was malformed; the corrected `CategoryTheory.cechComplexFunctor` query returned only the complex functor, not a derived-evaluation comparison. Neither new statement is a few-minute closure from these component lemmas.

Changed during second reading: corrected the new section-presheaf citation to equation the project server and the new node citation of 03AZ to Lemma 03AZ; clarified that zero-row differentials vanish from page E2 onward (the horizontal E1 differential is the Cech differential); appended this review record. No proof or signature changes were necessary.

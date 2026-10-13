## What changed

Repair of the returned duplicate-helper rejection: generalized the private
`AlgebraicGeometry.naturality_transport` in place. It now assumes only transport
of the two specific inputs (`hs` and `ht`), rather than naturality of the entire
family along every isomorphism. The main proof supplies those two equations from
`hi`. This is strictly more general: a family may satisfy these two equations
without satisfying global isomorphism naturality. The cancellation argument
continues to be fully proved. The existing helper in
CanonicalTensorHomUncurryDescentNaturality is private, and that module imports
this item, so directly importing its helper is unavailable and would form an
import cycle. No other existing module was adapted. The second-reading section
below describes the prior delivery; this repair awaits a fresh second reading.

Proved `AlgebraicGeometry.tensorHomUncurry_chain_natural` with its signature unchanged.
Added proof-only imports of KFlatResolution, KInjectiveHomComplex,
and the new CanonicalTensorHomUncurryLocalizedEvaluation.
The main module proves right-fraction K-flat model squares, lifting of derived arrows
into K-injective complexes, naturality of the fixed Hom resolution factorization,
and a generic isomorphism-transport/cancellation lemma. The normalization hypothesis
is applied to two explicit chain representatives and their equality is transported
back. No other existing module or interface changes.

## Proved and sorry left

Closed: `AlgebraicGeometry.tensorHomUncurry_chain_natural`
(node `lem-pc-tensor-hom-uncurry-chain-naturality`). No sorry remains in the item.
Added: `AlgebraicGeometry.schemeTensorHomUncurry_localized_evaluation`
(node `lem-pc-tensor-hom-uncurry-localized-evaluation`), in its own new module.
This is a decomposition: one upper hole closed and one strictly smaller hole added,
net zero. The new lemma only concerns explicit chain-map evaluation composites:
no family t, no normalization assumptions, no arbitrary derived input or isomorphism
transport. Every private helper is proved. The item still reaches existing unproved
library declarations through its dependencies; this delivery does not claim a
sorry-free target or a proof of the new evaluation lemma.

## No longer needed

No original import was removed: the sole public import is required by the statement.
The second reading removed the redundant added proof imports
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` and
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`; their declarations are already
available through the retained imports. No module becomes unreachable from these removals.
The planned proof dependency `lem-pc-right-fraction-common-refinement` is unnecessary;
right fractions followed by K-flat resolutions give each required commuting square
independently. No use of the common-refinement module or additional homotopy-invariance
lemma is made. No separate resolution of M or Mprime, and no comparison of two lifts,
is needed: a single K-injective lift suffices for each arbitrary input. The other removed direct proof-dependency entries are
`lem-pc-tensor-hom-uncurry-differential`, `def-pur-hom-complex`,
`lem-pc-sheaf-modules-tensor-closed`, and `def-pc-derived-pullback-tensor-comparison`.
Their component naturality, sheaf adjunction, Hom complex, differential compatibility
and tensor comparison remain needed below the new evaluation node, rather than being
pruned transitively. No unit statement or realized step is bypassed; the unit's
realized lists are empty. Other modules may still need the common-refinement node.

## Where the brief, the DAG or earlier work was wrong

The previous delivery repeated the descent module's private generic helper
word for word. The landing duplicate check correctly rejected it. The repaired
helper needs only two individual transport equations, a weaker hypothesis than
global isomorphism naturality, and therefore has a distinct, generalized type.

The plan asks for common refinements and uncurrying of homotopies unnecessarily.
The actual proof first chooses one chain representative into the K-injective target,
then forms its transformed representative by composition; there is no lift-choice
independence calculation to prove. The existing declarations of the plan do not
state the componentwise localized evaluation equality, so that strictly smaller
calculation is split off rather than hidden in the main proof.

The cited Stacks sources were read online (08DJ, 0A90, 0A96, 06YS); local literature
files are absent on this machine. Source signatures and every stated proof dependency
were read. LeanSearch was unavailable (Internal Server Error), and is recorded as unavailable.
Searches used leanfinder, loogle, grep, repository rg, and blueprint searches
for tensor Hom evaluation natural, uncurrying, and tensor-hom. No exact existing
localized evaluation theorem was found. The new statement was checked on identity
and zero maps, with no boundedness or K-flatness assumption. Attempts to finish its
component calculation encountered expensive unfolding of the Hom bifunctor and fixed
resolution. Those attempts are not delivered as partial proofs or private holes.

## New nodes

`lem-pc-tensor-hom-uncurry-localized-evaluation` records the explicit localized
chain-evaluation identity, steps 2 and the localization portion of step 3 of the
original plan. Its docstring gives the full summand and comparison-map argument.
It is strictly smaller than the item: the main module implements the remaining
replacement, lifting, two substitutions, and isomorphism cancellation in Lean.
No change records or forced adaptations are required.


## Earlier second reading (a previous round; superseded)

1. **Public interface: pass.** Read both delivered modules and compared the existing
   module and node with the repository using `diff`. Extracted the existing theorem
   signature from `theorem tensorHomUncurry_chain_natural` to `:= by` and checked
   byte-for-byte equality. The parameters X, universe-polymorphic derived category,
   arbitrary family t, K-flat normalization ht, isomorphism naturality hi, and
   arbitrary derived input f are unchanged. All three original chain maps and the
   tensor/Hom conclusion are unchanged. No existing definition, public import or
   visibility changed. The four added private helpers are proved propositions;
   witnesses of resolutions and lifts are eliminated locally in proofs, with no
   data definition selecting an arbitrary unproved witness. No change record needed.

2. **Proof and axioms: pass as a decomposition.** Both files compiled in import order
   through `lcompile.py`, without errors or warnings. The main file has no sorry;
   the new file has exactly the single reported named theorem hole, and neither file
   contains axiom, unsafe, opaque, implemented_by or extern. Scratch copies with
   `#print axioms` for both public declarations returned only propext,
   Classical.choice, Quot.sound and sorryAx. The latter is expected: the explicit
   evaluation theorem is open, and the imported library still has open proofs.
   Checked the four private helpers: `Localization.fac.inv.naturality` gives the
   required Hom-model square, `Qh_map_bijective` and quotient fullness supply a lift,
   `right_fac` followed by K-flat resolution supplies the two model squares, and
   `naturality_transport` cancels only isomorphisms. The main argument applies ht
   twice to these actual lifts and hi twice to these actual replacement isomorphisms.

3. **Split statement: pass after a node correction.** Read the evaluation statement
   against its component definitions and the projection-map specification in
   `homComplex_exists`. Its maps a,b,c have degree zero, so no additional Koszul
   sign is introduced: on degree n=p+q both sides evaluate
   `(a_p tensor b_q);U(phi)_n;I(c)_n`. Naturality of the lax comparison and inverse
   augmentation gives the displayed localized identity without any K-flatness
   assumption. Checked all identity maps, each zero map, zero phi, and complexes
   concentrated in arbitrary integer degrees; all have the claimed identity or
   zero evaluation. The coproduct argument also handles unbounded complexes.
   The node prose had omitted the final Qc, making its right side have the wrong
   target; added it to agree with Lean and removed the inaccurate source label
   `lemma-compose`. This is a new node, so no existing statement was changed.
   Its docstring contains the complete summand, coproduct, comparison and
   augmentation argument; its new module and complete node carry matching names.
   This is strictly the explicit chain-evaluation part, with no family t, ht, hi,
   derived input lift, model replacements or isomorphism cancellation.
   Read Stacks [0A90](https://stacks.math.columbia.edu/tag/0A90) and
   [08DJ](https://stacks.math.columbia.edu/tag/08DJ) for the functorial tensor-Hom
   construction, and [0A96](https://stacks.math.columbia.edu/tag/0A96) and
   [06YS](https://stacks.math.columbia.edu/tag/06YS) for the two resolution facts.
   Repeated msearch with the different query “Evaluation of a Hom cochain complex
   commutes with total tensor maps and postcomposition”, Loogle tensorHomEquiv,
   and grep evaluation/uncurry composition; also searched the actual sheaf
   adjunction and repository using rg. Results include Mathlib tensorHom and
   abstract uncurry naturality, and upstream tensorHomEquiv naturality, but no
   existing localized composite theorem. The normalized-comparison and
   representative-coherence modules concern different inputs and remain open.
   The smaller calculation requires a component proof and substantial resolution/
   tensor-instance setup; no immediate existing theorem closes it in a few minutes.

4. **Route and pruning: pass after report/import repair.** Reviewed the reduction
   from the original hole downward. It uses the Mathlib right-fraction and
   K-injective morphism lemmas directly, with the existing K-flat resolution and
   Hom K-injectivity declarations; no duplicate such facts were added. The new
   hole isolates precisely the component calculation the original plan needed.
   Removal tests established the explicit Mathlib derived KInjective and Fractions
   imports were redundant, so removed both; removing KFlatResolution fails with
   unknown exists_isKFlatResolution, and removing KInjectiveHomComplex fails with
   unknown isKInjective_homComplex_of_isKFlat. The sole public import remains needed by the signature.
   Listed every old proof_deps entry absent from the new list in No longer needed,
   distinguishing the common-refinement node from dependencies retained through
   the new lemma. Read dag/units/sk-thm-picard-duality.json, including its statement,
   step and realized={statement:[],steps:[[]]}; no realized node is bypassed and
   no unit record is changed. This delivery closes one hole and adds one hole,
   with net zero, and claims no newly unreachable library module.

5. **DAG agreement: pass after correction.** The existing node changes only proof,
   proof_deps and proof_origin. Its three steps match kflat_arrow_rep, the
   K-injective lift plus Hom-model naturality and ht substitutions, and the
   proved generic cancellation helper. proof_deps is exactly the union of uses.
   Checked the named dependency declarations and their types against those calls.
   The new node contains the source, statement dependencies, two-step prose proof,
   proof-dependency union, searches, origin, split status, creation record,
   blueprint ancestry, matching chapter/unit and verbatim Lean signature.
   Corrected the missing Qc in its statement as described above.

Second reading changes: removed two redundant proof imports, corrected the new
node's missing final Qc and inaccurate source label, completed the explicit
pruning list, and added this independent review. The Lean proof is otherwise
retained; no additional holes or definitions were introduced.


## Second reading by M2

1. **Interface: pass.** Independently diffed the existing module and node against
   the read-only repository. The complete existing theorem signature is byte for
   byte identical (verified by extraction). Only proof imports, proved private
   helpers, the proof and its explanatory docstring change. No definition or
   public import changes, and no adaptation or change record is needed.

2. **Proof: pass as a decomposition.** Recompiled both actual modules in import
   order through lcompile.py (4.8 s and 32.0 s), without errors or warnings.
   Scratch copies printing the axioms of both public declarations compiled and
   showed exactly propext, Classical.choice, Quot.sound and sorryAx. The item
   contains no sorry; the new module contains exactly its reported named hole.
   Neither contains axiom, unsafe, opaque, implemented_by or extern. No data
   definition is added: existential resolutions and chain lifts are eliminated
   only inside theorem proofs. Read all four helpers and the main reduction.
   The revised transport helper assumes the two specific equations hs and ht,
   rather than global naturality; its functoriality and iso cancellation proof
   is valid, and its two uses of hi supply exactly those equations. Compared
   its type with the descent module's private helper: they differ genuinely,
   and importing the descent module would produce a cycle.

3. **Split statement: pass.** Read the component construction, coproduct extension,
   actual Hom projection functoriality equation in homComplex_exists, lax tensor
   comparison and inverse resolution augmentation. The component of both sides
   is evaluation after a_p and b_q, followed by I(c)_n. Degree-zero chain maps
   introduce no extra sign. With identities the component equality reduces to
   itself; with any zero map or zero input it reduces to zero; complexes in
   arbitrary single integer degrees obey the same formula. Coproduct
   extensionality works without boundedness. The source/docstring and matching
   node give the complete argument. The lemma is strictly the explicit chain
   evaluation calculation, without the family's hypotheses or derived lifting.
   Read Stacks 0A90 and 08DJ online independently. Repeated searches with
   leanfinder (evaluation commuting with pre/postcomposition), loogle
   uncurry_natural_right and grep uncurry_pre_app/braiding_naturality, plus rg
   throughout both Lean roots. Mathlib has the abstract adjunction ingredients;
   HomTensorNaturality has a different iterated-Hom currying statement, not
   this fixed localized evaluation identity. No exact existing lemma found.
   Closing the remaining component calculation requires more than a direct
   application of these results; no new holes were introduced in this reading.

4. **Route and pruning: pass.** The proof uses right fractions and K-injective
   bijectivity directly, existing K-flat resolution and Hom K-injectivity, then
   two normalization substitutions and cancellation. It does not rename the
   original hole. All five old proof_deps absent from the new list are already
   enumerated in No longer needed, with indirect dependencies distinguished.
   Retained proof imports supply the new evaluation theorem, K-flat resolution
   and Hom K-injectivity. No redundant explicit Mathlib imports remain.
   Read sk-thm-picard-duality's statement, step and empty realized lists; no
   realized unit route is bypassed. One closed hole and one added hole is net
   zero decomposition; no module is claimed transitively pruned.

5. **DAG: pass.** Existing node changes only proof, proof_deps and proof_origin.
   Both Lean signatures equal the corresponding node strings, and proof_deps
   equals the union of uses in proof steps (checked programmatically).
   Read each named dependency against its use. The new node has source,
   dependencies, complete proof, searches, split status, creation, blueprint,
   chapter/unit and Lean record. Its statement includes the final Qc and agrees
   with Lean. The transport-generalization description matches the code.

Second reading changed only this report: added a fresh independent review of
all five points after the transport-helper repair. Lean and DAG retained.

# Stage-1 delivery: lem-sf-ringed-forget-tensor-transposition

## Files written

- `dag/nodes/sec-six-functors/lem-sf-ringed-forget-tensor-transposition.json`: statement item, now split in ten steps; Mathlib no match. Its statement and statement dependencies are unchanged.
- `citations.json`: 25 step/node entries, each with a literal excerpt of the statement being used.
- `report.md`: this report. `searches.jsonl` is the search command's actual log; `write_split.py` is sandbox-only preparation code, not a project change.

New nodes: 0. New Mathlib leaves: 0. Existing nodes suffice for the proof.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and item id and for ringed forgetting, tensor forgetting, normalized adjunction and transposition/double-dual notions. The hits on forgetting and tensor concern other functors; none states all clauses of this item. No existing sorry declaration was counted as a proof.

## WANTED

None. The blueprint paragraph and the supporting Stacks sources are available locally.

## What was wrong or incomplete

The item was statement-only, not an accepted split. The blueprint's sentence “Naturality of evaluation proves its equivariance, and transposition gives the same conclusion for delta” does not itself establish the prescribed derived normalization. The proof now constructs the tensor comparison on actual coproduct total complexes, descends it, and compares the two fixed target augmentations before invoking transposition. Nothing in the imported statement needed correction. There is no STATEMENT-DISPUTED claim.

The nearest blueprint ancestor command prints `None`: the item's parent chain contains the maintainer-created native obligation. I retained its null ancestry and nonempty textual place and via fields, and identified the actual paragraph in split_report.blueprint. No blueprint or unit file was changed.

## Unfinished work

None for this one-level stage-1 split. Several cited nodes remain open elsewhere in the DAG; they are cited for their statements, and no proof or Lean completion of those nodes is claimed here.

## Searches and reuse

I searched the DAG for K-flat localization, tensor model rigidity, normalized currying, Hom into K-injectives and Tag 070I. This found `lem-weil-pbc-site-derived-tensor-descent`, `lem-pc-kflat-resolution`, `lem-coef-hom-kflat-into-kinjective-independent-coefficients` and `lem-sc-kinjective-quasi-iso-comparison`, among others. I read their statements rather than using hidden details of their proofs. In particular `lem-sp-kinjective-computes` is bounded below and `lem-sp-kinjective-comparison-principle` only asserts precomposition bijectivity; neither was substituted for the unbounded localization-to-Hom bijection. The latter is supplied exactly by the existing Mathlib leaf `lem-sc-kinjective-quasi-iso-comparison`.

Whole-blueprint searches ran for `tensor transposition`, `transposition`, `evaluation-normalized`, `K-flat`, `localization`, and `forgetful`. No blueprint node states the present general normalized forgetting theorem. The transposition hit `det-sp-unique-adjoint-coefficients` concerns coefficient adjoints, not this exact functor and its tensor/Hom representatives. No new node is needed. The related `lem-sf-cochain-tensor-model-rigidity` was read, but the older ringed-site tensor descent node already supplies the precise extension assertion needed, so it alone is cited.

Q72 ran LeanFinder twice with distinct phrasings, LeanSearch, Loogle, and the required command's source grep. The node retains the Q48 historical searches and adds the exact Q72 queries recorded in searches.jsonl. The Loogle hit `CategoryTheory.uncurry_expComparison` was inspected at `Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean:42-103`: it assumes Cartesian monoidal categories, so it does not specialize to derived sheaf tensor. The LeanFinder exact-functor hit was inspected in `DerivedCategory/ExactFunctor.lean:29-70`; it only gives the exact functor on localization, which is already a cited leaf. The injective-resolution hits concern ordinary right-derived functors, not the product internal Hom and signed total tensor compatibility here. No service failure was recorded as an absence result.

## Not duplicates

No new nodes were created; there are no new/existing pairs to justify. The actual component calculations and the formal double-dual computations remain steps of the item, rather than nodes restating its clauses.

## Review by Q72

I read the current item, its parent native-closed-forgetful statement, the six-functors chapter and the biduality unit, and the entire source paragraph in `main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md`. This is a generic tool below that unit's evaluation/transposition argument; it does not change its geometric biduality route. No SGA source is used. I also read Stacks `sites-cohomology.tex` at Tag 06YS (`lemma-K-flat-resolution`), 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`), 0A90 (`lemma-compose`), 0A96 (`lemma-RHom-from-K-flat-into-K-injective`), 08J9 (`lemma-internal-hom`), and 0FPT (`lemma-symmetric-monoidal-derived`), and `derived.tex` Tag 070I (`lemma-K-injective`). Stacks omits some tensor/Hom structural proofs; my coherence and transposition calculations are explicitly agent-written, not attributed to a nonexistent verbatim Stacks theorem.

Step 1 uses the exact-functor factorization node, whose statement explicitly says that termwise U represents D(U) for every complex without resolving U. Exactness and additivity are hypotheses of this item, so this applies to the unbounded categories here.

Step 2 uses the actual signed direct-sum definition of `def-pc-tensor-complex-sheaves`. The maps are built from the assumed coherent underived isomorphisms and the assumed preservation of small coproducts. Naturality handles each differential and additivity handles its integer sign. This is an elementary check on coproduct inclusions; it does not assume the tensor's sections are globally generated by pure tensors.

Step 3 uses the statement, not the proof, of `lem-weil-pbc-site-derived-tensor-descent`: it explicitly supplies flat-term K-flat localization, representative tensor isomorphisms, and extension/uniqueness for natural transformations of bifunctors. The present sites are small in the required universes, both coefficient sheaves are commutative, and U preserves the required class of representatives by hypothesis. Extending the inverse comparison proves invertibility without assuming it.

Step 4 uses the explicit representative associators/unitors/signed symmetry in `lem-sf-ringed-derived-closed-symmetric-monoidal`, closure with flat terms explicitly stated by `lem-pur-kflat-total-tensor-model`, and existence of flat-term K-flat representatives explicitly asserted by `lem-pc-kflat-resolution`. The tensor-unit complex is K-flat and flat because tensoring by the unit is the identity. On triple summands associativity is exactly the underived coherence assumed for U; the swap contributes the same sign on each path. Essential surjectivity of the chosen representatives suffices to check natural coherence diagrams; no functorial resolutions are assumed.

Step 5 uses the K-flat resolution node for both source objects, the K-injective existence node and derived-Hom definition for the fixed target I, the coefficient-independent K-flat-to-K-injective Hom lemma for K-injectivity of Hom(S,I), and the existing 070I Mathlib leaf for lifting every derived arrow to a chain map modulo homotopy. I checked that this last leaf allows an arbitrary unbounded source: a lemma only about two injective resolutions or bounded-below complexes would not suffice.

Step 6 uses the representative normalization, which explicitly provides the chain map psi and inverse localized target augmentation, and the two-injective comparison's explicit compatibility with precomposition by source resolutions. Thus chi's product formula may be evaluated on the K-flat source S without asserting S is K-injective. The Hom differential is taken from its actual definition. The final chain-map identity is precisely the underived evaluation-preservation hypothesis, tested on every product projection and tensor summand. It uses equality of sheaf morphisms and does not treat U as a sectionwise functor between unrelated sites.

Step 7 corrects the possible normalization gap by constructing j from UI to the fixed I'(UV). The 070I leaf gives a representative of the required localized isomorphism and gives the homotopy equation under the augmentations. The derived-category definition supplies cohomology factorization, showing j is a quasi-isomorphism as required for target replacement. The two-injective comparison's statement includes target-replacement compatibility; the model definition gives exactly the target normalized uncurrying. Postcomposition by j commutes with evaluation, and the identity eta' inverse times j equals (U eta) inverse cancels the two choices. This is the reason the proof establishes the specified adjunction, rather than merely producing some closed comparison.

Step 8 uses the named adjunction and symmetric-closed statements, together with the comparison's stated choice independence and the Hom bijection. Setting a to the identity gives exactly the displayed evaluation equation with mu in the required orientation. The proof establishes equality of derived morphisms, not merely equality on cohomology.

Step 9 checks naturality of delta by uncurrying both sides, using the explicitly natural adjunction and the evaluation and symmetry of the symmetric-closed structure. The two evaluations are written out with d=H(u,W), so contravariance is used in the right direction. Step 10 writes the iterated comparison with H(chi inverse,FW), again in the contravariant direction, and computes its uncurry in two equalities from Steps 4, 7 and 8. Cancellation gives exactly symmetric evaluation in the target. These are short formal calculations from already established steps, not separate hidden lemmas or duplicate nodes.

I checked delivery-errors B1-B10: there is no new statement-only node to audit or search; existing notions and metadata are retained; the recorded new searches actually ran; no Mathlib candidate was promoted without its hypotheses. For C1-C8, every non-elementary external input is an explicitly cited node with a statement quote in citations.json, not a source tag standing in for a dependency. The off-unit non-leaf tools needing declaration are generic ringed-site tensor localization, K-flat resolution, and closure of flat-term K-flat complexes under total tensor, recorded in split_report.tool_uses. The extra total-tensor closure citation prevents assuming without justification that an iterated tensor is still a representative with flat terms. The K-injective existence node lies on the unit route, and the Hom-localization and exact-functor nodes are Mathlib leaves. For D1-D5, the item carries the actual comparison, normalization, and transpose arguments and moves nothing into a clause-shaped new node. For E1-E7, no extra preservation hypothesis, boundedness, finite-generation or dualizability assumption is used. I checked the zero complex, the tensor unit in degree zero, one nonzero bidegree, and odd/odd swapping: both paths have the same differential and the same Koszul sign, including characteristic two. W may be zero or arbitrary; delta need not be invertible (for W=0 it is generally the zero map to zero). No step exceeds 2000 characters, and I checked each for an implicit independent subclaim.

## Validation

The preliminary remote review_split passed with 0 new nodes; the preliminary remote check_dag reported no finding introduced by the sandbox or on its nodes. A final delivery dry run follows the additional explicit total-tensor closure citation.

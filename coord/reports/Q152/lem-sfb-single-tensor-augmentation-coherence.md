# Worker report: lem-sfb-single-tensor-augmentation-coherence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-single-tensor-augmentation-coherence.json`: statement, split; no exact Mathlib match. Five proof steps; all shorter than 2000 characters. The imported statement and existing search records are retained.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `searches.jsonl`: actual searches made through the required msearch command.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. The general native derived localization result already exists, so making a new localization, coherence or augmentation node would duplicate it or restate the item.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag, single/lax notions and tensor augmentation found no declaration covering this item's full statement. `DerivedCategory.moduleCup_canonical_hzero_identification` in `AlgebraicGeometry/ModuleCupCanonicalHZeroIdentification.lean` gives the canonical tensorator and one-sided flat-model formula, but does not state the associativity, symmetry and both unit clauses. It is not an attachment. The generic lax localization declarations are prerequisites, not a declaration of this whole item.

## Wanted literature

None. No SGA source was used.

## Problems found and corrected

The item had no proof, and an augmentation formula alone does not prove its coherence. The split explicitly defines the map using the canonical lax localization tensorator, derives the two-resolution formula by naturality, and expands the diagrams. In particular, tensoring the augmentations is not assumed to give a quasi-isomorphism, and a resolution of F tensor a resolution of G is not passed off as a resolution of the ordinary tensor sheaf. The intermediate sheaves in the associativity law need not be flat.

The legacy chapter/unit records were read along with the current `literature/blueprint/latest/` unit and direct-images proof. The current detailed direct-images proof (3) and the imported provenance specify the geometric route; this item is the coefficient-tensor prerequisite reached through the coherent-H1/group-bialgebra chain recorded in its existing blueprint field. The generic localization tool does not change that geometric route. `blueprint_refs.py ancestor` returns `None`, as already recorded by the inherited item; the full existing place/via data is retained, rather than inventing an ancestor. Searches of the whole blueprint for augmentation, single, lax, derived monoidal and augmentation coherence found no node stating this particular normalized single-functor result.

No statement dispute was found. The source explicitly says the lax-single diagrams are an agent refinement, not verbatim assertions of the Stacks tags; the proof retains agent origin.

## Unfinished work

None for the one-level stage-1 split. No Lean was written and no compiler or build was run.

## Not duplicates

There are no new nodes and hence no same-tag new/existing pairs. Existing results are cited directly: in particular `lem-sf-ringed-derived-native-tensor` supplies the native localization tensor and its canonical lax tensorator. `lem-pur-kflat-cone-comparison` was read as a potential augmentation prerequisite but is unnecessary: the naturality equation already gives exactly the two-resolution formula. No cone or Tor-vanishing statement is used.

## Review by Q152

I read Stacks `cohomology.tex`, the construction preceding and including Tag 06YH (`definition-derived-tor`, with the K-flat-resolution and other-side quasi-isomorphism lemmas), Tag 0FP8 (`lemma-symmetric-monoidal-cat-complexes`, including its explicit unit and sign hints), and Tag 0FPB (`lemma-symmetric-monoidal-derived`). The latter omits the coherence proof, so I did not cite its omitted proof as if it provided an argument. I also read the latest blueprint's derived-monoidal statement/proof and the current unit/direct-images route. The supplementary source-library files `CategoryTheory/Monoidal/Instances/DerivedCategory.lean`, `CategoryTheory/Monoidal/DerivedBraided.lean`, and `FromJoel/CategoryTheory/Monoidal/Derived.lean` confirm which canonical lax maps and unit normalization the existing native construction uses; the last file defines its derived-localization unit map as the identity. No new node requires an additional source.

For step 1 I opened the complete statements of `lem-weil-pbc-sheafification-exact`, `lem-sf-ringed-derived-native-tensor` and `def-pc-scheme-derived-tensor-structure`. The first gives exact abelian sheafification, covering the additive sheafification hypothesis of the second on the small Zariski site. The native result supplies the canonical lax tensorator, invertibility on K-flat pairs, normalized comparisons and compatibility with braiding, associator and unitors. It applies to all module sheaves, not just quasi-coherent ones, and allows a chosen derived-category universe. The fixed scheme-derived tensor definition specifies this same K-flat construction and the unit O_X[0]. In the proof I explicitly use this unit identification; I do not replace an arbitrary unit map by the identity. No separation, quasi-compactness or finite-type assumption on X is needed for its small Zariski site.

For step 2 I read `def-pc-tensor-complex-sheaves` and `lem-pc-sheaf-modules-tensor-closed`. The first states the direct-sum total-complex formula and functoriality. The second states exactly the ordinary symmetric monoidal constraints and their origin in sectionwise module constraints. Only one summand of a tensor of degree-zero complexes survives; the only triple summand is (0,0,0). This makes the single-complex tensor isomorphism, its associativity equation, its unsigned braiding, and both unit equations direct component calculations. This is an elementary step, not a new coherence lemma hidden under a citation.

For step 3 the native localization theorem gives naturality of its canonical lax tensorator and its invertibility on the supplied K-flat representatives. The equation written in the step then represents m on the total tensor by the tensor of the two augmentations. Inverting Qa and Qb is legitimate because the hypotheses call them quasi-isomorphisms; inverting the tensorator is legitimate because P and T are K-flat. No tensor augmentation itself is inverted. This proves the prescribed normalization for every permitted pair and choice independence without needing lifts between projective resolutions, which need not exist for arbitrary flat sheaf resolutions.

For step 4 I expanded both occurrences of m in associativity. The native theorem's lax associativity law moves the two tensorators; their naturality moves Q of the single-complex tensor isomorphisms; the concrete equation from step 2 identifies the remaining complex map. Thus the cited statement really supplies the non-elementary coherence fact. I did not apply it only to K-flat F[0] or claim a composite sheaf was flat.

For step 5 I read the complete statement of `lem-pc-kflat-resolution` and verified that it applies to all complexes on the small Zariski site. To avoid taking the native theorem's K-flat comparison clause as an unstated global lax-braiding assertion, I added the explicit argument: choose K-flat replacements, invert the normalized representative comparison there, use naturality of the tensorator and braidings, and cancel the tensor of the localized replacement isomorphisms. This proves the braided equation for arbitrary sheaves from precisely what the cited statements give. I then used the native theorem's lax unit equations and the fixed scheme unit, together with the degree-zero identities already checked in step 2. The Koszul sign is +1 before shifting, since both indices are zero. The left and right unit arguments are both given, with the unit comparison factor explicitly identified. The full native-theorem statement is quoted for each use in citations.json, rather than quoting only its K-flat invertibility clause for a coherence use.

I checked delivery-errors B through E: all notions are inherited and already have statement dependencies; no new statement-only node is disguised as a proof; actual msearch calls are recorded; every proof citation was checked against the node's statement and copied verbatim; off-unit generic tools are declared in split_report.tool_uses; a read-only dependency traversal found no path back to this item from the used localization/structure nodes. Each proof step is under 2000 characters, with no long-step hidden lemma. I retained earlier Mathlib searches and appended six actual searches in the current search log, using two semantic phrasings plus Loogle, LeanSearch and grep. Ordinary sheaf tensor and ordinary monoidal localization search hits do not give this result in one line.

Small cases checked: X empty and zero sheaves give zero maps and tautological diagrams; taking F or G equal to O_X gives the unit identities; over Spec(Z), F=G=Z/2 has a nonzero negative Tor term, so the comparison cannot be silently assumed invertible. The construction kills the negative-degree part on a nonpositive flat model and has the required degree-zero augmentation. Characteristic 2 does not change the degree-zero sign computation. These checks support keeping the item's unrestricted hypotheses and its explicit non-invertibility qualification.

## Final self-review correction

The initial dry run passed at 6b8335d3fd2. A final C4 reading sharpened step 5: the native result explicitly gives braiding compatibility of the K-flat comparisons, so the revised step derives the unrestricted equation by replacements and cancellation, citing the existing resolution-existence node. Its entire statement is quoted in citations.json. This is a correction of the proof explanation, with no statement change or new node.

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-mayer-vietoris-ringed-space.json` (item, repaired split).
- `dag/nodes/sec-curve-estimates/lem-sc-ringed-space-restrict-injective-resolution.json` (statement-only node, no Mathlib match).
- `dag/nodes/sec-curve-estimates/lem-sc-ringed-space-injective-restriction-surjective.json` (statement-only node, no Mathlib match).

2. Attachments: none.

3. WANTED: none.

4. The returned proof incorrectly applied a derived-functor long exact sequence to a sheaf sequence whose middle terms are direct images, without identifying their cohomology with cohomology on the opens. I replaced it with the actual 01EB proof: choose an injective resolution on X; use the two new ringed-space nodes (01E1 and 01EA) to restrict injectives and obtain surjectivity on U∩V; form the short exact sequence of section complexes; and apply the long exact cohomology sequence for complexes. Naturality in F is now on lifted maps of injective resolutions, and restriction to W' is a morphism of the same complex-level short exact sequences. The prior sheaf short-exact node is no longer used by the item, since the complex argument supplies the needed exactness directly.

## Review by M1

I read the source proofs of Stacks Cohomology Lemmas 01E1, 01EA, and 01EB in `/home/ubuntu/c1-stacks-review/cohomology.tex`. Step 1 uses the definition node for injective-resolution cohomology, the new 01E1 node for injectivity after restriction, the new 01EA node for surjectivity of restriction maps of an injective, and the existing complex long-exact node. These statements give exactly the hypotheses used: each degree has exact sections by the sheaf condition, and the final restriction map is surjective. Step 2 uses the existing lift-to-injective-resolutions statement and restrict-injective node, then the existing naturality theorem for long exact sequences of short exact complexes; this explicitly handles connecting maps and homotopy-independent lifts. Step 3 uses the same restriction node to identify the restricted resolution and the complex naturality node for the restriction morphism, with the cohomology definition identifying the terms. I checked that all cited quotes are verbatim, that the new statements are self-contained for arbitrary ringed spaces, and that the previous direct-image argument is removed. Mathlib searches for each new node used LeanFinder, Loogle, and grep and found no match.

## Not duplicates

lem-sc-ringed-space-restrict-injective-resolution vs lem-weil-pbc-module-open-restriction-injectives: the existing node is scheme-only, while this node is for arbitrary ringed spaces and explicitly gives the restricted injective resolution.
lem-sc-ringed-space-injective-restriction-surjective vs lem-sc-ringed-space-restrict-injective-resolution: the former asserts surjectivity of sections of an injective (01EA); the latter asserts preservation of injective resolutions under restriction (01E1).
lem-sc-mayer-vietoris-ringed-space vs lem-sc-mayer-vietoris-open-cover-sheaf-short-exact: the item is the cohomological long exact sequence with naturality; the child is only the sheaf-level short exact sequence.
def-sc-ringed-space-module-cohomology vs lem-sc-ext-locally-free-second-naturality: the existing occurrence is an Ext naturality application, while this node gives the arbitrary ringed-space module cohomology definition used here.
def-sc-ringed-space-module-cohomology vs def-sc-sheaf-cohomology-functor: the existing node is scheme-specific, while this node is for arbitrary ringed spaces and O_X-modules.
def-sc-ringed-space-module-cohomology vs def-sc-topological-abelian-cohomology: the existing node concerns abelian sheaves, while this node concerns O_X-modules on a ringed space.
lem-sc-ringed-space-injective-restriction-surjective vs lem-sc-ext-coherent-hom-injective-flasque: the existing node is a scheme/coherent-Hom specialization, while this node is the general ringed-space injective section restriction lemma.
lem-sc-ringed-space-restrict-injective-resolution vs lem-weil-pbc-module-cech-vanishing-criterion: the existing use is within a scheme Cech argument, while this node states the arbitrary ringed-space 01E1 restriction result.
lem-sc-ringed-space-restrict-injective-resolution vs lem-weil-pbc-zariski-open-restriction-injectives: the existing node is Zariski/scheme-specific, while this node applies to every open subspace of a ringed space.
lem-sc-ringed-space-module-sheaves-enough-injectives vs lem-weil-pbc-scheme-modules-enough-injectives: the existing node assumes a scheme, while this node assumes only a ringed space.
lem-sc-ringed-space-module-sheaves-enough-injectives vs lem-weil-pbc-scheme-modules-functorial-injective-embeddings: the existing node is scheme-only and adds functorial embeddings, while this node is the general enough-injectives input.

5. Nothing remains unfinished.

## Second reading by M1

- Item statement: checked against Stacks Cohomology Lemma 01EB (label `lemma-mayer-vietoris`) in `cohomology.tex`; the ringed-space, two-open-cover, long-exact-sequence, restriction/difference-map, and module-naturality hypotheses and conclusions agree with the stated source and its proof-level restriction construction.
- Step 1: checked against the statements of the cohomology definition, restriction-of-resolution node, injective-section-surjectivity node, and complex long-exact node; each cited statement supplies the corresponding resolution, exactness, surjectivity, or connecting-map claim, with the sheaf-kernel calculation elementary.
- Step 2: checked against the lift-to-injective-resolutions and complex long-exact naturality statements; the step now uses only the cited lift formula for independence of the lift and explicitly obtains naturality of connecting maps.
- Step 3: checked against the restriction-of-resolution, cohomology-definition, and complex naturality statements; these give the restricted resolution and the morphism of short exact complexes, including connecting maps.
- `def-sc-ringed-space-module-cohomology`: checked against Stacks Tag 01DZ, label `section-cohomology-sheaves`, and its injective-resolution definition; self-contained and no Mathlib match.
- `lem-sc-ringed-space-restrict-injective-resolution`: checked against Stacks Tag 01E1, label `lemma-cohomology-of-open`; arbitrary ringed-space and open-subspace hypotheses are explicit and no Mathlib match.
- `lem-sc-ringed-space-injective-restriction-surjective`: checked against Stacks Tag 01EA, label `lemma-injective-restriction-surjective`; both restriction surjectivity and the two-open difference-map consequence are stated and no Mathlib match.
- `lem-sc-ringed-space-module-sheaves-enough-injectives`: checked against Stacks Tag 01DI, label `lemma-sheaves-modules-space`; the arbitrary ringed-space module category and enough-injectives hypotheses are explicit and no Mathlib match.
- Small cases: the empty cover is excluded by the explicit union setup unless X is empty; for X empty or U=V=X the sequence reduces to the identity/restriction cases, and degree zero agrees with the sheaf equalizer. No node asserts a nontrivial conclusion for a zero module or field beyond these identities.

Changes made: corrected the item node's `created.item` ownership from the unrelated open-cover item to this item, and removed the uncited homotopy-uniqueness assertion from Step 2, replacing it with the cited derived-functor lift formula. Re-ran the full delivery preflight after these repairs.

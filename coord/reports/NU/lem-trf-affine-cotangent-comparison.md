## Worker report

Files written (all under the item sandbox):

- `dag/nodes/sec-trace-formula/lem-trf-affine-cotangent-comparison.json`: split, nine proof steps, statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-topos-inverse-image-differentials.json`: new statement, unsplit; no Mathlib match for geometric inverse image of sheaf differentials.
- `dag/nodes/sec-trace-formula/lem-trf-localization-cotangent-vanishing.json`: new statement, unsplit; no Mathlib match for vanishing of the full simplicial cotangent complex of an arbitrary localization.
- `citations.json`: one verbatim statement quotation for every dependency of every numbered proof step. Full statements are quoted so that all hypotheses remain visible.

Attachments: none. Searched `WeilConjectures/` in slopmaster2 for the item tag, cotangent complex, CotangentComplex, cotangent/conormal notions, and the two proposed dependency notions. The relative-differentials definitions in `AlgebraicGeometry/TangentSpace.lean:175-188` and `AlgebraicGeometry/Modules/Differentials.lean` do not state the topoi-level comparison, a standard simplicial complex, or localization in all degrees. Master was also searched as reference material; its declarations are not treated as finished proofs.

WANTED: none. All mathematical sources used are present in `literature/stacks-project/`.

What was wrong: the item was an unsplit package, not a false statement. No statement correction or dispute was needed. I preserved its provenance, original searches and blueprint ancestry. The arbitrary-polynomial-resolution part of `lem-trf-cotangent-resolution-coherence` is not used: only its explicit standard complex and strict functoriality for squares of rings are used.

Unfinished: the two new statements are deliberately left unsplit for subsequent stage-1 work. No Lean was written and no compiler, Lake or build command was run.

## Sources and route

Read `cotangent.tex` at 08SR (`definition-standard-resolution-sheaves-rings`), 08SS (`definition-cotangent-complex-morphism-sheaves-rings`), 08SV (`lemma-pullback-cotangent-morphism-topoi`), 08SW (`lemma-compute-L-morphism-sheaves-rings`), 08SX (`remark-map-sections-over-U`), 08T0 (`lemma-stalk-cotangent-complex`), and 08SF (`lemma-localize`). For localization I also read 08QZ, 08R2 and 08R3, including their proofs. The proof of the base-localization comparison can equally be obtained directly from transitivity and 08R2(3), so no extra base-localization lemma is introduced.

For the new differentials node, read `sites-modules.tex` 08TP (`lemma-differentials-sheafify`) and 08TQ (`lemma-pullback-differentials`), including the presentation by a cokernel of free modules. The comparison is the one preserving the universal derivation. Naturality and composition are its canonical universal-property identifications. For the new vanishing node, read `cotangent.tex` 08R2 (`lemma-when-zero`), case (3), with no finite-presentation assumption.

Read the chapter and unit records `sec-trace-formula` and `sk-i-curve-zero` and the current main-20261015 locality proof. This item is a lower commutative-algebra/sheaf input in the previously recorded semistable-curve/dualizing-line branch, through the lci presentation. I retain that ancestry; this split does not replace the unit's proof or add a route through SGA. The off-unit generic tools are declared in `split_report.tool_uses`; they provide only sheafification, inverse image, tensor, stalk, flatness and derived-category formalities.

## Existing-node and Mathlib searches

Searched the whole DAG by the source tags 08SR/08SS/08SV/08SW/08SX/08T0/08SF, 08TP/08TQ, 08R2, by polynomial/free-algebra, inverse-image, sheaf differentials, localization, tensor and cotangent titles/statements. Ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for cotangent, localization, differentials, polynomial, free algebra, 08TP, 08TQ and 08R2. No blueprint node states either proposed new lemma. The two new nodes inherit the exact ancestor and via chain required by that command.

All new Mathlib queries were run through `msearch.py` and read. The exact tool/query and returned hit counts, names and digests are recorded in the nodes and in `searches.jsonl`. Complete outputs of the first batch are in `search-results.txt`; subsequent narrow differentials queries were read directly. Two semantic phrasings were tried for both new nodes. All four services used here returned successfully. The inherited item searches are preserved separately from the appended searches of this worker.

Important candidates read: Mathlib `RingTheory/Extension/Cotangent/Basic.lean:53-65` defines a presentation differential, not the full complex in all degrees; `RingTheory/Etale/Kaehler.lean:279-284` is the localization equivalence only for H1Cotangent. `Algebra/Category/ModuleCat/Differentials/Presheaf.lean:10-35` explicitly describes a presheaf construction and further intended work, not a theorem that sheaf differentials commute with every geometric inverse image. The search also returned free-module pullback comparisons, which do not assert the differentials comparison. Thus neither new node can be marked a Mathlib leaf.

## Not duplicates

lem-trf-localization-cotangent-vanishing vs lem-trf-etale-cotangent-vanishing: both use 08R2, but the existing node is case (5), requiring an etale, finitely presented algebra. The new node is case (3), for arbitrary multiplicative sets, including Z to Q and the zero localization, with no finite-presentation hypothesis. The existing statement does not cover it.

lem-trf-localization-cotangent-vanishing vs lem-trf-affine-cotangent-comparison: the new node states the vanishing of a localization's relative complex; the item proves a comparison for an arbitrary ring map together with the sheafification, inverse-image and stalk clauses. Steps 7 and 8 use vanishing as an input to the existing transitivity triangle and actually prove the comparison.

lem-trf-topos-inverse-image-differentials vs lem-trf-affine-cotangent-comparison: the new node concerns a single underived differential sheaf for any geometric morphism. It says nothing about standard simplicial resolutions, their differential complexes, section maps or ring localization. Steps 1--5 carry those arguments.

## Review by NU

I checked B--E with the cited node statements open, rather than relying on names or on their proofs. The item agrees with the cited Stacks places: the comparisons concern the alternating standard complex, not derived sections; section maps are only claimed to give an isomorphism after sheafification; inverse image is ordinary geometric inverse image, not a ringed-space tensor pullback along an arbitrary coefficient map; and arbitrary simultaneous localizations have the stated image condition on their multiplicative subsets.

1. Step 1 uses the definition of a geometric morphism, which supplies an adjunction and finite-limit preservation. The free-algebra comparison is proved here by the displayed four Hom identifications. Restriction of the adjunction to algebra maps follows by applying naturality of the unit to the product-operation equations, as the text states. Preservation of evaluation/unit is checked on coefficients and generators. This is a universal-property computation, not a new node.

2. Step 2 uses the existing left-exact set-sheafification statement, whose own statement includes the left adjunction. This makes sheafification a geometric inverse image from the chaotic-topology presheaf topos. Standard-resolution coherence supplies both the explicit sectionwise complexes and functorial restrictions, not just independence of resolutions. The new differentials statement gives the needed comparison for the two ring sheaves; the existing ringed-topoi tensor statement applies with S equal to the inverse-image ring and coefficient map the identity. In that specialization its module pullback is simply inverse image, since S tensor over itself is the identity. The equality of the alternating-face differentials follows term by term, so the conclusion is an isomorphism of complexes. I did not claim that taking sections preserves sheaf cokernels or computes derived sections.

3. Step 3 checks the hypotheses of the existing site inverse-image statement explicitly: preimages preserve terminal opens, intersections and covering unions. Its left adjoint is the usual topological inverse image by uniqueness of the left adjoint to direct image. Its exactness on underlying abelian sheaves also gives exactness of the induced module functor; kernels and cokernels have the same underlying abelian kernels and cokernels. The new differential-sheaf comparison and existing tensor comparison again have identity coefficient map, so they identify each term before passing to the derived category. No flatness of a map of scheme structure sheaves is assumed.

4. Step 4 checks the naturality/composition clause on coefficients, formal generators and differential pure tensors. The new differentials statement explicitly supplies compatibility with the universal derivation and with compositions. Standard-resolution coherence explicitly supplies strict composition of the maps for ring squares. Equality on generators gives equality of the induced maps, not merely an unnamed isomorphism of their sources and targets.

5. Step 5 applies step 3 to the singleton inclusion. The existing topological inverse-image stalk statement covers both rings and underlying abelian groups and explicitly gives the germ formula; that formula also respects the module action. The existing module-stalk exactness statement explicitly includes general ringed spaces, so the arbitrary space T is allowed. Identifying sheaves on a singleton with their value on its sole nonempty open is elementary. Restriction to an open containing t does not change the germs, proving the compatibility clause.

6. Step 6 checks that S maps to units of C, so A to C really factors through D. The existing localization-flatness statement allows an arbitrary multiplicative subset, including one containing zero. The existing flat-tensor-exactness statement is used to preserve the cycle/boundary sequences; I did not infer tensor exactness from a definition of flatness alone. The K-flat definition then applies to C in degree zero, and the existing ordinary-module tensor-model statement supplies the derived-to-termwise comparison. Symmetry moves the K-flat degree-zero factor to the first slot of that model.

7. Step 7 uses exactly the triangle for A to B to C from the existing transitivity statement. Its statement identifies the first arrow with the standard functoriality arrow. The new vanishing statement applies to B to W-inverse-B, and the existing distinguished-zero-cone criterion gives that first arrow is invertible. Thus the nontrivial comparison is actually derived in the item.

8. Step 8 repeats this argument for A to D to C, now using vanishing for A to S-inverse-A. There is no assumption that C is flat over D and none is needed: a derived tensor of the zero object is zero, computed using its zero K-flat representative. After rotating the distinguished triangle the same zero-cone criterion applies to its second arrow. The strict functoriality assertion of the resolution-coherence statement identifies the composite with the canonical comparison, rather than merely some isomorphism between the objects.

9. Step 9 writes the tensor-associativity formula and uses the strict composition assertion already supplied by resolution coherence. This proves the requested successive-localization equality on the actual induced chain maps; no extra compatibility of connecting arrows is assumed.

For the two new statements I checked self-containment and small cases. The differential-sheaf node introduces both sites, the geometric morphism, ring sheaves, module structures and its sheafified differential construction; it contains no proof. It works for the identity morphism, sheafification from a chaotic site, maps with zero target ring, the empty topological site, and point inverse images. The localization-vanishing node introduces the multiplicative set and ring of fractions; it has no proof. For S={1} it gives L(R/R)=0; if 0 is in S the target and module category are zero; for Z to Q it covers a localization not covered by the finitely-presented etale node. No domain, Noetherian, injectivity or finite-generation assumption was used.

I corrected the initial plan to avoid new nodes for free-algebra preservation, flatness, tensor compatibility, K-flat computation and the zero-cone criterion: the first is written out as an elementary argument and the others already have suitable nodes. I also used transitivity to prove base localization instead of making a second node that merely restated half the desired comparison. All nine steps are below 2000 characters; none hides a longer inline comparison argument. No cited proof is used in place of its node statement. The quoted statements are complete, the proposed dependency closure has no path back to the item, and new-node Mathlib and duplicate searches are recorded.

# Q75: lem-per-normal-projective-compactification

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-normal-projective-compactification.json`: statement, split into ten steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-h-projective-permanence.json`: new statement-only lemma, unsplit; no Mathlib match. This is a general cancellation theorem for scheme projectivity, not a trait compactification or a clause of the item.
- `citations.json` records a verbatim statement for every node used by every item step. `searches.jsonl` is the unmodified msearch log. Neither is a live-project edit.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 checkout for the exact blueprint id, normal/projective compactification, and the trait/constant-field terminology. The smooth projective compactification in AlgebraicGeometry/Curve/Compactification.lean:188 concerns dimension-one schemes over a perfect field, not this arbitrary-dimensional mixed-characteristic trait assertion. No project declaration states the full item. The master's reference declarations are not used as completed proofs.

## WANTED

None. ILO and the Stacks sources used for this split are present locally.

## Problems and corrections

The item's statement is retained unchanged. Its empty proof did not justify the algebraic-constant base change, preservation of the entire open X, finite-projective-space projectivity, or geometric integrality. The proof now gives these arguments. In particular, the unspecified dense isomorphism open supplied by excellent normalization preparation does not suffice: Step 4 proves that normalization is an isomorphism over all of the original regular X. Likewise, properness cancellation is not enough for Step 8: the new node asserts projective-space embeddings.

The arbitrary Noetherian-base form of finite-over-projective must not be read as global H-projectivity. Step 5 uses the existing projective-bundle-to-H-projective conversion after establishing an ample line bundle on Y; S is affine. All later uses of projectivity are in the same finite-projective-space convention. The original statement includes some unused terminology conventions (smoothness, etaleness); I did not change the mathematical statement merely to tidy them.

This item has no slopmaster2 audit or declaration recorded. The blueprint ancestor is the historical purity branch of lem-per-artin-gabber-affine-curve, through the item's recorded via chain. I retain that provenance. The present algebraic-geometric tool expands ILO XVI 3.7; it does not change the fixed Fourier chapter/unit route or any target. Other-unit generic tools are declared in split_report.tool_uses.

## Not duplicates

lem-per-h-projective-permanence vs lem-weil-pbc-finite-separable-base-refinement: both cite 0C4Q, but the existing node assumes a finite separable extension of fields and smooth projective composite, and concludes smoothness and projectivity over that field. The new node is for arbitrary schemes and arbitrary separated g, with no smoothness or field hypothesis, and retains the same projective-space dimension. The existing node cannot be applied to a trait.

lem-per-h-projective-permanence vs lem-pc-projective-base-change: both mention 01WF; the existing node changes a projective morphism by a fibre product. The new node cancels a separated postcomposition for an already given morphism. The closed graph needed to compare that given morphism with a base change is its substantive additional content.

Before creating the node I searched the entire DAG for 0C4Q, projective permanence, separated/projective composites, and the proposed id; blueprint_refs searches for projective permanence, 0C4Q, and projective-and-separated found no blueprint duplicate. The specialized field node above was opened and rejected as insufficient. The existing projective-base-change node also was opened. Searches for projective closure identified only the field/curve quasi-projectivity theorem; the item's construction instead uses the existing general schematic-closure node. All other facts are existing nodes, including excellent normalization preparation, finite constants, henselian integral-algebra permanence and torsion-free flatness.

## Review by Q75

I read ILO Expose XVI 3.7, printed p.254 (PDF page 260), especially the first paragraph from the regular integral quasi-projective flat trait reduction through extension of the trait to algebraic constants and normalization of the projective closure. I read Stacks morphisms.tex, lemma-H-quasi-projective-open-H-projective (01WA), lemma-nagata-normalization (035S), lemma-normalization-normal (035Q), normalization localization, lemma-projective-permanence (0C4Q) and its closed-graph proof, and the projective-bundle/H-projective distinction. The sole new statement is exactly the same closed-graph proof applied to an embedding into P^n_B: the graph into Z times_B T is closed because g is separated, and its composition with the base change of the original embedding lands in P^n_T. Thus n is unchanged. I checked the empty source case (empty closed immersion), n=0, and g the identity. There is no finite-type hypothesis on g in that proof; I have not introduced one.

1. Step 1 uses the actual statement of flat-module-torsionfree-domain for injectivity into the nonzero generic field, not just the definition of flatness. The residue-field finite-generation node applies to a finite-type affine R-algebra and a prime over (0). The finite-algebraic-closure node then applies to F/K, with no dimension-one hypothesis. The characteristic-zero separability node supplies separability for the finite constants. These four statements were opened and give exactly those conclusions. Flatness and nonemptiness are used before treating K as a subfield of F.

2. Step 2 uses finite-type-over-Noetherian for X, projective-space properness for separatedness of the ambient projective space, and the full statement of sk-lem-nagata-sketch-closure for the quasi-compact immersion into that quasi-separated ambient scheme. It does not take any construction hidden inside a node's proof. I wrote out why the closure is integral: schematic density injects affine functions into functions on the nonempty integral open; the support is its irreducible closure. Density identifies function fields. These are elementary deductions once the closure exists. On a Noetherian space every open is quasi-compact, so the immersion satisfies the closure node's hypothesis even if X misses the special fibre.

3. Step 3 uses complete-local-excellence with the complete Noetherian DVR R, finite-type-localization-excellence with the affine rings of Y, and excellent-normalization-preparation only after Y is reduced, Noetherian and excellent. I opened all three statements and the normalization definition. In the integral case there is one normalization component and its affine rings are subrings of F. No finite-normalization theorem for an arbitrary nonexcellent base is being assumed. The source tags 07QW, 07QU, 035S and 035Q justify precisely these facts.

4. Step 4 uses regular-normal to obtain normal local domains, the function-field-sections-glue statement to turn pointwise regularity into an affine section, and the localization-of-integral-closure statement to compare the actual charts of the normalization. This proves the isomorphism above every principal chart in X. I corrected the tempting but insufficient inference from an unspecified dense isomorphism open. The normalization definition says integral closure, so once A is proved integrally closed there is no additional existence or factorization theorem hidden here. This yields the same X, not a base change of it.

5. Step 5 uses projective-ample-invertible only with an affine base S, finite-projective-bundle for the finite normalization map, projective-bundle-to-h-projective with the ample line bundle on Y, and h-projective-composition to conclude H-projectivity over S. Each cited statement was opened. This checks the global versus local projectivity issue explicitly; I did not use a finite morphism being H-projective over an arbitrary base without an ample sheaf.

6. Step 6 uses finite separable integral closure only with the normal Noetherian DVR R and the finite separable L/K from Step 1. The integral-closure-finite-extension-normal node gives a domain with fraction field L. The integral-component-henselian-permanence node explicitly has the strictly henselian conclusion, which applies since the domain has no nontrivial idempotents. The finite-over-complete-local-product node explicitly concludes completeness and locality for a domain. The Dedekind integral-closure node gives dimension one, and normal-dim1-dvr finishes. I read Stacks 09E8, 032L, 0325 and the domain case 092X; these verify the completeness, dimension and strict henselian assertions independently of any closed-point rationality assumption.

7. Step 7 uses the function-field-sections-glue node on C, now known integral and normal, and the full locally-ringed-space affine-spectrum adjunction node, which gives maps from arbitrary schemes to Spec R0, not only affine sources. The monic equations are over R inside every local ring of C, so no normality of a ring not known normal is used. Uniqueness in F checks addition and multiplication of the extended constants and compatibility with the original S-map. No extension of F occurs.

8. Step 8 uses the finite-closed-map-finite-fibres statement specifically for separatedness of the finite S0-to-S morphism, and the new H-projective-permanence statement for the factorization of the projective C-to-S composite. The latter says exactly what this step needs over traits. This also explains why the existing smooth field-only refinement node is not sufficient.

9. Step 9 uses the valuation-torsionfree-flat theorem with A=R0 and each local ring of C as an R0-module. Those local rings inject into F and R0 injects into F; torsion-freeness is therefore written out rather than inferred from normality alone. At a closed base point the base local ring is R0; at a generic point it is the field L, where flatness is the elementary vector-space fact. This checks flatness in the precise local-ring definition of def-weil-flat-morphism.

10. Step 10 checks both parts of geometric integrality. The generic fibre is a nonempty integral localization with field F and finite type over L. Characteristic zero makes L perfect; geometric-reduced-perfect applies to this entire finite-type fibre, not merely to a generic field. For irreducibility, every element algebraic over L is algebraic over K and hence already in L by its definition. The algebraically-closed-in-field node gives geometric irreducibility of Spec F and the generic-point criterion gives it for the whole fibre. Both node statements were opened and no smoothness or curve hypothesis is imported. Geometric reducedness and irreducibility give integrality after every field extension by the stated definition.

All ten non-elementary steps are below 2000 characters; none conceals a separate long comparison lemma. The new node has no proof or proof dependencies and has self-contained hypotheses and definition citations. Its actual msearch hits were read: both semantic phrasings give properness cancellation (IsProper.of_comp) rather than projective-space embeddings; the Loogle hits concern Proj sheaves, and the source grep found no projectivity-cancellation theorem. Proper.lean:124 and Normalization.lean:15-28 were read to rule out an exact Mathlib specialization. The queries and results are recorded from the log, with no invented searches. There were no unavailable services in this session.

Small cases checked for the item include X=S (identity constants and compactification), X=Spec K (the generic open in S), X=Spec L with finite separable L/K (the generic open in the integral-closure trait), and positive relative dimension with ramified constants. X is integral, so the empty-scheme case is excluded by hypothesis. None of these require extending the function field of X. The existing statement is true in each case. I also inspected dependency reachability: no cited dependency reaches the item. No live project, launcher, Lean file or compiler was modified or run.

## Unfinished

No part of the one-level split is left unfinished. The general H-projective permanence lemma is intentionally statement-only for a later stage-1 item. Its proof idea is the closed-graph argument described above, not an additional sorried Lean declaration.

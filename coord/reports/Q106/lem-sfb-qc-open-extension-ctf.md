## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-qc-open-extension-ctf.json: statement, split; no Mathlib match for the whole item. The original statement and every statement dependency are retained.
- citations.json: 30 step/node citations, with verbatim statements from the cited live nodes.
- report.md and searches.jsonl: report and actual search records. write_split.py is sandbox-only preparation, not a delivery file.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. Existing general topology, module restriction and derived projection nodes suffice.

## Attachments

None for the item. The blueprint tag search in lean/WeilConjectures found no declaration. Concept searches found AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek_obj, lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Constructible.lean:145. I read its statement and proof: it assumes TopologicalSpace.NoetherianSpace X, uses locally finitely presented module objects, and proves only the sheaf part. It does not give the present arbitrary-scheme, constant-scalar-model, fixed-Tor-interval result. The ordinary etale theorem IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact in ConstructibleSheaf/ExtensionByZero.lean has different coefficients/sites and likewise cannot attach this item. The bounded constructible definitions and Noetherian triangulated-category instance in ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean do not state the item; the latter has sorry.

## WANTED

None. The needed blueprint and Stacks texts are present locally. The assembly proof is marked agent-written because the refinement proof only calls for this extracted input and does not give its full general-scheme argument.

## Findings and changes

The item had no proof. Its statement is mathematically consistent and is unchanged. The source is the current main-20261015 refinement (2), the bounded constructible generator input to the proper-open boundary argument. I also read sk-def-sfb-dc-restricted-functors/lem-sfb-dc-open-lower-shriek-preserves.proof.md: it gives the familiar add-the-complement proof, but its unqualified local-closedness sentence alone does not ensure constructibility on a non-Noetherian scheme. The delivered argument checks retrocompactness and uses Stacks 09YD explicitly. It preserves the unit's proper-open comparison route; no SGA material is used.

I read the chapter and unit records. The existing unit record sk-prop-sf-comp-coherence still names sec-smooth-purity and the older snapshot; the item is in sec-six-functors-basics and explicitly names the current refinement proof. I kept both records unchanged and followed the item's current source. The proof serves the same bounded-constructible input of det-sf-comp-coherence-cocycle named by blueprint ancestor, not a different compactification construction.

Whole-DAG key-word and source searches, followed by blueprint_refs.py searches for extension by zero, Tor interval, constructible-image-retrocompact, qc-open-extension, and exact functor cohomology, located the relevant existing nodes. lem-sf-open-extension-zero-constant-model-constructible and lem-sfb-open-immersion-derived-tensor-projection are field-restricted and were not used. No node was created. The item's blueprint.from.place was already specific and is retained; same_as is [] because no blueprint node has its whole arbitrary-scheme statement.

The five new Mathlib queries recorded in this sandbox were run through msearch.py. I read every returned hit: condensed module categories, scheme open/gluing functors, extend-by-zero for functions, general exact-functor Ext maps, and sheaf finite-presentation predicates. None states this item or specializes to it in one line. The second LeanFinder phrasing deliberately changed from the combined theorem to exact extension and finite scalar presentations. The previous item's search entries are retained as provenance; only the new five queries are claimed as this worker's searches.

## Tool uses

split_report.tool_uses declares the existing open localization, disjoint-image vanishing, cartesian coefficients, unbounded projection formula and generic scheme/topology inputs. These are black-box facts needed for the unit's bounded constructible extension input. The field-restricted versions cannot replace them. No maintainer-owned top-level tool_uses field was written. The reduced induced complement is constructed by its existing node, not inferred from the definition of reducedness.

## Not duplicates

No new nodes. In particular no new copy of the sheaf constructibility clause or of an existing projection formula was made.

## Review by Q106

I read the item's current source det-sf-comp-coherence-refinement.proof.md, specifically (2), and the open-extension constructibility proof in the same current blueprint. I checked the sheaf exactness input in Stacks sites-modules.tex, Tag 03DJ (lemma-extension-by-zero-exact); the open restriction identities and open/closed sequence in proetale.tex, Tags 09BN (lemma-open-immersion) and 09AH (lemma-ses-associated-to-open); the Boolean operations and retrocompact-open image lemma in topology.tex, Tags 005H (lemma-constructible) and 09YD (lemma-quasi-compact-open-immersion-constructible-image); and schemes.tex, Tag 01J3 (lemma-reduced-closed-subscheme). These sources require neither a Noetherian scheme nor ell invertible for this untwisted argument. There are no new node statements to audit.

Step 1: I opened the reduced-induced-closed-subscheme statement and used clause (2), which really constructs the complementary closed scheme. I opened condensed-support-derived-localization: its invertible open extension/restriction unit is on ordinary unbounded pulled-back module categories and only requires a quasi-compact complementary open. The chosen j has exactly that hypothesis. The disjoint-vanishing node gives actual coefficient-module inverse image zero for every scheme morphism missing U, not merely the complement or geometric stalks. Exactness from module-lower-shriek and cartesian-coefficients permits degree zero of the derived unit. Thus the restriction isomorphism is linear over the intended coefficient ring.

Step 2: I checked affine-scheme-qcqs gives quasi-compact intersections of quasi-compact opens; affine opens of D are affine opens of V under the actual open subscheme identifications, so its intersection assertion applies to them. I checked both implications of quasi-separated-affine-cover-criterion and use its converse only after verifying the intersection hypothesis. Quasi-compactness of D is precisely the hypothesis on j applied to the affine V. The definition sk-def-sfb-constructible supplies the finite stratification on the now qcqs scheme D: the affine-local condition restricts from U because each affine open of D is affine in U. No assertion that intersections of affine opens are affine is used.

Step 3: I opened qcqs-scheme-spectral and spectral-open-retrocompact-iff-quasi-compact. V meets the former's qcqs assumptions by affine-scheme-qcqs; D meets the latter's quasi-compact open assumption by step 2. I then read constructible-image-retrocompact-open: it says exactly that a constructible subset of the retrocompact open stays constructible in V. The definition's Boolean clause gives V minus D. The complement scheme is genuinely supplied by the existing reduced-induced node. For the old strata the closed-in-open factorization, followed by an open inclusion, remains closed-in-open. This two-line argument supplies the immersion without hiding a composition theorem. Disjointness and coverage are unchanged, so these are actual scheme strata with their original scheme structures.

Step 4: I read the composition-isomorphism clause of sk-def-sfb-module-pushforward-pullback. It is for the actual module-object functors and every condensed ring. It supplies the iterated-restriction identification on each S_a. The model has exactly its original cover and original scalar module; there is no inference from a general local finite presentation to a constant scalar presentation. I read det-def-sfb-constructible-local-model, whose final sentence explicitly warns that the converse fails. The complement restriction is zero by the disjoint node, and P=0 is finitely presented with the empty matrix. Hence the argument meets the stronger finite constant scalar-model definition. This is elementary assembly from the stated restrictions and the definitions, rather than an uncited comparison between coefficient categories.

Step 5: I checked module-lower-shriek states exactness for every condensed coefficient ring. The cohomology-sheaves definition gives kernel modulo image in precisely this module category, including nonconstant completed coefficient rings. The proof explicitly applies exactness to kernel, image and quotient and hence obtains a natural comparison before localization. The same comparison sends quasi-isomorphisms to quasi-isomorphisms. It proves preservation of any cohomological vanishing interval, not merely boundedness. Applied to each constructible cohomology sheaf this gives all bounded-constructibility claims. This is an elementary exact-functor calculation, so no new homology-commutation node was created.

Step 6: I read condensed-support-projection-formula in full. Its open formula is j!(L tensor^L j^*T) isomorphic to j!L tensor^L T, for ordinary unbounded pulled-back modules on arbitrary schemes. It really permits L=K unbounded and T=F[0] for an arbitrary degree-zero module sheaf, and its only open/complement requirement is supplied by j and step 1. I verified cartesian-coefficients states exact pullback and imposes ell invertible only on its Tate-twist clauses; no twist is used here. Thus j^*F is a valid degree-zero Tor test on U. The Tor hypothesis gives the same interval inside J, and the explicit cohomology calculation of step 5 gives the same interval outside. No local-to-global uniform-bound lemma, K-flat preservation claim, completeness comparison or field approximation is silently used.

For the small cases I tested U empty, U=X, X empty, the zero module/complex, the zero coefficient ring, empty strata, and a scheme with a non-quasi-compact underlying space. The construction uses only affine V, and D is compact by j, so no global qcqs hypothesis leaks into these cases. For ell equal to residue characteristic the untwisted coefficient-cartesian and extension statements still apply. Non-Noetherian affine examples with quasi-compact proper open D retain constructible strata by 09YD; if j were not quasi-compact this is exactly where the proof would fail, so the hypothesis is used rather than assumed redundant. All six steps are below 1000 characters and hide no long lemma. I corrected no statement and introduced no new one. I checked the cited nodes' dependency closure has no path back to this item. The server dry run remains the authoritative mechanical check.

## Unfinished

Nothing mathematical is left to split in this one-level delivery. The existing unsplit dependencies remain their owners' items. The required server validation and push are performed after this report is written.

# Worker report

Repair of the human return of 2026-10-17: old step 7 (3356 characters) hid comparison lemmas. The item statement and Lean record are unchanged; the other original proof arguments remain, with the two necessary step-number references adjusted after insertion. All thirteen resulting steps are shorter than 2000 characters. No Lean was written and no compiler was run.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-structural-maps-commshift.json: split, old step 7 replaced by four shorter steps.
- dag/nodes/sec-trace-formula/lem-trf-proetale-proper-open-transport.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-compatible-tower-compositor-calculation.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement excerpts for each citation in the item.

## Attachments and literature

No attachment found. I searched the blueprint tag and notions in WeilConjectures, read ProEtale/Derived/LowerShriekComparison.lean, and compared the abstract CompactSupportFormalism/Composition.lean interface. The former chooses a direct-image isomorphism and does not prove its required counit-mate normalization or the geometric compositor coherence; the latter assumes a compact-support formalism and does not identify the finite etale/pro-etale comparisons. Neither states all four clauses of this item or the new lemmas. Upstream master sorry declarations are not accepted as proofs.

I read Stacks more-etale.tex, lemma-shriek-proper-and-open (0F7B), including its K-injective representative, and lemma-shriek-composition (0F7J), including the compatible triangle and its comparison diagram. I read proetale.tex lemma-jshriek-comparison (09AF); it supplies the adjointly normalized sheaf comparison, not the whole derived tower assertion. The new nodes record precisely the finite-site normalized comparisons assembled from these sources and the existing DAG; they do not claim to be verbatim Stacks theorems. The existing derived-shift and adjunction route is retained. No SGA source is used. No WANTED document.

## Searches

Read the retained searches.jsonl and their hit descriptions before continuing. New nodes use exactly the recorded commands, including two semantic phrasings each, Loogle, source grep, and LeanSearch. The proper/open queries found Scheme.Modules.restrictFunctorComp, general sheaf comparisons, and condensed functors. The compositor queries found sheafPushforwardContinuousComp and pushforwardComp. These are underived sheaf composition, not the stated normalized finite geometric maps. Mathlib's Proetale and ElladicCohomology sources define the site and coefficient objects without this compact-support formalism. Thus neither new node is a Mathlib leaf. Existing logs of the item are retained; no unrun query is represented as run.

Whole-DAG tag/word searches included 0F7B, 0F7J, proper/open interchange, site/composition, and the S_Q,T_Q expressions. Whole-blueprint searches via blueprint_refs.py included interchange, proper open, proper/open, site comparison, compact-support, and compositor. No blueprint statement gives the needed named-map transport equality. The new nodes inherit the ancestor lem-trf-global-operator-triangulated, serving its sentence about natural transformations of exact functors; they do not replace the unit's trace-additivity route.

## Review by Q70

I reread the item, sk-i-additivity and its chapter, and the current main-20261015 parent proof. Its source says that the structural maps are transformations of exact functors, which needs these shift squares; the repaired proof still proves the very same four transformations with their given shifts.

Steps 1--6 retain the shifted-resolution argument. For step 1 the constant-ring-map statement gives an isomorphism of coefficient sheaves, the two inverse-image exactness statements and comparison-pullback statement give exact module inverse images, exact-functor-derived-factorization gives the degreewise shift, and kinjective-shift plus the comparison principle justify the shifted resolution. Step 2 uses the explicit Hom bijection of termwise-adjunction-homotopy and the representing formula of pre-derived-adjoint-functors-general, not a definition standing in for the theorem. Step 3 uses ringed-topoi-derived-pushforward-composition's normalized arrow g_*j; the cited extension nodes state exactness, adjunction, composition and the termwise site comparison. Step 4 uses exactly the K-injective normalization in proper-open-interchange-coherence. Step 5 uses the canonical-mate statement and pullback comparison to identify b_u, the formal comp/whisker leaf to combine its shift squares, and class-compact-support-comparison for invertibility. Step 6 uses proper-open-comparison-site-normalization's displayed equality for the actual refinement arrow, the definition's theta formula and compactification-coherence for comparisons through refinements. Its inverse equation and witness cancellation are written out.

New step 7 cites the compatible-compactification triangle for b,q,j and the etale comparison theorem for its actual three-arrow tower normalization. The formula is written explicitly; its factors were handled in steps 3--4. New step 8 cites the new transport node for the general proper/open square, including the source and target of S_Q and T_Q. I corrected the draft's reversed S_Q orientation: S_Q goes from H(i_!Rr_*) to i_!Rr_*H, so the formula uses S_Q inverse. This is distinct from the existing refinement-only normalization. Step 9 uses the second new node for the hidden calculation moving the site comparisons through the tower, then comp/whisker and inverse shift calculus; no proof of another node is used as a statement. Step 10 gives the witness conjugation argument and uses composition choice-independence and compactification coherence for the original choices. The new nodes assert comparison identities, not the item's shift-compatibility clause.

Original steps 8--10 are now 11--13. The adjoint-shift uniqueness leaf supplies the specified etale right-adjoint shift and its counit square in step 11. Step 12 uses constructible-origin and tor-amplitude reflection for its domain, site comparison for the unit isomorphism, and the finite-adjoint comparisons and explicit adjunction-transfer counit formula to identify e with the required counit. Its triangle identity is written out. Step 13 checks the Noetherian and qcqs assumptions using the finite-type and qcqs lemmas, and the stated preservation/adjunction domains using the compact-support composition and finite-adjoint statements. All citations were opened and read; citations.json quotes their statements verbatim.

For both new nodes I checked B1--B9: complete objects and hypotheses, statement-only with empty proof/dependency list, real source labels, definition dependencies for sites and coefficients, and explicit blueprint ancestry. The transport statement is restricted to D^+ finite constant coefficients; the tower statement restricts to finite-type schemes over a field with ell invertible. Proper maps are qcqs, and their ambient schemes are Noetherian. I checked empty schemes, zero input, identity opens, identity proper maps, and n=1: the comparisons reduce to identities or the unique zero map and the formulas are well typed. No cancellation treats evaluation as faithful, and nothing extends to arbitrary pro-etale inputs. C1/C4 were checked by reading the cited statements, C6 by the server DAG check, and D1/D2 by comparing the new comparison equations with the item's four shift assertions. This repair extracts both hidden arguments rather than only adding paragraph breaks. The retained long steps have length at most 1825 characters and each carries its original resolution or adjunction calculation.

## Not duplicates

lem-trf-proetale-proper-open-transport vs lem-pur-open-projection-site-transport: the existing node compares the open tensor projection and its adjunction inverse across sites for F=L[m] with L finite locally free and arbitrary bounded-below G; the new node compares a proper/open interchange in a square with two proper vertical maps, using the proper direct-image mates b_r,b_p and S_Q,T_Q. Neither a tensor projection nor a locally free tensor factor occurs in the new statement, and the existing statement supplies no proper/open interchange.

lem-trf-compatible-tower-compositor-calculation vs lem-cbc-complete-proetale-composition-pasting-coherence: the new node states the finite étale/pro-étale site-comparison conjugation formula for the three compact-support compositors on a compatible tower; the existing strict-tower node states tower-level compositor, refinement, and base-change coherence for normalized strict-tower operations and has no site-comparison maps $c_f,c_g,c_{gf}$.

lem-trf-proetale-proper-open-transport vs lem-sf-open-comparison-tensor-normalization: the new node states transport of the proper/open interchange through site comparison, involving proper direct-image mates and $S_Q,T_Q$; the existing node states tensor compatibility of the open-extension comparison and contains no proper/open interchange.

lem-trf-proetale-proper-open-transport vs lem-sf-open-comparison-unit-normalization: the new node states transport of the proper/open interchange through site comparison, involving proper direct-image mates and $S_Q,T_Q$; the existing node states only the adjunction-unit normalization of the open-extension comparison and contains no proper/open interchange.

lem-trf-compatible-tower-compositor-calculation vs lem-sf-composition-projection-mate: the new node states the site-comparison conjugation formula $\alpha^p=c_{gf}H(\alpha^e)c_g^{-1}P_g(c_f^{-1})$ for finite étale/pro-étale compact-support compositors; the existing node states a projection-formula mate identity for tensor inputs and does not compare étale and pro-étale compositors.

lem-trf-compatible-tower-compositor-calculation vs lem-trf-compact-composition-proper-square-normalization: the new node compares the finite étale and pro-étale compositors through the three site-comparison maps; the existing node normalizes a compact-support composition transformation in a proper square on one pro-étale site and has no site-comparison conjugation.

lem-trf-proetale-proper-open-transport vs lem-sf-composition-projection-mate: the new node transports a proper/open interchange across the étale/pro-étale site comparison using $S_Q,T_Q$; the existing node is a projection-formula mate identity for compact-support composition and contains no site-comparison transport.

lem-trf-proetale-proper-open-transport vs lem-sf-proper-open-projection-mate: the new node gives the cross-site conjugation formula for the proper/open interchange; the existing node gives a tensor projection identity for a single pro-étale proper/open square and does not involve étale/pro-étale comparison maps.
lem-trf-compatible-tower-compositor-calculation vs lem-weil-pbc-compatible-compactification-triangle: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Compatible geometric compactifications of a composable pair” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-weil-pbc-etale-compact-support-open-closed-triangle: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Open-closed localization for relative etale compact support” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-weil-pbc-etale-lisse-open-relative-line-constructibility: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Lisse coefficients on an open relative affine line over an integer model” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-weil-pbc-etale-shriek-qcqs-composition: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Composition of qcqs etale compact-support candidates” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-weil-pbc-etale-shriek-relative-mayer-vietoris: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Relative Mayer Vietoris for qcqs etale compact support” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs fix-prop-projection-formula: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Compact-support projection formula at all coefficient stages” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-sf-compact-coefficient-composition: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Finite coefficient comparison respects compact-support composition” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-sf-kunneth-coherence: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Coherence of the relative product” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-sf-unbounded-compact-support-proper-composition: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Unbounded ordinary etale compact supports composed with a proper direct image” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-weil-delta-proper-pushforward: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “The double-dual morphism under a proper push-forward” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs thm-weil-etale-geometric-biduality: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Finite-stage etale Verdier biduality” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-sfb-quasifinite-compact-support-exact: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Quasi-finite compact support is exact and agrees with compactifications” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs sk-lem-geo-affine-local: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Affine space and étale localization” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs cor-amb-affine-space-adjunction: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Affine-space ambient adjunction” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs fix-lem-exchanges: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Exchange functoriality: naturality, identities, and pasting” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-amb-etale-adjoint-locality: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Etale localization of the ambient adjoint” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-amb-etale-compact-comparisons: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “The etale compact-support comparisons” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-amb-unbounded-compact-support-comparisons: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Unbounded ordinary etale compact-support comparisons” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-cbc-compactifiable-compatible-tower: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Compatible compactification towers with a supplied compactification of the composite” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-pur-projection-purity-agreement: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Agreement with the affine-line route on affine space” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-pur-system-level-projection-formula-coherence: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Strict-system projection formula composition coherence” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-sp-coefficient-tower-shriek-calculus: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Compact-support calculus on varying coefficient towers” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-sp-et-proet-coefficient-compatibility: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Finite coefficient compact-support comparison respects site transport, refinement and composition” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs prop-asd-smooth-base-change: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Arbitrary base change for smooth ambient duality” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs thm-cbc-finite-torsion: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Compact-support base change at finite coefficients” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs thm-sf-comp-composition: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “The composition law for $Rf_!$” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-trf-filtered-derived-operation-lifts: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Filtered lifts of sheaf-derived operations and their canonical adjunction maps” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-trf-finite-horizontal-shriek-mate: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Compact-support exchange as a mate along finite horizontal arrows” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-trf-finite-structural-maps-commshift: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “Canonical finite-coefficient structural maps commute with shifts” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-compatible-tower-compositor-calculation vs lem-trf-global-operator-triangulated: new node states the equality intertwining the named finite-site compact-support compositors with c_f,c_g,c_gf; existing “The global operator is triangulated in the coefficient” supplies geometry, etale/tower comparison or a different compatibility, not this three-comparison finite-site equality.

lem-trf-proetale-proper-open-transport vs det-pe-constructible-comparison-classical: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Constructible pro-étale sheaves are classical” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-weil-pbc-etale-open-proper-interchange: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Open extension by zero and proper derived pushforward interchange” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-weil-pbc-etale-shriek-qcqs-composition: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Composition of qcqs etale compact-support candidates” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-weil-pbc-finite-ring-constructible-sheaf-origin: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Constructible sheaves over a finite ring have etale origin” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs fix-prop-projection-formula: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Compact-support projection formula at all coefficient stages” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-compact-coefficient-composition: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Finite coefficient comparison respects compact-support composition” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-etale-smooth-stratified-ctf: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Smooth-stratum finite-Tor devissage over an arbitrary algebraically closed field” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-unbounded-compact-support-proper-composition: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Unbounded ordinary etale compact supports composed with a proper direct image” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-weil-delta-proper-pushforward: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “The double-dual morphism under a proper push-forward” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs thm-weil-etale-geometric-biduality: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Finite-stage etale Verdier biduality” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs det-ctf-finite-comparison-localizing: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “$\nu_X^*$ identifies the localizing closures” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs det-proper-heart-bound-torsion: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “The torsion bound over a weakly contractible base” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs det-uniform-constructible-ext-torsion: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “The torsion stratum bound” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sfb-quasifinite-compact-support-exact: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Quasi-finite compact support is exact and agrees with compactifications” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs sk-lem-uniform-constructible-ext: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Uniform Ext bound” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs def-cbc-finite-constant-coefficient-transport: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Normalized finite scalar and etale-origin transport to constant coefficient modules” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs def-cbc-strict-constant-tower-operations: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Strict constant-coefficient towers and normalized inverse/direct-image operations” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs def-cbc-strict-tower-open-extension: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Normalized exact open extension on strict constant-coefficient towers” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs def-cbc-strict-tower-proper-open-arrows: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Unit-normalized proper and open arrows on strict towers” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs fix-lem-exchanges: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Exchange functoriality: naturality, identities, and pasting” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-amb-etale-adjoint-locality: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Etale localization of the ambient adjoint” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-amb-etale-compact-comparisons: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “The etale compact-support comparisons” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-amb-unbounded-compact-support-comparisons: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Unbounded ordinary etale compact-support comparisons” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-amb-unbounded-proper-open-interchange: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Unbounded torsion-coefficient proper/open interchange with its canonical maps” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-cbc-etale-local-compact-support-extension: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Zariski-local extension of etale compact-support functors and exchange morphisms” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-cbc-open-extended-injective-proper-acyclic: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Open extension of an injective sheaf is acyclic for the proper right-hand map” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-cbc-proetale-extension-zero-comparison: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Comparison of extension by zero with the site morphism” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-cbc-proper-open-interchange-coherence: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Proper/open interchange and its base-change and composition equations” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-cbc-strict-tower-proper-open-calculus: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Normalized proper/open calculus on strict pro-etale towers” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-exc-proetale-cartesian-open-injective-acyclic: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Proper acyclicity of injectives extended from an arbitrary Cartesian open” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-exc-proetale-proper-open-sheaf-comparison: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Proper/open comparison for pro-etale module sheaves” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-pur-compact-support-integral-coefficient-comparison: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Integral compact support under finite free coefficient extension” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-pur-projection-purity-agreement: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Agreement with the affine-line route on affine space” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-pur-system-level-projection-formula-coherence: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Strict-system projection formula composition coherence” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-pur-vector-integration-site-comparison: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Finite-level site comparison of normalized vector-bundle integration” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-class-compact-support-comparison: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “On the coefficient class the compact-support functor is computed on the étale site” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-constructible-partition-local-closed-stratum: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Locally, a stratum of a constructible partition is closed with quasi-compact complement” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-proetale-constructible-origin: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Constructible pro-étale coefficients are of étale origin” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-proetale-open-closed-sequence: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Open-closed short exact sequence on the pro-etale site” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sf-proper-open-comparison-site-normalization: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Normalization of the proper/open comparison under the site comparison” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sp-coefficient-tower-shriek-calculus: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Compact-support calculus on varying coefficient towers” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sp-et-proet-coefficient-compatibility: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Finite coefficient compact-support comparison respects site transport, refinement and composition” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sp-proetale-open-injective-proper-acyclic: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Open-extended injectives are proper-direct-image acyclic on pro-etale sites” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sp-proper-open-derived-support: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Proper pro-etale direct image preserves extension-by-zero support” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-sp-proper-open-tower-comparison: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Open-adjunction normalization of proper/open interchange on strict coefficient towers” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-weil-finite-compact-projection-formula: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Finite-coefficient compact-support projection formula” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-weil-pbc-proper-open-comparison-proetale: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Proper-open comparison for complexes from the etale site” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs prop-compactification-coherence-detailed: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Compactification coherence” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs prop-exc-base-change-proper: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Base change for a proper morphism, against an open immersion” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs thm-cbc-complete-proetale: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Complete pro-etale compact-support base change” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs thm-sf-comp-composition: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “The composition law for $Rf_!$” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-trf-filtered-derived-operation-lifts: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Filtered lifts of sheaf-derived operations and their canonical adjunction maps” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-trf-finite-horizontal-shriek-mate: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Compact-support exchange as a mate along finite horizontal arrows” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-trf-finite-structural-maps-commshift: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “Canonical finite-coefficient structural maps commute with shifts” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-proetale-proper-open-transport vs lem-trf-global-operator-triangulated: new node fixes the general finite etale/pro-etale proper/open transport identity on D^+; existing “The global operator is triangulated in the coefficient” does not state that general site-transport normalization (the refinement-only case, when applicable, is explicitly reused).

lem-trf-compatible-tower-compositor-calculation vs lem-pur-system-compactification-pf-substitution: the existing node proves tensor projection-formula compatibility with proper refinements in the derived category of strict semilinear coefficient systems; the new node compares the etale and pro-etale composition isomorphisms for a pair of geometric morphisms at one finite coefficient ring, through c_f,c_g,c_gf. The existing statement has neither site comparisons nor that compositor identity.

lem-trf-proetale-proper-open-transport vs lem-trf-open-base-change-site-transport: the existing node transports the open base-change map q^*j_! to j'_!r^* in a Cartesian square; the new node transports i_!Rr_* to Rp_*k_! for a commutative proper/open square, including non-Cartesian proper-refinement squares. The maps have different domains and targets.

lem-trf-proetale-proper-open-transport vs lem-trf-proper-open-site-transport: the existing statement assumes a Cartesian square and finite vertical maps and identifies the geometric adjunction mate. The new statement concerns the transported proper/open arrow in the compact-support construction for arbitrary proper vertical maps and also identifies its non-Cartesian proper-refinement specialization. The tower's proper maps need not be finite; its needed assertion is not a specialization of the existing finite-map statement.

## Continuation audit (2026-10-17)

The first dry run after resuming the retained repair rejected only a missing same-tag comparison with lem-pur-open-projection-site-transport (09AF). I opened its full statement: it transports the open tensor projection and inverse for a shifted finite locally free factor, without proper direct images. I added the precise distinction above. A comparison against the current repository confirms that only proof, proof_deps, status and split_report differ on the item; its statement and Lean record are identical. I also rechecked all 46 step citations against the current cited statements; each excerpt occurs verbatim. All thirteen non-elementary steps remain below 2000 characters (maximum 1825). The original step 7 route and its explicit tower map are retained, while its two hidden comparison arguments are the two new statement-only nodes.

The next resumed dry run detected three newer same-tag nodes. I read all three complete statements. The strict-system tensor/refinement lemma does not compare sites or geometric compositors; the open base-change transport has pullbacks in place of proper direct images; the proper/open transport assumes finite vertical maps and a Cartesian square. Neither our proper tower nor the non-Cartesian refinement specialization follows from those statements. Their precise distinctions are recorded under Not duplicates. The retained search log was read in full; the recorded queries and hit names agree with the two helper records, so no search was repeated. The current repository still marks the returned item unsplit. Only the four previously reported item fields differ, and the statement and Lean record remain unchanged.

## Remaining work

No unresolved point in the return. The two statement-only lemmas join stage 1 for later splitting and stage 2 in the normal process. Required delivery dry run and push follow this report.

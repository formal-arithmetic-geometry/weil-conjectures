# Worker report

## 1. Files written

All node files are under `dag/nodes/sec-purity-real-sheaves/` in the assigned sandbox.

- `lem-a1-finite-flat-affine-relation-quotient.json`: item, statement retained, complete 13-step split of Stacks 03BM.
- `lem-a1-affine-groupoid-integral-invariants.json`: statement, unsplit; 03BJ, no Mathlib match for a general affine groupoid.
- `lem-a1-affine-groupoid-orbit-fibres.json`: statement, unsplit; 03BL, no Mathlib match for a general affine groupoid.
- `lem-a1-affine-groupoid-basis-descent.json`: statement, unsplit; finite nonempty basis case of 03C8, no Mathlib match.
- `lem-a1-semilocal-submodule-basis.json`: statement, unsplit; 03C1 with the finite locally free constant-rank version supplied by 02M9, no Mathlib match for the prescribed-submodule conclusion.
- `lem-a1-finite-monomorphism-closed-immersion.json`: statement, Mathlib leaf; `AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`, `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:124` (reverse implication).

`citations.json` contains one verbatim statement quotation per use per step. `searches.jsonl` and the full outputs in `research/` retain the actual msearch queries and results. The search script, drafting script and review notes are sandbox artifacts, not extra project edits.

## 2. Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the item id and finite-flat relation/quotient terms, then for groupoid invariants/bases, semilocal bases and finite monomorphisms. There is no declaration proving every clause of the item. The Mathlib finite-monomorphism theorem is a leaf, not a project attachment.

## 3. WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## 4. Findings and changes

The item's statement is true and agrees with 03BM. No statement correction was necessary. Its additional surjectivity and unique arbitrary-S structure follow from 03BL and fpqc descent of morphisms, respectively. The proof does not assume S affine, separated or Noetherian. In particular I prove finiteness of the comparison into the affine product over Spec C using module generators, rather than making an unsupported assertion about a product over arbitrary S.

The original item had no proof. I followed 03BM's basis argument and included the descent details: flat base change of the invariant equalizer, infinite residue field extension at every prime, semilocality, a basis inside target pullbacks, and descent of the relation algebra comparison and finite presentation. The degree argument of 03BI is carried by the existing degree-locally-constant and fibre-degree-base-change nodes. It is not a new node. Rather than decompose the original rings into all ranks, I observe over the local invariant base that all maximal points are in one orbit, hence all ranks agree; local constancy extends this to every prime. This is the same source rank argument below the unit, not a replacement of a unit step.

I initially considered an affine finite-locally-free/module-criterion node but did not create it: the existing finite-pushforward-locally-free, standard-free-cover and finite-free-algebra-spectrum statements already supply its needed directions. I also did not create a node for invariants commuting with flat base change: the exact kernel calculation is step 4 using the actual flat-tensor-exact theorem, not merely the definition of flatness.

The historical `blueprint.from` points to the affine quotient invoked in the inherited 03XX representability split below `lem-a1-affine-hc0`. The current main-20261015 hc0 proof is the direct compact-support argument and contains no finite quotient. I retain the existing ancestry and exact historical place; none of the chapter/unit records are changed. All other-unit tools are declared in `split_report.tool_uses` with their roles. No SGA source is used.

## 5. What remains

The item is completely split. The four new unsplit statements are intentionally statement-only; their own proofs are subsequent stage-1 items. No Lean was written and no compiler, Lake, local DAG checker or git command was run in the shared repository.

## Not duplicates

The tag search over every DAG node found no existing node containing any of the five new nodes' source tags 03BJ, 03BL, 03C8, 03C1, 02M9 or 03BB. Hence there are no same-tag new/existing pairs to list.

I also searched all blueprint nodes using `tools/blueprint_refs.py search` for the individual tags, invariants, basis, semilocal, finite monomorphism and groupoid. General group-action invariant-ring results are not general affine groupoid results; a finite locally free groupoid can have non-etale infinitesimal arrows. The existing degree-locally-constant result was reused rather than duplicated. The existing semilocal-Dedekind statements concern normalization/conductors and do not assert selection of a module basis from a generating submodule. Existing finite-pushforward/module standard-cover results were reused instead of creating the initially considered affine criterion.

The basis-descent lemma is not a restatement of the item. It takes a specified basis of B consisting of target pullbacks, does not assume an equivalence relation or finite locally free source and target, and makes no assertion about sheaf representability or S-descent. Steps 2–9 of the item do the substantive work of producing that basis. Integrality and the topological orbit statement likewise supply intermediate facts for semilocality, not an affine quotient conclusion.

## Review by NY

I read `groupoids.tex` from the invariant-ring setup through 03BM, including the proofs of 03BJ, 03BK, 03BL, 03BI and 03C8. For the semilocal basis statement I read `algebra.tex`, labels `lemma-locally-free-semi-local-free` (02M9) and `lemma-semi-local-module-basis-in-submodule` (03C1). The second assumes a finite free module; the first supplies exactly that freeness from the constant-rank finite locally free hypothesis used in the delivered statement. I read `morphisms.tex` label `lemma-finite-monomorphism-closed` (03BB) and the entire matching Mathlib proof at Finite.lean:124–138. It assumes precisely finite and categorical mono, with arbitrary schemes.

I opened every statement listed by every step's uses; the quotes in citations.json are copied verbatim from those statements. The application audit is as follows.

1. The affine fibre-product theorem gives exactly Spec of the tensor product with its two maps. Yoneda full faithfulness, now explicitly cited, gives morphisms for the natural groupoid operations, not an unexplained appeal to representability. The empty A case is treated before choosing primes or positive ranks.
2. The new finite-monomorphism leaf applies to the comparison into U times_M U. Its finiteness follows from the same finite A-module generating list, and mono follows from the original functorial relation assumption. The closed-immersion definition explicitly includes the affine surjective-ring-map characterization used here.
3. The two new groupoid statements give exactly integrality and surjective orbit fibres; they do not presume a scheme quotient. All their groupoid hypotheses were built in step 1.
4. The cited flat tensor theorem actually preserves the kernel sequence including its initial zero. Its application identifies D with the invariant equalizer. The groupoid operations base change over M because invariants equalize the two structure maps. This small exactness computation needs no new lemma.
5. The existing 03C3 statement allows any extension of the residue field, so the rational function field is permitted. The two cited flatness statements provide flat localization and faithful flatness for the local flat map. No faithful flatness of C to C_p itself is claimed.
6. The finite-pushforward statement has all three required hypotheses (finite, flat, lfp). On an affine target its local free bases are ordinary module bases on principal opens. These bases explicitly tensor to the pulled-back cover, and the finite-free-algebra-spectrum theorem supplies the geometric property. This does not rely on the weaker Noetherian-only finite-flat-affine-basis node.
7. Integrality comes from 03BJ after step 4. The two existing maximal-ideal lemmas provide both directions needed to identify the closed fibre with the maximal ideals. The orbit lemma then puts every maximal point in the image of one finite source fibre, proving semilocality. This is why a mere definition of integrality would not have sufficed.
8. The existing degree-locally-constant theorem and fibre-degree-base-change theorem supply exactly the two facts used. The isomorphism of source fibres is composition with an arrow, inverted by composition with its inverse; these are groupoid identities. Values are equal on the single maximal orbit and on specialization chains. The identity section rules out rank zero over this nonempty local reduction.
9. All hypotheses of the semilocal selection statement were checked: local D with infinite residue field; semilocal A; mA in the Jacobson radical; constant positive rank B; and D-submodule tau(A) spanning B. The last condition is exactly the already proved surjectivity of phi. The resulting basis has precisely the form required by the basis-descent statement. Its map uses sigma on the first tensor factor throughout.
10. The faithful-flat definition really detects exactness, and the flatness descent statement concerns modules, not only algebra maps. Localization exactness permits kernel/cokernel localization. The annihilator argument proves the local zero test in the text and the injection criterion for flatness globally; no hidden local-freeness descent is assumed here.
11. Surjective spectra plus already established flatness gives faithful flatness using the cited theorem. The finite standard-open free cover of B gives its finite presentation using the cited module theorem. The descent theorem is applied to the C-module A and C to A, not to the separate auxiliary local extensions. This avoids incorrectly inferring global finite presentation from unrelated primewise presentations.
12. Now finite presentation supplies finite generation, so the finite-flat-over-a-local-ring theorem is applicable. The local-freeness-to-projectivity criterion has exactly the finite presentation hypothesis we just proved. Its standard-free-cover successor and finite-free-spectrum statement return to the geometric finite locally free conclusion. The affine product theorem identifies the original projections.
13. A finite locally free surjection is an fppf and fpqc cover, as the two cited definitions require. Local bases and nonzero finite fibres verify its pullbacks. The representable-descent statement applies to maps into any scheme S, so produces the unique S-structure and also proves the required representable sheaf property. Local lifting and equality of quotient classes are verified explicitly before applying the cited local-bijection sheafification criterion. The site's chosen small universe is the size convention built into the existing fppf-site definition, matching that criterion.

For B1–B9, all four non-leaf children have empty proof and proof_deps and standalone statements introducing their schemes, rings and maps; groupoid and semilocal meanings are written inline. Tags were resolved against `tags/tags`. No child contains a proof sketch. Each child has the exact inherited blueprint ancestor and full via list, a specific supporting source place, an empty same_as after searching, and recorded real queries of all four required kinds. I read the actual hits. The invariant-ring hits assume a finite constant group action; the semilocal hit `Module.nonempty_basis_of_flat_of_finrank_eq` gives an arbitrary basis, not a basis lying in N; the other local basis hits assume E local. These are not matches. Service results in this batch were available. The only full match is the finite-mono leaf, with its actual file and line recorded.

Small cases checked: A=B=0 gives the empty quotient with its unique map to S; the identity groupoid has C=A and rank one; a disjoint union of different degrees is handled locally rather than assuming global constant rank. Infinitesimal groupoids are allowed: for example alpha_p translation of affine space in characteristic p has invariants k[x^p], so constant finite group invariance lemmas do not suffice. The basis lemma's strong hypothesis excludes nonfree infinitesimal stabilizers and does not falsely force arbitrary groupoid quotients to be torsors. For the semilocal selector, the infinite-field hypothesis is essential: over F_2, the even-parity subspace of F_2^3 generates the rank-one module over E=F_2^3 but contains no unit of E, so it contains no E-basis. Our delivered hypothesis excludes that counterexample. No Noetherianity, reducedness or characteristic restriction was added.

I corrected a potential C1 omission by adding the existing Yoneda full-faithfulness node explicitly; I also removed the unnecessary rank-strata and affine-criterion node proposals before writing any such node. All proof steps are below 2000 characters, and no step hides a separate unrecorded comparison or identification. The only new comparison theorem is the stated 03C8 basis-descent dependency.

Final repair audit: the first dry run found two shape errors, which are corrected: the finite-mono leaf now has `mathlib_match.line: 124`, and every combined definition citation in a new statement was separated into individual bracketed ids. I additionally checked the fppf-to-fpqc inference rather than leaving it implicit. Step 13 now cites `lem-weil-pbc-flat-lfp-open`, whose whole statement says a flat locally finitely presented morphism is open universally, and writes out the finite affine-piece refinement over each quasi-compact affine target. Thus the existing fpqc representable-descent node really applies to every fppf covering. The new citation `lem-trf-fppf-covering-base-change` states precisely stability of an arbitrary fppf family under arbitrary pullback and supplies the lifting cover H times_M U. Both statements were opened and included verbatim in citations.json. Step 5 now applies flat tensor exactness in two successive stages, avoiding an unstated composition-of-flat-maps appeal.

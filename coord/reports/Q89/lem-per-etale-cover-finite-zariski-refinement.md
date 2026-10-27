## Worker report

Files written:
- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-cover-finite-zariski-refinement.json: split the existing statement, with no change to its statement or eight statement dependencies.
- citations.json: exact statement quotations for all seventeen proof-step citations.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale (lean/WeilConjectures/AlgebraicGeometry/EtaleFiniteRefinement.lean:70) is already attached to lemma-weil-pbc-finite-refinement-etale-cover. Its statement gives the main finite refinement, but does not state the present item's reduced source in alt/S or its individual family indices. It is reused, not claimed as an exact attachment of this item. No declaration with this item's blueprint tag was found. Searches of the project for finite-surjective etale refinements found that theorem and its applications, not an exact theorem with the present clauses.

WANTED: none.

What was wrong: the existing item had no proof. No false statement or source error was found. The statement is retained verbatim, including arbitrary I, the empty convention, and absence of normality or degree restrictions. An important distinction is that the finite refinement Y need not itself be reduced or an alteration object: it must be replaced by its reduced dominant part, not merely assumed to have all components dominant. The finite-type assumptions on the individual U_i cause no difficulty, but the assembled coproduct need not be finite type; the quoted 09Z0 node does not require its source to be finite type.

Unfinished: none at stage 1. There is no Lean change or compilation.

## Sources and searches

Read ILO, Expose II, pp.23--26, Definitions 1.1.2, 1.1.8--1.1.9, 1.2.2 and paragraphs 1.2.5--1.2.9; and pp.28--29, Proposition 3.1.1, 3.1.2 and the ordinary-case beginning of 3.2.1. The ordinary parameter 1 case has no restriction on the degrees. The finite-refinement engine was read in literature/stacks-project/more-morphisms.tex, Tag 09Z0, label lemma-there-is-a-scheme-integral-over, statement and proof. The implementation was read in lean/WeilConjectures/AlgebraicGeometry/EtaleFiniteRefinement.lean:49--104. The existing node's audit reports its main declaration closed. The result is a generic geometry tool below the fixed unit route, not a replacement of a unit step.

Also read Stacks Properties Tag 01OY (label lemma-locally-Noetherian-quasi-separated), Morphisms Tag 01T6 (label lemma-finite-type-noetherian), and Algebra Tag 00FN (label lemma-Noetherian-permanence), and the statement of every dependency used in the five proof steps. The source descriptions and precise definition nodes in the DAG supply the finite-map, closed-immersion and residue conventions.

Read the current latest blueprint ancestor lem-per-artin-gabber-affine-curve and the current unit _section.md, together with the chapter and unit records. The alteration input is below the ancestor's duality branch through the recorded long provenance chain; the latest ancestor itself contains no alteration-cover statement. No chapter or unit record is changed.

Seven new Mathlib searches ran through msearch.py, and their exact query texts and actual hits are appended to the inherited item searches. LeanFinder was tried with two phrasings; LeanSearch and corrected Loogle both responded. Source grep used two refinement patterns and a further candidate-location pattern, all in AlgebraicGeometry. The Loogle candidate AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt was read at Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:49--54: it produces an etale neighbourhood with one finite clopen piece, not the finite-surjective refinement sought. Etale-site, Zariski-topology inclusion, general cover-refinement and locality hits do not imply the full item in one line. No new unsplit or Mathlib nodes were created.

Whole-DAG and blueprint searches for finite refinement, finite surjective, etale covering, reduced closed, dominant components and dominant part found the existing main refinement, dominant-part and coproduct nodes. All were opened. No blueprint node states this exact reduced family refinement as a separate theorem. The general 09Z0 node is used instead of duplicated. The integral-base lem-per-finite-generic-dominant-parts was opened but is not used on the possibly reducible S; the general-base lem-per-dominant-part-coreflection is the correct citation.

## Not duplicates

No new nodes. The existing 09Z0 single-morphism refinement supplies the nontrivial engine. The item additionally imposes the reduced dominant source and maps to specified individual family members; those are proved by the assembly steps.

## Review by Q89

I checked the node files and the sources against delivery-errors B--E, including the statement of each cited node. There are no new nodes to hide a proof, restate a clause, duplicate a source tag, or omit a Mathlib search. All five steps introduce the objects they use and cite statements rather than constructions buried in another node's proof. No step exceeds 2000 characters.

Step 1 uses the locally-Noetherian quasi-separatedness statement exactly for S. The finite affine cover in the hypothesis supplies both local Noetherianity and quasi-compactness. The coproduct statement supplies an actual scheme with disjoint open summands and the induced map. Etale locality on the source applies to exactly those open summands, whose restrictions are the given u_i. Joint surjectivity is checked pointwise. In particular I is allowed to be infinite.

Step 2 uses every clause of the already closed 09Z0 node: the only hypotheses are that u is surjective and etale and S is qcqs, all established in step 1; the output is a finite surjective r with a finite open cover and actual S-morphisms. The statement does not assume separatedness, affineness or finite type of U. I did not invoke an unproved argument from the node's proof.

Step 3 uses finite type over a Noetherian base to obtain Noetherianity, with finite type verified by finite module generators. The general-base dominant-part statement supplies a reduced closed subscheme with the specified dominant components and its proper-surjective preservation clause. The finite-map closedness statement explicitly says finite maps are proper, so this clause applies to r. The coreflection applied to the reduced source S and its identity gives a right inverse to the closed immersion S_md→S; its monomorphism property then proves this is an isomorphism. This explicitly identifies the target dominant part with S. The closed-immersion affine quotient statement gives B/J on each finite affine chart, and the images of finitely many R-module generators prove finiteness of the composite. This is a direct elementary module calculation, not an unquoted finite-composition lemma. Reapplying finite-type Noetherianity proves F is Noetherian. No hypothesis of irreducibility of S is silently used.

Step 4 checks the remaining alt/S condition. Finite-map base change applies to the actual residue-field fibre. The scheme-fibre definition provides the point above x, and the fibre-product residue-field statement identifies its residue field with κ(x), since κ(x)⊗κ(s)κ(s)=κ(x). The finite-over-field node gives the fibre’s affine finite-dimensional algebra. Quotienting by the point's prime is a finite-dimensional domain, and the quoted field theorem makes it a field, so its fraction field (the point's residue field) is a finite extension of the base residue field. The ordinary alteration definition explicitly gives exactly reducedness, finite type, dominant generic points and finite residue extensions as its object conditions. There is no need for a separability or prime-to-degree condition.

Step 5 pulls back opens and restricts morphisms, using only the coproduct's open-summand statement and the equalities already constructed. For a point in an O_a its image lies in some U_i, so the inverse-image opens cover F. Quasi-compactness then gives a finite subcover, with no gluing of the maps required and no need to force a whole W_a to land in a single summand. This is an elementary use of definitions, correctly marked elementary.

Edge cases checked: S empty (empty finite scheme and empty cover); S=Spec k (finite residue extensions, including inseparable finite extensions allowed); reducible reduced S (use the dominant part over all generic points, not an integral-only theorem); an infinite redundant family (assemble it and take a finite subcover only at the end); nonseparated etale source (09Z0 allows it); Y with nilpotents or vertical components (dominant reduction removes them). I corrected the initial temptation to use the integral-base dominant-part lemma and instead used the existing general-base statement. The item statement required no correction or STATEMENT-DISPUTED marker.

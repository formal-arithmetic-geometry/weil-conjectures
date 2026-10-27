# Q99 stage-1 delivery: lem-trf-section-comma-bar-contraction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-section-comma-bar-contraction.json: statement split, existing statement retained verbatim; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for each step's citation.
- report.md: this report. Search outputs and searches.jsonl retain the searches actually run.

No new DAG nodes and no Mathlib leaves were created. The supporting initial-object contraction is a short calculation with the stated faces, not a new lemma node.

## Attachments

None. Searched the live project WeilConjectures tree for the blueprint id, bar-complex terminology, comma categories, prism homotopy and vertical sections. The representation bar complex and Kan-extension comma-category declarations do not state this coefficient-sensitive augmented chain homotopy equivalence. No compiler was run; no sorry declaration was treated as a finished proof.

## Literature wanted

None. Read literature/stacks-project/cotangent.tex, Tag 08QW (lemma-triangle-compute-lower-shriek), and literature/stacks-project/sites-cohomology.tex, Tags 08PG (example-left-derived-colimits), 08PH (example-morphism-categories), and lemma-initial-final. These provide the intended lower-shriek context and bar formulas; the section and coherent coefficient arguments are explicitly marked agent-written. No forbidden SGA reference is used.

## What changed and what was wrong

The imported item had a statement but no proof. The statement is correct as written, including the coherent section coefficient K(epsilon). I retained it and all original searches and provenance. The proof now constructs the comma natural transformation, checks its coefficient restriction, proves the specified augmentation has the specified inverse, and handles the coherent case using the two actual natural transformations and coefficient equations. The topology phrase is interpreted as the identity-generated Grothendieck topology, as in the bar node.

Read the fixed chapter sec-trace-formula and unit sk-i-curve-zero, including the current main-20261015 locality proof. This item is a supporting algebraic input under the recorded ancestor chain; it changes no chapter, unit, target or proof route. Its existing blueprint.from.place describes lower-shriek steps 3--4 and is retained. Whole-blueprint searches for bar contraction, natural transformation and contraction found no same statement. DAG searches for prism homotopy and the Stacks tags found the existing general bar and coefficient-prism nodes. I reuse the general bar node, whose statement already includes the needed homotopy, rather than duplicating these facts.

## Unfinished work

None in this one-level split. The existing general bar node and its dependencies remain subject to the project's independent formalization and review; this delivery claims a natural-language split only.

## Not duplicates

No new nodes. In particular no new node is made for either an initial-object contraction or a special case of the coefficient-bar prism homotopy.

## Review by Q99

I checked delivery-errors B--E against the sources and opened the statement of every cited node. All six proof steps cite only lem-trf-derived-colimit-bar, whose statement gives the actual differential, the chain-level reindexing generator formula, preservation of composition, and the chain-homotopy conclusion for a natural transformation with its contravariant coefficient map. It is in the same unit as this item. I also read the statements of the size, site, and module-category definitions in the item's statement dependencies; each supplies the notion named. No derived-existence result is being used to infer a chain homotopy, and no statement of a node is replaced by something from its proof.

Step 1 uses the bar differential to verify the augmentation in degree -1: K(a)K(u(h))=K(a') for u(h)a=a'. It checks that the comma categories remain small, so the bar node's small-index hypothesis is available. Step 2 uses the bar composition clause for PB=1 and its natural-transformation clause for BP homotopic to 1. I checked that eta_U is an arrow of the comma category, natural there, and that the coefficient restriction is the identity precisely because u(eta_U)=1. Both augmentation equations are checked on the degree-zero generators; all other components are zero.

Step 3 uses the stated face convention, with faces numbered from the leftmost vertex and the restriction at the last face. Inserting the initial object on the left gives d_0 S=1 and the shifted other faces, including the coefficient face. At n=0 the remaining face is i A, yielding d S_0=1-i A. This is an explicit contraction calculation, marked elementary; it does not quote a generic theorem whose hypotheses were not checked. Step 4 composes these chain homotopies with B and P, checking the exact degree-zero inverse Bi at (sV,1), rather than merely proving a quasi-isomorphism.

In step 5 I checked the coherent case separately: epsilon naturality is needed to make s_V a comma functor and K(epsilon) a coefficient transformation. The first natural transformation has direction ps_V to identity and coefficient H(epsilon); the second has direction identity to s_Vp and uses K(epsilon_uU). The given equation epsilon_uU u(eta_U)=1 makes their coefficient composite the identity, in the correct contravariant order. Thus both uses of the general bar homotopy satisfy every hypothesis of its statement. Step 6 verifies K(epsilon_W^{-1}a)K(epsilon_W)=K(a), A_I Bi=1, and the other inverse homotopy by composition. This also identifies the advertised coherent inverse at (sV,epsilon_V^{-1}). Naturality in K follows from the component naturality equation for a map of presheaves and coefficient-preserving insertion; the bar prism uses the same restrictions. No coherence of eta on s-objects is assumed or needed.

I tested the terminal one-object category (the unnormalized constant alternating complex), an initial-object arrow category with nonconstant restriction map, K=0, R=0, and the empty D case (there is then no V to check). The insertion sign and n=0 coefficient face give the claimed equations in each case. In the coherent case I also checked that the structural arrow at the image of T is epsilon_V^{-1}, not 1, and the section coefficient is K(epsilon_V); the two inverse restrictions cancel. I found no statement dispute and made no statement change.

The searches actually run are logged in searches.jsonl. I read their returned results, including ExtraDegeneracy.homotopyEquiv at Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:415 and the Dold-Kan comparison at Mathlib/AlgebraicTopology/DoldKan/HomotopyEquivalence.lean:79. ExtraDegeneracy requires the additional degeneracy data and does not construct these comma functors or their coefficient homotopies; Dold-Kan compares the normalized and alternating complexes. The representation-specific and constant-alternating-complex matches do not cover the item. The second semantic phrasing therefore also gives no whole-item leaf. No searches not run have been added. Each non-elementary step is under 2000 characters, and none hides an additional comparison lemma: the general homotopy is already the statement of the cited node.

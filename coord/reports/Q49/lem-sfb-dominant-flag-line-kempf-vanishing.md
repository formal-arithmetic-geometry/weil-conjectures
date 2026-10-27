# Q49 stage-1 report: lem-sfb-dominant-flag-line-kempf-vanishing

## Files written

All node files below are under `dag/nodes/sec-six-functors-basics/` in this sandbox. No Lean source, repository file, launcher script, or unit record was written.

- `lem-sfb-dominant-flag-line-kempf-vanishing.json`: existing statement, now split; six proof steps, no Mathlib match.
- `lem-sfb-strict-dominant-flag-line-ample.json`: new statement-only node, unsplit; no Mathlib match.
- `lem-sfb-flag-canonical-character.json`: new statement-only node, unsplit; no Mathlib match.
- `lem-sfb-flag-frobenius-rho-pushforward.json`: new statement-only node, unsplit; no Mathlib match.
- `lem-sfb-kodaira-vanishing.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement excerpt for every cited node in each proof step (13 entries).
- `report.md`: this report. The authentic `searches.jsonl`, search-plan and individual result files retain the searches for reuse and audit. `cited-statements.json` retains the statements actually read.

## Attachments

None. I searched the live project's `lean/WeilConjectures/` by the item's id and blueprint tag and by Kempf, Kodaira, Andersen, dominant flag-line, canonical flag, and Frobenius-pushforward terminology. I also checked `lean/Sheaf/` for relevant notions. No project declaration states this item or any of the four new statements. In particular an abstract group-cohomology theorem or a Lie-module weight calculation is not this theorem about Zariski sheaf cohomology on an algebraic-group flag scheme. No compiler or Lake command was run.

## Literature wanted

WANTED: Jantzen, Representations of Algebraic Groups, second edition, Part II section 4 (especially 4.4--4.5), for `lem-sfb-flag-frobenius-rho-pushforward` and `lem-sfb-dominant-flag-line-kempf-vanishing`; also the flag-line ample-cone discussion in Part II for `lem-sfb-strict-dominant-flag-line-ample` (the exact ampleness sub-number has not been checked in the unavailable book).

WANTED: Brion--Kumar, Frobenius Splitting Methods in Geometry and Representation Theory, section 2.1, equations (7)--(8), printed pp.63--64, for `lem-sfb-flag-canonical-character` and the flag geometry used by `lem-sfb-strict-dominant-flag-line-ample`.

WANTED: Mathieu, Tilting Modules and their Applications, Advanced Studies in Pure Mathematics 26 (2000), Lemma 3.1 and proof of Theorem 3.2, printed pp.157--158, for `lem-sfb-flag-frobenius-rho-pushforward` and `lem-sfb-strict-dominant-flag-line-ample`.

WANTED: Thomsen, Flag varieties, Toric varieties and characteristic p geometry (1998), Part I Theorem 5.1, printed p.27, for `lem-sfb-flag-frobenius-rho-pushforward`.

WANTED: Popa, Kodaira dimension of algebraic varieties, section 1.6 opening paragraph and Theorem 1.6.1, printed pp.22--23, for `lem-sfb-kodaira-vanishing`.

These are missing local literature files, not claims that I read an unavailable local book. I read the relevant local Milne pages and the named online author copies of Brion--Kumar, Mathieu, Thomsen and Popa without downloading literature into the project. URLs are recorded in the new nodes' sources. Because the assembly is written here and the cited Jantzen book is absent, `proof_origin.by` is `agent`.

## What needed correction or clarification

The imported item had no proof. Its mathematical statement already uses the correct sign: with positive roots in Lie(B), put M_mu = L_(-mu-tilde). I retained every hypothesis and the conclusion for every i>0 in every characteristic. I normalized inherited doubled TeX backslashes; this is a formatting correction only. I added the cohomology-definition statement dependency because the statement uses H^i.

Milne 22.51's wording must be read with care against his 22.48 and the preceding convention warning in 22.49. I used the imported item's already corrected sign, not a new sign change. For SL2 with the upper Borel, M_n is O(n) on P1. Thus the item covers n>=0; replacing M_n by L_n=O(-n) would already fail at n=2, since H^1(P1,O(-2)) is nonzero. This convention check is why both new rho formulas explicitly use M. There is no dispute with the imported item's corrected mathematical statement.

The positive-characteristic proof must not cite `lem-sfb-steinberg-induced-module-irreducible`: its dependency chain already runs through the parent Weyl-dimension formula and this item. I instead isolated ordinary Frobenius-pushforward triviality, without asserting an induced-module dimension formula, irreducibility, or self-duality. Its statement is strictly a sheaf formula and does not contain the target vanishing assertion. A future worker can follow the independent infinitesimal Andersen--Haboush argument (Mathieu Lemma 3.1), rather than route back through the existing parent.

The source formula is often given for first Frobenius. The new node explicitly asks for all iterates. The extension has an independent induction: (p^r-1)rho=(p-1)rho+p(p^(r-1)-1)rho; pullback multiplies a line's transition units by p-powers, and the ordinary projection formula and first-Frobenius formula identify f_*M_((p^r-1)rho) with a finite direct sum of M_((p^(r-1)-1)rho). Push forward the remaining r-1 times. This neither needs Kempf vanishing nor computes the Steinberg character. The new node remains statement-only, as required.

## Searches and blueprint route

For the item and each new node I ran the prescribed `msearch.py` command with leanfinder (two distinct phrasings), leansearch, loogle and grep. I read the returned declarations and types. All services answered these calls. There is no Mathlib leaf: the hits concern Lie root strings, affine Proj charts, cotangent-module smoothness, abstract projective representations/Tor, Witt isocrystals, convex cones and ordinary module pushforward, not the asserted flag geometry, canonical character, Andersen--Haboush formula or Kodaira vanishing. The JSON records use the exact query strings that actually ran, with their actual returned outputs; the item also preserves its inherited searches.

Before naming the four nodes I searched the whole DAG for their concepts and literature places, and searched the whole imported blueprint with `tools/blueprint_refs.py search` using Kempf, Frobenius splitting, Kodaira, ample, canonical bundle, Steinberg, Frobenius direct, strictly dominant and canonical sheaf. Relevant nearby candidates are distinguished below. I also read the current latest blueprint's unit section and `sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), whose frontmatter is `det-thm-sf-ctf-stability-direct-images`. This is a supporting representation-theoretic prerequisite along the inherited alteration/quotient/Haboush chain, not a replacement for a unit step. It is not a unit key statement, so no `realized` fields were edited.

`tools/blueprint_refs.py ancestor lem-sfb-dominant-flag-line-kempf-vanishing` returns None for the existing created-item chain. I retained that inherited null ancestor, the full inherited via chain and its descriptive place; each new node adds the item to via and specifies which geometric or characteristic branch it supports. All five same_as lists are empty after the searches; I did not invent a blueprint id to replace the tool's result.

## Not duplicates

- lem-sfb-strict-dominant-flag-line-ample vs lem-sfb-flag-projective-linear-system: the existing result gives a globally generated line's evaluation morphism and pullback O(1); it does not say regular-dominant characters give ample lines or that this morphism is an embedding.
- lem-sfb-strict-dominant-flag-line-ample vs lem-sfb-borel-quotient-proper-geometry: the existing result supplies smoothness, geometric integrality and properness of a represented homogeneous quotient; it does not give character-line ampleness. Those geometric properties are included in the new ample-cone statement to state its setting precisely.
- lem-sfb-strict-dominant-flag-line-ample vs lem-sfb-dominant-character-highest-line: existence of a highest-character line does not assert ampleness of the associated invertible sheaf on the flag scheme.
- lem-sfb-flag-canonical-character vs lem-sc-canonical-sheaf: the existing node is about smooth curves; the new one computes the specific canonical character on a flag scheme of arbitrary dimension, including dimension zero.
- lem-sfb-flag-canonical-character vs lem-sfb-smooth-jacobian-canonical-line: the latter is a rigidified ample line on a relative Jacobian, not the top exterior power of differentials on S/B.
- lem-sfb-flag-frobenius-rho-pushforward vs lem-sfb-rho-section-modules: constructing the character rho and its section modules does not give Frobenius pushforward triviality.
- lem-sfb-flag-frobenius-rho-pushforward vs lem-sfb-rho-section-self-duality: self-duality of a global-section representation is different from the displayed ordinary sheaf-pushforward isomorphism.
- lem-sfb-flag-frobenius-rho-pushforward vs lem-sfb-steinberg-induced-module-irreducible: the existing assertion is irreducibility of an induced representation, with a dependency through this item's parent; the new statement is the ordinary Frobenius pushforward formula and is intended for an independent proof.
- lem-sfb-flag-frobenius-rho-pushforward vs lem-trf-scheme-frobenius-finite-radicial: the existing node concerns the scalar-extended Frobenius of a finite-field model, not arbitrary absolute Frobenius on an algebraically closed-field flag scheme, and has no rho line or trivial-pushforward assertion.
- lem-sfb-kodaira-vanishing vs lem-weil-pbc-coherent-serre-vanishing: Serre gives eventual vanishing after large ample powers for arbitrary coherent coefficients; Kodaira gives vanishing at the first ample power after the canonical twist in characteristic zero.
- lem-sfb-kodaira-vanishing vs lem-sfb-dominant-flag-line-kempf-vanishing: Kodaira concerns arbitrary smooth projective characteristic-zero varieties and a canonical twist. The item concerns all dominant character lines in every characteristic. The item's argument identifies its canonical twist and checks ampleness explicitly; no new node restates an item clause.

No new node claims a Stacks tag for one of these representation-theoretic theorems. The Stacks inputs in the proof are existing nodes, whose exact tags and labels were read. In particular the finite-comparison source is coherent.tex 0B5V/lemma-surjective-finite-morphism-ample, 01YP/lemma-affine-morphism-projection-ideal, 089W/lemma-relative-affine-cohomology, and cohomology.tex 01E8/lemma-projection-formula.

## Review by Q49

I checked delivery-errors B--E with the node files and sources open. The four new files each have one self-contained quantified statement and no proof, proof dependencies or embedded proof sketch. They introduce the group, Borel, character, scheme and sheaf they use; general smooth/projective/integral, ample, invertible and cohomology notions cite their actual definition nodes. The canonical and Kodaira statements define the differential sheaf by gluing the universal affine differential modules and define exterior power inline, including exterior degree zero. I read `def-weil-pbc-kahler-differentials` and verified that it defines the affine universal module being glued, rather than pretending it already states the global canonical-character theorem.

For the item I read Milne 18c (printed pp.389--390) and 22.48--22.51 (pp.479--480). For the ample node I read Mathieu's proof of Theorem 3.2, especially projectivity and regular-twist ampleness on p.158, and the flag geometry in Brion--Kumar section 2.1. For the canonical node I read Brion--Kumar equations (7)--(8), matching its L(nu) to our M_nu. For the Frobenius node I read Mathieu Lemma 3.1 and its infinitesimal proof, and Thomsen Part I Theorem 5.1; these give the sheaf formula without invoking Kempf's theorem. For Kodaira I read the actual invocation in Milne 22.51 and Popa section 1.6's opening characteristic-zero extension and Theorem 1.6.1. The missing local copies are explicitly WANTED above.

Step 1 uses the actual quotient-line construction and specified trivializations in `lem-sfb-homogeneous-line-bundle-sections`, and the fully faithful descent equivalence in `lem-pc-fpqc-descent`. The product map has multiplier mu(b)nu(b)=(mu+nu)(b); this is the written elementary reason the descended tensor identity holds, with its unit, inverse and nonnegative powers. I did not create nodes for these elementary identities or use merely an equality of section spaces in place of a sheaf identity.

Step 2 uses exactly the new ample-cone statement, properness from `lem-sfb-reductive-borel-pair-structure`, and the simple-coroot equality in `lem-sfb-rho-regular-weyl-orbit`. I checked that the latter holds in the rational character space in all characteristics; the item's simply connected hypothesis supplies rho as an actual character. Strict positivity follows from adding 1 or 2 to each nonnegative pairing, so singular dominant lambda is included.

Step 3 uses the proper-field lemma's explicit Noetherian/coherent conclusions and the actual Serre statement for a coherent module and an ample line over a Noetherian affine base. The base here is Spec F, Q is proper, and M_-rho is invertible. I checked the Serre bound is uniform in all positive cohomological degrees as stated. Taking q=p^r beyond its threshold leaves the coefficient M_-rho fixed; this avoids an unsupported claim of vanishing for a varying coherent coefficient.

Step 4 uses the new finite Frobenius statement with r>=1 and d_r>=1, the homogeneous-line node's coherence, and the whole finite ideal-twist comparison, not a projection-formula definition. I opened its statement and substituted F=D, J=O_Q, L=M_lambda and n=1. With this unit ideal its H and JG are D and f_*D, and its conclusion supplies both the tensor projection and the cohomology comparison. Its locally Noetherian hypotheses hold on source and target by step 3. No ampleness of M_lambda or F-linearity of absolute Frobenius is needed. The q-power transition-function computation writes out the pullback/power identification used in the argument.

Step 5 uses `pqf-def-cohomology` as an actual functor: first-summand inclusion followed by projection has identity composite, so its image under H^i has identity composite too. Since the larger cohomology group is zero by step 4, the retract is zero. This elementary argument avoids hiding a new finite-sum or faithfulness lemma, and requires only d_r>=1.

Step 6 uses the precise new canonical-character isomorphism and Kodaira statement. I verified smoothness, projectivity, geometric integrality, pure dimension, characteristic zero and ampleness before applying Kodaira. The sign calculation M_-2rho tensor M_(lambda+2rho)=M_lambda is written using step 1. This is the characteristic-zero branch of the cited source, not an all-characteristics use of Kodaira.

I copied a verbatim statement excerpt for every step/node pair into citations.json and checked each is a literal substring of the cited current statement. The non-elementary inputs in the six steps are all named above; none is supported merely by a source tag or by the proof of another node. Generic off-unit descent, coherence, Serre, finite-comparison and cohomology tools are declared in `split_report.tool_uses` with their purpose; no top-level tool_uses field was set.

For small cases I checked S=1, empty roots and dimension zero (rho=0, O on Spec F); SL2/P1 (strict n>0 gives O(n), omega=O(-2), Frobenius sends O(q-1) to a nonzero trivial bundle); lambda=0; singular dominant weights; and p=2. The canonical formula remains an equality of characters/sheaves in small characteristic, not a claim about distinct differential weights. For the general Kodaira node I checked dimension zero and P1, and retained characteristic zero because the corresponding positive-characteristic generalization is false. No node was added for an elementary tensor computation, a specialization of a cited statement, or a clause of the item. Every non-elementary proof step is below 2000 characters. I checked the six-step assembly for cycles and deliberately avoided the parent Steinberg/Weyl-dimension chain.

## Unfinished work

No part of this one-level split is left unwritten. The four new statements intentionally remain unsplit for later workers; their eventual proofs and Lean formalization are outside this stage-1 delivery. The server's preliminary review_split check passed before this report was written. The required full delivery dry run and direct push follow this report; their output determines the final delivery answer.

# Q57: lem-sfb-restricted-rho-simple-dimension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-restricted-rho-simple-dimension.json: statement, split; numerical dimension proved by affine linkage, an explicit dominance-cone argument, the existing induced dimension formula and highest-weight uniqueness.
- dag/nodes/sec-six-functors-basics/lem-sfb-induced-composition-linkage.json: statement, unsplit; general composition-factor linkage and highest-weight multiplicity for the actual dominant induced regular-function module. No Mathlib match.
- citations.json: ten entries, one for each step/node citation, quoted verbatim from the actual node statement.

One new node, zero Mathlib leaves. New-node proof and proof_deps are empty. No Lean was written or compiled, and no repository file was written. No agents were started.

## Attachments

None. Searched the live lean/WeilConjectures/ by the item blueprint tag, restricted-rho/highest-weight/Steinberg notions, and linkage/composition-factor language. The Steinberg hits concern Lang--Steinberg for semilinear Frobenius, not the rational algebraic-group representation. The available representation composition-series files concern abstract group representations. No declaration states the item or the new linkage statement.

## Wanted literature

WANTED: J. C. Jantzen, Representations of Algebraic Groups, second edition (2003), Part II, Chapters 2, 5 and 6, for lem-sfb-restricted-rho-simple-dimension and lem-sfb-induced-composition-linkage; the existing item's II.3.18 reference records the numerical conclusion. The book is absent locally and was not downloaded.

WANTED: H. H. Andersen, The Steinberg linkage class for a reductive algebraic group, arXiv:1706.00590v2, sections 2.2 and 2.8, for lem-sfb-induced-composition-linkage. Read online at https://arxiv.org/pdf/1706.00590. Section 2.2 gives the simple socle, top-weight multiplicity and weight bound; section 2.8 gives linkage for indecomposable rational modules in arbitrary positive characteristic. Only these general inputs are used, not the later equivalence theorem or any Steinberg simplicity assertion.

WANTED: G. Williamson, Algebraic representations and constructible sheaves, arXiv:1610.06261v1, sections 1.2, 1.3 and 1.9, for the same general linkage input and the existing dimension formula. Read online at https://arxiv.org/pdf/1610.06261. Section 1.9 defines the p-dilated dot action and states linkage before imposing any later large-prime assumptions. Neither the later Lusztig formula nor finite-group representation theory is used.

The local source actually read was Milne, Algebraic Groups (2017), printed pp.467--470, Proposition 22.17, Theorems 22.18--22.20, Definition 22.21 and Propositions 22.22 and 22.27. These fix the rational highest-weight meaning and the actual regular-function induced-module convention. There is no Stacks tag for this algebraic-group representation-theoretic linkage theorem; no unrelated tag has been supplied. The proof_origin is explicitly agent: the numerical and cone assembly is written here, with the unavailable textbook requested rather than presented as locally read.

## Corrections and route

No mathematical statement dispute was found. The item had no proof. Its statement contained doubled TeX backslashes; I normalized those characters and retained all its mathematical hypotheses and conclusion, including the ordinary integer dimension, p=2, reducible root systems and the trivial group.

The parent lem-sfb-steinberg-induced-module-irreducible uses this item to compare dimensions. Citing that parent here would create a cycle. This proof instead establishes the first-weight simplicity consequence from general linkage: at eta=(p-1)rho, a lower linked dominant mu forces nu=(mu-eta)/p to be both dominant and a nonzero negative sum of simple roots. An averaged positive definite form makes this impossible. The existing general induced Weyl dimension formula then computes the dimension. This does not change the parent route or assume a numerical Steinberg result under another name.

Read the chapter and unit records and the newest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (frontmatter det-thm-sf-ctf-stability-direct-images), paragraph (3). No chapter/unit record is changed. The numerical input belongs to the already recorded projective-quotient/Haboush prerequisite chain. blueprint_refs ancestor reports None for this inherited chain; I preserved its null node and full place, and placed the item at the head of the new node's via list.

## Searches

The only Mathlib searches were the required msearch.py commands, whose exact queries and actual hits are in searches.jsonl and the node mathlib_searches fields. All services returned successfully. For the new node I searched both affine-linkage wording and costandard/highest-weight multiplicity wording with LeanFinder, the full composition-factor sentence with LeanSearch, the Loogle pattern "Representation", "Ind", and two greps. For the item I ran a direct dimension query in LeanSearch and LeanFinder, a Steinberg Loogle query and two greps; the item's earlier recorded searches are retained.

Read the promising returned definitions and statements: Mathlib/RepresentationTheory/Induced.lean:61 (IndV, an abstract group algebra tensor/coinvariant), Coinduced.lean:62 (coindV, arbitrary equivariant functions on an abstract monoid), LinearAlgebra/RootSystem/Irreducible.lean:125 and :162 (the root reflection representation), RepresentationTheory/FDRep.lean:160 (Schur's Hom-space dimension), and CategoryTheory/Preadditive/Schur.lean:87, :157 and :169. None supplies rational algebraic-group highest-weight composition factors, affine linkage or a Steinberg dimension. LieModule.chainTop/chainBot and rank hits concern Lie-module weight strings or nilpotent ranks, not rational algebraic-group modules, and some require characteristic zero. These are not one-line specializations of the needed statements.

Before introducing the new id, searched the whole DAG for linkage, affine Weyl, costandard, highest weight and composition factors, and the whole imported blueprint through blueprint_refs search for Steinberg, Weyl, linkage, costandard and composition factors. The latter composition-series nodes concern Weil representations, and Lang--Steinberg concerns semilinear maps. No duplicate or attachment was found.

## Not duplicates

lem-sfb-induced-composition-linkage vs lem-sfb-induced-module-primitive-line: the latter identifies the U-invariant line of a nonzero regular-function module, but gives no affine constraint on composition factors or top-factor multiplicity.
lem-sfb-induced-composition-linkage vs lem-sfb-simple-module-dual-highest-weight: the latter classifies already simple modules by their highest weight and describes duals, but gives no composition factors of nonsimple induced modules.
lem-sfb-induced-composition-linkage vs lem-sfb-induced-weyl-dimension-formula: the latter gives only total dimension; the new statement gives composition-factor weights and linkage, with no dimension formula or simplicity conclusion.
lem-sfb-induced-composition-linkage vs lem-sfb-steinberg-induced-module-irreducible: the parent concludes simplicity only at special weights; the new general linkage theorem neither asserts simplicity nor singles out those weights and does not depend on the parent.
lem-sfb-induced-composition-linkage vs lem-sfb-restricted-rho-simple-dimension: the item gives a number for an already simple module at a single weight; the new statement concerns the composition structure of all dominant induced modules. The item still carries the congruence, cone exclusion, dimension calculation and comparison arguments.

## Review by Q57

I read delivery-errors B--E in both the main and merged new-target sections and reviewed the node files against them. The new statement introduces its field, semisimple simply connected group, Borel pair, rational coaction, simplicity, highest weight, root lattice, order, induced module and finite composition series. The non-elementary input is genuinely general linkage with its induced-module highest-weight structure; it is neither the dimension assertion nor Steinberg simplicity renamed. It is statement-only, with precise online corroboration and a WANTED textbook reference. Its hypotheses agree with the item: algebraically closed field, positive characteristic, split maximal torus, semisimple simply connected group, arbitrary prime, no good-prime or rank restriction.

For step 1 I opened lem-sfb-reductive-borel-pair-structure and checked that it explicitly gives semisimple implies reductive and the integral reduced root datum. I opened lem-sfb-rho-regular-weyl-orbit and checked its simple-coroot pairing and w_0 rho=-rho assertions in rational character space. These give dominance of eta without dividing by 2 in F. I opened lem-sfb-induced-weyl-dimension-formula: it explicitly uses the same actual right-equivariant regular functions, left translation, rational/integer dimension and positive denominators. Each factor becomes p in Q. This step does not assume simplicity of E.

For step 2 I reread the new linkage statement, including its w_0 convention. Our I(eta) is E_B(w_0 eta); at eta=(p-1)rho this is exactly E_B(-eta), not a different representation with the same dimension. The statement supplies an actual finite composition series, exactly one highest factor, dominance of every other factor, strict root order and the displayed affine equation. Andersen section 2.2 and section 2.8 independently corroborate those inputs. The simple socle makes the induced module indecomposable, so the general linkage principle applies. The multiplicity-one weight and the weight bound give exactly one top factor. These are precisely the general facts recorded in the new node, not facts silently borrowed from its future proof.

For step 3 the already opened root-datum and rho nodes give the integral simple-coroot pairing. From mu+rho=p(w rho+gamma), nu=w rho+gamma-rho is a character because rho is integral by the item's hypotheses. The inequality p<nu,alpha^vee> >= -(p-1) forces the integer pairing to be nonnegative even when p=2. The strict-order conclusion of step 2 supplies the nonzero coefficients; this is not assumed from linkage alone.

For step 4 I opened lem-sfb-weyl-reflection-realization and verified its finite group, rational root-span action and exact reflection formula. These justify the finite averaging on the real root span. The root-datum statement supplies positive simple-root coefficients, and the rho node supplies each simple-coroot pairing 1. I wrote out the reflection pairing calculation, positivity of the averaged form and both signs of (nu,rho), so no cone-separation theorem, classification theorem or unproved identification is hidden here. This step is an elementary calculation from the cited statements. It is 1033 characters, and every proof step is below 2000 characters.

For step 5 no lower factor survives. A composition series of length one says exactly that E is nonzero simple and has the stated highest weight. I opened lem-sfb-simple-module-dual-highest-weight and verified its final sentence gives an equivariant linear isomorphism for two finite-dimensional simple rational modules with the same highest weight. The hypotheses apply to E and the given V. A transported basis proves dimension equality; no semisimplification-dimension comparison is assumed. The first dry run requested longer citation excerpts; I replaced the short rho/Weyl excerpts with their full relevant clauses and also expanded the root-datum and linkage excerpts. Each node citation has a verbatim quote in citations.json; I checked the stored doubled TeX in existing statements when selecting those quotes.

Small-case checks: for A1, eta=p-1 and the induced Weyl product is p; the negative-cone contradiction excludes the putative lower linked dominant factor. For p=2 the same integrality estimate is valid and no characteristic-zero Lie-algebra result is used. Reducible root systems work in the whole finite reflection representation; no irreducibility of the root system is assumed. For an empty root system there is no strictly lower root combination, the series has one factor and the Weyl product is 1. For the new lemma eta=0 gives exactly one trivial factor and no lower dominant factor, while arbitrary eta is allowed to have additional strictly lower linked factors: the node does not falsely assert that all induced modules are simple. I checked the dependency direction explicitly: no step cites the parent or a statement whose proof requires this dimension item. No SGA source was used.

## Unfinished work

The new general linkage statement is deliberately unsplit for a later stage-1 worker; its source, hypotheses and searches are recorded. No part of the item's assembly is deferred. Required server dry run and direct push are the remaining delivery operations.

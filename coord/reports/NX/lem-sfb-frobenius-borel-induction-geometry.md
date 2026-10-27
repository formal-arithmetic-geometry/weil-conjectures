# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-borel-induction-geometry.json`: item, statement; split into five explicit proof steps. Its statement, imported metadata, existing search record and ancestor chain are retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-connected-group-frobenius-flat.json`: new statement-only node; unsplit, no Mathlib match. It supplies finite faithfully flat Frobenius for smooth connected affine groups, including the solvable Borel group.
- `citations.json`: one entry for every node used in every step, quoting its statement verbatim.

There are no Mathlib leaves in this delivery.

## Attachments

None. Searches for the item tag, Borel, flag schemes and Frobenius induction in the project's `lean/WeilConjectures/` found no declaration proving this item. Existing absolute-Frobenius declarations concern scheme maps, not this quotient and the restriction of covariant functions. No compiler was invoked.

## Wanted literature

WANTED: Kaneda, *On the Frobenius morphism of flag schemes* (1994), Sections 2.3--2.5, printed pp.320--323, local copy at `literature/kaneda-frobenius-morphism-flag-schemes-1994.pdf`, for the item. I read the primary PDF online at https://msp.org/pjm/1994/163-2/pjm-v163-n2-p07-s.pdf. In particular, 2.3 defines induction by functions satisfying covariance on all algebras; 2.5 identifies the Frobenius-thickened quotient with the twisted flag scheme. That paper does not state the precise restriction isomorphism of this item: the explicit descent proof here is marked agent-written.

No literature was downloaded or written to the repository.

## Findings and changes

The imported item was unsplit and its statement is correct. There is no STATEMENT-DISPUTED correction. The parent statement's positive-root convention differs from Kaneda's, but this item works with an arbitrary Borel character and its displayed inverse covariance; it uses no highest-weight sign convention. The simply connected hypothesis and the positive roots are not needed for this geometric argument and were retained.

The represented quotient, Borel torsor and proper geometric integrality are already present in the DAG. I reused them instead of restating the quotient as a new lemma. The existing reductive Frobenius-twist node is insufficient for the second use of Frobenius, on B: a Borel of a positive-rank semisimple group is generally solvable and nonreductive. The new node covers precisely that missing general input. Its proof will iterate Milne 2.29; finiteness is Stacks 0CCD/0CCG, and local finite presentation follows because the source and target have finite-type coordinate rings over a field. This is a prerequisite, not either conclusion of the item renamed.

I avoided claiming a factorization on field-valued points or a globally chosen Frobenius inverse. The actual cover is the scheme W = H_r times_{B^(q)} B. On it l = h b^{-1} lies in S_r, and the formula chi(b)^{-1} f(l) descends. On two lifts a = b b'^{-1} lies in B_r, so l' = l a; the inverse-character factors cancel exactly. This check also works over nonreduced test algebras. The right covariance, restriction identity and inverse identity are written out, rather than hidden behind 'Mackey' or 'transport'.

The latest blueprint unit and its direct-image proof were read in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. This is a deep supporting algebraic-group input in the inherited alteration/Steinberg ancestor chain, below the same unit; the direct-image route is unchanged. `tools/blueprint_refs.py ancestor` returns None for this preexisting ancestor chain, so the inherited null ancestor is preserved and the new node has that same ancestor with the item prepended to its via list. Whole-blueprint searches for Borel, smooth connected affine groups, smooth connected Frobenius and Frobenius flatness found no blueprint node stating either the item or the new input. The unrelated Borel--Moore nodes are not duplicates.

## Not duplicates

lem-sfb-smooth-connected-group-frobenius-flat vs lem-sfb-reductive-frobenius-twist: the existing theorem requires reductivity and includes root-datum comparisons; it cannot be applied to B. The new input permits arbitrary smooth connected affine groups and supplies the fppf cover for B.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-trf-relative-frobenius-finite: the existing general scheme theorem proves only finiteness, not flatness or faithful flatness; the new input uses smooth connected group structure to supply those additional assertions.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-trf-scheme-frobenius-finite-radicial: the existing node is about scalar-extended Frobenius of a scheme over a finite field, with no flatness assertion; the new input is relative Frobenius of a smooth affine group over an arbitrary algebraically closed field.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-sfb-frobenius-twist-geometric-integrality-affine: the existing node gives integrality of a twist and affine coordinate formulas, not a flat morphism.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-sfb-relative-frobenius-function-field-image: the existing node identifies a function-field image for a smooth proper curve, not a faithfully flat map of group schemes.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-sfb-purely-inseparable-curve-frobenius: the existing node factors purely inseparable morphisms of smooth proper curves; it makes no group-scheme flatness assertion.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-sfb-smooth-curve-relative-frobenius-degree: the existing node computes a function-field degree for proper curves; the new input concerns affine groups and includes faithful flatness.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-sfb-automorphism-twist-curve-lift: the existing node constructs and compares lifts on curves along a field automorphism, not fppf Frobenius covers of groups.
lem-sfb-smooth-connected-group-frobenius-flat vs lem-sfb-frobenius-image-field-tower-degree: the existing node computes degrees of towers of p-power subfields; it makes no assertion about a morphism of schemes being flat.

## Mathlib research

The new node records exactly the five msearch queries logged in this sandbox: two semantic phrasings, a Loogle query, a grep restricted to AlgebraicGeometry and a LeanSearch query. I read all returned types. The semantic hits about perfect-ring Frobenius are bijectivity of Frobenius on a perfect ring, not faithful flatness of relative Frobenius on a smooth group: the coordinate algebra k[G] is generally not perfect. Smooth algebra flatness concerns the structure map k -> k[G], not relative Frobenius. Arithmetic Frobenius at primes, RingHom.Flat/FaithfullyFlat definitions, and finite-field algebra homomorphisms likewise do not prove this node. Loogle and the scheme-source grep had zero hits. All services answered; none was recorded as unavailable or as a fabricated empty search. The item's earlier searches are retained.

## Review by NX

I read Kaneda 2.3--2.5 in the primary online PDF, Milne's local book 2.26--2.29 on printed pp.47--49, and the local Stacks source at varieties.tex labels lemma-relative-frobenius-finite and remark-n-fold-relative-frobenius. Milne explicitly treats smooth connected groups, with no reductivity assumption, so the new statement applies to B as well as S. Its finite-presentation assertion has a Noetherian target, since G^(q) is finite type over a field; the usual finite-type-to-finite-presentation implication therefore has the required hypothesis. The new node contains no proof steps or proof dependencies: that proof is future work, and this paragraph records the intended literature argument without putting it inside its statement.

For step 1 I opened the actual statements of lem-sfb-reductive-borel-pair-structure, lem-sfb-local-borel-quotient-geometry, lem-sfb-borel-quotient-proper-geometry and the two covering lemmas. The first expressly includes semisimple implies reductive. The local quotient theorem applies over the nonzero Noetherian local ring F; its hypotheses on all geometric fibres follow because F is algebraically closed and the Frobenius twist is base change along a field automorphism. It supplies the represented fppf quotient, properness, the quasi-compact locally finitely presented torsor map and its exact kernel pair. The geometric quotient theorem supplies geometric integrality for that represented homogeneous quotient; I did not take it to construct the quotient. Base change of an fppf cover and the fppf-to-fpqc statement supply the fpqc-local lifts required by that theorem.

For step 2 the new Frobenius theorem supplies finite fppf Frobenius on S; the existing space fppf calculus explicitly specializes back to schemes and composes these covers. The quotient node supplies the B^(q)-torsor kernel pair. The elementary inverse (g,g') -> (g,g^{-1}g') is computed on arbitrary test schemes, hence yields the stated scheme isomorphism. I checked that no reduction to F-points enters that computation. Quasi-compactness is written using finite affine covers of inverse images; no uncited properness assertion for the quotient projection is used. The existing representable fpqc-descent statement, Stacks 023Q, says exactly that compatible maps to any scheme descend uniquely, and it proves the invariant-map consequence including F-linearity of the structural map. Base-changing the fppf cover supplies local surjectivity for the coset-sheaf quotient.

For step 3 the same new input is applied to B, which is smooth connected affine of finite type by hypothesis, not by a reductivity assumption. The existing fpqc base-change node makes W -> H_r a cover. I checked the coordinate formula for l = h b^{-1} and the overlap element a = b b'^{-1}; the latter lies in B_r and hence P_r. The displayed cancellation has the inverse covariance from the item's statement. Stacks 023Q is used with the actual regular map W -> A^1, so it provides a regular global function, rather than a function only on field-valued points.

For step 4 I checked the right multiplication map (h,b) -> (hc,bc); its Frobenius equality is valid without commutativity of B, and hc(bc)^{-1}=hb^{-1}. The cited fpqc base-change theorem gives the cover of H_r times B and the cover over L_r. Descent uniqueness proves both the right covariance and the equality of restricted functions. Over L_r the second coordinate b is in P_r because its Frobenius equals that of h; this uses the scheme-theoretic inverse-image definition, not a statement about geometric points.

For step 5 I checked both inverse identities, including uniqueness on W for a function already defined on H_r. F-linearity is restriction of regular functions. The left-translation equation is a regular identity after every scalar extension; it gives equality of coordinate coactions, the exact equivariance required in the item. There is no appeal to complete reducibility or to an abstract-group induction theorem.

I checked all B--E failure modes: the sole new node is self-contained with definitions cited, has its own genuine prerequisite statement and an empty proof, and is neither a clause of the item nor a renamed restriction theorem. Every proof citation is supported by the opened node statement, and citations.json contains an exact quote for each. No comparison is taken from another node's proof. Generic covering/descent results from other units are declared as tool uses in split_report, without replacing the unit's route. All five steps are shorter than 2000 characters; none hides a long separate argument. Rank zero/trivial S gives Q_q = Spec F and the identity F -> F on functions. On G_a and G_m the new Frobenius input is the qth-power map with the expected finite free coordinate module; smoothness is essential (the zero Frobenius on alpha_p is not faithfully flat onto its twist). No assumption excludes p=2. Characters take invertible values so every inverse used in the proof is defined. The group B can be nonreductive, and the test algebra can be nonreduced, exactly the cases the split must handle.

## Unfinished work

The new Frobenius node remains statement-only, as required for one-level splitting. No part of the item's natural-language proof is postponed. Server dry-run and push outcomes are recorded by the delivery command.

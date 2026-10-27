# Stage-1 delivery: lem-sfb-groupoid-strict-local-reduced-orbit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-groupoid-strict-local-reduced-orbit.json: item, statement unchanged, six proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-sepclosed-purely-insep.json: statement, Mathlib leaf for arbitrary algebraic extensions of a separably closed field, both separable closedness and pure inseparability.
- citations.json: verbatim statements for every step citation.
- searches.jsonl: actual search-command records; write_split.py is a sandbox-only writing aid, not part of the delivery.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by groupoid, stabilizer, strict-local reduced orbit, and invariant terminology. No project declaration states every clause of the item. The geometric-lift tool is an existing dependency, not an attachment of this item.

## WANTED

None. Read the local Stacks sources and the current literature/blueprint/latest sources.

## Findings and changes

The imported statement is correct; no STATEMENT-DISPUTED correction is needed. The proof was empty. The source's first claim in Tag 0DT9 was expanded, including its suppressed reduced-coordinate-ring identification. In particular a pointwise equality of endpoints is not enough to apply the stabilizer square: step 4 proves equality of the two field maps before passing through the diagonal. Closedness is proved over C/m, without assuming that p-prime was already closed or that A is finite type over C. Finite locally free source maps need not have constant rank and A need not be finite over C.

Read the chapter and unit records and the latest sk-thm-sf-ctf-stability section and det-thm-sf-ctf-stability-direct-images proof (3). The inherited ancestry passes through the alteration and coarse-moduli supporting route. blueprint_refs.py ancestor returns None for this chain, and that value and the existing via list are preserved. No chapter or unit record was changed.

The exact Mathlib matches for the new leaf are Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed, PurelyInseparable/Basic.lean:148-153, and Algebra.IsAlgebraic.isSepClosed, same file:567-572. Both use algebraicity, not finite dimensionality. Existing finite-extension leaves do not cover the potentially infinite algebraic residue extension here. Searches were run through the required msearch command; the leanfinder and leansearch hits and the two exact source declarations were read. Loogle IsSepClosed, Algebra.IsAlgebraic returned exactly these two declarations. Categorical Groupoid and etale-algebra hits do not give the item. A second natural-language phrasing was also read. The additional general field leaf has a statement only and no proof sketch.

## Review by NW

I read groupoids.tex Tag 0DT9 (lemma-etale), especially the first part of its strictly henselian claim, and Tags 03BJ and 03BL in full at their relevant statements and proofs. I also read algebra.tex Tag 00GA's proof, 00E0(7), and 00DT's Chinese remainder statement and proof. For the new leaf I read fields.tex Tag 030K (lemma-separable-first) and Mathlib's exact general statements at lines 148 and 567. The source's use of algebraic extensions is essential: replacing algebraic by finite without proof would not be justified.

Step 1 uses the statements of lem-a1-affine-groupoid-integral-invariants and lem-a1-affine-groupoid-orbit-fibres, opened and read, for integrality, surjectivity and the existence of an arrow between any two points in the same invariant fibre. All affine and finite locally free hypotheses hold for both groupoids. The finite-closed-map-finite-fibres statement really supplies finite ordinary fibres; def-pc-finite-locally-free explicitly includes finiteness. An orbit is the target image of a source fibre, so its finiteness does not rely on finite generation of the invariant algebra.

Step 2 uses the integral residue-extension lemma, whose statement explicitly permits arbitrary integral maps and says algebraic, with C -> A. The henselian terminology definition explicitly says the closed-point residue field is separably closed. The new Mathlib leaf supplies both field properties under algebraicity. I read the existing etale-lift-sepclosed-base statement and its source proof in GeometricLifts.lean:54-88: it gives precisely g-prime with the two factorization identities used here, for an arbitrary field extension Omega/L. Applying it to the canonical residue point proves that the original residue embedding is invertible. I wrote both induced identities on fields instead of substituting a bare assertion about etale residue extensions.

Step 3 uses the ordinary orbit clause of the same orbit-fibres node and the cartesian source square. Step 2 first identifies the two residue fields, so the scheme-theoretic source fibres really agree. The lift is explicitly formed on a kappa(r)-point; its target remains above p-prime since source and target agree on every invariant in C-prime. This verifies membership in Z-prime, not merely in a fibre over the point u of U.

Step 4 again uses the ordinary orbit clause to choose r-prime with the specified endpoints. The two maps kappa(u) -> kappa(r-prime) agree on k=C/m. The definition of pure inseparability gives the p-power calculation proving equality; characteristic zero is treated separately. The diagonal fibre-product definition is exactly what then factors the field-valued arrow through G. The stabilizer square produces its lift in G-prime, and uniqueness in the source square identifies this lift with the original arrow. Thus the two source-groupoid endpoints coincide. No unstated full-faithfulness theorem is used. The proof is specific to the present arrow and point, with no hidden general groupoid comparison lemma.

Step 5 is elementary and I checked its algebraic inverse formula against 00GA. Both domains contain C/m and embed in algebraic extensions of that field; each nonzero element has a polynomial equation with nonzero constant coefficient, so its inverse lies in the domain. This proves maximality of both primes, including the primed primes before assuming p-prime closed. A finite union of closed points is closed. This few-line argument is retained as a step, not a new node.

Step 6 uses the exact radical/intersection clause in lem-weil-pbc-zero-locus-eq-iff-radical-eq and the exact finite ideal-family CRT in lem-pc-crt-ideal-quotient-product. I checked coprimality from distinct maximality and the kernel relation q-prime intersect A=q. The product coordinate map is explicitly the original residue map, so the resulting isomorphism is the induced A/J -> A-prime/J-prime in the statement, not just an abstract isomorphism between the two rings. The CRT node's source record says 00U3, which actually denotes etale algebras over a field; its statement and Mathlib match are nevertheless correct. I cite the correct source Tag 00DT in this delivery and report the external metadata error without editing another node.

Each cited node's statement was opened and its exact verbatim text is in citations.json. The off-unit groupoid orbit and integrality tools, and the geometric-lift tool, are declared in split_report.tool_uses as generic black boxes. The new leaf is Mathlib and imposes no route change. Every proof step is shorter than 2000 characters (the longest is 1165). There is no new lemma restating a clause of the item.

I tested the identity groupoid over a strictly henselian ring with several etale components, a pair groupoid on finitely many copies of a separably closed field, nonreduced identity groupoids, and purely inseparable residue fields in positive characteristic. A pair groupoid shows why the source square is needed; the comparison of arrow endpoints shows where the stabilizer square is used. A nonperfect separably closed field with an infinite purely inseparable algebraic extension shows why the new leaf cannot be replaced by an existing finite-extension statement. Empty U or U-prime cannot satisfy the hypothesis that p-prime exists: integrality and orbit surjectivity force the two chosen fibres nonempty. Degree-one and variable-rank cases cause no special-case failure. No Noetherian, perfection, finite-generation or separability assumption was added.

## Not duplicates

lem-sfb-algebraic-sepclosed-purely-insep vs lem-zl-geometric-irreducibility-separable: its statement concerns Separable elements in a geometrically irreducible extension; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-trf-strict-henselization-quasi-finite-ring: its statement concerns Strict henselization under a quasi-finite local map; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-pc-kbar-pure-insep: states pure inseparability only for a chosen algebraic closure and does not state separable closedness of an arbitrary algebraic top field.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-sfb-proper-generic-radicial-etale-factorization: its statement concerns Generic radicial-etale factorization of a proper generically finite map; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-sfb-multiradical-galois-degree: its statement concerns Galois group and degree bound for a finite multiradical extension; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-sfb-curve-frobenius-separable-factorization: its statement concerns Frobenius and separable factors of a nonconstant smooth proper curve map; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-sfb-nested-open-regular-alteration: its statement concerns Regular alteration adapted to nested opens and a prescribed finite cover; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-sfb-generic-orbit-dense-quotient: its statement concerns A generic geometric orbit gives a finite universal-homeomorphism quotient on a dense open; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-per-finite-henselian-algebra-local-model: its statement concerns Finite algebras over a local henselization have finite-type strict local models; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-dl-a1-henselian-global-inertia-comparison: its statement concerns Comparison of henselian local inertia with inertia in a global separable closure; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-dl-a1-ind-etale-residue-action-rigidity: its statement concerns Residue kernel detected by fixing an ind-etale local algebra with separably closed residue; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-per-normalization-field-extension-homeomorphism: its statement concerns Normalization after field extension compares by a universal homeomorphism; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-per-cohen-gabber-finite-presentations: its statement concerns Cohen–Gabber presentations with an etale open meeting the special fibre; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-dl-a1-trivial-inertia-finite-etale-normalization: its statement concerns Finite Galois normalization with trivial inertia is finite etale; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-per-tame-trait-quotient-log-etale: its statement concerns Tame trait quotient and change of logarithmic base; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-dl-a1-normal-finite-aut-separable-subfield: its statement concerns Finite separable subfield of a normal extension with finite automorphism group; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-dl-a1-integral-normal-residue-etale-splitting: its statement concerns Etale splitting of an integral fibre with normal residue fields; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-popescu-enlarge-solution-modulo: its statement concerns Enlarging a solution modulo q^n to contain a power of a unit; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-separable-first-purely-inseparable: decomposes an arbitrary algebraic extension over its relative separable subfield; it neither assumes a separably closed base nor states that the top field is separably closed.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-normal-extension-purely-inseparable-then-galois: its statement concerns A normal extension is Galois over a purely inseparable subextension (Stacks 030M (2)); it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-make-separably-generated: its statement concerns A finitely generated field extension becomes separably generated after finite purely inseparable extensions; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-separable-split-purely-inseparable-residue-fields: its statement concerns A finite separable extension making all residue fields of finitely many finite extensions purely inseparable; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-separable-purely-inseparable-linear-disjoint: its statement concerns Separable and purely inseparable extensions are linearly disjoint; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-separable-tensor-purely-inseparable-field: its statement concerns Separable algebraic tensor finite purely inseparable is a field; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs def-weil-pbc-separable-field-extension: its statement concerns Separably generated and separable field extensions (not necessarily algebraic); it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-etale-local-finite-multiple-points: its statement concerns Isolated locally finite type points become finite after an etale base change; it does not state both field properties for every algebraic extension of a separably closed field without a finiteness hypothesis.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: requires a finite field extension; the new leaf allows arbitrary algebraic extensions and also states pure inseparability.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-kun-sep-closed-finite-extension-sep-closed: requires finite field degree and states only separable closedness.

lem-sfb-algebraic-sepclosed-purely-insep vs lem-kun-sep-closed-finite-extension-purely-inseparable: requires finite field degree and states only pure inseparability.

## Unfinished work

None in the stage-1 split. Independent maintainer review and later Lean formalization remain with their respective roles. The required delivery checks are recorded by deliver.py.

## Delivery check repair

The first full dry run required an explicit mathlib_match.line field in addition to the two verified line references in how. Added line 567 (the separable-closedness declaration); the other clause remains identified at line 148. The 00GA advisory is discharged by step 5's complete inverse-polynomial argument, marked elementary.

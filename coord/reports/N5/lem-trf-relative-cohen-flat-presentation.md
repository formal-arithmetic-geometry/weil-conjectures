# N5: lem-trf-relative-cohen-flat-presentation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-cohen-flat-presentation.json: item, statement, split into eight steps; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-regular-complete-coefficient-coordinates.json: new statement-only input, unsplit; no Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and source grep.
- citations.json: 24 step/node entries, each quoting the cited statement verbatim.
- searches.jsonl: actual msearch.py results; earlier item searches retained in the item, new searches appended.

One new node, zero Mathlib leaves. Only sandbox files were written; no Lean was written, no compiler/build was invoked, and no git command was run in the shared repository.

## Attachments

None. Searches in lean/WeilConjectures for the item tag and coefficient/Cohen/power-series terminology found no exact declaration. Existing CohenStructurePowerSeriesSurjection and FlatClosedFiberKernelRigidity were read as supporting results, not proposed as attachments for the item. Searches for the new single-ring theorem likewise found no exact project declaration; the existing full-coordinate theorem assumes its target is already a power-series ring.

## WANTED

None. All the sources used are present in literature/stacks-project/.

## Corrections and interpretation

The item's statement is unchanged. Its source explicitly identifies it as an agent-written compatible-coefficient refinement, rather than the literal statement of 07NQ or 032A. Accordingly proof_origin.by is agent. Stacks 07NQ supplies the flat-presentation and kernel-rigidity method; 032A, 0322 and 07NJ give the additional compatible coefficient construction.

The key refinement is that b must extend the chosen map fhat a. Independently choosing Cohen fields in both rings does not prove this. The proof first chooses a and then lifts the identity of L as a K-algebra map into Bhat using formal smoothness of arbitrary characteristic-zero field extensions. It imposes no finite generation or separable-generation assumption on L/K. Likewise the ordinary Cohen-surjection statement does not prescribe the coefficient map; the proof constructs its own map by evaluation and proves surjectivity using the complete-source lemma.

The item is a supporting commutative-algebra input on the existing historical resolution branch of lem-trf-local-term-locality, not a new route for the unit's trace theorem. Its inherited chapter, unit, blueprint ancestor and via chain are retained. Its blueprint same_as was checked by whole-blueprint searches for Cohen, coefficient field, complete regular local, power series ring and 0C0S; none states this local-algebra result. No unit realization is due: this is not the key node of sk-i-curve-zero. Generic commutative-algebra uses from sk-thm-p1 are individually declared in split_report.tool_uses.

## Unfinished work

The new single-ring coordinate theorem remains statement-only, as required for this one-level split. Its future proof follows 0C0S(2): evaluate any minimal parameter tuple, apply complete-source surjectivity, and use regularity and dimension to kill the kernel. This sketch is recorded here rather than in its statement or proof fields.

## Not duplicates

lem-trf-regular-complete-coefficient-coordinates vs lem-per-prime-field-complete-coordinate-model: the existing node chooses a coefficient section and parameters existentially, with a further polynomial-completion clause; the new node starts with an arbitrary specified coefficient map and arbitrary specified regular parameters. The proof requires the coefficient map induced by the already constructed b, so choosing another section does not suffice.

lem-trf-regular-complete-coefficient-coordinates vs lem-per-inseparable-surface-differential-data: the existing node concerns two-dimensional characteristic-p rings and an inseparable degree-p fraction-field extension, adjoining an inseparable root and constructing differential data. It does not assert coordinates for an arbitrary specified coefficient field in a regular complete local ring of any dimension.

lem-trf-regular-complete-coefficient-coordinates vs lem-per-prime-field-punctual-purity: the existing node asserts punctual etale purity on regular schemes over prime fields. Its source uses 0C0S in a larger purity argument; its statement does not provide any coefficient-field coordinate isomorphism.

lem-trf-regular-complete-coefficient-coordinates vs lem-weil-pbc-power-series-full-coordinates-field: the existing node assumes the target is already k[[X]] with its given coefficient embedding; the new node starts with an abstract complete regular local k-algebra. Identifying that abstract algebra with a power-series ring compatibly with its specified coefficient map is exactly the missing input.

lem-trf-regular-complete-coefficient-coordinates vs lem-trf-relative-cohen-flat-presentation: the new node has one regular ring and a given coefficient map; it asserts the absolute regular-coordinate theorem 0C0S. It says nothing about flat local maps, compatible coefficient sections, arbitrary singular source rings, or extension of relations. The item's construction, surjectivity and kernel identification remain in its own steps.

## Review by N5

I read 07NQ's (2) implies (3) proof through the special-fibre kernel argument, the characteristic-zero lifting paragraph and final presentation paragraph of 032A, characteristic-zero assertion (3) of 0322, and the statement and lifting construction of 07NJ. For the new node I read 0C0S(2) and its proof in algebra.tex: the proof explicitly uses a given coefficient map and any cotangent-space basis. A generating d-tuple is such a basis when C is regular of dimension d. It is not a new relative-presentation theorem hidden below the item.

For step 1, I opened the statements of adic-completion-noetherian, local-completion-local-ring, module-completion-complete and flat-completion. They respectively give Noetherianity, the exact maximal ideals and residue maps, completeness for the powers of those ideals, and flatness of the induced map of completions. The last statement really is for completing both rings, not just the flatness of A -> Ahat. The original localness and Noetherian hypotheses hold. The localness of fhat follows by its map on residue fields, which is the original inclusion.

For step 2, I read quotient-local-structure and surjective-image-noetherian to check C is a nonzero Noetherian local ring (mB is contained in n). Local-completion-quotient gives the isomorphism Bhat/(mB)Bhat -> Chat, including the canonical-map formula used to identify the ideals. Local-completion-local-ring supplies m_Ahat=mAhat. Completion-regular-local and completion-dimension say exactly what is required for Chat to be regular of dimension s. Module-completion-complete applies to C at its finitely generated maximal ideal. This step does not assume the mB-adic completion equals Bhat; it takes the completion of C at the image of n.

For step 3, coefficient-residue-section gives a section for Ahat in characteristic zero. Char-zero-field-extension-formally-smooth explicitly permits an arbitrary extension, not just a finitely generated extension. I checked fs-adic-lift-into-complete's statement: use source ideal zero, target completion ideal n_0, and closed ideal J=n_0. J is closed since J+I^h=J, with t=r=1, so none of that lemma's topological hypotheses is omitted. The lifted map is a K-algebra map. That is precisely the equality b|K=fhat a; reduction is the identity of L.

For step 4, power-series-universal-property-complete supplies evaluation for the already fixed a. Power-series-field-cohen-regular-complete gives completeness and the variable maximal ideal of R. Complete-source-surjective-mod-ideal requires completeness of R, Hausdorffness for the image ideal in Ahat, and surjectivity modulo that image ideal. Here these are exactly the m_0-adic conditions and the identity of K on constants. The argument establishes q and I directly; it does not extract an unasserted compatibility from the existing Cohen-structure-surjection node.

For step 5, the new 0C0S statement applies to the complete regular ring C_0 of dimension s and the specified coefficient map obtained from b. Quotient-local-structure gives the exact maximal ideal image needed to lift the chosen parameters inside n_0. Thus every hypothesis and the specified coefficient and variable formulas of rho are supplied, not merely an abstract ring isomorphism.

For step 6, the same universal-property and complete-source statements are applied to S and Bhat. I checked the image ideal equals n_0: lifting generators of n_0/m_0Bhat gives n_0=m_0Bhat+(t), and the X images generate the first summand. Surjectivity on residues is via b. The power-series structure statement gives S Noetherian and local, which are needed again in step 8.

Step 7 is an elementary computation from the displayed maps. I checked its sole cited statement, the universal property, includes uniqueness for the prescribed coefficients and variable images. The equality vj=f_0q then follows with exactly the coefficient equality proved in step 3. For the special fibre, setting X=0 has kernel (X) by grouping each surviving monomial by the first X variable with positive exponent; there are only finitely many such groups. The reduction of v is rho composed with this map because the coefficients and all variables agree. Injectivity of rho gives the needed kernel inclusion. No non-elementary quotient or comparison lemma is hidden in this step.

For step 8 I read the entire flat-closed-fibre-kernel-rigidity statement and its project-source proof/docstring. It requires R,A_0,S local, S Noetherian, q and v surjective, j local, f_0 flat, the commutative square, and ker(v) contained in the extended maximal ideal of R. Steps 1, 4, 6 and 7 provide exactly these. It does not require flatness of R -> S or a finite residue extension. Its conclusion is exactly ker(v)=(ker q)S. The quotient isomorphisms therefore carry both coefficient structures and the map, and localness makes them continuous with continuous inverses. The T classes remain the specified parameter tuple of C_0.

I checked B–E of delivery-errors.md against these files: the new node is self-contained and statement-only, sources name actual tags and labels, its search records are actual logged calls, every used non-elementary fact is a node statement, no step uses the proof of another node as its interface, and no existing node was modified. Citations quote the full statements actually read. Every step is below 2000 characters. The source comparison corrected the tempting but invalid justification of compatibility by independent choices of Cohen fields; that argument is not present in the delivered proof.

Edge cases checked: A and B fields give e=s=0 and the identity residue presentations. A Artinian nonreduced, such as K[epsilon]/(epsilon^2), with B=L[epsilon]/(epsilon^2)[[T]], keeps the nonzero relation I=(X^2) rather than assuming A regular. For s=0, C_0=L and no T variables occur; for e=0, R=K and I=0 and the kernel argument gives Bhat=L[[T]]. Infinite transcendence degree L/K is permitted by 0322 and 07NJ. For the new node, d=0 forces a field, while C=k[[u,v]] with any generating pair and any coefficient section has the required parameter count. Nonregular rings such as k[[u]]/(u^2) are excluded by the new node's regularity hypothesis, so its conclusion does not assert a false regular presentation of singular rings.

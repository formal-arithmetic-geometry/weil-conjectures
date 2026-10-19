# Worker report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-generic-dominant-parts.json: item, statement, split into six steps; no exact Mathlib match.
- citations.json: every node cited in every step, with a verbatim statement quotation.
- report.md: this report and the author's review.

No new nodes; no Mathlib leaves created. The statement is unchanged. Added statement dependencies for generic points, scheme fibres, finite field extensions, and the reduced induced closed subscheme construction. The chapter and unit records were read and left unchanged because this is not a unit key node.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 checkout for the blueprint tag, finite generic fibres and dominant components; also checked dag/lean_names_upstream.json. The generic-point dominance lemma and Noether-normalization files do not state all the item's clauses. There is no lean_audit frontier on this newly created item.

## WANTED

None. The ILO PDF and all Stacks sources used are present.

## Findings and corrections

The item arrived with no proof. Its mathematical statement agrees with ILO Expose III Proposition 3.1(i),(iii), printed pp.37--38, and Expose II 1.2.5--1.2.6, printed p.25. The item isolates the finite-generic-fibre observation used in that approximation argument; no excellent/henselian or nonemptiness hypothesis is needed for this isolated observation. The existing lem-per-dominant-part-coreflection covers functoriality and the etale dominant-part identification; this delivery does not duplicate those clauses.

The field-finiteness lemma with a properness hypothesis, lem-pc-dim-zero-finite-over-field, was not used. The applicable existing node is lem-pc-algebraic-dim-zero-affine-finite, which only assumes finite type and dimension at most zero. Likewise no node defining etaleness was used alone for the nontrivial isolated-fibre-point theorem: the proof cites lem-weil-pbc-unramified-fibre-point-isolated. The empty scheme is treated separately where def-pc-dimension only defines dimension for nonempty schemes.

Mathlib searches were run only through the prescribed msearch.py command. The log records LeanFinder twice (whole item and etale-source phrasing), Loogle, grep, and LeanSearch. I read the returned declarations and the local IsFinite and LocallyQuasiFinite source definitions: they do not give the whole item by a one-line specialization. The inherited Q72 searches remain unchanged; the actual Q34 queries and results were appended. DAG keyword searches and blueprint_refs searches for dominant, finite generic, zero, and completely decomposed yielded existing tools but no equivalent blueprint node. No new node is needed.

## Not duplicates

No new-node/existing-node pairs: this delivery creates no nodes. Existing dominant-part-coreflection is cited, not restated as a new lemma.

## Unfinished work

None in the one-level split. Its cited unsplit prerequisites remain their own items.

## Review by Q34

I read ILO Expose II 1.2.5, the proof of 1.2.6, and 2.1.1 (printed pp.25--26), together with Expose III Proposition 3.1 and its proof (printed pp.37--38). I also opened the precise Stacks statements and proof passages: 01W5/lemma-closed-immersion-proper, 01T3/lemma-composition-finite-type, 01T4/lemma-base-change-finite-type, 01WH/definition-integral, 01JT/lemma-points-fibre-product, 02GO/lemma-base-change-etale, 02G7/lemma-unramified-over-field, 00KH/lemma-Noetherian-dimension-0, 06LH/lemma-algebraic-scheme-dim-0, and 01IS/lemma-scheme-sober. There are no new-node sources to audit.

Step 1 uses the actual statement of dominant-part-coreflection: its reduced closure is precisely the union in this item and is in the finite-type dominant subcategory. The closed-immersion-proper node explicitly includes finite type in its proper conclusion, and finite-type-composition-base-change states composition. The base S is Noetherian and T is finite type exactly as those hypotheses require; integrality supplies the unique base generic point. No separatedness is inferred or needed.

Step 2 uses finite-over-field-affine-finite-dim to obtain the actual K-algebra B, finite-dimensional-domain-is-field only on the nonzero domain B/p, the residue-field and spectrum definitions to identify its fraction field, and spec-irreducible-closed-subsets-primes to turn maximality of every prime into zero topological dimension. The topological dimension definition states the chain convention, including the empty case. Finite-type-composition-base-change gives finite type of T_eta, so finite-type-dim-zero-artinian applies and explicitly supplies discrete topology. The quotient spanning-set argument is elementary linear algebra, not a new lemma. No assertion that an arbitrary finite set is discrete is made.

Step 3 cites both halves of the fibre-product-point calculation: fibre-product-points gives the point above (t,eta), and fibre-product-point-residue-field gives the residue-field isomorphism compatibly with K. The latter statement was opened and checked; the former alone would not justify the field assertion. The closed immersion definition gives the affine quotient R/I, whose residues at q and q/I are the same field by the residue-field definition. Thus the argument proves finite extension for the actual component generic points without assuming T is reduced or integral. It does not apply the generic-fibre-finiteness criterion in the wrong direction.

Step 4 checks finite type of each V_j over S before base change; etale alone would not supply global quasi-compactness. Etale-scheme-base-change states the required theorem for arbitrary base change. The etale and unramified definitions imply the hypotheses of unramified-fibre-point-isolated, which explicitly says the point is isolated in the fibre subspace. Scheme-fibre states the necessary homeomorphism with the set-theoretic inverse image. Since Step 2 makes the base point open, the fibre subspace is open in W; hence the isolated point is open in W. This proves discreteness, without an implicit separatedness assumption or a claim that every quasi-finite morphism is finite.

Step 5 turns discreteness into zero topological dimension by the written closed-subset argument. Scheme-dimension-local-rings identifies that dimension with the local-ring dimension used by algebraic-dim-zero-affine-finite. That node has the finite-type hypothesis actually available from Step 4 and no properness hypothesis. Finite-over-field-affine-finite-dim supplies the precise affine/finitely-dimensional meaning of the conclusion. The empty source is finite by definition and is treated without appealing to a nonempty dimension definition.

Step 6 uses the full statements of fibre-product-points and fibre-product-point-residue-field, again separately: the zero prime of the explicitly identified tensor field yields a lift, and the residue comparison identifies its residue with kappa(t') through the second projection. The formula uses alpha inverse, which exists by complete decomposition; beta need not be an isomorphism for this argument. Etale-scheme-base-change supplies the etale clause. This actually proves the lifting property for arbitrary base change, specialized to the dominant closed immersion, so no extra descent theorem is hidden. Empty families over empty T and empty dominant parts are vacuous.

I checked B--E against the written files: there are no new statements to violate B1 or D1/D2; every non-elementary invocation has a node whose statement was read, and citations.json copies that statement verbatim. The proofs have no step longer than 2000 characters. A dependency walk found no path from any cited node back to this item. Off-unit generic scheme/algebra/topology tools are declared in split_report.tool_uses, preserving the ILO approximation route below the fixed Fourier-perverse unit. I tested T empty; T entirely vertical over S (empty dominant part); S a point with T=Spec(k[e]/e^2); several dominant and vertical components; empty etale source; and a nonseparated etale finite-type source. The latter is harmless because the argument uses discrete generic-fibre topology and finite type, not separation. No statement dispute or route change was found. The main repairs during this review were choosing the non-proper zero-dimensional finiteness node, including both point and residue comparison nodes, and treating the empty dimension case explicitly.

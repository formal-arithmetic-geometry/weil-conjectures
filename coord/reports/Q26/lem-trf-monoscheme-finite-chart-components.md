# Stage-1 report: lem-trf-monoscheme-finite-chart-components

## Files written

- dag/nodes/sec-trace-formula/lem-trf-monoscheme-finite-chart-components.json: statement unchanged; nine complete proof steps, with explicit sources and citation union; status split. Added the existing irreducibility and fraction-localization definition nodes to statement dependencies.
- citations.json: verbatim statement excerpts for every node cited in each of the nine steps.
- report.md: this report. searches.jsonl retains the actual Mathlib searches made by msearch.py. ilo.txt is a sandbox-only pdftotext reading aid and is not a delivery node.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are reused, rather than restated. The item splits entirely over existing supporting statements and direct elementary arguments.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for monoscheme, toric realization, monoid spectra and generic lattice terminology. The common generic lattice hits concern ideal sheaves and not monoid stalk groups. No project declaration states this item.

## WANTED

None. The ILO PDF and the Stacks source required here are present and were read.

## Problems found and changes

The live item was statement-only and the sandbox had no earlier node or report. There is no released repair note for this item. The statement is faithful to the cited ILO passages and needs no correction. I replaced no unit or chapter route. The assigned item is a retained supporting lemma on the historical alteration branch: the current latest blueprint proof of lem-trf-local-term-locality uses contracting correspondences, and I read that current proof rather than silently treating its old historical branch as its current proof. The item's existing blueprint ancestry and its precise from.place are preserved, and same_as remains empty after blueprint searches.

The arguments now distinguish the monoid generic point from the generic point of a scheme. In particular the realization of the open monoid singleton is the whole group-algebra torus, not a singleton scheme. I wrote the common-open gluing and the explicit localization map so that no unjustified transport or separatedness assumption is needed.

## Searches and reuse

Whole-DAG searches by title and statement located lem-trf-monoid-prime-minimal-neighborhood, lem-trf-fg-torsionfree-group-free, lem-trf-affine-monoid-unique-sums, lem-trf-unique-sums-algebra-domain, lem-weil-pbc-affine-open-section-vanishing-prime, lem-weil-pbc-spec-irreducible-closed-subsets-primes and lem-weil-pbc-affine-scheme-reduced-iff. I opened their statements, status, source and dependency lists. The first is already split; the other six are Mathlib leaves. Their statements supply precisely the inputs used, so no new monoid-topology, algebra-domain, or scheme-basic-open node is introduced. lem-trf-monoid-algebra-domain-fraction was also read; its stronger fraction-field conclusion is unnecessary, so its extra dependency branch is not used.

Ran blueprint_refs.py searches for monoscheme, monoid algebra, monoid spectrum, group algebra, torsion-free and localization and read the returned results; no blueprint node states the item. Ran ancestor for the item and retained the stated ancestor lem-trf-local-term-locality. The broad localization search returns many general tools and not this monoidal construction.

Actual msearch.py calls are retained in searches.jsonl and added to the item's mathlib_searches: LeanFinder with the item named in the query; Loogle for "Monoscheme"; grep for Monoscheme|monoidSpectrum|SpecMon|toric in AlgebraicGeometry; LeanSearch for fine-monoid realization and dense generic group completion; a second LeanFinder phrasing in terms of cancellative monoids and finite prime spectra; and a general grep for domain/basic-open/reduced declarations. Every service used answered successfully. Loogle's MonoScheme hits concern categorical monomorphisms of ordinary schemes. The semantic services returned ring spectra, profinite decompositions, topological group completions and finite-type group algebras. None gives the complete item. The useful general domain and basic-open inputs already have the existing DAG nodes listed above. There are no newly created nodes whose search records need separate certification.

## Not duplicates

No new nodes. In particular, the generic group freeness, affine monoid unique sums, domain criterion and scheme-localization facts are citations of existing nodes. I did not make nodes for the item's own components or generic-torus clauses, or for elementary finite-generator and fraction computations.

## Review by Q26

I read ILO, Expose VIII 3.1.2--3.1.4, 3.1.9--3.1.10(ii), Proposition 3.2.2 and 3.2.4, printed pp.98--100,103, plus the opening monoid-domain argument of Lemma 3.2.12(ii), p.104. These give respectively the finite prime topology, unique maximal generalizations, torsion-free stalk condition, localization-compatible realization and generic torus. I read the Stacks algebra.tex statement/proof lemma-irreducible (00ES), schemes.tex lemma-standard-open-affine (01I3) with the localization sheaf construction (01HV), and lemma-affine-reduced (01J2). No SGA source is used. The proof follows these passages, with the finite coefficient and fraction calculations written out.

Step 1 uses the face-generator statement of lem-trf-monoid-prime-minimal-neighborhood, not a definition pretending to be a finiteness theorem. A face is generated by exactly the chosen generators it contains, so prime ideals inject into a finite powerset. Its hypotheses require only a fine monoid and a finite tuple, which each chart supplies. The finite union argument is elementary.

Step 2 uses the actual prime/basis definition in def-trf-fine-fan-blowup and the chart definition in def-trf-monoscheme-toric-realization. I proved directly that the empty prime belongs to every nonempty open and that any other prime is excluded by a basic open. Openness forces every generalization of a point to remain in any chart containing it. This checks independence of the chart and rules out a hidden global separatedness hypothesis. The component partition is clopen because each chart has one generic point; irreducibility, connectedness and maximality are then checked from the explicit definitions in def-weil-irreducible-components and def-weil-connected-scheme. This step is elementary topology with its argument present, not an appeal to a general local-irreducibility theorem.

Step 3 uses the smallest-neighborhood and localization clauses of lem-trf-monoid-prime-minimal-neighborhood at the empty prime, where F=P, to identify the stalk with P-P. The sheaf's germ maps give the canonical overlap identifications. Finite generation is by the chart generators as group generators. Torsion freeness is exactly the monoscheme assumption at the generic stalk, so the hypotheses of lem-trf-fg-torsionfree-group-free hold. Its statement supplies the finite basis; it is not used for any unrelated splitting of units.

Step 4 checks all hypotheses of lem-trf-affine-monoid-unique-sums: finite generation, cancellation from the injection into the group completion, and torsion freeness from that group. The unique finite-pair assertion then matches exactly the hypothesis of lem-trf-unique-sums-algebra-domain. The coefficient ring is a field, hence a nonzero domain. Applied also to the group as a monoid, this needs positive and negative group generators; I included that check. Finite algebra generation is the explicit monomial-product formula and finite linear support, with no unjustified noetherian or saturation hypothesis.

Step 5 uses the face clause of lem-trf-monoid-prime-minimal-neighborhood and the localization definition, and writes the inverse of each generator in P-N a. This is an elementary calculation, not a new localization lemma duplicating the item's clause. The same generator test identifies the generic open as the singleton empty prime, also for the empty tuple.

Step 6 explicitly checks the asserted ring isomorphism from the fraction-equivalence definition in def-weil-ring-localization-away and the monomial algebra definition in def-trf-monoscheme-toric-realization. Coefficient extension is injective, fraction equality is preserved by multiplication by units, and each group exponent has the form p-ma by Step 5. Finite sums give surjectivity. Agreement on each monomial and inverted monomial checks compatibility with further localization. No mere equality of fraction fields substitutes for the actual localization-ring isomorphism.

Step 7 takes precisely clause (b) of lem-weil-pbc-affine-open-section-vanishing-prime: basic opens are affine with the stated localization ring and restriction map. The localization-compatible gluing is the construction explicitly present in def-trf-monoscheme-toric-realization. Every chart overlap of the same component contains its intrinsic generic open, and its restriction acts as the identity on the common stalk. This proves that the realized tori coincide. The construction uses the open monoscheme inclusion, rather than an invalid inference that a scheme morphism factors through a subscheme from its set image. The disjoint union argument follows from the absence of overlaps between different clopen pieces. This generic-open gluing is written out, not cited from the proof of some other node.

Step 8 uses exactly the closure and irreducible-closed-set clauses of lem-weil-pbc-spec-irreducible-closed-subsets-primes. Both chart and group algebras were proved to be nonzero domains in Step 4; thus zero is a prime, V(0) is the whole space, and e^a is outside the zero prime. These checks give nonemptiness and density, without assuming a monomial is nonzero in an arbitrary ring. I supplied the short closed-cover argument that a dense irreducible subspace forces irreducibility of the ambient component, and the definitions give connected-component maximality.

Step 9 uses lem-weil-pbc-affine-scheme-reduced-iff in its actual direction from a reduced ring to a reduced affine scheme. Domains are reduced, and every local ring is computed in an open chart, so reducedness glues immediately by the local-ring definition in def-pc-reduced-scheme. The reduced-and-irreducible equivalence is explicitly stated in def-pc-integral-scheme. The finite-affine-cover criterion is explicitly in def-weil-finite-type-morphism. Thus no theorem is borrowed from a node that merely defines an unrelated notion. The six general supporting results from other units are already Mathlib leaves; the only non-Mathlib theorem input, the monoid prime neighborhood lemma, is in this item's unit. No off-unit nonleaf tool authorization is needed.

I checked small cases: the empty monoscheme (empty realization and no components); P={0} with no generators (a=0, all localizations are identities and the torus is Spec k); P=Z^r (one monoid prime, all chart algebra generators invertible); P=N (the usual dense G_m in A^1); P=<2,3> in Z (the nonsaturated cusp, which is a domain but is not claimed normal); two copies of Spec_mon N glued at the generic point (a nonseparated realization still has a common dense torus and is integral); and a finite disjoint union of these examples. Repeated generators and unit generators do not affect inversion of their sum. The arguments use neither sharpness nor saturation, algebraic closure, smoothness, nor separatedness.

I checked delivery-errors B--E against the files and sources. There are no unsplit new nodes with proofs, no missing new-node notions, no hidden elementary nodes, and no clause moved into a fresh wrapper. Every non-elementary fact is an existing cited statement. Every use has a literal quote in citations.json. All nine steps have at most 1005 characters, so none exceeds the 2000-character review threshold or hides a long standard subargument. Statement dependencies and proof dependencies have been audited separately, and proof_deps is exactly the union of step uses. No imported or maintainer-owned field was edited. The statement itself is unchanged.

## Unfinished work

None for this one-level stage-1 split. All proof inputs are existing DAG nodes. Required server dry run and push follow this report; no Lean code, compiler, Lake command or build was run.

1. Files written:
- dag/nodes/sec-trace-formula/lem-trf-valuation-finite-module-injectivity.json — repaired five-step proof of Tag 0GSG.
- dag/nodes/sec-trace-formula/lem-trf-valuation-general-mod-injective.json — replaced the former valuation-ring special case by the faithful Tag 046Y statement; Mathlib searches found no match.
- dag/citations.json and citations.json — verbatim quotations for every cited node in Steps 1–4.

2. Attachments: none.

3. WANTED: none.

4. The returned D1/D5/E1/C4 fault was repaired. The old helper repeated the item's finite-module situation and cited Tag 046Y without stating its hypotheses. It now states the local-ring criterion with \(S\) explicitly essentially of finite presentation (a localization of a finitely presented \(R\)-algebra), both modules finitely presented over \(S\), the target flat over \(R\), and injective reduction modulo \(\mathfrak m_R\). The item proof now follows Tag 0GSG in the required order: represent \(B\) by a quotient of \(P_{\mathfrak q}\), check explicitly that \(A\to P_{\mathfrak q}\) is local, approximate \(N\) over \(P_{\mathfrak q}\), apply Tag 0GSE(2) to \(M\), apply Tag 046Y with source and target exchanged, and identify \(N_\lambda\) with \(N\). The old incorrect claim that \(u\) factors through \(N_\lambda\) was replaced by the direct definition \(u_\lambda=u\circ\pi_\lambda\). No duplicate node was found for Tags 0GSG, 0GSE, or 046Y; the existing 00ME node is the Noetherian criterion and is not the same statement. No SGA source is used.

5. Nothing remains unfinished.

## Review by Q147

I reread more-morphisms.tex Tag 0GSG (the statement and all five relevant proof paragraphs), more-algebra.tex Tag 0GSE(2), and algebra.tex Tag 046Y. The item's statement still agrees with 0GSG: valuation ring, local essentially finite type map, finite modules, flat target, injective closed fibre, and the two conclusions are unchanged. The repaired helper agrees hypothesis by hypothesis with 046Y after writing its source as \(M\), target as \(N\), and explicitly defining “essentially of finite presentation” by a localization of a finitely presented algebra. The finite-module approximation node agrees with the second paragraph of 0GSG, and the flat finite-presentation node agrees with 0GSE(2).

Step 1 cites the definitions of essentially finite type, finite type, and finite presentation. I checked that the source reduction gives a quotient \(P_{\mathfrak q}\twoheadrightarrow B\), that the quotient is local, and that locality of \(A\to B\) therefore makes \(A\to P_{\mathfrak q}\) local; the polynomial algebra and its localization give the helper's essentially-finite-presentation hypothesis. Step 2 cites exactly the approximation node: its finitely presented modules, surjective transitions, colimit, and eventual closed-fibre isomorphism are the facts used, and the map \(u_\lambda\) is correctly defined by composition with the colimit surjection. Step 3 cites 0GSE(2) for the finite flat target \(M\) over the new local algebra \(P_{\mathfrak q}\). Step 4 cites the repaired 046Y node and checks the local map, essential finite presentation, finite presentation of both modules, flat target, and injective closed-fibre hypotheses one by one; the source/target exchange is explicit. Step 5 is the elementary kernel argument showing the chosen surjection is an isomorphism and transports the cokernel flatness. Every citation quotation in citations.json is verbatim from its node statement.

I reran the required LeanFinder, LeanSearch, Loogle, and Mathlib grep searches for the repaired helper and the item; none states either criterion. I searched the DAG and both blueprint snapshots for the Tags 046Y/0GSE/0GSG statements and for the key terms before retaining the existing three auxiliary nodes. Edge checks include a field valuation ring, \(B=A\), \(N=0\), free \(N\), identity maps, and the polynomial-localization reduction; the conclusions reduce as expected. The previous review's unsupported 046Y citation and missing \(P_{\mathfrak q}\) locality check are the corrections made here.

## Not duplicates

- lem-trf-valuation-general-mod-injective vs lem-trf-valuation-finite-module-injectivity: the repaired node assumes a local map essentially of finite presentation and finitely presented source and target, while the item starts with an essentially finite type map and merely finite modules and performs the approximation and polynomial-localization reduction.
- lem-trf-valuation-flat-finite-module-presentation vs lem-trf-valuation-general-mod-injective: the former only proves finite presentation of one flat finite module over an essentially finite type algebra; the latter proves injectivity and flatness of a cokernel under a fibre condition for two finitely presented modules.
- lem-trf-valuation-finite-module-fp-reduction vs lem-trf-valuation-finite-module-injectivity: the new node only supplies a filtered finitely presented approximation of a finite module with eventual closed-fibre isomorphism; the item proves injectivity and flatness of the cokernel after applying that approximation.

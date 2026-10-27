# Stage-1 delivery: lem-sfb-reductivity-eventual-ring-colimit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-reductivity-eventual-ring-colimit.json: existing statement, split in six steps; statement and statement dependencies unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-geometric-neutral-reductivity-field-invariance.json: new statement-only field-extension lemma and its fibrewise base-change consequence; unsplit, no Mathlib match.
- citations.json: one exact statement quotation for every node cited by each numbered proof step.

One new node, zero Mathlib leaves. The scratch text milne.txt and write_split.py are research aids only, not DAG delivery files. All writes were confined to this item's sandbox. No Lean was written, no compiler or Lake command was run, no repository git command was run, and no agents were started.

## Attachments

None. The exact blueprint tag and reductiv/Reductiv searches in lean/WeilConjectures found only unrelated reductive Lie-algebra material. No declaration there proves the group-scheme assertion.

## WANTED

WANTED: Brian Conrad, Reductive group schemes (2014), local file literature/conrad-reductive-group-schemes.pdf, Corollary 3.1.11 pp.88-89, Proposition 3.1.9 pp.85-88, Exercise 3.4.1 p.104, for this item and the new node. Read the Stanford PDF online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. Milne's Algebraic Groups (2017) is present locally and Proposition 1.34 was read there. No SGA source was used.

## What was wrong or missing

The imported item has a correct statement but no proof. The point requiring care is that openness in Conrad Proposition 3.1.9 concerns reductivity of the geometric identity component, not connectedness of the entire fibre. The split therefore treats connectedness separately using existing Stacks 055I and 055F nodes and the 05F4 limit lemma. It never assumes a non-Noetherian reductive locus is quasi-compact. For the closed-complement argument I used the existing Stacks 0A2W spectral compactness node, in place of reproducing Conrad's radical-ideal colimit calculation. This is the same reductive-locus route and does not change any unit-level step.

The nearest-blueprint-ancestor tool returns null, as in the imported item. I retained that inherited null ancestor and its complete via chain, and gave the new node its parent item plus that chain. I read the current latest unit statement and proof and chapter record. No current blueprint node states reductivity descent or the new field-invariance lemma (blueprint searches reductive, reductivity, reductive geometric, identity component, and field extension reductivity). The inherited place traces this supporting result to the direct-image alteration branch and the spread split reductive model before recovering its torus/pinning. No chapter/unit files changed.

## Not duplicates

lem-sfb-geometric-neutral-reductivity-field-invariance vs lem-sfb-reductivity-eventual-ring-colimit: the new lemma concerns field extension and invariance of a fibre property; it has no directed ring system, openness or eventual-stage conclusion.
lem-sfb-geometric-neutral-reductivity-field-invariance vs lem-sfb-reductive-torus-fibre-openness: openness varies a fibre over an open neighbourhood of a fixed base; the new lemma compares one fibre over different extension fields and supplies exact pullback equality, which the openness node does not state.
lem-sfb-geometric-neutral-reductivity-field-invariance vs lem-sfb-maximal-torus-field-extension: the latter compares maximal tori under field extension and does not state reductivity invariance.
lem-sfb-geometric-neutral-reductivity-field-invariance vs lem-weil-pbc-geometric-component-count-base-change: the latter compares numbers of connected components, not reductivity of their identity component.
lem-sfb-geometric-neutral-reductivity-field-invariance vs def-wf-algebraic-components: that blueprint definition concerns characteristic-zero matrix groups and does not give a theorem on reductivity or arbitrary field extension.
lem-sfb-geometric-neutral-reductivity-field-invariance vs lem-wf-algebraic-component-cosets: the coset theorem concerns components, not field-extension invariance of reductivity, and uses characteristic-zero matrix-group conventions.

lem-sfb-geometric-neutral-reductivity-field-invariance vs lem-sfb-split-reductive-finite-diagram-model: finite-diagram spreading along ring colimits is not reductivity invariance under extension fields.
lem-sfb-geometric-neutral-reductivity-field-invariance vs lem-sfb-reductive-framed-noetherian-descent: framed Noetherian approximation of reductive groups is not the neutral-component field-invariance assertion.

The source-place search also finds the parent lem-sfb-split-reductive-finite-type-spreading, which cites Conrad 3.1.11 precisely as an input and does not state the new lemma. No new Stacks-tag overlap was introduced: Stacks does not state this group-theoretic field-invariance result. DAG source/place and statement searches found no existing equivalent.

## Mathlib searches

searches.jsonl records the actual commands and responses. The new node records both semantic phrasings (base-change invariance of reductive geometric neutral fibres; reductivity under extension of algebraically closed fields), Loogle's GroupScheme query, the grep in AlgebraicGeometry, and LeanSearch's locus-pullback query. Responses were successful, not unavailable. The semantic hits concern geometrically reduced algebras, finite-group representations and Lie algebras. LeanSearch also gives ordinary scheme group-object pullback and general affine/smooth base-change declarations, which do not assert invariance of reductivity. Loogle and the source grep returned no group-scheme reductivity match. These names/types were read in the responses. No hit states the new node or specializes to it in one line. The item retains its earlier actual searches, and also records this run's semantic eventual-stage search, which returned affine-limit and reduced-scheme results, not reductivity.

## Review by NP

I read Conrad Corollary 3.1.11 and its complete proof on printed pp.88-89, the statement of Proposition 3.1.9 on p.85, and Exercise 3.4.1(i)-(iii) on p.104. I read Milne Proposition 1.34 and its proof on pp.16-17 and his definition 6.46 on p.135. For the supporting topological arguments I read Stacks limits.tex at lemma-limit-contained-in-constructible (05F4), topology.tex at lemma-inverse-limit-spectral-spaces-nonempty (0A2W), and more-morphisms.tex at lemma-nr-geom-connected-components-constructible (055I), including its proof. The item is marked agent-origin because I supplied the spectral-compactness implementation of Conrad's closed-complement argument.

For the new statement, Milne 1.34 supplies compatibility of identity components with arbitrary field extension. Conrad Exercise 3.4.1 proves preservation of reductivity between algebraically closed fields: spread a nonzero smooth connected normal unipotent subgroup and its additive composition series over a finite-type subalgebra and specialize at a rational point. The converse detects an existing nonzero unipotent normal subgroup after the faithfully flat field extension. Passing through an algebraic closure inside a common algebraically closed overfield gives the arbitrary-field formulation. Applied to residue-field extensions this is exactly the pullback assertion Conrad uses in Corollary 3.1.11. This argument is recorded here as the intended future split, not hidden as a proof inside the new statement-only node. No eventual-stage descent theorem is used to prove the field-invariance input.

I opened the statement of every cited node; citations.json quotes those statements without alteration. Here is what each step actually takes:

1. The affine-transition limit node gives the scheme limit and its Spec-of-colimit description; affine-scheme-qcqs gives exactly both compactness and quasi-separatedness. The smooth clause of lem-pc-proper-base-change, the affine clause of affine-morphism-permanence, and clause (3) of qcqs-morphism-permanence preserve the three model properties. The group-operation diagrams are exactly those in def-sfb-pinned-split-root-realization and base change by the fibre-product universal property. The cofinal tail argument is written explicitly. All these nodes apply to arbitrary schemes/ring maps.
2. Reductive-torus-fibre-openness supplies open neighbourhoods of all reductive identity-component fibres; I use only its first clause, requiring no torus. The new field-invariance node supplies equality, rather than just containment, of the inverse-image loci. The definition of reductivity gives U=S from the hypothesis on H. Complements then satisfy the same pullback identities by set theory.
3. Qcqs-scheme-spectral applies because of step 1. The spectrum-limit node expressly states inverse images of quasi-compact opens are quasi-compact; specializing it to a two-object system establishes spectrality of each transition. The definitions of spectral space and constructible topology show directly that the latter refines the Zariski topology, so each Z_i is closed there. The 0A2W node gives a compatible family if all Z_i are nonempty. The same spectrum-limit node identifies compatible primes with an actual point of Spec A, contradicting its empty inverse image of Z_i. The transition maps need not be surjective, flat or injective on rings. Once one Z_a is empty its inverse images are empty at every later index.
4. The geometric-connected-fibre-locus node gives local constructibility of E_1 for finite presentation; it does not by itself claim global constructibility over arbitrary bases. I explicitly use locally-constructible-qcqs-global to get global constructibility over our affine stage. The geometric component-count base-change node gives the exact inverse-image identities for H and every H_i. Group fibres have their identity point, so E_1 is precisely the connected-fibre locus. This step does not cite a definition as evidence for constructibility.
5. The 05F4 node is applied to that constructible set with the actual scheme limit of step 1; the small directed tail, affine transitions and qcqs stages meet all its hypotheses. Its conclusion is image containment for every sufficiently late stage, exactly what the step uses to obtain connected fibres by step 4.
6. Directedness gives a common upper bound for the two thresholds. A connected geometric fibre is its entire identity component. The already-proved properties and the cited definition therefore give reductivity over every point of each later spectrum. This is the only assembly step marked elementary.

I tested the trivial group and rank-zero case (all loci are total); a disconnected finite smooth group (neutral fibres are reductive but connectivity is not automatic); and a system starting with k x k and passing to k by projection, with G_m on the retained component and G_a on the discarded one. That example checks noninjective maps and removal of bad fibres only eventually; it is itself a flat projection. Separately, the nonflat specialization k[t] to k, t mapping to 0, with a constant G_m model checks that no flatness assumption enters. A second discarded component can instead carry a nontrivial finite constant group to test the connectedness argument separately. Algebraically closed field extensions in positive characteristic and imperfect original fields are covered by geometric, rather than pseudo-reductive, hypotheses. No new statement needed correction. All six steps are below 2000 characters; none conceals a further comparison lemma: the required field comparison is the new node, and the two limit tools are already cited nodes.

The off-unit nodes listed in split_report.tool_uses are generic topology, scheme permanence and limit tools, not substitutes for a unit's proof. In particular the node filed under sec-trace-formula is only the general qcqs local-to-global constructibility lemma; it uses no trace formula in its statement. The spectrum-limit node under sec-deligne-laumon-a1 is only the prime-spectrum limit theorem, not a weight result.

## Unfinished work

No part of this one-level split remains unfinished. The single new node intentionally has no proof and joins stage 1 as an unsplit input. Delivery still requires the tool's successful dry run and push.

# Worker report: lem-per-henselian-finite-extension-topology

## Files written

All paths below are in this item's Q09 sandbox, relative to it.

- `dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-finite-extension-topology.json`: item, statement, split; original statement and metadata retained, four proof steps, searched again, no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-valuation-normalization-localizations.json`: new statement, unsplit, no Mathlib match; general normalization/prolongation correspondence without henselianity.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-valuation-coarsenings.json`: new statement, unsplit, no Mathlib match; permanence of henselianity under coarsening.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-algebraic-valuation-coarsening-correspondence.json`: new statement, unsplit, no Mathlib match; torsion of the value-group quotient and restriction of coarsenings.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-valuation-topology-common-coarsening.json`: new statement, unsplit, no Mathlib match; topology comparison through a proper common valuation overring.
- `citations.json`: one entry per use in each numbered item step, quoting the cited statement verbatim.

`searches.jsonl` is the search command's unmodified record. `write_split.py` is a sandbox-only generation script, not a project tool or delivery file. No Lean files, builds, compilers, live repository files, or launcher scripts were changed.

## Attachments

None. Searched the project Lean under `WeilConjectures/` for the exact blueprint id and henselian/valuation/extension/topology terms, including the FieldTheory and valuation directories. No declaration stating the whole item, or the proposed general valuation facts, was found. Henselian etale sheaf results are unrelated. The reference master is not treated as proof evidence.

## Wanted sources

WANTED: Bourbaki, Commutative Algebra, Chapter VI, §§4 and 8 (valuation coarsenings, topologies and extensions), for all four new lemmas and the valued-field background of lem-per-henselian-finite-extension-topology. The item itself already identifies this source as unavailable locally. I read ILO XX 4.4, printed pp.373–374, which explicitly invokes forms of Krasner and Bourbaki VI §8 exercises 12 and 14(a), but does not give these four auxiliary theorems. I do not claim to have read Bourbaki. The item proof is marked agent-written; the new nodes are statement-only queue items, with this bibliographic limitation disclosed in their source fields. No missing document was downloaded.

## Corrections and scope

No statement dispute: every original clause is retained, including arbitrary rank, finite possibly inseparable extensions for prolongation, and the topology-only quantifier in the separable clause. The original item had no proof. In particular, uniqueness of a prolongation of a fixed valuation does not by itself prove uniqueness relative to a base topology. A rank-two refinement of a rank-one valuation may have the same topology but a different valuation ring. The proof now handles precisely that distinction through common coarsenings, and never assumes the competing base valuation is henselian. Only the coarsening of the original henselian valuation is shown henselian.

The existing general connected-integral-algebra permanence result is reused, rather than creating a domain-only duplicate of Stacks 092X. There is no claim that the integral closure is finite as a module, or Noetherian, or a DVR. The new normalization theorem explicitly permits nonfinite normalizations and inseparability. The final argument happens to work for finite inseparable extensions too; this is a proof observation, not a change to the item's statement.

The chapter and unit records were read, together with the main-20261015 ancestor and unit markdown. This is background for the already recorded chain from the affine-curve duality step through completion/open rigidity to dense henselian field comparison. It changes no chapter or unit route. The integral-henselian permanence statement from another unit is declared as a generic tool in split_report.tool_uses.

## Not duplicates

lem-per-valuation-normalization-localizations vs lem-weil-pbc-valuation-ring-normal: the existing Tag 00IC statement only proves that a valuation ring is integrally closed in its own fraction field. The new node describes its integral closure in a finite larger field and classifies prolongations by maximal localizations; normality alone does not assert this.

lem-per-valuation-normalization-localizations vs lem-trf-sepclosed-valuation-geometric-components: the existing statement assumes the fraction field separably closed and proves separable closedness of residue fields and geometric integrality/component behavior of schemes. It does not describe the integral closure in a finite arbitrary field extension or classify prolongations. Tag 00IC is only background in both sources.

lem-per-valuation-normalization-localizations vs lemma-nagata-valuation-ring-extension: the existing node only supplies some prolongation to an arbitrary field extension; it does not identify the prolongations with maximal localizations of the integral closure. The new node has no henselianity hypothesis and does not claim uniqueness of the prolongation; the item's Step 1 derives uniqueness using locality.

lem-per-valuation-normalization-localizations vs lem-trf-integral-component-henselian-permanence: the existing node treats connected integral algebras over a henselian local base; it does not identify normalization localizations as valuation rings. The proof uses both assertions, with their different hypotheses.

lem-per-valuation-normalization-localizations vs def-fin-normalization-extension: the latter defines scheme normalization by integral closure; it does not classify valuation prolongations.

lem-per-valuation-normalization-localizations vs lemma-nagata-local-domain-valuation-dominates: domination existence (Stacks 00IA) gives neither the normalization-localization classification nor its converse. The tag is mentioned only as partial background in the new node source.

lem-per-valuation-normalization-localizations vs def-trf-valuation-ring: the latter is only the x-or-inverse definition, not the normalization theorem. The shared valuation-section tag is background only.

lem-per-algebraic-valuation-coarsening-correspondence vs lem-trf-valuation-prime-convex-correspondence: the existing node identifies primes and convex subgroups for a single valuation ring. It has no field extension and does not say that restriction of overrings is bijective in an algebraic extension or that the quotient of value groups is torsion.

lem-per-henselian-valuation-coarsenings vs lem-trf-integral-component-henselian-permanence: overrings/coarsenings are generally localizations and need not be integral over the original ring. Integral permanence cannot replace coarsening permanence.

lem-per-valuation-topology-common-coarsening vs lem-per-henselian-finite-extension-topology: the new lemma compares two valuations on a single arbitrary field, without a field extension or henselianity. It does not assert the unique topology on an algebraic extension; Step 4 establishes that by lifting the common coarsening and identifying its prolongations.

lem-per-henselian-valuation-coarsenings vs lem-per-henselian-finite-extension-topology: the new lemma concerns a valuation overring in the same field; none of the item's conclusions concerns such overrings.

lem-per-algebraic-valuation-coarsening-correspondence vs lem-per-henselian-finite-extension-topology: the new lemma assumes a given prolonged valuation and transports its coarsenings; it gives neither existence nor uniqueness of prolongations nor uniqueness of their topology.

Before creating files I searched the whole DAG statements for prolongation, coarsening, valuation normalization and integral-closure/localization language, and the whole blueprint with blueprint_refs.py for valuation, valuation topology, henselian valuation, valuation integral, integral closure, valuation extension, coarsening, value group and prolongation. Existing same-tag/background statements were opened, in particular the Nagata extension node, the connected integral permanence node, and the prime/convex correspondence node. No existing statement supplies any entire new lemma.

## Review by Q09

I read the worker brief and delivery-errors B–E in full, then checked the actual files against them. The source read for the item is ILO XX 4.4, especially the sentence on printed p.374 reducing the comparison to dense henselian valued fields and the reference to Bourbaki forms of Krasner. For the normalization input I also read the local Stacks valuation section (algebra.tex, Tag 00I8), including Tag 00IA, label lemma-dominate, and Tag 00IC, label lemma-valuation-ring-normal. These are supporting background, not a substitute for the missing normalization/prolongation theorem. For the henselian integral step I read more-algebra.tex, Tag 092X, label lemma-integral-over-henselian, statement and proof. For algebraic coarsenings I read the valuation-ring restriction/localization statements in that same local Stacks valuation section (0AAV and 088Y), and Mathlib's explicit primeSpectrumEquiv source. For the topology comparison I read the ILO valued-field passage; the full textbook background is missing and WANTED, so I checked the assertion directly as described below. The four source fields carefully distinguish direct source content from missing background; they do not attribute these whole assertions to the smaller Stacks lemmas.

Step 1 cites the complete statement of the new normalization lemma and the existing integral-component permanence lemma. I read the latter's statement: it requires a nonzero integral algebra with no nontrivial idempotent, not a finite algebra. The new normalization lemma supplies a domain integral over V, so these hypotheses hold. The displayed factorization e(e−1)=0 verifies the idempotent condition. The normalization lemma explicitly supplies both directions of the maximal-localization classification, so locality proves uniqueness without using anything hidden in the proof of a cited node. Localization at the unique maximal ideal adds only inverses of units, a direct calculation. No finiteness of the normalization is smuggled in.

Step 2 cites only the new algebraic coarsening correspondence, specifically its torsion assertion. I checked the arithmetic in an arbitrary totally ordered abelian group: if nδ lies in Γ then n max(δ,0) does too, and adding any positive ε from Γ gives a Γ-threshold strictly above δ. This yields cofinality without selecting a cofinal sequence or using an Archimedean estimate. Equality of intersections of balls then proves the subspace-topology clause directly.

Step 3 uses exactly the same torsion assertion for the competing valuation, then the two new comparison/permanence statements. The finite algebraic extension is still E/F. If the restricted valuation were trivial, the torsion quotient and ordered-group torsion-freeness force the extended valuation to be trivial, giving a discrete induced topology, contrary to the nondiscrete topology of a nontrivial valuation. Thus the positive ε needed in the cofinality argument exists. The common-coarsening theorem applies to the actual restricted valuation topology after this check, rather than conflating it with the induced topology in advance. Its conclusion is a proper valuation overring U of both base rings. The henselian-coarsening statement applies because V, not the competing V_w, is henselian. This avoids assuming henselianity is a topological invariant.

Step 4 cites all four statements it uses: the algebraic correspondence to obtain U_W and U_C, the normalization classification and existing henselian integral permanence to prove they are the same ring, and the common-coarsening/topology criterion on E. The correspondence explicitly preserves properness. U is henselian by Step 3, so the two prolongations of U are compared by the fully written local-normalization argument, not by an invocation of the item under proof. The common overring in E is proper and both valuations are nontrivial, which are precisely the hypotheses of the topology criterion. Each cited statement was opened; citations.json quotes it verbatim.

Small cases and prospective auxiliary proofs were checked before treating the new statements as usable. For normalization: E=F gives C=V and the sole maximal localization V; a nonhenselian field can have several prolongations, and the statement allows several maximal ideals. Finite inseparable extensions are allowed; no separable trace or primitive element argument is being used. For coarsening permanence: U=V is immediate, and U=K is a field, hence henselian; localizations of arbitrary henselian rings were not substituted for this valuation-specific result. For algebraic coarsenings: E=F gives the identity bijection, and Γ=Z inside (1/e)Z gives the expected torsion quotient and the same convex-subgroup lattice. In general a polynomial relation for x has at least two terms of minimal valuation, yielding (i−j)w(x) in the base value group; convex-subgroup saturation then explains the correspondence. For the topology criterion: equal valuations work, a rank-two refinement and its nontrivial rank-one coarsening have equal topologies, while independent p-adic and q-adic valuations on Q have no proper common valuation overring. The properness condition is essential and is included.

For a direct sanity check of the topology criterion: if V1,V2 induce the same topology, choose a v2-ball contained in the v1-maximal ideal. Taking inverses bounds v2 below on V1. Every element of the ring generated by V1 and V2 is a finite sum of products ab with a in V1 and b in V2, so the same lower bound holds on the generated ring. It is therefore proper, since a nontrivial value group is unbounded below; it is a valuation ring because it contains V1 and every nonzero field element or its inverse lies in V1. Conversely, a proper common overring is a nontrivial quotient valuation of either value group; representatives of quotient thresholds give mutually cofinal balls. This comparison is kept as its own statement-only node rather than hidden in a long item step. The integral-normalization and coarsening facts are substantive background, not relabelled clauses of the item and not elementary two-line nodes from already cited statements.

All new nodes have complete standalone statements, definition dependencies, no proof, and no proof dependencies. Every one has actual leanfinder, leansearch, loogle and grep searches, plus a second conceptual phrasing; I read the printed hits. The no-match conclusions distinguish stronger valuation equivalence from equal topology and complete/discrete special cases from arbitrary rank. The invalid initial Loogle pattern containing IsTorsion was corrected to ValuationSubring, Algebra.IsAlgebraic; the corrected actual query is the one recorded on the node. No unavailable service is counted as evidence of absence. Existing source searches copied with the item are preserved, and no searches were invented.

No item step exceeds 2000 characters (lengths 1022, 825, 1041, 1084 at writing). I checked that no step conceals another comparison theorem: the normalization and all three coarsening/comparison facts are explicit nodes, while the remaining arguments are domain idempotents, inverses of units, an ordered-group inequality, and intersections of balls. All external proof uses are declared; no elementary label is used to hide a lemma. The new nodes have exact ancestor/via provenance and searched same_as fields. The original item's statement, citations and old search records were retained. The sandbox was initially empty, so there was no earlier proof or report to overwrite.

## Remaining work

The four new statements intentionally remain unsplit for their own queue items. Their missing textbook source is disclosed above. This worker completed a one-level split, not their later formalization. Final server checks and delivery results follow below.

The first full dry run requested two additional same-tag comparisons (00IC). I opened both complete statements and added the two explicit distinctions above; neither is a substitute for the new normalization lemma. The stand-alone server review_split check passed.

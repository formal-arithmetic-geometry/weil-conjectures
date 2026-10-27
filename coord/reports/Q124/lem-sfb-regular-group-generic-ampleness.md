# Worker report — Q124

Item: lem-sfb-regular-group-generic-ampleness. Stage 1 only; no Lean files, compiler, Lake, repository or launcher files were changed.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-regular-group-generic-ampleness.json: corrected disputed statement and six-step split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-ample-power-extension.json: statement-only Raynaud input; no Mathlib match.
- citations.json: eight verbatim quotations, one for each step/node citation.
- report.md: this report. searches.jsonl contains the actual launcher search records, retained across interruptions.

## Attachments

None. The project-source searches for the blueprint tag, generic ampleness, Raynaud, semiabelian and symmetric line extensions did not find a finished declaration stating this item. The existing field-only group quasi-projectivity declarations do not suffice. No Mathlib leaf was identified.

## Missing local literature

WANTED: Michel Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes, LNM 119 (1970), XI Theorem 1.13, especially the ample extension of a power of a symmetric generic line, for lem-sfb-symmetric-ample-power-extension. Proposed local citation path: literature/raynaud-faisceaux-amples-LNM119-1970.pdf. It does not exist in the read clone.

WANTED: Pierre Deligne, Le lemme de Gabber, Asterisque 127 (1985), Sections 4.1–4.3 and 4.8, printed pp.141–144, for the item and its canonical Picard-line application. The node's inherited local PDF path is absent. I read these sections online at https://www.numdam.org/item/AST_1985__127__131_0.pdf .

WANTED: Laurent Moret-Bailly, Pinceaux de varietes abeliennes, Asterisque 129 (1985), VI Proposition 3.1 and Remark 3.1.1, for checking the symmetry issue and the connected-fibre uniqueness argument. The original PDF is too large for the web reader. I read the author's corresponding Proposition 3.1 and Remark 3.1.1 in the indexed text of his 1984 thesis, Familles de varietes abeliennes, printed p.137: https://www.numdam.org/item/BJHTUP11_1984__0154__P0_0.pdf . The argument explicitly assumes symmetry, invokes Raynaud XI 1.13 and uniqueness in the connected case, and leaves the nonsymmetric case open.

WANTED: Kenz Kallal, Ampleness of non-symmetric line bundles on degenerations of abelian varieties, arXiv:2610.26133v1 (19 October 2026), Section 4.1, for the statement dispute; read online at https://arxiv.org/html/2610.26133v1 . No files were downloaded. The proof is marked agent-origin because the supporting originals are missing locally; I do not claim to have read the unavailable original Raynaud theorem.

## STATEMENT-DISPUTED

The imported assertion for an arbitrary line bundle is false, even in its intended semiabelian setting. Kallal Section 4.1 constructs a degeneration over the regular ring R=C[[q1,q2]], with generic elliptic fibre and closed fibre G_m. Its period is q1*q2 and its line cocycle is psi(y)=q1^((y²+y)/2)*q2^((y²−y)/2). The generic line is ample. For every positive power, the Fourier recurrence forces all nonconstant coefficients to vanish modulo (q1,q2). Restrictions of all global sections to the closed torus are constant, preventing their nonvanishing opens from generating its topology; the line is not ample. This is an actual smooth connected separated finite-type group counterexample, not a counterexample for an unrelated nonproper variety.

I repaired the node to symmetric lines on semiabelian schemes with a dense proper abelian open, precisely the situation of Deligne's canonical Picard line. The original extraction generalized Deligne's use to arbitrary smooth commutative groups and arbitrary lines without justification. Deligne 4.1 explicitly supplies symmetry. The corrected theorem retains regular locally Noetherian bases, all generic components and the conclusion over every affine open. Adding symmetry alone while retaining every possible smooth group would assert a generalization I have not verified. I therefore also made the actual semiabelian and abelian-open hypotheses explicit rather than hide them in a citation.

The sole application found is the existing split lem-sfb-stable-picard-theta-ampleness, step 5. That parent now needs its hypothesis check updated: its extended canonical line is symmetric by the symmetry in lem-sfb-smooth-jacobian-canonical-line and the uniqueness clause of lem-sfb-regular-group-rigidified-line-extension (normalize the inverse-pullback comparison at the identity). Its nodal Picard identity components are semiabelian and its dense smooth-curve open is abelian; however lem-sfb-nodal-picard-etale-schematic currently does not explicitly state the semiabelian clause. The maintainer should record that missing input in the parent when reviewing this statement repair. I have not edited another worker's node or claimed the parent needs no repair.

The inherited blueprint.from.node is null along a long created-item ancestry. blueprint_refs.py ancestor confirms this pre-existing broken anchor. I retained the exact ancestry and added the current item to the new node's via list. Searches of the latest blueprint and blueprint_refs.py for Raynaud, generic ampleness, symmetric ample and ample extension gave no matching statement.

## Not duplicates

lem-sfb-symmetric-ample-power-extension vs lem-sfb-regular-group-generic-ampleness: the new node is an existence theorem over a normal base, starting only with a symmetric relatively ample line on the dense abelian open; it supplies a possibly higher-power ample extension locally. It does not compare this extension with a supplied line on the whole group. The item's proof performs that comparison using regular-base rigidified uniqueness, extracts the positive tensor root and assembles the local conclusion.

lem-sfb-symmetric-ample-power-extension vs lem-sfb-regular-group-rigidified-line-extension: the existing extension theorem is an equivalence of rigidified-line groupoids over a regular base and says nothing about ampleness. The new node works over a normal base and supplies an ample extension of a power, not an equivalence or uniqueness.

lem-sfb-symmetric-ample-power-extension vs lem-sfb-stable-picard-theta-ampleness: the existing statement constructs a canonical relatively ample line on a stable-curve Picard space with all its base-change and equivariance data. The new input is a general scheme-only normal-base existence result, with a prescribed symmetric line on a dense abelian open; it does not construct that canonical line or its descent comparisons.

No existing node sharing the original Raynaud XI 1.13 citation states the new existence theorem. Searches included the entire DAG's statements and source places, not just filenames; field quasi-projectivity, affine-boundary criteria, proper-family ampleness neighbourhoods and fpqc ampleness descent have different hypotheses and conclusions.

## Review by Q124

I read Deligne 4.1–4.8 and compared the actual canonical symmetric line there with the overly broad imported statement. The newer counterexample made the difference decisive. I also read Moret-Bailly's connected-fibre proof in the thesis indexed text, which uses existence from Raynaud and uniqueness rather than an arbitrary-line ampleness assertion. The original Raynaud text remains WANTED: the new node explicitly records this limitation and agent responsibility. I did not cite the forbidden SGA route. Stacks sources were read in the local source tree for proper ampleness spreading (Tag 0D2N), locality (01VJ), normal components (033M) and the ampleness definition (01PS). No Stacks tag was invented for Raynaud's specialized group theorem.

Step 1 uses the two relevant clauses of rem-pc-regular-normal: regular implies normal and a Noetherian normal scheme is a finite disjoint union of open-and-closed integral components. Local triviality of e*L is part of the definition of invertibility; these trivializing affines can be split into affine components. The empty base produces no pieces and no assertion of a generic point. An affine over a locally Noetherian scheme is Noetherian, so the decomposition's Noetherian hypothesis is satisfied.

Step 2 uses lem-trf-smooth-connected-fibre-normal-integrality exactly for geometric integrality, including nonemptiness supplied by the identity. This is the fibre hypothesis needed later by the uniqueness theorem. The neighbourhood theorem is applied only after restricting to the specified proper abelian open. Thus its properness hypothesis is genuinely available, and no nonproper fibrewise-ampleness principle is used. The base neighbourhood is affine Noetherian, and the generic line is ample by the item hypothesis. The affine-cover lemma converts absolute ampleness over this affine U to the relative formulation the new node requires.

Step 3 checks every hypothesis of the new node: normal integral Noetherian affine base, semiabelian fibres, dense proper abelian open, rigidification, symmetry and relative ampleness. Its conclusion supplies B_i with precisely the rigidified restriction isomorphism required by step 4. The new node is not simply a clause of the item: normal-base existence of an ample extension does not identify that extension with any supplied L, and it introduces a positive power which must subsequently be removed. This follows the existence-and-uniqueness argument in the source, rather than moving the item's conclusion under a new name.

Step 4 uses the actual full-faithfulness sentence of lem-sfb-regular-group-rigidified-line-extension, which I opened and read. Both lines are supplied on the same whole group, the comparison respects rigidifications, the base is regular locally Noetherian, and the fibres are geometrically integral by step 2. The theorem is for group algebraic spaces and therefore also applies to schemes. No generic-fibre-only comparison is passed to a theorem requiring a dense open: U intersect T_i is an actual dense open. This is the main C4 check.

Step 5 is elementary and is not a new node. A section of (L^n)^m is the same section of L^(nm), with the same nonvanishing locus under the tensor-associativity identification. Thus the definition supplies the converse from ample positive power to ample L directly. Quasi-compactness is already supplied by ampleness of B_i. This avoids citing the existing positive-power lemma backwards: that existing lemma only proves ample L implies ample powers.

Step 6 uses the conclusion of lem-trf-scheme-relative-ample-affine-cover verbatim for all affine opens, not just those chosen in the proof. Finite presentation supplies quasi-compactness of p. Its hypotheses do not require S globally Noetherian or quasi-compact, so the original locally Noetherian generality is retained.

I checked B–E of delivery-errors against these steps. The new theorem introduces its own objects and exact meaning of semiabelian, symmetry, rigidification, normality and relative ampleness. Small cases include empty base, dimension-zero base, r=0 (abelian fibres), and a torus special fibre; none requires a nonexistent generic point or a positive toric rank. The counterexample is excluded by symmetry, not by an artificial dimension restriction. Every non-elementary fact used in the assembly has a cited node; every cited statement was opened and matched, and every citation quote is a verbatim substring. The properness and density checks above are the hypotheses most likely to be lost in this argument. No proof step exceeds 2000 characters. No elementary statement-only node, duplicate Mathlib leaf, test mirroring the proof or unperformed Mathlib search was introduced. All four search tools and two natural-language phrasings were run; unrelated hits were read, and their names are recorded without asserting a match. The inherited Q120 search records were preserved, with verdicts corrected to describe their relevance to this item.

## What remains

The stage-1 mathematical split and statement repair are complete. The new Raynaud input is deliberately unsplit, as required for a one-level stage-1 delivery. Missing originals and the downstream parent-hypothesis repair are explicitly reported above. Delivery preflight and push results are recorded after the required commands finish.

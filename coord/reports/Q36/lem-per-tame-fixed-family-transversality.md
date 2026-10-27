# Stage-1 delivery: lem-per-tame-fixed-family-transversality

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-tame-fixed-family-transversality.json: item split into five argument steps; searched again, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-tame-fixed-local-regularity.json: statement-only local algebra lemma, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and source grep, with two semantic phrasings.
- citations.json: the full verbatim statement of each dependency used by each step.

One new node, zero Mathlib leaves. The original item, source, inherited search records and blueprint ancestry are retained. The item statement has the same hypotheses and conclusions; over-escaped TeX was normalized and the source's parameter meaning of normal crossings and cotangent-dual meaning of tangent space were made explicit. No Lean was written and no compiler was run.

## Attachments

None. I searched WeilConjectures for the item id, fixed subschemes/fixed loci, tame actions and regular-local fixed-point algebra. The project has no finished declaration covering this item. The generic regular-local algebra declarations already associated with existing DAG nodes are reused through those nodes, not claimed as an attachment of the item.

## WANTED

None. The ILO PDF and the supporting Stacks source are present locally.

## What was wrong or incomplete

The imported item was statement-only. It needed the local fixed-quotient input and an actual boundary-compatible parameter proof. Its printed TeX had doubled backslashes, now corrected. Its boundary normal-crossings predicate was not spelled out, now defined by simultaneous parameter subsets, exactly ILO VIII 4.1.2 and 4.2.4--4.2.5(ii). The geometric tangent convention is the dual of the local cotangent space after residue extension, as in the cited VIII proof; no relative tangent space over an unstated base is used.

The last paragraph of ILO VIII 4.2.3 proves boundary containment by regularity and a tangent comparison. I replaced that compressed reasoning by the direct local unit calculation: if h(t_i)=u t_i and the residue of u differs from 1, then (u-1)t_i is a fixed ideal generator and u-1 is a unit. This proves t_i is actually in the fixed ideal, rather than merely in its radical or first-order image. I also made the subsequent generation of the whole fixed ideal explicit using 00NR and Nakayama. This is the same parameter route as the source, with its algebra expanded.

## Unfinished work

The new local-ring theorem remains statement-only for a later stage-1 worker. No part of the item's assembly proof remains unfinished. That theorem is a local, boundary-free algebra input, not a relabelling of the family theorem: it requires no scheme, SNC divisor, generic freeness or global action, and does not assert transversality, nowhere-density, family intersections, the free open or equivariance of the family.

## Not duplicates

lem-per-tame-fixed-local-regularity vs lem-per-tame-fixed-family-transversality: local algebra of one arbitrary regular local ring and its difference ideal, without boundary or generic freeness, versus the global family and its boundary transversality. Steps 3--4 carry the latter's principal argument.

lem-per-tame-fixed-local-regularity vs lem-per-gabber-fixed-locus-log-chart: the existing node requires a log smooth morphism and provides an equivariant chart and blowup comparisons; the new node applies to arbitrary regular local rings, including mixed characteristic without any log smooth chart.

lem-per-tame-fixed-local-regularity vs lem-per-tame-smooth-representation-chart: the existing node requires a smooth morphism over a localized cyclotomic coefficient ring; neither smoothness nor such a coefficient ring is available in the present regular-scheme problem.

lem-per-tame-fixed-local-regularity vs lem-per-tame-equivariant-cohen-gabber: the existing node is an equal-characteristic positive-dimensional finite separable power-series presentation, not fixed-quotient regularity in arbitrary characteristic.

lem-per-tame-fixed-local-regularity vs lem-weil-pbc-regular-local-quotient-kernel-parameters: 00NR assumes the quotient is regular; the new node proves regularity of this special quotient and identifies its cotangent space. The item cites 00NR separately after that regularity is established.

I searched all DAG statements for fixed subschemes/loci, invariant tangent and coinvariant cotangent spaces, and the source locations VI 4.2 and VIII 4.2.3. I ran blueprint_refs searches for fixed locus, tame, coinvariants, regular local and fixed. The blueprint fixed-locus nodes concern Frobenius correspondences and their trace pairing, not tame finite group fixed quotients. No equivalent blueprint statement was found. The ancestor command gives lem-per-artin-gabber-affine-curve; the new node has that ancestor and the full inherited via list prefixed by the item. The current latest blueprint's ancestor proof and the unit/chapter records were read. This is the existing equivariant-modification branch of the ancestor's regular-purity input, not a replacement route for its perverse arguments.

## Mathlib search assessment

The item retains the four inherited 2026-10-19 records and adds the actual searches of 2026-10-24 in searches.jsonl. The new node records only the relevant searches present in that same log. LeanFinder's first phrasing returned invariant-subring and residue-field statements; its second returned arithmetic inertia statements. LeanSearch returned abstract representation coinvariants, not the fixed-ideal regularity theorem. Loogle with IsRegularLocalRing and MulSemiringAction gave zero results; RingTheory grep for regularity combined with fixed/invariant/coinvariant gave zero. For the item, the hits are normalization, abstract fixed-point sets and unrelated fundamental-domain statements. Set-theoretic fixedPoints_subgroup_sup is consistent with Step 1, but does not state the geometric item or the scheme-theoretic local algebra. No unavailable service is described as a negative result.

## Review by Q36

I read ILO Expose VI 4.1 and Proposition 4.2 with its complete equal- and mixed-characteristic proof, printed pp.76--77; VI 4.4, p.78; VIII 4.1.2, 4.2.1--4.2.5, pp.117--120, in particular the entire proof of 4.2.3 on p.119. For the new node, VI 4.2 is precisely the regular fixed-quotient theorem, and VIII 4.2.3 explicitly states the invariant tangent-space consequence. I stated that consequence in canonical coinvariant-cotangent form. The hypotheses are local automorphisms, trivial residue action and invertible group order; completeness and a coefficient field are not assumed, since completion and Cohen linearization belong to the proof, not its input. Its future proof plan is the source's completion/linearization proof in both characteristics, followed by descent; no such sketch was put into the new node statement.

Step 1 uses only the closed diagonal definition of separatedness and the defining simultaneous equalizer. On every test scheme, fixing both subgroups is equivalent to fixing their generated subgroup, and conjugation gives the displayed permutation identity. Thus these are scheme identities, not identities only on geometric supports.

Step 2 cites the new node. I checked its full statement supplies both regularity of R/I and the kernel D of the cotangent map. At a point of X^H the residue action is trivial, since the geometric point is fixed; tameness implies |H| invertible by subgroup divisibility. The stalk equalizer really is the ideal of all differences, including fractions. Dualizing a quotient gives exactly the invariant tangent vectors. No ambient |G| invertibility is assumed away from points fixed by G; only the particular |H| is needed.

Step 3 cites lem-per-snc-boundary-parameter-criterion for the boundary product equation. I added lem-trf-etale-component-coordinate-identification, read its full statement, and use it with the identity etale morphism after representing the germs and shrinking. It gives exactly the labelling of individual components by the t_i. Its locally Noetherian, reduced-boundary, regular-component and regular-parameter hypotheses follow from the stated SNC boundary and regular X. G-strictness now gives H-stability of each component through the fixed point, hence the actual unit equations h(t_i)=u_{h,i}t_i. I wrote the Reynolds idempotent identities explicitly rather than invoking an uncited semisimplicity theorem. The nontrivial character sum vanishes because multiplication by a value other than 1 permutes it. The unit equation proves actual vanishing on the fixed subscheme.

Step 4 uses exactly the statements of the existing cotangent-dimension, local Nakayama and regular-local-quotient-kernel-parameters nodes, which I opened and read. I also read Stacks algebra.tex, Tags 00NQ (lemma-regular-ring-CM) and 00NR (lemma-regular-quotient-regular), and the Nakayama lemma-NAK (00DV). The first node makes the chosen basis have dim R elements. Nakayama on the finite maximal ideal makes them parameters. The 00NR node applies because R and R/I have already been proved regular. Its parameter generators for I show directly that I/mI injects into the ambient cotangent space; coefficient reduction gives this without a hidden conormal lemma. Its image is D by Step 2. Nakayama applied to the finite ideal I then proves that the newly selected, boundary-adapted elements generate I. Thus there is no inference from tangent containment alone to scheme containment. The three local-algebra nodes and the component-identification node are declared as generic off-unit tools, with their uses and reasons in split_report.tool_uses.

Step 5 needs no new theorem: each closed fixed support misses the given dense free open, so has empty interior. There are finitely many subgroups; the complement of their closed supports is an invariant open and has exactly trivial geometric stabilizers. This proves both maximality and the union formula. Applying Steps 2--4 to the generated subgroup proves all nonempty intersections. This does not claim the whole fixed family has one common parameter system; only weak boundary normal crossings is asserted.

I checked B--E against the actual node files. Every new object is introduced, local ring regularity is cited by its defining node, and cotangent/difference ideals are defined explicitly. The only new node is statement-only with empty proof and proof dependencies and genuine logged searches; no elementary fact became a node. Every proof dependency has a citation quote in citations.json, and all quotes are verbatim full statements. The graph has no return edge from the new node. The source route uses ILO and Stacks only, with no prohibited SGA citation. Each proof step is shorter than 2000 characters.

Small cases: H=1 or the trivial action gives I=0 and unchanged cotangent in the new node; a field has zero cotangent and only the trivial residue action; reflection x maps to -x over a field of characteristic different from 2 gives I=(x), with a boundary x=0 contained in the fixed locus and an invariant y=0 boundary transverse to it. In the mixed-characteristic regular ring Z_p[[x,y]]/(p-x^2-y^2) for odd p, simultaneous sign change gives fixed quotient F_p, matching the invariant cotangent dimension zero and illustrating why a smooth-over-a-coefficient-field hypothesis would be inappropriate. For a free orbit all nontrivial fixed loci are empty; for G=1 the whole family is empty and the largest free open is X. With an empty boundary the coordinate argument simply chooses generators of I among parameters. The empty scheme, disconnected X and empty intersections cause no change: the nowhere-density argument uses a dense free open, not integrality. The wild example x maps to x+1 in characteristic p is not used to extend the theorem, since the necessary order-invertibility hypothesis fails.

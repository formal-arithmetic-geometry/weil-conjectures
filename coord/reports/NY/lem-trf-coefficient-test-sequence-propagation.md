# Stage-1 repair: lem-trf-coefficient-test-sequence-propagation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-coefficient-test-sequence-propagation.json: repaired split, fifteen steps; necessary jet-bound hypothesis made explicit. Not a Mathlib leaf.
- citations.json: 31 checked verbatim quotations, one for each step/node citation.
- report.md: this report, replacing the mathematically incorrect review of the first delivery.

New nodes: 0. New Mathlib leaves: 0. The sandbox's earlier searches and source citations are retained. repair.py is sandbox scratch, not a delivered node or project file.

## Attachments

None. Repeated the project-source search for the exact item tag, Hilbert--Samuel spellings, coefficient data, marked ideals, and test sequences. The hits concern unrelated coefficient sheaves; none states this result. The existing Sheaf datum definitions are not propagation proofs. No Lean was written or compiled.

## WANTED

WANTED: Bierstone--Milman, Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant, Invent. Math. 128 (1997), Definition 6.2, formulas (6.1), Theorems 7.20--7.21 and the proof of Theorem 9.4, for lem-trf-coefficient-test-sequence-propagation.

WANTED: Bierstone--Milman--Temkin, Functorial desingularization over Q: boundaries and the embedded case, arXiv:0905.3580, sections 5.2 and 6.2--6.3, for lem-trf-coefficient-test-sequence-propagation.

These sources remain unavailable in the permitted local literature. I read ILO VIII 2.3.8--2.3.17, printed pp.93--95 (PDF pp.99--101). Its remarks refer to BM/BMT, discuss synchronization and functoriality, and prove invariance of the regular locus and equivariance. They do not prove coefficient-transform formulas. The proof_origin is therefore explicitly agent, not document. No SGA source is used.

## Returned error and its repair

The returned E5/C4 and D4 findings are correct. The former step 4 applied the boundary clause of formal-coefficient-transform-criterion over a point below the reference level. Its proof step 13 only starts at a point satisfying the five conditions. Neither it nor ILO supplies the missing argument. Ordinary pullback can raise coefficient order: (W1+W2)W4 becomes e(1+u)W4, whose order increases at u=-1. Thus keeping five conditions only at the current equality locus cannot justify another induction step.

The new invariant stores the full boundary history and the lexicographic upper bound everywhere. A boundary germ is either a free zero-section/toric-coordinate germ over an earlier X, or lies over an earlier permissible center, hence an earlier equality point. In the second case the proof retains supported multiplication identities on the entire exceptional fibre, including its lower-level points. For Z^beta f_i the source center-order is v=d_i+|beta|. The existing coordinate-blowup division lemma gives ord_P(q_h)>=v-d_h, so e^(d_h-v) sigma*(q_h) is regular. Its transverse support is unchanged. Later boundary substitutions change W only, hence preserve these identities even through intermediate points outside cosupport.

At a newly created order point, the pure-transverse degree-d_i forms come from the earlier equality point. A block-triangular division matrix gives homogeneous division. The stored identities express every polynomial multiple of a generator as a supported sum; closedness of the supported-sum space extends this to arbitrary formal multiples. This proves condition (3), rather than confusing ordinary ideal generation with supported division. Conditions (4),(5) are retained as identities, independently of order equality. The first dropping block supplies an independent relation outside the earlier prefix diagram, giving strict lexicographic decrease off the new order locus and excluding equality off N. This also supplies the global upper bound required by the next permissible blowup. A local pointwise upper neighbourhood at an equality point is supplied separately by extended-hilbert-local-upper-bound before using a full regular datum there.

The previous blanket claim that the boundary operation preserves all numerical values at corresponding lower-level points has been removed. Its retained reference level remains L_j, while new equality points are allowed. The proof explicitly handles them. Restarting the smooth-pullback induction now starts this strengthened invariant with empty test boundary and constructs the same identities at each later upstairs permissible center.

## Source error: STATEMENT-DISPUTED

The imported item omitted Q>=max_i d_i-1. That hypothesis is explicit in common-power-hilbert-marking and is needed in the first-dropping-block use of condition (5). It is not implied by def-trf-regular-hilbert-coefficient-datum, whose Q is an arbitrary natural number. The corrected item now requires that bound, vacuously for an empty vertex family. This is the sole statement change; no target or definition was edited.

Here is a reduced counterexample to the omitted bound, already at prefix zero. Take Z=A^5_Q with coordinates (t,u,v,z1,z2), N=V(z1,z2), and X defined by

    g1=z1^2+u^3,  g2=z2^3+v^4.

This is the product of two geometrically integral cusps with A^1_t, hence reduced. At the origin use f1=g1 and f2=g2+t*g1, with vertices z1^2,z2^3 of degrees 2,3, and set Q=0. Their initial forms are z1^2 and z2^3+t*z1^2; the second differs from z2^3 by a multiple of the first, so the supported homogeneous division matrices and supported generation have the stated triangular form. The derivatives chosen in (4) are 2z1 and 6z2. Condition (5) is vacuous for Q=0: the first prefix diagram starts in degree 2. The coefficient order locus forces u=v=t=0. On that locus all five supplied conditions hold; the complete-intersection Hilbert function has its local maximum there.

However X and its Hilbert--Samuel function are independent of t. Every point (c,0,0,0,0) with c nonzero has H_X=H_X(0). The coefficient of z1^2 in f2 is t, with weight 3-2=1. It is a unit there, so the marked cosupport excludes that point. Every Zariski neighbourhood of the origin meets these points. The uncorrected conclusion is therefore false. With Q>=2, condition (5) would forbid this spurious later coefficient: partial_z1^2 f2=2t is not in (z1).

## Blueprint, duplicate search, and current main

Read the chapter and unit records, the current latest blueprint sec-trace-formula/_section.md, sk-i-curve-zero/_section.md and lem-trf-local-term-locality.proof.md. latest points to main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). This remains the historical resolution branch in the item's existing ancestry; the active contracting-correspondence route is unchanged. The existing from.place is specific and same_as remains the searched empty list. No unit or chapter file was changed.

Compared the retained delivered node with the current read-only repository without git: the original changed fields were proof_origin, split_report, status, proof_deps, proof, and mathlib_searches; the repository supplied no replacement argument. Retained the existing proof route and useful arguments, repaired the returned boundary inference, and added the demonstrated missing jet bound. The first required dry run was run before editing and exited OK (not pushed) at 80954077d83; that receipt certifies the former mechanical shape only. The final dry run below checks the repaired version against current server state.

Searched the DAG and blueprint for division, flat Hilbert families, boundary intersections, and coefficient generation. Existing homogeneous-continuous-formal-division, coordinate-blowup-division-generators, implicit-taylor-coordinate-calculus and extended-hilbert-local-upper-bound provide the needed inputs; no new node duplicates them. There are no new same-tag pairs requiring a Not duplicates table.

## Mathlib searches

Read and retained searches.jsonl and all previous item search entries. After correcting the statement, ran the authorized msearch wrapper for two LeanFinder phrasings, Loogle, grep, and LeanSearch. The first LeanFinder returned single-variable Weierstrass division and preparation; the second returned stable ideal filtrations, adic bases and prime-spectrum chains. LeanSearch returned division-monoid identities and Laurent expansion of a quotient. These have different objects and do not state a finite-test coefficient presentation or a one-line generalization. Loogle and grep returned zero hits. Recorded the actual logged tool/query/results metadata and no-match verdicts; no service was unavailable. No invented search is recorded.

## Tool uses

sbc-thm-etale-local-normal-form remains the declared generic tool: smooth maps factor etale-locally through affine space. I read its statement and Stacks Tag 054L, morphisms.tex, lemma-smooth-etale-over-affine-space. Its relative affine-space dimension is r on a constant-relative-dimension piece. Every other proof citation is in the item's unit. No new tool-use exception is requested.

## Review by NY

I checked delivery-errors B--E against the actual statements of every cited node, and read the obtained source above rather than attributing a coefficient proof to ILO. There are no new statement-only nodes, Mathlib leaves, or definition nodes. The statement correction and its reduced counterexample are recorded separately above. The strengthened proof is fifteen steps; its longest step is under 2000 characters. The steps carry the boundary argument rather than moving the disputed clause to a new node or citing a proof of another node as though it were its statement.

Step 1 uses common-power-hilbert-marking for initial coherence and locus equality, and the definition for the supplied conditions and pointwise bound. The jet bound has now been checked explicitly. The invariant additionally includes the whole-neighbourhood lexicographic bound, coefficient-power identity, and historical identities at lower-level boundary points; it no longer presupposes what the boundary step must prove.

Step 2 uses the datum's pure-coefficient vertices and five conditions, and homogeneous-continuous-formal-division for supported division and its filtration estimates. The triangular matrix restriction is written out for each prefix, with all complementary variables set to zero. The source parameters vanish at the fixed earlier equality point throughout the substitutions, which justifies convergence without transporting arbitrary formal series to another point.

Step 3 uses the same two nodes as the accepted former step 2: the chart theorem supplies smooth flags, regular controlled ideals and boundary geometry; the marking theorem supplies the bound, locus equality, and five conditions at equality. The center really lies in S by induction. Centers removing components, empty transforms and charts missing N are explicitly included.

Step 4 uses coordinate-blowup-division-generators for both actual saturation generation and the precise quotient order inequality. Its hypotheses are met at the source center: the datum gives homogeneous division and supported generation, the center is coordinate, and ord_P(f_i)=d_i since f_i belongs to P^d_i and has ordinary order d_i. Applying it to Z^beta f_i gives v=d_i+|beta|. Every displayed exponent is therefore nonnegative after substitution. Supports only constrain transverse exponents; coordinate-variable substitutions preserve them. This proves regular supported identities at all points of the N-chart fibre, not only equality points. The same theorem gives ordinary ideal generation on the other charts.

Step 5 uses the datum identities and implicit-taylor-coordinate-calculus for differentiation, regular models, faithful flatness and residue-field compatibility. The derivative scaling factors are displayed. Membership in (Z'^ell) is contracted before exceptional inversion because its quotient is a power-series domain and e is a coefficient variable. Thus (4),(5) are identities at lower-level boundary points too. Degree-d_i pure-transverse values are computed from the coefficient transform formula and evaluated at the earlier source S-point. On charts missing N the first nonzero essential direction gives a nonzero constant derivative row, which step 10 uses for strictness.

Step 6 retains the accepted line argument: the formal criterion supplies ordinary coefficients; the jet statement supplies one summation at every scheme point, including fibre-generic points; the marking statement supplies order/cosupport conversion. The new independent variable retains every stored identity. Smooth order compatibility is also stated by logarithmic-differential-transform, used in step 7.

Step 7 is the induction on boundary origins, using the recursive test definition. Its explicit A[e,u,...] charts explain why pairs descended solely from zero sections remain smooth products over the earlier X. The jet node and smooth order compatibility give their values and orders. Every other affected germ lies over an earlier permissible center, an actual earlier S-point; a later affecting permissible blowup restarts this history. No assertion places the whole present boundary intersection in the present equality locus.

Step 8 uses permissible-coordinate-chart for both ratio charts and labelled boundary equations. N is the smooth cartesian Z=0 pullback. The actual ideal generation comes from step 4 over the earlier equality point, then ordinary pullback, not from an unjustified new use of the boundary clause of formal-coefficient-transform-criterion. The pure-transverse matrix argument supplies (1),(2) at every newly created order point.

Step 9 uses precisely the closed-supported-sum assertion of homogeneous-continuous-formal-division. Polynomial multiples are covered by the retained multiplication identities and unrestricted coefficient-variable supports; closure handles arbitrary formal multiples. This proves supported generation (3). The jet theorem identifies the resulting formal Hilbert counts with the extended Hilbert--Samuel function at nonclosed points as well. Conditions (4),(5) were already identities. This is the missing argument for points over non-equality images in the return.

Step 10 uses homogeneous uniqueness and counts independent relations in the actual Taylor ideal. For the first dropping block the earlier prefix columns count D through the first drop degree; condition (5) and the now-explicit Q bound make the new low form a nonzero remainder. Thus a strict lexicographic decrease occurs. Off N the stored nonzero derivative row forces a dropping block; if the pivot is transverse it cannot belong to an earlier retained block. Earlier retained essential variables are therefore still present for the same count. This establishes the global lexicographic bound and excludes equality outside N, rather than assuming numerical invariance over lower-level points.

Step 11 uses the product/sum order formulas of logarithmic-differential-transform to identify the common-power cosupport from the coefficient inequalities; the equalities are explicitly computed. extended-hilbert-local-upper-bound and jet-diagram-hilbert-control supply the local pointwise upper neighbourhood when a subsequent permissible center requires a full datum. Their finite-module and finite-value hypotheses are stated for these Taylor ideals. This local preparation does not remove lower-level points from the global invariant.

Step 12 is the recursive finite-test definition applied to the already proved equality and identical ordered boundary. Step 13 retains the accepted first-difference proof that summation is injective and order-reflecting; no non-elementary order theorem is silently used. Step 14 retains smooth local factorization and the extended Taylor count, with the same relative dimension r; restarting now explicitly constructs the stronger history and identities at arbitrary upstairs centers. Step 15 uses the stated etale and residue-extension localization clauses for open restriction and separate relative-dimension pieces.

Small cases checked: zero vertices and I=0,b=1; no boundary initially; no type-(iii) test before two boundary labels exist; empty cosupport; component-removing and Cartier centers; both ratio charts; two free zero sections; an intersection containing a permissible exceptional component; nonclosed points and residue-field extensions; order rise of (W1+W2)W4 at u=-1; z^3+w1*w2*w3 over a lower-level boundary point; Q=0 in the explicit counterexample above; and r=0, r=1 and first differences at index zero or later. The latter boundary examples no longer require their lower-level images to satisfy five conditions. New order points use the historical multiplication identities, pure-transverse bases and Jacobian identities instead.

All citations.json quotes are verbatim substrings of the statements read, proof_deps is exactly the union of step uses, and no non-elementary result is cited from another node's proof. The only writes were to this sandbox; no repository git, compiler, Lake, build tool, other agent, or launcher edit was used.

## Unfinished

No part of this stage-1 split is left open. Existing cited nodes remain existing DAG inputs; this delivery does not claim to have proved their Lean. The detailed BM/BMT literature remains WANTED. Final delivery checks and their receipt are recorded after the required dry run.

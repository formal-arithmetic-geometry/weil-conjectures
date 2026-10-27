# Stage-1 delivery: lem-sfb-smooth-group-proper-neutral

Group NE; 2026-10-23. Continued the sandbox after the interrupted provider calls and launcher pause. No delivery had been started; the earlier read-only server check lost its process handle. Retained the existing split, citations, and actual search log. No Lean was written or compiled.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-group-proper-neutral.json`: statement, split; six proof steps, original statement retained; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-artinian-etale-lift-smooth-point.json`: statement, unsplit; no Mathlib match. General pointwise criterion, not a neutral-group assertion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-space-proper-component-neighbourhood.json`: statement, unsplit; no Mathlib match. Extension of one proper fibre component, without any group structure or global neutral-locus assertion.
- `citations.json`: one entry for every step/node incidence, with verbatim statement text.
- `report.md`: this report. `searches.jsonl` retains the search command's actual outputs; `write_split.py` is sandbox scratch, not a project file.

Two new statement-only nodes, zero Mathlib leaves. No chapter or unit file changed.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item's blueprint tag, neutral/identity components, smooth group spaces and proper group spaces did not find a project declaration giving the whole assertion with a completed proof. Scheme matrix-group identities and quasiprojective group-space results do not state this item. The inherited Lean audit is `none`.

## Wanted literature

WANTED: Kleiman, *The Picard Scheme*, Proposition 5.20 and its proof (printed p.47), for lem-sfb-smooth-group-proper-neutral. This PDF is absent locally. I have not treated its proposition as read or as an exact source for the stronger relative lifting hypothesis. The proof is an agent assembly from the Stacks results below.

## Corrections and blueprint route

There is no statement dispute. In particular, geometrically smooth fibres alone would not justify smoothness over a nonreduced base; the given relative lifting hypothesis is used, not discarded. The proof first obtains smoothness only at neutral points. It does not apply a flat-family smooth-locus theorem to the possibly nonflat ambient group.

The inherited item was unsplit. The current blueprint is `literature/blueprint/latest/` (main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345). I read the chapter, unit, and the current direct-images proof (3). The item is an inherited auxiliary prerequisite of the Picard/abelian-space calculation under that direct-image argument; that blueprint paragraph does not itself give this neutral-component proof. `blueprint_refs.py ancestor` returns no ancestor for the inherited created-item chain. I retained its null ancestor, filled the places concretely, propagated the inherited via chain, and recorded whole-blueprint searches with no equivalent statement. This does not replace the unit's direct-image route. Generic off-unit open-subspace tools are declared in `split_report.tool_uses`.

## Searches

I read all results in `searches.jsonl` before continuing. For each new node I ran LeanFinder twice with distinct phrasings, LeanSearch, Loogle and the source grep through the prescribed msearch command. The item also has real recorded searches. All were available. The pointwise searches returned ring-theoretic `FormallySmooth`/`Smooth` declarations, not a pointwise criterion for morphisms of algebraic spaces. The proper-component searches returned no algebraic-space component-extension theorem; topological connected-component results and proper map facts do not specialize in one line. Item hits concern topological groups and scheme smooth loci, not this relative algebraic-space subgroup statement. The JSON search records reproduce actual queries and verdicts; no search was reconstructed as if run.

Before creating either node I searched the whole DAG by statement keywords and by all its source tags, used whole-blueprint searches, and searched project Lean. Existing henselian lifting, properness descent, open-image calculus and group-over-field results are cited instead of recreated. Same-tag distinctions are below.

## Review by NE

I read delivery-errors B through E and checked the actual node statements, not just their titles. The item source I used is the Stacks pointwise smoothness argument (spaces-more-morphisms.tex, Tag 0APN), the formal-smoothness discussion and Tag 04AM, and the proper-component material at Tags 0CWI and 0E1E. I also read the maximal smooth open in spaces-morphisms.tex (0DZI), the open-subspace and factorization statements in spaces-properties.tex (03BZ and 03IE), and the group identity-component proof in groupoids.tex. The proof is marked agent-written; it is not presented as a verbatim Stacks lemma.

For the new Artinian point criterion I read 0APN's equivalence and proof and the discussion preceding 04AM. The source's point criterion has actual lifts; the new node deliberately states the etale-local variant. This requires descent of the affine infinitesimal obstruction after passing to etale scheme charts: its vanishing is faithfully flat local, and the possible lifts form the associated quasi-coherent torsor on an affine test scheme. The new node is a genuine prerequisite awaiting its own split, rather than an assertion that 0APN literally has etale-local arrows. The target is locally Noetherian and the map locally finitely presented, stronger than the local finite type assumption of 0APN. Testing only Artinian small extensions suffices there; our node assumes all square-zero surjections of Artinian local rings. No reduced-base or perfect-field assumption has been inserted.

For the new proper-component neighbourhood node I read the full henselian-pair lemma 0CWI, the local constancy theorem 0E1E, and spaces-limits.tex Tags 0827 and 08K1. Its intended argument is: restrict near the chosen proper component to a quasi-compact finite-type open, pass to a strict localization of the locally Noetherian base, and split off the proper clopen part using 0CWI. A geometric component descends to the separably closed residue field (purely inseparable field extensions do not change components). Descend the quasi-compact open to a pointed etale neighbourhood and spread properness by the finite-presentation limit theorem. The descended open is smooth as an open of the smooth ambient space. For the resulting proper smooth finitely presented map, 0E1E makes the number of geometric components locally constant; shrink to the neighbourhood on which it is one. This gives nonempty geometrically connected fibres. Local Noetherianity supplies finite presentation for the finite-type separated proper part. The original ambient space need not be quasi-compact: quasi-compactness is used only for the finite-type open containing the chosen proper component. This is a smaller component-extension lemma, not the item's assertion or its global conclusion in disguise.

Step 1 uses the exact field-level conclusions of `lem-sfb-locally-separated-group-space-scheme` and `lem-sfb-locally-algebraic-group-identity-component`. The first gives a scheme for a locally finite type locally separated group space; the second gives the clopen subgroup and field-extension invariance. Restricting the separated diagonal and local finite-presentation charts to a geometric fibre gives the required hypotheses. The latter statement is over an algebraically closed field, precisely where it is used. The geometric irreducibility clause also supplies geometric connectedness. Field-extension invariance makes the predicate independent of representatives of space points.

Step 2 uses the new point criterion, `lem-sfb-space-maximal-smooth-open`, and `lem-a1-space-open-factor-scheme-tests`. Every Artinian local test has only one topological point, so a test centered at a neutral point has only neutral geometric images, using Step 1. Thus the item's lifting assumption supplies every diagram of the criterion. The maximal-smooth-open statement has no flatness hypothesis on the original map. Its full statement gives the open W, and the factorization node gives the identity section's factorization from its point images. These uses require no unproved global smoothness assertion.

Step 3 uses the new one-component neighbourhood lemma, open-factor calculus, and `lem-sfb-space-proper-cancellation`. The neutral component lies in W and remains a clopen connected component after this open restriction; its properness is an item hypothesis. W is separated and smooth and locally finitely presented over the locally Noetherian base, so the new lemma applies. Shrinking T to the identity section's inverse image retains the distinguished point and preserves the stated family properties. Proper cancellation says exactly that V -> G_T is proper when V -> T is proper and G_T -> T separated; it does not assume ambient properness or quasi-compactness. Its universal-closedness clause makes the already open inclusion closed. The elementary connected/clopen argument then identifies every fibre, not just the chosen fibre, with its identity component.

Step 4 uses `lem-a1-space-etale-open-image`, `lem-a1-space-open-factor-scheme-tests`, and `lem-a1-space-point-open-calculus`. The maps V -> G are representable etale because they are an open inclusion followed by an etale scheme base change. The first node gives openness of their images and the open-subspace correspondence. The covering includes every base point and Step 3 identifies its fibres, so their union is exactly the neutral predicate. The second node gives precisely the factorization equivalence for arbitrary test schemes. The third identifies opens from equality of point subsets, establishing H_T=V as subfunctors. No identification merely of closed points or of reduced spaces is used.

Step 5 uses `lem-sfb-space-flat-proper-fp-locality` separately for properness and finite presentation, and proper cancellation again for H -> G. The former statement explicitly allows each property separately on an fppf cover; the etale cover is such a cover. Smoothness of the open H inside W follows by restricting the smooth etale charts. Geometric connectedness follows from the fibre equality and the geometric irreducibility statement of Step 1. Proper cancellation uses separatedness of G over S, not a hypothesized separatedness of a quotient. The node's universally closed conclusion gives closedness of H in G.

Step 6 uses the exact arbitrary-base-change and factorization clauses of the open-factor node. Group operations preserve neutral points by Step 1, so unique factorization gives their restrictions. The equations follow on sections because an open subfunctor inclusion is a monomorphism. This is an elementary assembly argument, not an extra subgroup theorem. After arbitrary S' -> S, a geometric fibre is a field extension of a geometric fibre used in Step 1; hence the pullback predicate is the neutral predicate there. The open-factor node permits arbitrary algebraic-space maps, so no flatness, finite type, reducedness or Noetherianity of S' is introduced.

I checked the small cases: empty base is vacuous; the trivial group gives S; over an algebraically closed field the conclusion is the assumed proper smooth identity component. An infinite discrete disjoint union of proper components shows why G is allowed not to be quasi-compact and why properness is proved only for H. A smooth affine line component fails the new component lemma's properness hypothesis, so it supplies no spurious proper open family. A nonreduced base cannot be handled by fibre smoothness alone; the explicit infinitesimal assumption is used in Step 2. Nilpotent test schemes remain covered by the subfunctor factorization criterion and arbitrary base-change statement. The new point criterion also does not falsely declare a nonsmooth infinitesimal group smooth: it must pass its square-zero tests.

C1/C4: every non-elementary prerequisite is a node cited by the step using it, and I opened every such node and read its statement. `citations.json` quotes verbatim text from those statements for every incidence. The elementary operations on opens, chart restrictions, connected clopen subsets and monomorphisms are written out in the steps. No step exceeds 2000 characters, and neither new node is silently proved inside a long assembly step. The two new nodes contain statements only. No SGA source or trace-route argument is used.

## Not duplicates

lem-sfb-space-artinian-etale-lift-smooth-point vs lem-sfb-etale-local-infinitesimal-lifts-smooth: the existing theorem is for schemes with lifting at every affine diagram and concludes global smoothness; the new theorem is for algebraic spaces and tests only Artinian local diagrams centered at one point.

lem-sfb-space-artinian-etale-lift-smooth-point vs lem-sfb-space-infinitesimal-lift-pseudotorsor: the existing statement describes the pseudotorsor of lifts for one diagram; it does not give the pointwise smoothness criterion.

lem-sfb-space-artinian-etale-lift-smooth-point vs lem-sfb-smooth-space-affine-infinitesimal-lift: the existing implication assumes smoothness and produces lifts; the new criterion deduces smoothness at a point from centered Artinian lifts.

lem-sfb-space-artinian-etale-lift-smooth-point vs lem-per-etale-local-lift-torsor-quasi-coherent: the existing statement describes a scheme lifting torsor; it does not assert pointwise smoothness for algebraic spaces from Artinian tests.

lem-sfb-smooth-space-proper-component-neighbourhood vs lem-sfb-space-henselian-proper-clopen-lift: the existing theorem starts with a finite-type space over a henselian pair and a proper clopen part of its closed fibre; the new result extends one geometric component over a pointed etale neighbourhood in an ambient space that need not be quasi-compact, with geometrically connected smooth proper fibres.

lem-sfb-smooth-space-proper-component-neighbourhood vs lem-sfb-space-limit-open-cover-descent: the existing statement descends a finite quasi-compact open cover in an inverse system; it does not construct or extend a proper fibre component.

lem-sfb-smooth-space-proper-component-neighbourhood vs lem-sfb-space-proper-strict-local-test: the existing statement tests properness of an already specified finitely presented map at all strict localizations; it does not construct a proper open subspace from one component.

lem-sfb-smooth-space-proper-component-neighbourhood vs lem-sfb-space-qcqs-base-eventually-proper: the existing statement spreads properness of an already specified finitely presented family over an inverse limit; it does not extend a single component or provide connected fibres.

lem-sfb-smooth-space-proper-component-neighbourhood vs lem-sfb-space-eventually-proper: the existing statement is eventual properness for a specified inverse-limit family; the new theorem constructs the component neighbourhood before applying such spreading.

## Unfinished work and validation

The two prerequisites are intentionally unsplit stage-1 nodes for subsequent workers. There is no unresolved attachment, source claim, or statement correction. The required server dry run and delivery are the remaining validation steps.

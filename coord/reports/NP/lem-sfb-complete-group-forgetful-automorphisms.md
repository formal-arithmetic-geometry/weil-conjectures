# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-complete-group-forgetful-automorphisms.json`: item, statement unchanged, split into eleven steps; not in Mathlib at the stated generality.
- `dag/nodes/sec-six-functors-basics/lem-sfb-compact-closed-finite-intersection.json`: statement, Mathlib leaf, exact `CompactSpace.iInter_nonempty`, `Mathlib/Topology/Compactness/Compact.lean:825–829`.
- `citations.json`: the two step/node citation pairs, each with a verbatim statement excerpt. `searches.jsonl` was produced by the required search command. `write_split.py` is sandbox-only preparation, not a delivered project file.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag, Noohi, complete-group, nonarchimedean, and forgetful/automorphism terms. No project declaration states the item. A use of the compact intersection lemma in `Topology/SpectralSpace/Constructible.lean` is not a declaration of either this item or the generic compactness fact.

## WANTED

None. All sources used are present locally.

## Corrections and scope

The item statement and its hypotheses are correct and were retained verbatim. There was no imported proof to retain; the sandbox initially had only dispatcher marker files. The essential issue to expose is that compatibility of the images of identity cosets alone does not immediately establish two-sided Cauchy convergence. Step 6 includes the inverse image of the identity coset under the natural automorphism, giving both differences without requiring open subgroups to be normal. No completeness of an automorphism group or existence of a group completion is invoked without proof. The compact branch uses a generic compactness leaf rather than silently assuming compact groups are complete.

The inherited blueprint ancestry is detached: the required ancestor command returns `None`. I preserved its `from.node: null`, exact existing place, and via list, and prepended this item to the new leaf's via list. The route is the inherited all-continuous-coefficient obligation in paragraph (3) of `det-thm-sf-ctf-stability-direct-images`, through complete-group torsor monodromy. I read the recorded chapter and unit, including the clause (iii)/(vii) direct-image route. This subsidiary topological argument does not change either. Whole-blueprint searches for `forgetful automorphisms`, `Noohi`, `Cauchy`, `finite intersection`, `compact intersection`, `closed subsets`, and `005D` found no equivalent blueprint statement.

## Mathlib searches and reading

All new searches ran through `/home/ubuntu/weil-launcher-all/batch2/msearch.py NP lem-sfb-complete-group-forgetful-automorphisms`, and their exact queries are in the node records and command-generated log. I retained the item's inherited search records. For the item I tried two semantic formulations, Loogle, LeanSearch, and source grep. I read `Mathlib/CategoryTheory/Galois/IsFundamentalgroup.lean`, especially its `CompactSpace G` hypotheses, `FintypeCat` fibre functors and lines 271–290. Its finite Galois category reconstruction does not cover noncompact complete groups or the orbit category of all open subgroups. The NonarchimedeanGroup and DiscreteContAction hits define relevant notions but do not prove reconstruction.

For the new leaf, LeanSearch and LeanFinder both return `CompactSpace.iInter_nonempty`. Loogle returns the more general compact-subset statement `IsCompact.inter_iInter_nonempty`. I read the local declarations and proofs at `Compact.lean:295–299` and `825–829`; the leaf has exactly the latter hypotheses and conclusion. The source grep over `Topology/Compactness` confirms its file and line. The empty finite intersection is explicitly included; Mathlib's empty bounded intersection is the whole space. No service failed in these searches.

## Not duplicates

lem-sfb-compact-closed-finite-intersection vs lem-sfb-compact-discrete-quotient-realization: the existing leaf realizes compatible choices over all discrete quotients of a compact space; it does not state the finite-intersection property for arbitrary closed subsets. The new leaf is the generic compactness theorem used directly on cosets.

lem-sfb-compact-closed-finite-intersection vs lem-sfb-finite-quotient-fiber-product: the existing node identifies a fibre product of profinite spaces with a compatible finite-set limit; it does not state the closed-family theorem on a general compact space.

lem-sfb-compact-closed-finite-intersection vs lem-weil-pbc-quasicompact-components-clopen-intersection: the existing node identifies a point's connected component using clopen neighborhoods, assuming a compact-open basis and quasi-separatedness; neither that conclusion nor its hypotheses give the generic closed-family intersection theorem.

lem-sfb-compact-closed-finite-intersection vs lem-weil-pbc-spectral-proconstructible-closure-specialization: the existing node obtains a specializing point in an intersection of constructible sets of a spectral space; the new leaf requires only quasi-compactness and concerns arbitrary closed sets.

lem-sfb-compact-closed-finite-intersection vs det-pe-condensed-point-basis: the existing node identifies affine ind-etale schemes over a separably closed field with profinite sets; it does not state generic compactness.

lem-sfb-compact-closed-finite-intersection vs det-pe-wc-cover-second-stage: the existing node constructs a faithfully flat ind-Zariski ring extension with w-contractible spectrum; it is not a topological closed-intersection lemma.

lem-sfb-compact-closed-finite-intersection vs lem-weil-pbc-constructible-module-support-constructible: the existing node concerns stalk vanishing and constructibility of module-sheaf support, not intersections of closed sets in compact spaces.

lem-sfb-compact-closed-finite-intersection vs lem-weil-pbc-spectral-constructible-finite-intersection: the existing statement assumes a spectral space and constructible subsets (closed in its constructible topology); the present use is a family of closed cosets in an arbitrary compact topological group, with neither a spectral-space hypothesis nor a constructibility hypothesis. The new leaf is already an exact Mathlib theorem and supplies the general topology fact directly.

## Review by NP

I read Bhatt–Scholze, *The pro-etale topology for schemes*, the local arXiv PDF, printed pp. 63–64: Definitions 7.1.1 and 7.1.3, Lemma 7.1.4, Proposition 7.1.5, and Example 7.1.6. The source uses compatible identity cosets and their inverse cosets to construct a Cauchy filter; my proof writes that argument as a net indexed by finite coordinate constraints and uses exactly the completeness assumption stated in this item. For the new node I read Stacks `topology.tex`, `lemma-intersection-closed-in-quasi-compact` at line 1724, and checked in `tags/tags` that its tag is 005D. The lemma assumes only quasi-compactness and permits arbitrary closed subsets. I also read the exact Mathlib declaration, not just the search summaries.

Step 1 cites `def-nagata-category`. I opened its full statement: it gives objects, arrow sets, identity, composition and their laws. I use it only for those category axioms. The sets of open subgroups and arrows ensure smallness; the definition of natural automorphism is written in the step, including inverse naturality. Step 2 directly computes the naturality and group laws of translation and the finite coordinate conditions for continuity of multiplication and inversion. Step 3 computes stabilizers and their open-and-closed cosets and proves injectivity using the actual Hausdorff and subgroup-basis hypotheses. The stabilizer of the identity coset pulls back to U, which also gives continuity of the inverse after surjectivity. These are elementary calculations, not an invocation of finite Galois reconstruction.

Step 4 explicitly gives the single common open subgroup V and every comparison arrow q_j; naturality at V proves simultaneous realization. No new node restates that part of the item's conclusion. Step 5 defines the directed set and the chosen net and records the closed sets C_x. Step 6 verifies both differences by evaluating at x and alpha-inverse(x), so it uses neither normality nor an abelian-group convention. Step 7 invokes the *hypothesis* of two-sided net completeness, then proves the closed-tail limit argument in one line. None of steps 4–7 hides a standard lemma about completion, uniform embeddings, or closed subgroups.

Step 8 is the only non-elementary tool invocation. Its cited new node says exactly that an arbitrary family of closed subsets of a quasi-compact space, including the empty finite subfamily, has nonempty total intersection when all finite intersections are nonempty. Step 5 established closedness and step 4 established those finite intersections; compactness of G supplies the remaining hypothesis. The citations file quotes the complete statement of that leaf verbatim. Step 9 assembles the already obtained equalities into bijectivity and the topological group isomorphism.

Steps 10 and 11 prove the all-actions clause explicitly. For each point s, continuity gives the open stabilizer U_s; the arrow q_s from its orbit is written down. Naturality determines every extension at s, and translations supply existence. This proves restriction is a group isomorphism without assuming that arbitrary natural automorphisms preserve a previously chosen orbit decomposition. The formula beta_S(s)=q_s(alpha_{U_s}(U_s)) proves the inverse restriction map continuous one coordinate at a time; finite conditions give precisely the topology in the statement. This is an elementary consequence of the displayed arrows and evaluation definitions, not an unproved category equivalence.

I tested G=1, arbitrary discrete groups (where U={1} occurs), finite and profinite groups, and the complete noncompact permutation group of an infinite set. The proof uses finite intersections of conjugate subgroups rather than finite index or normality, so the noncompact and nonnormal cases are included. On the incomplete subgroup of finitely supported permutations of a countable set, the constructed net can tend to an infinite permutation outside G; step 7 correctly requires completeness and does not claim convergence there. The empty action has a unique bijection and imposes no coordinates. The new compactness leaf is true for empty X vacuously (the empty finite intersection hypothesis then fails), for a one-point space, and for arbitrary non-Hausdorff quasi-compact spaces. Every proof step is below 2000 characters. I checked B–E against these arguments: no added hypotheses, weakened conclusions, SGA references, new unsplit nodes, duplicate statement, or unsupported non-elementary citation remains. Only the two stated citation pairs occur, and both quotes were checked as literal substrings.

## Unfinished

None in this one-level split. No Lean was written and no compiler, Lake, or build command was run. The final required dry run and push are performed with the supplied delivery tool.

## Dry-run repairs

The first preflight returned two metadata diagnostics on the new leaf: it needed an explicit node citation in its statement and an explicit Mathlib line field. I added `mathlib_match.line = 825`, already verified in the pinned source. For size, I opened and read `def-weil-size-convention`: its first sentence fixes compatible Grothendieck universes, which is the only part used. The leaf now cites this convention for the sets and index families, matching the item's existing universe qualification and the existing compact-discrete-quotient leaf. The topology, compactness and closed-set meanings are still given directly; the size node is not cited as a theorem about topology. This is a statement dependency of the leaf only, so it introduces no new item proof-step citation. The verbatim step 8 quote in citations.json was updated to the final leaf statement. No mathematical hypothesis or conclusion of the compact-intersection fact changed.

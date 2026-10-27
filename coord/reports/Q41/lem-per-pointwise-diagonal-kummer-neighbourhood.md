## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-pointwise-diagonal-kummer-neighbourhood.json: item, split in ten steps; no Mathlib match; statement unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-affine-inert-equivariant-refinement.json: new statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-log-regular-generization.json: new statement, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for each dependency of every proof step.

There are two new nodes and zero Mathlib leaves. New nodes carry statements only; neither is a replacement name for the pointwise diagonal model. The item still proves the tensor comparison and its descent explicitly.

## Attachments

None. Searched the actual live project under lean/WeilConjectures for the item tag and for pointwise diagonal, logarithmic regularity, very tame actions, Kummer charts, inert etale neighbourhoods and equivariant neighbourhoods. Existing Kummer-cohomology, fundamental-group inertia and equivariant sheaf statements do not state this logarithmic local model. The two new statements have no corresponding project declaration either. No Lean file was written and no compiler or Lake command was run.

## Wanted literature

None: all source passages used here are in the retained ILO PDF or the retained Stacks source. Kato's original article is referenced by ILO VI 1.3 but is not a separate source used in this delivery.

## Corrections and qualifications

The imported item has no proof; it is a valid pointwise formulation. Its statement, hypotheses and all its original metadata remain unchanged. I did not infer the item from lem-per-very-tame-log-quotient: that node assumes both a globally very tame action and generic freeness, neither available here. Nor did I cite the integral-pair quotient-log-regular node, whose hypotheses likewise do not apply. Those existing proofs helped locate reusable statements, but their internal arguments are not used as black boxes.

The source's terse VI 3.7(c) says the closed immersion becomes an isomorphism. Steps 4--7 supply the dimension and domain argument. It is essential to establish log regularity on the whole spectrum of the invariant strict local ring before applying the existing Kummer ascent theorem. That is why the new generization lemma is needed; regularity of a closed stratum at one point is not an assertion that some regular locus is open. Steps 8--9 descend the isomorphism using finite modules over the invariant base; shrinking only the source inside a standard cover would lose the tensor presentation requested by the item.

No statement dispute or source correction is asserted. In particular the source's phrase “of group H” is not used to assert faithfulness in our nonfaithful setting: the character pairing and the entire proof allow a kernel. The proof never applies a Galois-cover theorem requiring a faithful H-action. The final ring called B is explicitly renamed from the localized finite-type neighbourhood, not the intermediate strict local ring.

## Searches and blueprint

Read the current blueprint through literature/blueprint/latest, including lem-per-artin-gabber-affine-curve and the enclosing chapter and unit records. The nearest ancestor is lem-per-artin-gabber-affine-curve; these tools serve its inherited regular-local-model/purity dependency chain, not a replacement route for the Fourier unit. The item is not the key statement of its unit, so no unit realization record was changed.

Before creating either node, searched the whole DAG statements, source places, and keywords, as well as tools/blueprint_refs.py search for Kummer, very tame, inert, inertia, inertia-preserving, equivariant neighbourhood, equivariant affine, affine equivariant etale, log regularity, log-regular, log regular generization, and Kato, 1994, 7.1. No blueprint node states either new result. The 52 Kummer hits concern cohomological Kummer maps and purity, not this model. same_as is empty on both new nodes and remains empty on the item.

All Mathlib searches were run with batch2/msearch.py and are recorded from searches.jsonl. Each new node has LeanFinder, LeanSearch, Loogle and grep searches, with distinct natural-language formulations. Affine refinements returned ordinary etaleness/base-change, general affine refinements and set-theoretic stabilizers; these do not construct an equivariant inertia-preserving affine refinement. Generization returned ordinary regular rings, local-ring closed points, specialization and generalizing-map facts; these do not treat fs log structures or the logarithmic dimension criterion. In particular IsRegularRing.isRegularLocalRing_localization is ordinary regularity, not log regularity. Loogle's item query reported an unknown IsEtale identifier in its index; that query is not evidence of absence on its own. The semantic and source searches also found no item match. No unsupported successful search or unavailable service was invented.

## Not duplicates

lem-per-affine-inert-equivariant-refinement vs lem-per-pointwise-diagonal-kummer-neighbourhood: generic refinement of an already given equivariant etale neighbourhood, with no log regularity, character pairing, invariant ring or tensor model; it is one scheme-theoretic tool in Step 1, while Steps 2--10 carry the actual local-model argument.

lem-per-affine-inert-equivariant-refinement vs lem-per-abelian-inert-rigidification-cover: the latter constructs global rigidifications for regular quasi-excellent SNC pairs, with abelian inertia and freeness off the boundary, and depends on the item's parent; the new node has no boundary or rigidification and refines arbitrary pointed equivariant etale maps for arbitrary finite groups.

lem-per-affine-inert-equivariant-refinement vs lem-per-inert-etale-quotient-comparison: the latter compares existing quotients and describes an inert open locus, but does not construct affine equivariant refinements through an arbitrary, possibly nonseparated, etale source, or preserve the stabilizers in a larger group G.

lem-per-affine-inert-equivariant-refinement vs lem-per-simultaneous-cohen-rigidification-lift: the latter lifts two rigidifications to ambient complete regular schemes; its inert-induction reference is not the generic pointed affine refinement asserted here.

lem-per-affine-inert-equivariant-refinement vs lem-per-cyclotomic-finite-etale-cover: adjoining roots of unity is a specific finite etale base change; the new statement refines any given equivariant etale neighbourhood and uses no roots.

lem-per-affine-inert-equivariant-refinement vs lem-per-cyclotomic-monic-positive-degree: the latter is a polynomial fact used at the same ILO place, with no neighbourhood or inertia assertion.

lem-per-affine-inert-equivariant-refinement vs lem-per-cyclotomic-field-root-criterion: the latter characterizes primitive roots of unity over fields, not equivariant affine refinements.

lem-per-affine-inert-equivariant-refinement vs lem-per-very-tame-equivariant-sharp-chart: the latter constructs diagonal logarithmic charts from tameness and trivial characteristic action; it does not assert affineness or equality with all ambient G-inertia groups at all geometric points.

lem-per-affine-inert-equivariant-refinement vs lem-pd-invariant-affine-neighbourhoods: the latter concerns transport descent for finite flat covers with a finite-subset affine condition; it does not refine arbitrary equivariant etale maps or control inertia in G.

lem-per-log-regular-generization vs lem-trf-log-regular-completed-chart: completed normal forms assume a log regular scheme and describe one completion; they do not state propagation of pointwise log regularity along generizations.

lem-per-log-regular-generization vs lem-trf-log-regular-divisorial-structure: the latter assumes global log regularity and concludes normality and divisorial reconstruction; the new node starts with log regularity at only one point and propagates that condition.

lem-per-log-regular-generization vs lem-per-ind-etale-regular-coordinate-locus: the latter is an openness and coordinate-invariance theorem for quasi-excellent ordinary SNC situations; the new statement is about arbitrary locally Noetherian fs log schemes and does not assert openness.

## Review by Q41

I read ILO VI 1.2--1.3 (printed p.69), 1.6--1.8 (p.70), 2.2--2.3 (pp.72--73), 3.1 and 3.4--3.7 (pp.73--76), and VIII 5.3.6--5.3.7 (pp.124--125). I also read the cited normality conventions in VIII 3.4--3.5 and the Stacks source behind the module descent. Tags 00HP and 00IK were checked against tags/tags and algebra-lemma-ff and algebra-lemma-Noetherian-basic, respectively. I read the statements of every dependency below; citations.json contains their actual text, not a quote reconstructed from a proof.

For the new affine-refinement node I checked the generic construction behind VIII 5.3.7, without importing its unnecessary quasi-excellence, abelian or SNC hypotheses. One proof for its later worker is: take an affine pointed open in V and form the finite product over X of its H-translates. This product is affine because X has closed diagonal; the twisted permutation action fixes the chosen point. The open locus where all maps to V agree contains that point, since V/X is etale and its diagonal is open. On that locus the projection is equivariant. In an affine H-scheme with an H-fixed geometric point every invariant open neighbourhood contains an invariant principal neighbourhood: choose D(t) inside it and replace t by the product of its H-translates. Remove also the inverse images of X^g for g outside H. For h in H, on the closed inverse image of X^h the condition h fixes the source point is open and closed, since the source map is separated etale. Its complement is therefore closed in the source. Remove the finitely many such bad sets and choose another invariant principal neighbourhood. This produces the asserted equality of geometric stabilizers, including residue-field embeddings. Etaleness gives local Noetherianity and the affine source is Noetherian. This is a genuine general equivariant neighbourhood lemma, not an assertion that the logarithmic tensor model already exists.

For the new generization node I read the explicit assertion in VI 1.3, which states exactly preservation of log regularity under generization, using the definition at a point in VI 1.2. The local-spectrum consequence follows because every prime is contained in the maximal ideal. It has no tacit excellence assumption and does not strengthen generization stability to openness.

1. Step 1 uses the actual equivariant sharp-chart theorem for the diagonal chart and fixed roots, the new affine-refinement theorem for an affine inert neighbourhood, and strict-local invariance for the stalk identifications. The refinement's input point is H-fixed, X is separated locally Noetherian, and the pulled-back chart has the same characteristic. The global chart's equivalent cyclotomic formulation supplies the fixed coefficient map; it is not assumed from a mere germ.
2. Step 2 uses the finite tame admissible scheme quotient and finite-quotient strict-local invariants, whose statements do not assume generic freeness or log regularity. Affineness supplies admissibility, and inverting n supplies tame inertia at every point even though very tameness is only known at the selected point. The strict-henselization Noetherian equivalence applies to both local rings.
3. Step 3 uses exactly the local Kummer-quotient statement: P, its group completion and finite index, the invariant chart, and the stratum isomorphism B/J = A/I. The finite extension, fixed roots, invertible order and trivial action on A/I were all checked first. The chart on U, not merely a strict-local chart, makes a(p) an actual invariant global section for p in P.
4. Step 4 uses finite implies integral and equality of dimensions for injective integral maps. The equality of ranks is proved from nQ^gp contained in P^gp. The fs log definition gives the closed-point condition from B/J = A/I. The new generization theorem is applied on the spectrum of the strictly local B to obtain the global hypothesis needed next. No global very-tame condition has been smuggled in.
5. Step 5 gives the finite set of monomial module generators explicitly, and uses finite-algebra Noetherianity and the finite henselian-product theorem for precisely their stated conclusions. The nilpotent monomial ideal in the closed fibre has residue quotient k(B), so the product has one factor and its residue field is separably closed. Sharpness and saturation rule out torsion, as written in the step. This checks locality without a flatness assumption on the Kummer cover.
6. Step 6 applies the invertible-Kummer chart ascent theorem to the now globally log regular local base. Its comparison is the identity, not an unproved etale map. Noetherianity is Step 5; Kummer and the group cokernel condition are Step 3. The log-regular divisorial theorem explicitly says every local ring is a normal domain, hence gives the domain property of C.
7. Step 7 uses only the strict-local surjection clause of the closed-immersion node, not any unasserted equivariance or quotient-cartesian property of its neighbourhoods. The coefficient-base tensor equality is the universal identification of the common Lambda coefficients. Injectivity B -> C follows from B -> A. The finite-dimensional prime-chain argument for zero kernel is written out; it is not a hidden logarithmic lemma. The completion-dimension statement explicitly includes finiteness of dimension for Noetherian local rings.
8. Step 8 uses the quotient's actual orbit-fibre assertion and the finite-base strict-localization decomposition. The selected point is fixed by all of H, so there is one geometric fibre point and exactly one strict-local factor. This justifies the entire base-changed ring R0 tensor B = A; knowing only B = A^H would not by itself justify it.
9. Step 9 uses faithful flatness of the strict henselization, flat tensor exactness, detection of a zero module, and finite generation of submodules of a finite module over a Noetherian ring. These statements say exactly what the kernel/cokernel descent needs. The existing Mathlib leaf lem-weil-pbc-localization-module-exact is also cited to identify the localized kernel and cokernel; I added this explicit citation during the final C1 audit. Its source is Stacks Tag 00CS (algebra-proposition-localization-exact). Both source modules are finite over B0; the common denominator outside the selected prime is written explicitly as the product of the finitely many denominators killing their generators. The restriction is on the invariant base.
10. Step 10 uses the affine-open Noetherian theorem for the localized base, the log-chart definition for the strict log isomorphism, and the affine-refinement node for the inertia equality inherited under invariant restriction. The selected point survives because f is outside its base prime. Equivariance is checked on b and on every monomial, so there is no missing transport argument.

I tested the following small cases. For H trivial, n = 1, Lambda = Z and P = Q, so the tensor model is the original charted neighbourhood. For a trivial H-action with H nontrivial, adjoining roots of unity and inverting n is etale at the tame point, the pairing is trivial and again P = Q; no generic freeness conclusion is claimed. With Q = 0, I = 0 and very tameness forces the whole strict local action to be trivial, so C = B = A. For Q = N with a cyclic diagonal action of weight one, P = nN and the displayed ring is the usual invariant coordinate root model; a nonfaithful weight simply gives a smaller finite-index invariant monoid. The affine-refinement statement also allows nontrivial action on the residue field outside H; geometric, rather than ordinary-point, fixed loci are used. The generization statement is vacuous for y = x and includes the trivial-log ordinary regular-local case.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against these files and source passages. New nodes are self-contained statement-only records with definition dependencies and exact blueprint ancestry; there is no new Mathlib leaf or unverified declaration line. No proof step exceeds 2000 characters. No new node is derived and then cited circularly; dependency paths from the reused logarithmic tools do not reach this item. Cross-unit tools are declared in split_report.tool_uses, and the server review accepts those declarations. The pre-report server checks returned check_dag OK and review_split PASS.

## Unfinished work

None within this one-level stage-1 assignment. The two new nodes are deliberately unsplit statements for later workers. The independent maintainer review remains the project acceptance step.

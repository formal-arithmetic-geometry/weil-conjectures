# Q79 stage-1 report: lem-sfb-flag-canonical-character

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flag-canonical-character.json`: item split; statement unchanged; four proof steps, with all dependencies explicit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-cotangent-associated-bundle.json`: new statement-only general smooth-quotient cotangent lemma; Mathlib verdict no match (two LeanFinder phrasings, LeanSearch, Loogle and source grep).
- `citations.json`: eleven step/node entries, each with a verbatim statement excerpt, checked as a substring of the actual dependency statement.
- `searches.jsonl` and `search-*.txt`: search command records and actual output. Additional zero-weight searches were exploratory; the existing rank-one-reflections node already supplies this fact, so no new zero-weight node was made.

## Attachments

None. Searched the live read-only `lean/WeilConjectures/` by the item id and by flag/canonical/cotangent/homogeneous-bundle terms; no project declaration states this result. Ring-theory quotient cotangent comparisons are different objects. No Lean was written or compiler invoked.

## WANTED

WANTED: Brion--Kumar, *Frobenius Splitting Methods in Geometry and Representation Theory*, Section 2.1, printed pp.63--64, for the item and the associated-bundle background of the new node. The named local PDF is absent. I read the primary author PDF at https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf, including equation (7), the paragraph defining L(V), and equation (8). No copy was written into the shared repository. This source calls the canonical-character formula easy to see; it does not provide its determinant argument. The proof is therefore marked agent-written and expanded from Milne's locally available group-theoretic material, not presented as an existing human proof.

## Findings and changes

The imported item was statement-only and had no complete proof. Its sign is correct. In its conventions L_chi uses inverse scalar action in the right quotient, its stabilizer fibre has character chi, and M_mu=L_(-mu). Thus a cotangent determinant character +2rho gives L_(2rho)=M_(-2rho). Brion--Kumar writes L(lambda)=G times^B k_(-lambda); their formula L(-2rho) has precisely this fibre character. No hypothesis or conclusion was changed, and no statement dispute was found.

The nearest blueprint ancestor command returns None, consistently with the inherited `blueprint.from.node: null`; I retained this ancestry and prepended the item to the new node's via list. The newest blueprint (`latest`, snapshot main-20261024) has the six-functors stability unit in sec-six-functors-basics, whereas the old dag/units record names sec-six-functors. I read both and retained the assigned chapter/unit; this is a supporting lemma below the long, already recorded alteration/representation-theory route, not a change of the unit's route. No unit key statement or realized field is owned by this item.

I searched the entire DAG statements/titles and the blueprint index for canonical bundle, canonical line, root space/decomposition, cotangent, cotangent bundle, homogeneous, homogeneous vector, homogeneous bundle, homogeneous quotient and homogeneous cotangent. The existing `lem-sfb-reductive-rank-one-reflections` explicitly states the full adjoint decomposition including the zero character space and the one-dimensional root spaces. I reused it instead of creating the prospective zero-weight lemma. General Lie-algebra root-space results found in Mathlib use weights of Lie algebras; these do not identify algebraic torus characters in small characteristic and are not one-line matches.

## Not duplicates

lem-sfb-homogeneous-cotangent-associated-bundle vs lem-sfb-flag-canonical-character: the new node has arbitrary smooth G and H, no roots, rho, Borel or claimed character; it supplies the differential/associated-bundle comparison, while the item actually calculates the determinant character.
lem-sfb-homogeneous-cotangent-associated-bundle vs lem-sfb-homogeneous-line-bundle-sections: the existing node constructs character line bundles and semi-invariant sections; it gives neither tangent quotient exactness nor a comparison with the sheaf of differentials.
lem-sfb-homogeneous-cotangent-associated-bundle vs lem-sfb-homogeneous-orbit-quotient-geometry: the existing node gives representability and torsor/orbit geometry; it does not give the cotangent representation or its associated vector bundle.
lem-sfb-homogeneous-cotangent-associated-bundle vs lem-sfb-borel-quotient-proper-geometry: the existing node gives smoothness and properness, without identifying differentials or exterior powers.
lem-sfb-homogeneous-cotangent-associated-bundle vs lem-sfb-borel-characteristic-picard-sequence: the existing node gives an exact Picard sequence for Borel quotients, not a cotangent comparison for arbitrary smooth stabilizers.
lem-sfb-homogeneous-cotangent-associated-bundle vs def-sc-relative-differential-sheaf: the existing node defines relative differentials on affine charts; it states no homogeneous comparison theorem.
lem-sfb-homogeneous-cotangent-associated-bundle vs def-sc-sheaf-exterior-power: the existing node defines the sheaf exterior powers; it states no compatibility with homogeneous cotangent descent.

## Review by Q79

I read the item source in the Brion--Kumar author PDF, Section 2.1, including the definition of positive roots as weights in Lie(U), the convention (7), and formula (8). For the general new node I read Milne iAG2017 Proposition 7.15 (pp.142--143: smooth stabilizer gives smooth quotient projection) and Section 18c (pp.389--390: descent and reconstruction by the stabilizer fibre, especially 18.11 and the proof of 18.14). These motivate the general vector-bundle comparison, which remains an explicit unsplit prerequisite, rather than hiding it inside a supposedly elementary proof step. Milne 18.14 itself only treats line bundles; I did not cite the existing line-bundle-sections node as if its statement gave cotangent reconstruction.

For step 1 I opened the entire statement of reductive-borel-pair-structure: it says semisimple implies reductive and supplies the represented quotient and right B-torsor. The new node assumes exactly such a torsor for smooth G and H; here S and B are smooth by the item hypotheses. Its statement explicitly supplies the contragredient cotangent comparison, top-wedge comparison and pure dimension. This closes the significant geometric input, and step 1 is not marked elementary.

For step 2 I opened rank-one-reflections and regular-cocharacter-borel-description. The former explicitly writes Lie(S)=Lie(T) plus all root spaces and says each root space has dimension one. The latter says every B through T is P(lambda) and writes its Lie algebra as Lie(T) plus its positive root spaces. The positive system in reductive-borel-pair-structure has one sign for each root, so quotienting those displayed direct sums leaves exactly the negative root lines. This is elementary linear algebra from the cited statements, not a new root-theoretic assertion. I read Milne p.425, Theorem 21.11(b), and 21.29--21.35, pp.433--435, to check this in all characteristics.

For step 3 the displayed dual-basis calculation is written on arbitrary F-algebras; it computes the product of the positive-root characters. I opened rho-section-modules and checked that its statement supplies the actual integral character rho with 2rho=sum positive roots. I opened unipotent-to-multiplicative-trivial and checked its statement applies to every unipotent source and multiplicative-type target. Here the source is the unipotent radical U and the target is G_m, which is itself a torus; there is no finite-order or reduced-point assumption. I read Milne Corollary 14.18(a), p.284, in full. The already cited split product B=U semidirect T implies that the determinant character on all of B is (2rho) composed with p. This is two elementary calculations from the cited black boxes, so the step is marked elementary with its dependencies, not asserted without them.

For step 4 the new node explicitly includes top exterior powers; the homogeneous-line-bundle-sections statement explicitly gives the inverse-scalar quotient action. I checked these actions agree, rather than treating an abstract existence of an invertible sheaf as an identification of its character. The rho definition and the definition of M then give M_(-2rho). For the empty-root case the regular-cocharacter node explicitly says P(0)=T=G; since B is P(lambda), Q is a point. The empty wedge and empty character product are O and 1. Each of the eleven uses has a literal quote in citations.json; the report spells out the additional relevant clauses where the chosen short quote does not contain the whole cited statement.

I tested the new lemma on H=1 (left-invariant cotangent trivialization), H=G (zero-dimensional point quotient), and a torus with a subtorus (trivial adjoint quotient representation). I tested the item's sign on S=SL_2 with upper triangular B: the tangent weight at eB is -alpha, the cotangent weight is +alpha=2rho, and the canonical line is O(-2), in agreement with the stated convention. This remains valid in characteristic 2 because alpha is the torus character t maps to t^2, even when its differential vanishes. The proof never uses a Killing form or identifies characters with their derivatives. I checked N=0 separately as above. No source error was found.

Against delivery-errors B--E: the single new node has a self-contained statement, declared notions and explicit group-scheme actions, no proof or proof dependencies, searched Mathlib with actual logged queries and a second phrasing, and filled blueprint ancestry. It is a general prerequisite, not the item's conclusion moved to another id. I reused all existing root and unipotent facts and did not make elementary determinant computations into nodes. Every non-elementary input is named; every cited node was read as a statement, not mined for an extra fact in its proof. The proof-dependency list is exactly the union of step uses. No step exceeds 2000 characters, and the four-step assembly is below 3000 characters in total. I wrote no review acceptance record or maintainer-owned fields.

For a future split of the new node, the intended argument (not part of its statement) is to obtain tangent exactness from smooth q and identify its kernel with Lie(H) by the torsor fibre. Translation trivializes q-pullback of the cotangent bundle with fibre (Lie(G)/Lie(H)) dual. Changing a lift g to gh changes the fibre coordinate by h inverse; the torsor relation supplies the cocycle. Descend this comparison and then apply the same calculation to exterior powers. The hypotheses explicitly require smooth H to avoid inseparable quotients with a non-surjective tangent differential.

## Unfinished work

No part of this one-level split is omitted. The new general cotangent lemma is deliberately statement-only and joins the stage-1 queue. The required server checks and delivery follow this report.

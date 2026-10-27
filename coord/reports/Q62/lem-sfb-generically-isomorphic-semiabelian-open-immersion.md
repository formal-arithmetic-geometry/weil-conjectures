## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-generically-isomorphic-semiabelian-open-immersion.json`: item, statement; ten-step complete argument, status split; no Mathlib match. Original statement, original search records and provenance retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite.json`: new statement-only lemma, status unsplit; Conrad Corollary 3.3, no Mathlib match after both semantic phrasings, Loogle and source grep.
- `citations.json`: one exact statement quotation for every step/node pair.

## Attachments

None. Searched the read-clone `lean/WeilConjectures/` for the item's blueprint tag and for semiabelian, semi-abelian, generic-isomorphism and relevant torsion notions. No project declaration states the item or the new lemma. The Mathlib candidates concerning open immersions, birational maps and abstract torsion groups do not supply these assertions.

## Literature wanted

WANTED: Brian Conrad, Semistable reduction for abelian varieties, Corollary 3.3 (printed p.8) and proof of Theorem 4.4 (printed pp.12–14), for lem-sfb-generically-isomorphic-semiabelian-open-immersion and lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite. The local PDF is absent; I read the primary author PDF online at https://math.stanford.edu/~conrad/DarmonCM/2011Notes/SemistableReduction.pdf . No literature was downloaded or written. The item's proof is marked agent-written because the printed theorem has abelian generic fibre and a Neron target, whereas this item extracts the given-map argument for a more general target.

## Problems and changes

The imported item was unsplit. I found no false assertion and retained its entire statement, including arbitrary DVR, possibly imperfect residue field, and no quasi-compactness or finite-type assumption on B. The most delicate potential error was to import a finite-type-target group-fibre lemma or to assert that B[ell] is finite. Neither follows from the hypotheses. Instead I give the translation isomorphism of each nonempty geometric fibre explicitly and prove triviality of the etale torsion kernel by its open-and-closed identity component and flatness. Zariski Main Theorem is applied over affine target opens, where its qcqs hypothesis holds, and its integral normalization map is treated by the existing integral-birational-normal isomorphism lemma, without assuming the normalization finite.

The current blueprint is the latest 2026-10-24 main snapshot. I read the current six-functor chapter/unit and searched all blueprint references for the item's notions, subgroup torsion, finite kernels, and normalization. The inherited created.item chain has no blueprint ancestor (`blueprint_refs.py ancestor` returns None); I preserved its from/via chain and supplied the exact trait-extension local role. No same_as was found. `coord/repair-notes/lem-sfb-generically-isomorphic-semiabelian-open-immersion.json` and `coord/dag-sync.md` were absent. No Lean was written or compiled; no git command was run in the read repository.

## Unfinished work

The new lemma is intentionally statement-only as required by a one-level stage-1 split. Its later worker can follow Corollary 3.3. There is no unfinished part of the item's assembly proof.

## Review by Q62

I read Conrad Corollary 3.3 itself for the new node, including its treatment of nonreduced closed subgroups, and Theorem 4.4's proof for the item's route. I checked the proof against the actual generality here rather than identifying our statement with the printed Neron-model theorem. I read the corresponding Stacks statements for etale permanence (02GW), etale base change (02GO), unramified diagonals (02GE), smooth ascent of normality (034F), relative normalization (035H/035I), Zariski Main Theorem (02LR), and the integral birational normal-target argument (0AB1). The cited tag/label pairs were checked in the local Stacks tag index. No SGA source is used.

In step 1 I checked the statements of the closed-base-change, proper/fp-permanence and finite-type-permanence nodes: they give precisely the graph's closedness, closed implies proper implies finite type, and base-change/composition finite type. The graph and relative diagonal squares are written out. Finite presentation supplies finite type via the cited finite-presentation and finite-type definitions; this establishes finite type of the MAP even when B is not quasi-compact.

In step 2 I read the geometric-power-integrality node: its n=1 assertion applies to the semiabelian geometric generic fibre because the definition supplies a split torus extension by an abelian variety over the algebraic closure. The field-extension descent is written out by a vector-space basis, including nonemptiness. In step 3 smooth-flat and the flat-ring definition justify injectivity of uniformizer multiplication on stalks; the localization definition gives both injectivity into C[1/pi] and the zero-localization criterion. I used stalk flatness rather than silently assuming flatness of an arbitrary section ring. Every nonempty affine therefore meets the integral generic fibre, proving the required integrality and density without a qc hypothesis.

In step 4 I checked that the DVR definition supplies PID, the PID node supplies normality, localization-normality and the affine-stalk node supply normal local rings of Spec R, and smooth-normal-ascent allows an arbitrary smooth scheme over that normal base. No excellence or residue-field perfection is inserted.

In step 5 I read the invertible-multiplication node carefully: it asserts etaleness and base-change compatibility for any smooth commutative group algebraic space, explicitly WITHOUT finite torsion. It applies to represented group schemes. The chartwise-etale-permanence node explicitly permits every map between etale objects over the same base, which is the assertion used for E to D. The kernel is its scheme base change along the identity. Closed identity sections, their pullbacks, and separatedness of their composites are justified by the closed-immersion and proper/permanence nodes; I added the separated-composition citation during review.

In step 6 I verified the unramified-permanence and diagonal-open statements, including their scheme-base-change clause. Pulling the diagonal back along (1,e p) makes the identity open; step 5 makes it closed. The generic isomorphism kills the complementary generic fibre. The flatness clause in the etale definition and the explicit localization relation contradict a nonempty complementary affine. This proves L=T without henselian lifting or finite torsion. The fibre-product identification needed in step 7 is given on all test schemes with inverse projection maps, not inferred merely on geometric points.

In step 7 I checked the new lemma's hypotheses one by one: Omega is algebraically closed, ell is invertible, A_Omega is smooth by clause (2) of the proper-base-change node (which also states smooth base change), separated by the diagonal square, finite type by base change, and semiabelian by the prescribed geometric-fibre definition. The kernel is a closed subgroup even if nonreduced; its scheme-theoretic ell kernel is L_Omega. Conrad's Corollary 3.3 then gives precisely finiteness.

In step 8 the cited finite-map node gives finiteness of the underlying set of a finite scheme over a field. The surjective-base-change node applies to Spec M over Spec kappa(y). Translation by the chosen point is exhibited with both inverse maps and the group-law equations; thus no torsor triviality theorem or finite-type assumption on B is hidden. The fibre-discrete node needs only local finite type and a finite underlying fibre, both already established. The quasi-finite definition then applies globally to the finite-type map.

In step 9 I checked the normalization-open node's separated finite-type everywhere quasi-finite and qcqs-target hypotheses. I added the existing affine-qcqs lemma explicitly rather than leaving this hypothesis implicit. Relative-normalization clause (iv) gives exactly integrality of N from integral X; its qcqs MAP hypothesis holds since f is finite type and separated. In step 10 the generic-fibre isomorphism and open j give the same generic local rings. The cited integral-birational-normal lemma applies to an INTEGRAL map, without requiring finite type, and to the normal integral V. The final open identifications and their inverse maps agree because they restrict the same a, and hence glue as described by the open-immersion definition.

I checked edge cases: zero torus/zero-dimensional abelian quotient; finite nonreduced kernels in residue characteristic p; mixed characteristic with ell different from p; residue characteristic zero; empty fibres of a; and a smooth target with extra special-fibre components and no qc assumption. The new lemma allows finite nonreduced H (e.g. p-primary torsion) and does not assert H trivial. The torsion step never uses characteristic-p multiplication. Each proof step is below 2000 characters; none contains a deferred standard comparison. I compared every uses entry with the node's actual statement and produced its verbatim statement quote in citations.json. The elementary field, localization, kernel and translation computations are written in the item; they were not inflated into new nodes.

## Not duplicates

lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite vs lem-sfb-smooth-group-invertible-multiplication: the latter makes invertible multiplication and its kernel etale for a smooth ambient group, but does not deduce finiteness of an arbitrary possibly nonreduced closed subgroup from trivial torsion.

lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite vs lem-sfb-finite-kernel-group-fibres: the latter assumes a finite kernel and concludes finite group-map fibres with finite-type targets; the new node proves finiteness of a closed semiabelian subgroup using its torsion.

lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite vs lem-sfb-semiabelian-geometric-power-integrality: the latter states integrality of powers of a semiabelian group, not the closed-subgroup torsion criterion.

lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite vs lem-sfb-generically-isomorphic-semiabelian-open-immersion: the new field-level subgroup criterion has no trait, generic comparison, or open-immersion conclusion. It isolates the independent Corollary 3.3 input rather than restating a clause of the item.

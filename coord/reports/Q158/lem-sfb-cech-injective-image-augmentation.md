# Stage-1 delivery: lem-sfb-cech-injective-image-augmentation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cech-injective-image-augmentation.json: statement, now split into seven proof steps; no Mathlib match for the whole item.
- No new DAG nodes, hence zero new Mathlib leaves. citations.json contains the 18 step-node citations with verbatim statement excerpts. searches.jsonl records the actual searches for this delivery.

## Attachments

None. The exact blueprint tag is absent from lean/WeilConjectures. Concept searches found general presheaf-nerve acyclicity and special site/topological Cech augmentations, but no project declaration giving every clause of this item. In particular injective_presheaf_module_nerve_acyclic gives only positive presheaf-nerve vanishing; injective_cech_augmentation_quasiIso concerns abelian coefficients and site-representable covering families. Neither gives this module-valued ringed-topos direct-image augmentation with arbitrary slice objects.

## WANTED

None. All sources used are present in literature/stacks-project.

## Audit and changes

The item had no proof and was unsplit. I retained its complete statement and its statement dependencies, and used existing DAG lemmas rather than creating new names for its clauses. The proof follows the supplied Cech route. It distinguishes arbitrary sheaf-object slices from representable site slices, and injectivity as modules from injectivity of the underlying abelian sheaf. The latter is never assumed.

The item inherits chapter sec-six-functors-basics and unit sk-thm-sf-ctf-stability. I read both records and the unit's direct-image clause. This auxiliary construction is not a key-node realization of that unit; I did not change the unit. The ancestor tool reports null for this created-node chain, so I preserved blueprint.from.node = null and its inherited via chain, specifying which parts of the parent proof are supplied. Blueprint searches for Cech injective, augmentation, presheaf nerve, Čech and injective did not produce a duplicate: sk-thm-picard-cech is a Cech-to-derived spectral sequence for abelian coefficients and site covering families, not this injective module direct-image assertion.

The source tag table identifies module sheafification exactness as 03EI and the kernel-pair coequalizer as 086K; I corrected these tag references while preparing the proof. There is no mathematical statement dispute or change to a target. The source's representable-site 03FC is not being cited as if it already states the arbitrary-object extension: the extension is the actual argument in Steps 1–4.

## Not duplicates

No new nodes. The exact slice adjunction, presheaf-nerve acyclicity, exact module sheafification, effective-epimorphism descent, Yoneda and total-augmentation tools already exist and are cited directly.

## Searches

I read the inherited searches, retained them, and ran fresh searches through msearch.py only: LeanSearch for Cech descent of an injective module sheaf on arbitrary topos objects; Loogle with "Injective", "cech"; grep for injective/Cech and total-quasi-isomorphism patterns in CategoryTheory; and two LeanFinder phrasings, one about the whole augmentation and one about arbitrary presheaf nerves. All services answered. Hits were Mayer–Vietoris squares, generic injective resolutions, local injectivity, ShortComplex.Exact.descToInjective and Stone–Cech injectivity. None states the whole item. I inspected the project presheaf-nerve theorem and its proof, and the abelian injective Cech augmentation, as the relevant existing specialized results. The queries and actual hits are retained in the item and the machine log; no unrun query is recorded.

## Review by Q158

I read Stacks sites-cohomology.tex at 03FB and 03FC, including the proof through injective presheaves and free Cech complexes, and homology.tex at 0133 including its explicit second-variable variant. I also read sites-modules.tex at 04IE, the exact extension-by-zero argument, and 03CY/03EI, and sites.tex at 0791, 00WM/00WN and 086K. No SGA source is used. No new-node sources require review because none were created.

Step 1 uses the actual statement of lem-weil-pbc-ringed-sheaf-slice-adjunction: it supplies a small presentation for arbitrary sheaf A and an exact left adjoint to restriction. The extension argument from the definition of injectivity is written explicitly. It needs no section of A, no subterminality and no assumption that A is representable. The larger coefficient universe contains the elements indexing this presentation.

Step 2 uses the module direct-image definition's underlying sheaf identification, its sheaf adjunction, sheafification's universal property and the general Yoneda bijection (not just fully faithful Yoneda). The slice lemma supplies relocalization and its ring. I checked the formula is Hom(A times V_n, underlying I), equivalent to sections on the indicated slice object. Precomposition by deletion is written down, as is the unit's actual restriction map; this also verifies addition, structural scalars and compatibility with d_I. No unstated base-change theorem for direct image is used.

Step 3 uses exact ringed-module sheafification, its adjunction, and the definition of injectivity to prove presheaf injectivity. The existing presheaf-nerve acyclicity statement explicitly permits arbitrary maps of presheaves with no site pullbacks. Here P=V_A and Q=1 have values in the chosen coefficient universe. I wrote the free-abelian universal-property identification of its cochains with generalized sections, including the boundary, so the step does not confuse that theorem with a covering-family theorem or assume abelian injectivity.

Step 4 uses the exact statements of the sheaf epi/local-surjectivity criterion and the kernel-pair coequalizer lemma. The original cover lifts locally on every element-site object; the slice epi hypothesis is verified before applying coequalizer descent. Equality on the two projections is precisely the zero-differential condition, and uniqueness proves injectivity of the specified augmentation. It proves the needed degree-zero claim rather than citing only positive acyclicity.

Step 5 uses the exact ringed-module sheafification theorem. Sectionwise kernel-image equality is an elementary presheaf computation, and exact sheafification gives sheaf exactness. It does not infer exactness of sections from sheaf exactness, or assert direct image is exact.

Step 6 cites the actual first-quadrant augmentation theorem, read in full: its B.flip resolution columns are exactly the fixed-q Cech rows. The conditions on b are verified for this unit, its first horizontal differential and the sign in degree zero. Both degrees are nonnegative and total diagonals finite. Thus no unbounded product total or unjustified convergence is involved. The theorem applies to any nonnegative complex of injectives, without assuming I resolves an object or is exact vertically.

Step 7 uses only the derived-category localization definition and total differential convention. The two coefficient equations check the transpose chain map on horizontal and vertical arrows individually. The involution and identity on n=0 also identify the augmentation exactly.

For small cases, V=1 gives the alternating complex with successive differentials 0, identity, 0, identity, so the degree-zero kernel and higher vanishing agree with the argument. If A is empty, its slice is the degenerate topos and all module-section groups are zero; the extension and descent arguments still apply. Zero I also gives the zero augmentation isomorphism. In bidegree (1,1) the transpose multiplier is -1 and the two displayed arrow formulas have the correct opposite cross signs. The argument never chooses a global section of V or assumes stalks exist. Every step is below 2000 characters, and no non-elementary comparison is concealed in a long step.

I checked B–E of delivery-errors.md: there are no new statement-only nodes to disguise clauses, no duplicate nodes or hidden proof sketch, and no weakening or missing hypothesis. I opened every cited node and generated citations.json directly from its statement; all 18 quotes are literal substrings. The three off-unit black boxes (arbitrary-sheaf slice adjunction, presheaf-nerve acyclicity, first-quadrant augmentation) are declared as generic tools in split_report.tool_uses with their roles. Their own geometric proof routes are not substituted for this unit's route.

## Unfinished work

None in the stage-1 split. The independent maintainer review and downstream formalization remain separate work.

## Validation

The server review_split check passed: 0 new nodes, proof written by an agent. The first complete dry run requested longer citation excerpts for three steps; those excerpts now quote the full cited statements. Required complete dry run and direct delivery follow this repair.

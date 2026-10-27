# Q03 stage-1 delivery: lem-exc-unbounded-coefficient-pullback-model

## Files written

- dag/nodes/sec-six-functors/lem-exc-unbounded-coefficient-pullback-model.json: existing statement, now split into five steps; Mathlib verdict no match for the whole statement.
- citations.json: thirteen entries, one per node cited per proof step, copied verbatim from the live statement fields.
- report.md: this report.

No new nodes; zero Mathlib leaves. The statement, statement dependencies, provenance and inherited search records are retained. Additional searches are recorded exactly as executed through msearch.py and retained in searches.jsonl.

## Attachments

None. A search of lean/WeilConjectures for the blueprint tag found no declaration. Concept searches led to Derived/ScalarExtension.lean: leftDerivedSheafExtendScalarsCompUpperStarIso assumes Module.Flat R S, Module.Finite R S and Module.Free R S in its surrounding section. It therefore does not attach to this arbitrary finite-ring-map statement. KFlatPullback.lean concerns topological structure sheaves, not arbitrary small pro-etale topoi.

## WANTED

None. All sources used are present in literature/.

## Corrections and scope

The live item had no proof. The existing generic site lemmas and the ordinary scalar-balancing chain lemma already state every non-elementary ingredient, so no new node is needed. In particular lem-pc-kflat-pullback-preservation and lem-pc-inverse-image-exact-kflat-resolution concern topological inverse image; they cannot justify a pro-etale claim. I use lem-weil-pbc-ringed-topos-kflat-pullback instead. I also retain the B-valued change-of-rings functor, instead of using the A-valued tensor theorem as if it already remembered the B-action.

The item inherits its chapter/unit from thm-exc-explicit-preservation. The current main-20261015 blueprint moved the latter text to sec-smooth-purity/sk-prop-sp-et-proet. Its final proof sentences still give precisely the inverse-image flat-resolution coefficient-comparison route; the inherited item metadata and blueprint ancestor are preserved. This item is not a key-unit node, so no unit record is changed.

No statement dispute was found. No Lean code or compiler/build command was written or run. Nothing was written in the shared repository or launcher directories.

## Not duplicates

No new-node pairs exist. Searches over all DAG statements, Stacks tags 0G7E/03EL and their labels, and blueprint_refs searches for K-flat, coefficient pullback, scalar balancing and coefficient comparison led to reuse of the existing nodes. The isomorphism-specific lem-weil-isomorphism-scalar-kflat-descent is too restrictive for arbitrary f. The ordinary lem-sp-proetale-scalar-balancing-chain gives the precise B-action, direction and chain formula needed here. The general coefficient-projection comparison is a related broader interface, but using it would introduce its entire normalization datum unnecessarily; this proof assembles the existing concrete ordinary comparison and resolution tools.

## Review by Q03

I read coord/delivery-errors.md B-E, including the merged copy, with the item and the cited node statements open. I read the current main-20261015 ancestor statement and separate proof, the recorded unit and chapter, and the older ancestor proof to locate the inherited paragraph reference. In Stacks sites-cohomology.tex I read lemma-K-flat-resolution (06YS, beginning at line 3207), lemma-derived-tor-quasi-isomorphism-other-side (06YT), the construction preceding definition-derived-tor (06YU), lemma-factor-through-K-flat (0G7D), lemma-pullback-K-flat (0G7E, line 3508) and lemma-derived-base-change (06YY, line 3585). In sites-modules.tex I read lemma-tensor-product-pullback (03EL, line 3649) and its bilinear-adjunction proof. The split is marked agent assembly of these sources and existing DAG statements, not a verbatim theorem of Stacks. There are no new nodes needing separate source verification. No SGA source is used.

Step 1 takes existence with flat terms from lem-pc-kflat-resolution and preservation with flat terms from lem-weil-pbc-ringed-topos-kflat-pullback. The latter explicitly quantifies over small sites and a geometric morphism with structural ring map, which the chosen compatible pro-etale skeletons and canonical inverse image supply. prop-weil-pbc-proetale-constant-ring-map supplies the actual structural-map isomorphism, not merely an abstract isomorphism between coefficient objects. prop-weil-pbc-proetale-constant-exact supplies kernels and cokernels for both finite coefficient rings. The displayed kernel/image-quotient calculation explains preservation of quasi-isomorphisms using exactly def-pc-quasi-iso-modules. This avoids the space-versus-site error and never treats exactness alone as K-flat preservation.

Step 2 uses lem-pur-derived-change-of-rings on X and V. Its statement gives both a functor to B-modules and computation at every K-flat resolution without flatness of the ring map. Exact f_B^* sends the resulting B-complex representative directly to a representative on V; no claim that an arbitrary tensor of two non-flat objects computes a derived tensor is used. The two representatives therefore have the correct coefficient category.

Step 3 uses the entire ordinary conclusion of lem-sp-proetale-scalar-balancing-chain, after renaming its source Y to X and target X to V. I checked its finite commutative-ring hypotheses allow arbitrary A -> B and arbitrary f. Its statement supplies commutation of the constant-ring square, the scalar restriction identity, B-linearity after that identity, the explicit unit-section tensor formula and a natural chain isomorphism for all complexes. Its direction is opposite this item's direction; the step explicitly takes its inverse. Both composites are identities in the common tensor presentation. For homotopy compatibility the step writes naturality on the degree-minus-one maps h^i and hence on dh+hd, rather than assuming naturality on derived morphisms. The pure tensors are local images of presheaf tensors in the sheafification, not arbitrary global tensor decompositions.

Step 4 takes from lem-weil-pbc-site-derived-tensor-descent exactly its first conclusion, the equivalence from the localized homotopy category of flat-term K-flat objects to the derived category. It does not apply its two-variable tensor formula with B falsely assumed K-flat over A. Preservation of quasi-isomorphisms for U and V is instead checked separately using clause (1) of lem-pur-derived-change-of-rings and the exactness established in step 1. The full natural-transformation conclusion (2) of lem-weil-pbc-localization-universal-property then descends t and its inverse. This is the cited localization property for functors and transformations, not a definition node silently used as a theorem.

Step 5 writes the component as gamma_P^{-1}[t_P]alpha_P with the two canonical computation isomorphisms specified. Alpha uses f_A^*q; gamma applies D(f_B^*) to the coefficient-derived computation on P. I corrected an initial draft that referred imprecisely to applying f_B^* directly to the A-resolution q: the final proof uses the B-derived computation isomorphism. The canonical two- and three-resolution comparisons and their cocycle follow from the cited coefficient functor statement and uniqueness/composition in localization-universal-property. No direct comparison map between two arbitrary K-flat resolutions is claimed. This is enough to identify the derived comparison with the derived ordinary coefficient map without adding a normalization hypothesis.

For B1-B10, no statement-only nodes, new notions, fake leaves or duplicate new nodes are introduced; the original TeX and blueprint fields are preserved and actual new queries are appended from the msearch log. For C1-C8, every non-elementary fact above has the exact statement citation described, the quote file covers every use, and generic off-unit tools are declared individually in split_report.tool_uses. For D1-D5, the proof genuinely constructs the chain comparison from the existing ordinary tool and descends it; no new clause-restatement node is created. For E1-E7, I checked both coefficient rings are finite commutative, sites are small in the selected common module universe, f is arbitrary, and the proof has no hidden noetherian, boundedness, constructibility or flat coefficient hypothesis. Each step is under 2000 characters, so no long step conceals a separate comparison lemma.

Small cases checked: f=id gives the identity chain map and its canonical derived coefficient extension; A=B gives the inverse-image unit comparison; B=0 and empty V give zero complexes on both sides, including the zero ring-sheaf convention. A=0 forces B=0 for unital maps. For the non-flat map Z/4 -> F_2 and K=F_2[0] at a point, the bounded-above free resolution with all negative differentials multiplication by 2 becomes the zero-differential F_2 complex in every degree <=0 after scalar extension. Both constructions give that same complex, so the proof retains the infinitely many Tor terms. A general finite map such as F_2 -> F_2 x F_2 is also within the ordinary comparison lemma, so the proof has not silently specialized to quotient maps. Unbounded K enters only through the unbounded resolution and localization statements, which explicitly impose no bound.

## Unfinished work

None for this stage-1 split. Existing unsplit dependencies remain independent DAG work; this delivery does not claim to prove their Lean declarations.

## Validation

The required server dry run and direct push are run after writing this report; their final results are recorded below.

The first dry-run citation gate required a longer quotation for the constant-ring-map node. Its quote now includes the adjoint structural map definition and its isomorphism conclusion verbatim. No proof change was needed.

Required dry run completed with exit 0: `OK (not pushed) deliver/Q03/lem-exc-unbounded-coefficient-pullback-model at 205a08e220d: preflight passed`. This included the server preflight and DAG/split checks. Direct delivery follows with the same node and citation files.

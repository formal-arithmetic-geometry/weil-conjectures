## Worker report

This is fresh stage-1 reconstruction under the released Q108 repair note of 2026-10-24 (`keep_plan=false`), answering the return of stale commit `2e6ba4aa`. It is not a stage-2 redelivery. The sandbox item was replaced from the current read-only live node before writing its proof; the statement, source, five statement dependencies, historical Mathlib searches, creation metadata, blueprint provenance and `lean_removed` evidence are preserved exactly. No withdrawn nine-step proof, Q39 review, N5 reviewed_lean record, `lean` attachment or extra statement dependency is restored.

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-projective-finite-group-quotient.json`: twelve-step proof of the unchanged theorem; status `split`, independent agent proof origin, generic tool uses declared.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-orbit-tensor-line-descent.json`: one new unsplit statement; Mathlib searches found no exact match. It concerns descent of a specified line bundle through an already given quotient, and asserts neither quotient existence nor ampleness.
- `citations.json`: each step/citation is backed by the cited node's full verbatim statement, read against the use.
- `report.md`: this report. Search output is retained in `searches.jsonl`.

Attachments: none. No Lean module is delivered or compiled. The old sandbox Lean file is withdrawn, consistently with stage 1 and the live deleted-module evidence.

WANTED: David Rydh, *Existence and properties of geometric quotients*, arXiv:0708.3333v2, Theorem 4.4, Proposition 4.7 and Remark 4.9, pp.20–23, for `lem-per-projective-finite-group-quotient` and `lem-per-orbit-tensor-line-descent`. The file named by the source is absent locally. I read the relevant text online at https://arxiv.org/pdf/0708.3333, but did not download into the read-only repository. Following the stage-1 brief, the detailed argument is explicitly marked `proof_origin.by = agent`; the paper motivates the invariant-affine gluing and norm construction rather than being cited as a proof of unstated intermediate claims. The new node also honestly identifies the independently supplied precise descent interface.

The returned work was wrong as a delivery: it restored a withdrawn proof graph, attached a deleted Lean module and carried stale certification. No false theorem statement was identified. This reconstruction does not use the homogeneous coordinate/projective-envelope argument. It constructs invariant-ring charts, proves their invariant-sheaf description and glues the actual orbit space; an orbit tensor and norm sections then yield an ample module downstairs. Source references in the steps specify the admitted Stacks results used. Nothing remains unfinished in the one-level split; the single new lemma is deliberately left unsplit for its own subsequent stage-1 work.

## Hypotheses and conclusions

1. The Noetherian hypothesis on B and its specified immersion over an affine Noetherian S=Spec R are used in Step 1 to obtain finite type over S and an absolute ample module. The relative finite-space immersion for V gives a relatively ample module; Stacks 0892 twists it by the pullback of an ample module on B. No replacement by an infinite-dimensional projective bundle or local-on-base projectivity convention occurs.
2. The finite-type hypothesis on V→B supplies finite algebra generators and quasi-compactness (Steps 1, 3, 7). The Noetherian base is essential for Artin–Tate; no unproved finite-generation assertion for invariants over an arbitrary ring is substituted.
3. Finiteness of H supplies finite orbits, finite locally free action-groupoid maps, monic orbit polynomials, a common annihilating power in invariant localization, and finite tensor products (Steps 2–4, 8–9). The action over B ensures the base coordinate rings lie in the invariant rings and makes p invariant (Steps 3, 6–7).
4. Step 5 constructs a scheme Q with finite surjective q; Step 3 establishes geometric-point orbit fibres over every algebraically closed field. Step 4 proves the invariant structure-sheaf identity on a basis, and Step 5 gives it on every open.
5. Step 6 proves the categorical property for morphisms into any scheme, including locality on stalks, and restriction to every invariant open, including opens that are not quasi-compact. It constructs the map Q→B by that universal property.
6. Step 7 proves Q→B finite type on invariant affine charts over arbitrary affine opens of B. Steps 8–10 prove global quasi-projectivity by descent, norm sections and an immersion into a single finite-dimensional projective space over B.
7. Step 11 uses projectivity of V→B only for properness, descends universal closedness through the universally surjective quotient, and turns the finite-space immersion into a closed immersion. Thus it proves the exact finite-projective-space convention.
8. Step 12 proves integrality only when V is integral, using irreducibility of the surjective image and domain invariant affine charts.

## New nodes

`lem-per-orbit-tensor-line-descent` is a smaller, independent descent lemma. Its hypotheses include an already given finite surjective q and the invariant-ring sheaf identity on all opens. It constructs the specific sheaf M=(q_*N)^H for N=⊗_h a_h^*L, fixes the permutation linearization, and asserts the evaluation and tensor-power isomorphisms, including power zero. It does not assume that |H| is invertible, that stabilizers are trivial, or that either scheme is normal.

Mathematical check of the new lemma: by the live `lem-sfb-finite-trivialize-invertible-upstairs` (Stacks 0BUT), around each y choose T on which L has a frame e on q^{-1}T. The tensor of its translates e_N=⊗_h a_h^*e is invariant under the permutation linearization and is a frame for N there. Hence fixed sections are exactly O_V(q^{-1}T)^H e_N=O_Y(T)e_N, compatibly on smaller opens. If e'=u e, the new norm frame differs by the invariant unit ∏_h a_h^*u, which descends, together with its inverse, to a unit of O_Y. The descended local rank-one modules glue to the stated sheaf M; evaluation is the identity in these frames and is equivariant. The same frames prove the tensor-power statement and its d=0 normalization. This explains why the new statement is valid in wild characteristic and is strictly smaller than the item. Its proof remains empty in the DAG as required for new nodes.

Statement dependencies of the new lemma: scheme (`def-pc-scheme`), finite morphism (`def-weil-finite-integral-morphism`), invertible module (`def-sc-invertible-module`), module pullback (`def-pc-module-pullback`), tensor product (`def-pur-sheaf-tensor-product`), and sheaf of modules (`def-weil-sheaf-of-modules-category`). The finite action, fixed sections, linearization and evaluation map are fully specified within the statement; no private alternate definition of a quotient is introduced.

## Searches

The new lemma was searched before creation:

- LeanSearch: “For a finite group acting on a scheme with a geometric quotient, the tensor product of all translates of a line bundle descends to a line bundle on the quotient”. Eight hits, including `Representation.Coinvariants.mk_inv_tmul`, `Rep.quotientToInvariantsFunctor_obj_V`, finite-set orbit quotients and a projectivization action. None states scheme line-bundle descent.
- LeanFinder: “The orbit tensor norm of an invertible sheaf for a finite group action descends through the invariant ring quotient via invariant local frames”. Eight hits concern representation coinvariants or representation norm transformations, not invertible sheaves on schemes.
- Loogle: `"Sheaf", "descend"`, zero hits.
- Mathlib grep, `AlgebraicGeometry`: `orbit.*tensor|tensor.*orbit|lineariz|linearisation|norm.*[Ll]ine|[Ll]ine.*norm`. Twenty-five hits were elliptic-curve `linear_combination (norm := ...)` tactics, not a norm line bundle. Exact wrapper output is recorded verbatim in the new node's `mathlib_searches`, with queries matching `searches.jsonl`.
- DAG and blueprint searches: `linearization`, `tensor norm`, `orbit tensor`, `finite group quotient`, and orbit/tensor/norm key words. No imported blueprint node supplies the new assertion. Existing relevant 0BUT nodes were read and distinguished below. The project's `lean/WeilConjectures` and `lean/Sheaf` were searched by item id and orbit-tensor/linearization key words; no matching declaration was found. The upstream declaration deleted with the old module is not an attachment.

The item's existing Mathlib search records were preserved exactly as Q108 requests; no old result was recast as a new search.

## Not duplicates

- `lem-per-orbit-tensor-line-descent` vs `lem-sfb-finite-trivialize-invertible-upstairs`: the latter only gives a frame for an arbitrary upstairs line bundle near a finite fibre. It neither supplies a group action nor descends the orbit tensor or identifies fixed tensor powers. It is the generic ingredient in the validity check above.
- `lem-per-orbit-tensor-line-descent` vs `lem-sfb-affine-invertible-finite-set-section`: the latter produces one section nonzero at a finite set on an affine scheme; it has no quotient or descent assertion.
- `lem-per-orbit-tensor-line-descent` vs `lem-sfb-finite-field-picard-norm-base-change`: the latter is the Picard norm for a finite field-extension projection, whereas the new statement concerns a possibly ramified, nonflat, nonfree finite group quotient and a specified orbit tensor, with equivariant evaluation and sheaf-level fixed tensor powers.
- `lem-per-orbit-tensor-line-descent` vs `lem-per-projective-finite-group-quotient`: the item constructs a quotient and proves geometric and projective properties; the new lemma assumes a finite invariant-sheaf quotient and only descends the particular line module. This does not move a clause of the item into a differently named node.

## Review by Q83

This is my self-review, not an independent review or certification. I reread all twelve steps and the complete statements of the 33 cited nodes. In particular: the relative ample twist has exactly the affine-open hypotheses proved in Step 1; the affine-groupoid orbit theorem is applied to the finite locally free constant action groupoid; Artin–Tate is applied over Noetherian R or R_B; the invariant localization proof explicitly handles denominators killed by zero divisors; categorical factorization checks local ring maps; norm-section affineness uses the arbitrary-scheme affine-cap lemma, not the field-only ample-tensor lemma; the ample-to-finite-space-immersion lemma is applied only after finite type over S and ampleness are established; properness is used only in the projective case.

Edge cases checked: empty V, trivial H, ineffective action, nonfree stabilizers, residue characteristic dividing |H|, nonreduced coordinate rings and nilpotent localization denominators, nonproper V, arbitrary (including non-quasi-compact) invariant opens, and nonintegral V. No quotient is asserted to be integral unless V is integral. The tensor norm has no averaging operator or division by |H|. Invariant sections descend through the equivariant isomorphism, not an arbitrary nonequivariant pullback isomorphism.

The full statement/proof closure of the chosen live tools was traversed against `coord/route-pivot-dropped.txt`: empty intersection. In particular none of the six prerequisites named in the return is cited or reintroduced, and the new lemma is not an alias for one of them. The still-live generic algebra Artin–Tate node is used on affine coordinate algebras in this fresh construction, not to recover the withdrawn homogeneous-envelope argument. SGA 4/4.5, arbitrary-field adic duality and the discarded Artin–Gabber proof are absent. Blueprint provenance remains the admitted geometric quotient/projectivity passage of ILO XVI 3.7, before its cohomological application.

The delivery wrapper will rebase the stage-1 fields on current main and run the server preflight. No stale review, Lean record or file outside the stage-1 node/report packet is requested for delivery.

Preflight repair: the first dry run rejected only Unicode mathematics in the new statement. The new statement was converted to TeX without changing its content. An additional existing generic separatedness lemma now explicitly supports the immersion-to-separatedness inference.

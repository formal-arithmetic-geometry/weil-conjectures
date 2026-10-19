# Stage-1 worker report

Files written:

- `dag/nodes/sec-six-functors/lem-weil-boundary-proetale-q-compatibility.json` — repaired item, status `split`, four proof steps, no new nodes.
- `citations.json` — verbatim statement quotes for every cited node in every step.

Attachments: none. No finished declaration in `WeilConjectures/` states this item.

WANTED: none.

## Source error

The returned split cited the obsolete master paragraph as if it proved a pro-etale q comparison and a transpose calculation. The current `main-20261015` file `sec-smooth-purity/sk-lem-sp-tower/cor-weil-boundary-duality-discharge.proof.md` proves the boundary evaluation map and its biduality compatibility, but does not state the q comparison. I therefore record the q mate calculation as an agent proof, using the current main-20261015 finite and pro-etale projection-formula routes and the existing comparison-mate and tensor-comparison statements. The definition node `def-kun-projection-formula-map` explicitly makes no invertibility assertion, so the item statement now assumes that the two projection transformations used in q are isomorphisms and names their inverses. This repairs E7/C3/C4, E1/E5, and B9 without weakening the q conclusion.

## Review by Q58

I read the current unit `dag/units/sk-prop-sf-biduality-general.json`, chapter `dag/chapters/sec-six-functors.json`, the item node, and the main-20261015 sources `sec-smooth-purity/sk-lem-sp-tower/cor-weil-boundary-duality-discharge.md` and `.proof.md`, `sec-six-functors-basics/sk-thm-sf-pf-finite/thm-sf-pf-finite.md` and `.proof.md`, `sec-six-functors/sk-thm-sf-pf-proetale/thm-sf-pf-proetale.md` and `.proof.md`, and `sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.md` and `.proof.md`. I also opened the statements of every cited DAG node: `sk-thm-sf-pf-finite`, `sk-thm-sf-pf-proetale`, `lem-weil-pbc-comparison-direct-image-canonical-mate`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `def-kun-projection-formula-map`, `lem-weil-finite-duality-site-comparison`, and `lem-weil-duality-pairing`.

Step 1 uses the finite and pro-etale projection-formula statements exactly for their stated isomorphism conclusions. For the etale application I checked that the closed immersion is separated and finite type, `G_e N` is bounded constructible, and `M` has finite Tor amplitude. For the pro-etale application I checked that `C_T M` and `C_Z G_e N` are the etale-origin finite-Tor realizations required by the theorem. The comparison-mate statement supplies an isomorphism normalized on counits, and the ringed-topoi statement supplies the natural derived tensor comparison. Thus the inverses newly required by the repaired statement are available.

Step 2 uses only the statement of `def-kun-projection-formula-map` for the fact that the projection morphism is the counit-tensor mate, the comparison-mate statement for its counit normalization, and the ringed-topoi statement for monoidality. Applying the comparison to the mate gives the pro-etale projection map; invertibility from Step 1 gives the inverse equality. Uniqueness of adjoint mates then gives the displayed q equality. This is the agent-written calculation because the current corollary source does not contain it.

Step 3 uses the finite-duality comparison statement for internal-Hom, dualizing-object, evaluation, and double-dual transport, the duality-pairing statement for the definition of the transpose as the double-dual map, and the tensor-comparison statement for symmetry. I checked that each primitive arrow in a finite composite is covered, and that induction on composition uses only naturality and cancellation of comparison isomorphisms.

Step 4 substitutes `H = D_{T,e}K` into the displayed pairing. I checked the final hypotheses place `K`, `D_{T,e}K`, `i_e^*K`, `G_eD_{T,e}K`, and the indicated duals in the finite-Tor comparison class, and that the assumed dualizing identifications are the ones needed after evaluation. Step 3 therefore transports both the pairing and its tensor-Hom transpose to the identical pro-etale formula.

I tested the repaired inverse-projection clause on the identity immersion, the empty closed subscheme, and zero complexes: the projection maps are identities or zero maps on the relevant zero objects, and the assumed-isomorphism condition correctly excludes a non-invertible zero map on a nonzero object. No new node was created, so there are no duplicate-node pairs to report and no Mathlib leaf searches are required. The item’s blueprint ancestry and all proof sources now use `main-20261015`; the obsolete master source is mentioned only as the source error being repaired.

What could not be finished: nothing.

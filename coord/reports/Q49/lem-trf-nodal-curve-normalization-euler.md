# lem-trf-nodal-curve-normalization-euler — Q49

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-curve-normalization-euler.json`: item retained with its exact statement and split into four proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-normalization-quotient.json`: new unsplit supporting statement for the normalization exact sequence and one-dimensional quotient at each split node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-pc-finite-pushforward-euler.json`: new unsplit generic finite-pushforward Euler comparison; no Mathlib match.
- `citations.json`: verbatim quotations for every node cited by every item step.
- `report.md`: this report.

There are two new unsplit nodes and zero Mathlib leaves. The server `check_dag` preflight passed before this report was written.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` source for the exact item id, its blueprint tag, and declarations concerning nodal normalization and Euler characteristics. No declaration states this item without `sorry`; no Lean source was written or compiled.

## WANTED

None. The cited Stacks sources are present in `literature/stacks-project/`.

## Not duplicates

- `lem-trf-nodal-normalization-quotient` vs `lem-trf-nodal-contraction-euler-defect`: the new node computes the normalization quotient of a single proper nodal curve; the existing node computes the Euler difference for a contraction with a smooth target point and boundary count.
- `lem-trf-nodal-normalization-quotient` vs `lem-trf-nodal-normalization-adjunction`: the new node states the structure-sheaf normalization exact sequence and node quotient; the existing node states normalization branches and the dualizing-line adjunction formula.
- `lem-trf-nodal-normalization-quotient` vs `det-curve-normalization-constant-sheaf`: the new node concerns coherent structure sheaves and split-node local rings; the existing node concerns finite constant abelian sheaves and their stalk cokernels.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-euler-additive`: the new node adds the finite-morphism identity $chi(X,f_*G)=chi(Y,G)$ using affine vanishing; the existing node only gives additivity for short exact sequences and the general Leray alternating sum.
- `lem-pc-finite-pushforward-euler` vs `lem-weil-pbc-finite-pushforward-coherent`: the new node includes the Euler/cohomology comparison and higher-direct-image vanishing; the existing node records coherence of finite pushforward only.

- `lem-pc-finite-pushforward-euler` vs `pqf-lem-affine-vanishing`: the new node concludes a finite-morphism Euler identity; the existing node only gives higher-cohomology vanishing on one affine open.
- `lem-pc-finite-pushforward-euler` vs `lem-sc-invert-s-cohomology-affine-case`: the new node compares finite pushforward Euler characteristics; the existing node concerns localization of cohomology by a section on an affine case.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-affine-higher-direct-image-cohomology-vanishing`: the new node handles finite pushforward and Euler characteristics; the existing node vanishes cohomology of higher direct images over an affine base.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-cohomology-sections-affine-base`: the new node gives finite pushforward Euler equality; the existing node identifies cohomology with sections of higher direct images over an affine base.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-finite-affine-cech-model-acyclic-resolution`: the new node is a finite-morphism Euler comparison; the existing node constructs a Cech resolution for an affine cover.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-finite-affine-cech-model-derived-comparison`: the new node is a finite-morphism Euler comparison; the existing node compares an affine Cech model with derived sections.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-finite-affine-cech-model-perfect`: the new node is a finite-morphism Euler comparison; the existing node proves perfectness of an affine Cech model.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-proper-flat-affine-cech-perfect-model`: the new node is a finite-morphism Euler comparison; the existing node supplies a proper-flat affine Cech model.
- `lem-pc-finite-pushforward-euler` vs `lem-pc-proper-flat-cohomology-model-data`: the new node is a finite-morphism Euler comparison; the existing node packages proper-flat cohomology model data.
- `lem-pc-finite-pushforward-euler` vs `lem-sc-affine-open-sections-resolution-quasi-iso`: the new node is a finite-morphism Euler comparison; the existing node gives an affine-open sections resolution quasi-isomorphism.
- `lem-pc-finite-pushforward-euler` vs `lem-sc-cech-comparison-map-iso-affine`: the new node is a finite-morphism Euler comparison; the existing node concerns an affine Cech comparison map.
- `lem-pc-finite-pushforward-euler` vs `lem-sc-qcoh-alternating-cech-resolution-quasi-iso`: the new node is a finite-morphism Euler comparison; the existing node proves a quasi-coherent alternating Cech resolution.
- `lem-trf-nodal-normalization-quotient` vs `lem-trf-nodal-curve-normalization-euler`: the new node states only the normalization exact sequence and local node quotients; the item additionally computes the global Euler characteristic from component genera.
- `lem-trf-nodal-normalization-quotient` vs `lem-trf-nodal-point-finite-separable-splitting`: the new node computes the structure-sheaf quotient after normalization; the existing node concerns residue-field splitting after a finite separable extension and does not state a normalization exact sequence.

## Source error

No source statement error was found. For a split node the completed local calculation is exactly $k[[u,v]]/(uv)$ with normalization $k[[u]]\oplus k[[v]]$ and quotient $k$; a self-node is therefore counted once. The item’s formula agrees with the normalization exact sequence and the component Euler characteristics.

## Review by Q49

I read the item, chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the inherited blueprint ancestry through `lem-trf-local-term-locality`, and the complete Stacks proofs at Tags 0C1R, 0CBW, 01Y6, 01XB, 08AA, 0BEK, 0AYT, 0BUG and 0BY7. I also read the existing statements of `lem-trf-nodal-normalization-adjunction`, `lem-sc-normalization-properties`, `lem-pc-euler-additive`, `lem-pc-chi-zero-dim-support`, `lem-sc-global-functions`, and `def-sc-genus`. The item hypotheses match the source: proper, reduced, connected, pure one-dimensional over an algebraically closed field, with every nonsmooth completed local ring split nodal and with smooth proper connected component normalizations.

For the new normalization-quotient node, Step 1 uses `lem-sc-normalization-properties` only for finiteness and properness of each component normalization, exactly as its statement says. Its Step 2 is the explicit Tag 0CBW computation: pairs of power series with equal constant term map to $k[[u]]\oplus k[[v]]$, so the quotient has one $k$-dimension at a node and zero at a smooth point. Step 3 uses `lem-pc-chi-zero-dim-support` for the coherent zero-dimensional quotient, and the direct sum of skyscraper sheaves gives one global copy of $k$ per singular point. The node is strictly smaller than the item because it contains no component Euler or genus formula.

For the finite-pushforward Euler node, I checked the finite morphism is affine, inverse images of affine opens are affine, and Tag 01XB gives higher cohomology vanishing there. Tag 01Y6 gives coherence of the finite pushforward. The Leray/Euler calculation supplied by `lem-pc-euler-additive` then gives the stated equality. This node is generic for finite coherent pushforwards and does not mention nodal curves.

For item Step 1, the cited normalization-quotient statement supplies the exact sequence and the equation $chi(B,Q)=e$ verbatim. For Step 2, `lem-pc-euler-additive` supplies additivity on the short exact sequence, `lem-pc-finite-pushforward-euler` supplies the finite normalization pushforward equality, and the normalization quotient node supplies the quotient Euler term. The finite disjoint-union sum is the repeated split-sequence instance of the same additivity statement. For Step 3, `lem-sc-global-functions` gives $H^0(\widetilde B_i,\mathcal O)=k$ under proper, connected, reduced curve hypotheses; `def-sc-genus` gives the stated $g_i=\dim_kH^1$; and `def-pc-euler-characteristic` turns these dimensions into $\chi(\widetilde B_i)=1-g_i$. Step 4 is the displayed arithmetic substitution and is elementary.

I checked edge cases: a smooth irreducible curve ($v=1,e=0$) gives $\chi=1-g$; a rational nodal cubic ($v=1,e=1,g=0$) gives $\chi=0$; two smooth components meeting at one node ($v=2,e=1$) gives $\chi=1$; and a self-node is counted once because its completed normalization quotient is one copy of $k$. No tree condition or genus-zero hypothesis is introduced. The item and both new nodes have the required Mathlib searches recorded, and the required server `check_dag` passed.

All item steps are below 2000 characters and do not hide an additional lemma: the local quotient, finite pushforward comparison, zero-dimensional quotient Euler calculation, and proper-curve global-functions calculation are each exposed as cited statements. No SGA 4 or SGA 4½ source is used.

## What could not be finished

Nothing. The split, citations, self-review, and server DAG check are complete; the required delivery dry run remains.

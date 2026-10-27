# Stage-1 report: lem-sfb-profinite-field-scalar-annihilator-hull

## Files written

- Item copied unchanged to `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-field-scalar-annihilator-hull.json`; status remains `unsplit`.
- No new nodes were created.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag and for continuous/profinite scalar-kernel declarations; no project declaration states this item.

## WANTED

- An exact reference or complete proof of the degree-zero sheaf-kernel generation theorem for multiplication by an arbitrary continuous function `a : P → E` on an extremally disconnected profinite base, with the precise closure under ordinary derived products and common-termwise-lower-bounded filtered colimits used by this item.

## What I checked

The existing node isolates the rank-one field case after the integral finite-quotient and matrix-reduction arguments. I read Hemo--Richarz--Scholbach, Example 4.2 and Remark 6.4. Those passages explicitly warn that the actual sheaf kernel can be nonzero while its terminal sections vanish; they do not prove membership in the stated derived hull. I also read the existing parent split and its cited finite-bundle Roos and integral-realization statements. They prove the integral coefficient branch, but they do not imply the field branch because scalar extension from the integral tower does not commute with the required infinite products.

I searched the whole DAG and the current blueprint for an equivalent node, and searched Mathlib with LeanSearch, Loogle, LeanFinder, and source grep. The searches returned general condensed/profinite constructors, projectivity of profinite spaces, topological kernels, and adic inverse-limit lemmas, but no theorem that gives this sheaf-kernel generation statement or a one-line specialization. The routes I examined require an additional theorem controlling closed zero loci of continuous `E`-valued functions; none of the sources or candidate DAG statements I read supplies the generation assertion. I do not claim this proves the assertion false.

The tempting approximation by locally constant functions is insufficient: uniform approximation does not identify the actual degree-zero sheaf kernel in the ordinary uncompleted derived category. Likewise, terminal-section calculations are invalid by HRS Example 4.2. I therefore cannot write a complete proof without introducing an unproved theorem or weakening the item.

## Review by NA

I checked the item statement against its source field and against the parent split. The empty base, zero scalar, and invertible scalar edge cases are immediate, but they do not settle the arbitrary continuous scalar case. I checked every nearby candidate node's statement before considering it as a dependency: finite-bundle Roos exactness applies to finite locally constant towers, integral scalar realization applies to `\mathcal O_E` quotients, and the free-matrix statement only reduces an arbitrary field matrix to rank-one kernels. None states the missing field rank-one conclusion. The HRS example was tested as the required small edge case and rules out replacing the sheaf kernel by the kernel on global sections. No statement was changed and no unsupported auxiliary node was created.

This item remains genuinely unresolved at stage 1. A dry-run delivery would reject the unchanged `unsplit` node, so no delivery invocation or push was attempted.


## Concrete remaining gap

Choose a uniformizer `pi` and increasing clopen sets `U_n = {p : |a(p)| >= |pi|^n}` (after an irrelevant scalar rescaling). If `e_n` is the corresponding idempotent, the actual sheaf kernel has the sectionwise presentation

`K_a = ker(R_E → product_n e_n R_E)`.

Indeed the restriction of a section to every `U_n` vanishes exactly when its product with `a` vanishes, point by point. Each `e_n R_E` is a retract of the free sheaf, so the two displayed terms belong to the hull. Their derived fibre does too, but it also has the cokernel as another cohomology sheaf. The given closure conditions do not allow taking its degree-zero cohomology. I could not eliminate that cokernel.

Equivalently let `V_n = P minus U_n`. Then `K_a = lim_n e_(V_n) R_E` with the inclusion transitions. Products are exact on this profinite slice by the existing finite-bundle Roos node, but that fact alone does not identify this ordinary inverse limit with its derived limit. The finite-bundle local-surjectivity conclusion in that node cannot be used here: the fibres are the infinite field `E`, not finite groups. Claiming the difference map `1-s` surjective would introduce precisely an unjustified inverse-limit assertion.

For the HRS test `P = beta N`, `a(n) = ell^n`, the zero locus is the non-open boundary. The global kernel is zero because a continuous function zero on dense `N` is zero. On any nonempty profinite test mapping into the boundary, multiplication by `a` is zero, so the kernel is the full coefficient sheaf there. This checks both why the global-sections shortcut fails and why no clopen finite-model kernel can be silently substituted.

The log `searches.jsonl` contains five actual search invocations made for this item: two LeanFinder phrasings, LeanSearch, Loogle, and source grep (including the second phrasing). Results were read; no match was claimed. The original item's older search records were preserved unchanged. No new node or false search record was written.

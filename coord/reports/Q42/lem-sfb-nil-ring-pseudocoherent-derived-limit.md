# Stage-1 delivery: lem-sfb-nil-ring-pseudocoherent-derived-limit

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nil-ring-pseudocoherent-derived-limit.json`: item, split into six steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-jacobson-marked-free-complex-lift.json`: new statement-only lemma, unsplit; no Mathlib match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep.
- `citations.json`: one exact statement quotation for every citation of every proof step.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag and pseudo-coherence terminology, and read `RingTheory/StablyFreeComplexLift.lean` and the scope and hypotheses of `Algebra/Homology/DerivedCategory/PerfectTower.lean`. The former is unmarked; the latter needs perfect complexes, local rings and a principal adic quotient tower. Neither states this item or the new lemma exactly. No Lean was written or compiled.

## Literature wanted

None.

## What needed repair

The imported item was statement-only. Its statement is correct in the all-levels-pseudo-coherent branch of Stacks 0CQF and is unchanged. Existing nilpotent marked lifting and nilpotent reconstruction nodes cannot be applied to an arbitrary nil ideal. In particular a nil ideal need not have a common nilpotence exponent. The new lemma isolates the missing prescribed-marking form of the one-step lifting theorem, without moving a reconstruction clause into a new node.

The inherited blueprint ancestry has `from.node: null`. The read-only ancestor command prints `a node created for lem-sfb-nil-ring-pseudocoherent-derived-limit has blueprint.from.node = None`. I retained that value and the entire inherited via chain; the places describe precisely the inherited effectivity prerequisite under proof (3) of the current `det-thm-sf-ctf-stability-direct-images`. The current latest blueprint's direct-images proof and unit were read; no chapter or unit route was changed. Searches of all blueprint nodes for `pseudo-coherent`, `0CQF`, `stably free`, `marked`, `lift complex` and `inverse ring` returned no exact matching blueprint statement.

## Unfinished work

No part of this one-level split is unfinished. The new lifting lemma deliberately remains an unsplit statement for a later item. Its proof route is the prescribed-delta version of 0BCA applied to finite stably free modules as in 0BCB, not the nilpotent-projective argument: the latter would incorrectly use Nakayama without finiteness over a merely nil ideal.

For the later worker: in the 0BCA construction choose a bounded-above finite-free representative L of K with marking gamma, and choose delta from F to the reduction of L representing the inverse of alpha composed with derived reduction of gamma. The class of finite stably free modules satisfies the source's class conditions under the one-plus-ideal unit hypothesis. Lift Cone(delta) acyclically, lift the cone inclusion strictly to f:L to B, and take P=Coker(f)[-1]. The split cokernel construction supplies the reduction theta:P/I to F. With D=Cone(f), maps t:D to Coker(f) and p:D to L[1], define beta using the inverse of Q(t[-1]) and Q((-p)[-1]), followed by gamma. In coordinates on the reduction of D, write elements as (x,y,z) in Lbar^i plus F^{i+1} plus Lbar^{i+1}; the differential is (dx+delta y+z,-dy,-dz). The homotopy h(x,y,z)=x gives dh+hd=delta[1] rho t+p. Thus Q(-p)=Q(delta[1])Q(rho t), giving exactly the displayed marking equality after shifting and composing with alpha. Terms of P are finite stably free; their free reductions make them free by 0BC6. Above b their reductions vanish and finite Nakayama kills them, preserving the chosen cutoff. This retains the argument supporting the strengthened marking, but the new node itself contains no proof.

## Not duplicates

The following comparisons cover every existing node found by searching both shared tags, including occurrences inside older proof/search records.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-pseudo-coherent-lift-stably-free-complex: that statement gives an unmarked representation and reduction isomorphism; it does not require the reduction of beta to agree with a specified alpha. The new statement requires that equation and the specified cutoff.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-complex-lift-class-projective: the general class statement gives unmarked existence; it does not prescribe the derived marking of its reduction, and it requires the separate class hypotheses.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-finite-module-surjective-mod-ideal: this is a module surjectivity/Nakayama statement, reused in the item, not a marked derived-complex lifting theorem.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-complex-lift-strict-map: this lifts a chain map to an already given acyclic complex; it does not construct a finite-free representative with a prescribed derived marking.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-complex-lift-cone-cokernel: this identifies the reduction of a cokernel from existing cone data; it does not assert existence of the lift or marking.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-complex-lift-cone-properties: this asserts acyclicity and class membership of a mapping cone, not a marked lift of K.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-complex-lift-acyclic-enlargement: this is an auxiliary enlargement of an acyclic cone from already specified class data, without the marked conclusion.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-projective-class-reduced-splitting: this splits a right-exact module sequence under reduced splitting assumptions, not a derived complex marking.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-perfect-local-pseudocoherent-free-model: this constructs a residue-field minimal-rank model over a local ring; it does not lift a prescribed quotient complex over an arbitrary ring.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-nilpotent-marked-free-complex-lift: that node assumes I^N=0. The new lemma assumes only that every 1+x for x in I is a unit. The distinction is essential for this item's nil kernels without a uniform exponent.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-nilpotent-marked-free-complex-lift-unmarked: this requires nilpotence and does not give the marking equation.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-nilpotent-marked-free-complex-lift-marking: this Lean-statement node explicitly assumes I^N=0 and an already existing finite-free lift; the new lemma has neither restriction.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-nilpotent-projective-complex-lift: this assumes a nilpotent ideal and gives an unmarked projective lift, without finite-free or prescribed-marking conclusions.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-pseudocoherent-normalized-algebra-tower: this is reconstruction over Noetherian adic quotients; the new lemma is one-step marked lifting over arbitrary Jacobson ideals.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sfb-pseudocoherent-point-fibre-line: this concerns residue-field fibre complexes on algebraic spaces and line-bundle loci, not a chosen quotient-complex marking.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sfb-nil-ring-perfect-derived-limit: this reconstructs perfect objects from a ring tower and is the item's parent; the new lemma is the smaller, single-quotient pseudo-coherent model-lifting input.

The item itself also differs from `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction` and its `-models` node: both require nilpotent transition ideals; the item allows merely nil ideals. The normalized-algebra-tower variant adds Noetherian and adic hypotheses. The existing perfect inverse reconstruction statements require perfectness at every level; they are not replacements for this pseudo-coherent item and are not used to prove it.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-finite-constant-length-flat: This is finite flatness of a morphism of varieties from constant fibre length; it contains no derived quotient-complex lifting statement.

lem-sfb-jacobson-marked-free-complex-lift vs lem-pc-hilb-representable: This is representability of a Hilbert functor for schemes; it contains no prescribed finite-free derived marking.

lem-sfb-jacobson-marked-free-complex-lift vs lem-sc-regular-dim1-dvr: This identifies a dimension-one regular local ring as a DVR; it contains no complex lifting conclusion.

lem-sfb-jacobson-marked-free-complex-lift vs lem-pod-dvr-complex-amplitude-mod-uniformizer: This detects a cohomological interval over a DVR from residue reduction; it does not lift a specified complex and marking over an arbitrary Jacobson ideal.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-coherent-formal-modules-affine: This is an affine Noetherian formal-module equivalence for an adic tower; it does not lift a prescribed derived-complex marking over a single arbitrary quotient.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-completion-maximal-ideal-generators: This compares generator counts of maximal ideals under Noetherian local completion; it has no derived-complex conclusion.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-conormal-span-clearing: This clears a localized conormal spanning relation; it does not construct or mark derived representatives.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-criterion-flatness-fibre-noetherian: This is a flatness criterion over Noetherian local rings for modules; it is not a marked finite-free complex lift.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-finite-type-lift-nilpotent: This lifts finite generation of an algebra across a nilpotent ideal; it has neither the general Jacobson-ideal hypothesis nor derived marking conclusion.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-formal-systems-surjective: This detects epimorphisms of coherent formal sheaf systems at the first level; it does not lift a chosen quotient complex.

lem-sfb-jacobson-marked-free-complex-lift vs lem-weil-pbc-gabber-upstairs-tensor-coefficients: This constructs a faithfully flat algebra and a polynomial tensor relation in a finite algebra; it says nothing about a prescribed finite-free derived model.

## Review by Q42

I read Stacks `more-algebra.tex` at 0CQF (`lemma-Rlim-pseudo-coherent-gives-pseudo-coherent`), including both branches of its hypothesis (2), and used only the branch asserting pseudo-coherence at every level. I read 0BCB (`lemma-lift-complex-stably-frees`) and its use of the class construction in 0BCA (`lemma-lift-complex`) for the new node. The latter's choice of delta allows the prescribed derived marking, and its cone/cokernel construction gives the explicit homotopy recorded above. I also read the derived-limit comparison in `remark-how-unique`, the calculation in 091D (`lemma-compute-Rlim-modules`), and `derived.tex` 0H9J (`remark-functoriality-derived-limit`); these distinguish an arbitrary specified Roos triangle from a canonical functor, which is not available here.

For step 1 I checked that `def-pc-ring-pseudo-coherent-complex` actually supplies a bounded-above finite-free representative; the unit computation for each nilpotent element and the quotient-ring identification are written explicitly. No uniform power of a kernel is introduced.

For step 2 I read the full new lifting statement and verified every hypothesis with R=A_(n+1), I=ker(u_n), F=P_n, and alpha=beta_n^{-1} gamma_n. It supplies a marked lift with the SAME b, not just some upper bound. I read `lem-pc-module-bounded-flat-kflat` and the full `lem-pur-sheaf-ring-derived-coefficient-adjunction` statement. Its normalization (2), not just abstract existence of an adjunction, is exactly what identifies the chain transition with the supplied derived t_n. The source and target coefficient categories are ordinary modules via the one-object point site. No sheaf-encoding conversion is used.

For step 3 I read `lem-sc-finite-module-surjective-mod-ideal` and `def-weil-pbc-projective-module`. Nakayama is applied first with finite target P_(n+1)^i and then to 0 to T, where T is explicitly a finite direct summand of a finite free module. Projectivity is used only to split a surjection to the free target. These two cited statements and the split decomposition give the basis-lifting argument in a few lines. Compatible bases identify the termwise limit with A^{r_i} by finite coordinate tuples, and the componentwise differential and scalar projection map are explicit; there is no uncited formal-functions theorem or assumption that finite modules commute with arbitrary limits.

For step 4 I read the exact statement of `lem-weil-pbc-surjective-module-complex-tower-limit`: it gives a Roos triangle with the ORIGINAL projections under degreewise surjective chain transitions. Those hypotheses were checked. I read TR2/TR3 in `def-weil-triangulated-category` and the full `lemma-weil-pbc-r-lim-levelwise-isomorphism` statement. The latter requires a morphism of complete specified triangles, not merely a map commuting with individual projections. I construct that morphism by rotating and applying TR3 to the two products; thus its exact hypothesis is met, including the connecting arrow. The resulting isomorphism respects each p_n.

For step 5 the pseudo-coherence definition supplies exactly the claimed conclusion from P and h. The cited bounded-flat theorem gives K-flatness and `lem-pur-derived-change-of-rings` explicitly computes derived scalar extension on that model. Flatness of each free term is checked by the direct-sum description of its tensor product.

For step 6 I reread the coefficient adjunction statement, especially naturality and normalization (2). The formula for rho_n after precomposition with h tensor A_n follows from the exact projection equality in step 4, and its chain adjunct is exactly x tensor a mapped to a x_n. The inverse of the displayed composite proves invertibility of the actual projection-induced map; it is not merely existence of some unrelated isomorphism.

I checked B--E of `coord/delivery-errors.md` against the written files. The new node is self-contained, has statement dependencies for its derived categories, pseudo-coherence and derived scalar extension, contains no proof, and has exact Stacks tags and TeX. All non-elementary inputs of the item occur as cited statements and have verbatim quotations in `citations.json`; no source proof internals substitute for a cited statement. No new node restates a clause of reconstruction. All six proof steps are shorter than 2000 characters. Generic off-unit tools are explained in split_report.tool_uses.

Small cases checked: the constant tower and zero complexes; the zero ring (all involved modules are zero, so the chosen finite bases and split-kernel argument still apply); finite-free complexes concentrated in one degree; and an ideal consisting of nilpotent elements with no common exponent, for example the ideal generated by all x_i in k[x_1,x_2,...]/(x_i^2). Every element there involves finitely many variables and is nilpotent, while products of arbitrarily many distinct variables survive. This is why no nilpotent-ideal node is used for marked lifting. A fixed b is propagated from P_1 rather than inferred from varying arbitrary representatives. The new lemma also passes I=0 (take the given marking) and zero F (finite Nakayama kills a lifted finite-free model). I found no statement dispute or change of the item's hypotheses necessary.

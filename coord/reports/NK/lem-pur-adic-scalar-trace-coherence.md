# Stage-1 report: lem-pur-adic-scalar-trace-coherence

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-adic-scalar-trace-coherence.json: statement, split into five steps; no Mathlib match for the integral pro-etale trace identity.
- citations.json: verbatim statement quotations for each of the five node citations across Steps 1–3.
- searches.jsonl: the six searches actually run with msearch.py; the inherited searches in the item were retained as inherited records.
- report.md: this report. write_split.py is sandbox-only preparation material, not a node or delivery file.

New nodes: 0. New Mathlib leaves: 0. The statement is unchanged.

## Attachments

None. I searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint tag and for scalar/trace, integral/trace, and adic-scalar terms. No project declaration supplies this identity. The exact-master reference also has no declaration under the item's tag. The unrelated integral trace-class and algebraic trace results are not attachments.

## WANTED

None. This is an agent-written formal calculation from the existing comparison statements, not a claim that an unavailable reference proves the whole identity.

## Problems in the imported item

The item was statement-only. Its statement dependencies included lem-weil-scalar-extension-composition, whose statement is about rationalized coefficient categories, rather than integral derived-complete categories. I removed that dependency instead of using a rational theorem at the integral stage. The existing integral twist/scalar coherence and compact-support comparison already specify the required tensor associator and tower equations. The internal-Hom assertion in lem-pur-integral-operations-scalar-extension is also unused and was removed from the statement dependencies.

The formula in the statement suppresses coefficient-unit isomorphisms explicitly by its final convention. I restored them as u_E, u_F, and v in the proof, so its final equality is a typed equality with target U_F; suppressing v gives exactly the original formula. This is not a statement correction or additional trace normalization. The calculation holds for any chosen t_0, as required.

I read the old unit proof, especially Step 3's coefficient transitivity, the main-20261015 purity-transport unit, and its thm-pur-rational-and-qbar-purity node. The current transport route still requires coefficient transport. The item's inherited compatibility-unit binding is retained; this is an auxiliary node, not the statement node of that unit, so no unit realization fields are changed.

## Not duplicates

No node is created. Whole-DAG and blueprint searches for coefficient extension, scalar trace, scalar/trace coherence, and twist/scalar coherence found the existing integral twist and compact-support tools. I use them directly. prop-trf-trace-formal-laws concerns categorical traces of endomorphisms of perfect ordinary module complexes; its scalar clause is not this compact-support morphism. No clause of the item has been renamed as a child lemma.

## Review by NK

I read coord/delivery-errors.md B–E in full and checked the actual statements of all cited nodes, rather than their proofs. The item's source is the blueprint transport sketch: the old unit's Step 3 and the current rational-and-qbar purity statement. They motivate the coefficient transport, but do not supply a numbered theorem proving the displayed trace equality, so proof_origin is agent. No SGA source or smooth finite-coefficient purity construction is used here. There are no new node sources or statements to audit.

Step 1 uses lem-weil-finite-free-completed-scalar-comparison for the specified natural comparison between ordinary derived tensor and strict-tower extension. That statement explicitly assumes derived completeness and asserts both the isomorphism and completeness of the extended object. The units and their twists are in the integral category by prop-weil-twist-preserves; this proposition explicitly preserves integral constructibility, completeness, and the uniform finite-Tor interval. def-weil-finite-tor-amplitude is used only for the meaning of the domain, not as an assertion that arbitrary constructible objects have finite Tor amplitude. The unit has interval [0,0], its twist retains it, and [2d] moves it to [-2d,-2d]. The isomorphism theta_E places A_X T_0 on the same domain. I verified that ell is invertible on X and Y, and that f is separated finite type between separated finite-type schemes. Thus the compact-support comparison's hypotheses are satisfied without a purity assertion.

Step 2 uses exactly the equation in lem-weil-integral-twist-scalar-coherence, with its three fields renamed E_0,E,F, C the coefficient unit, and m=d. That statement specifies the associator transported from ordinary tensor via the same finite-free comparison, and its chain formula pins down the canonical twist maps. Specializing at the unit gives theta_F alpha = a B(theta_E). The scalar tensor is in degree zero, so taking the [2d] shift changes neither map nor associator sign. I wrote out the inverse equation used later. I also checked the coefficient-unit square explicitly: both routes multiply the two coefficient factors. This avoids assuming that unspecified isomorphisms between rank-one lines agree.

Step 3 uses lem-pur-compact-support-integral-coefficient-comparison. Its statement, not merely its proof, gives a natural isomorphism on D^b_ctf, states the exact three-field composition equation, and identifies alpha as ordinary tensor associativity. I substituted E_0,E,F and T_0 into that equation, then multiplied by the two indicated inverses. Its naturality at theta_E inverse gives the second equation with exactly the displayed sources and targets. In particular I did not infer transitivity from existence of separate coefficient comparisons.

Steps 4 and 5 use only equations already established in Steps 1–3, functoriality, associativity of composition, and the naturality defining the canonical tensor associator. I expanded the trace formula, moved theta_E inverse through c_B by the explicit naturality square, canceled the coefficient-comparison composition, and moved t_0 through alpha by its naturality. Restoring u_E and u_F then gives v B(t_E). These are elementary calculations, with all intermediate compositions displayed; they hide no new comparison theorem or construction.

The off-unit twist statements are recorded in split_report.tool_uses as generic coefficient tools. They do not replace the unit's purity transport route. I checked recursively that neither these tools nor the compact-support comparison or finite-free comparison depends on this item, so their use introduces no cycle.

For small cases I checked d=0 (the twist comparison is the unit comparison), E=E_0, F=E, and all three fields equal (the same equations reduce to identity-extension unit maps). For the identity morphism the calculation is the ordinary tensor associator naturality square. The empty scheme and t_0=0 cause no problem: the proof neither cancels t_0 nor assumes a nonzero object. A ramified extension changes none of the formulas: these are completed coefficient rings and their canonical comparisons, not an identification of residue rings at equal uniformizer exponents. Every non-elementary step is under 2000 characters, and no comparison proof is hidden in a long step.

The new Mathlib searches returned ordinary ModuleCat scalar associativity, generic NatTrans naturality, algebraic trace transitivity/base change, perfectoid/condensed objects, and compactly supported functions. None states this integral six-functor trace identity or specializes to it in one line. The generic naturality rule is the elementary manipulation used after the two project-specific coherence equations; it does not finish the item by itself. All six searches succeeded, and their exact queries are recorded unchanged.

## Unfinished work

None for this one-level split. The existing cited unsplit twist/scalar coherence node remains a separate item; I do not split or modify it.

## Validation

The server review_split check passed with zero new nodes. The full deliver.py dry run passed (preflight OK, zero new nodes). Final delivery follows the successful dry run.

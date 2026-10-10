Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-morphism-hom-out-of-perfect.json`: item split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-tor-independent-perfect-tensor-base-change.json`: one statement-only unsplit node; no Mathlib match.
- `citations.json`: verbatim step citations.

Attachments: none.

WANTED: none.

The item is the Stacks Tag 0AVW affine Hom-out-of-perfect base-change lemma. I checked the source wording and the existing DAG statements for perfect RHom-tensor comparison, affine derived equivalence, global derived Hom, and derived pullback. The proof is organized as the source's tensor-dual reduction, Tor-independent base change, pullback of the perfect dual, and affine identification over R and R'. The new child is strictly the tensor-factor base-change statement used in the reduction, rather than a restatement of the Hom conclusion. Its Mathlib searches were run with LeanFinder, Loogle, and Mathlib grep and found no scheme-level theorem. I tested the formulation on the identity square and on an affine identity morphism: the comparison reduces to the identity map; the Tor condition and perfect dual pullback hypotheses are then immediate.

## Review by J1

I read the item's source citation, Stacks `perfect.tex` Tag 0AVW, and checked that the statement retains the qcqs square, affine bases, stalkwise Tor-independence, perfect M, and quasi-coherent K hypotheses. Step 1 uses the existing `lem-pc-perfect-rhom-tensor-comparison` statement for the tensor-dual identification, `def-pc-global-derived-rhom` for the meaning of global RHom, and `lem-pc-affine-qcoh-derived-equivalence` for affine derived global sections; each cited statement supplies the claimed operation. Step 2 uses the new child's full Tor-independent tensor-factor base-change statement and the cited perfectness of M's dual. Step 3 uses exactly the existing pullback clause of the perfect RHom comparison, which states the base-change isomorphism for the dual. Step 4 uses the affine equivalence's derived-global-sections quasi-inverse and the definition of derived pullback to identify pullback with derived tensor over R. I checked that no step relies on a proof detail absent from its cited node, and that the new node is not already present under its Stacks tag or key words. The identity-square and affine identity cases agree with the stated comparison.

## Not duplicates

lem-pc-tor-independent-perfect-tensor-base-change vs lem-pc-affine-morphism-hom-out-of-perfect: the new node gives a pushforward base-change isomorphism for a perfect tensor factor, while the item gives the resulting global derived Hom comparison.
lem-pc-tor-independent-perfect-tensor-base-change vs lem-sc-affine-derived-pushforward-t-exact: the existing node states t-exactness and conservativity of affine pushforward, with no Tor-independence or perfect tensor factor; the new node states a base-change isomorphism.
lem-pc-tor-independent-perfect-tensor-base-change vs lem-sc-qcoh-acyclic-derived-pushforward-cohomology: the existing node compares cohomology of an affine pushforward with ordinary pushforward, while the new node compares two pushforwards across a Tor-independent square.
lem-pc-tor-independent-perfect-tensor-base-change vs lem-sc-finite-affine-derived-equivalence: the existing node is an affine derived-category equivalence/right-adjoint result, while the new node is a Tor-independent base-change theorem for a perfect tensor factor.
lem-pc-tor-independent-perfect-tensor-base-change vs lem-sc-qcoh-acyclic-derived-sections-comparison: the existing node compares derived sections with sections under acyclicity, while the new node gives a base-change isomorphism involving a perfect tensor factor.
lem-pc-tor-independent-perfect-tensor-base-change vs lem-sc-affine-derived-concentration: the existing node characterizes degree-zero concentration under affine pushforward, while the new node concerns Tor-independent base change and does not assert concentration.

## Second reading by J1

I read `/home/ubuntu/c1-stacks-review/perfect.tex`, Tag 0AVW (`lemma-affine-morphism-and-hom-out-of-perfect`), including both the statement and proof. The item statement agrees with case (1) hypothesis by hypothesis: cartesian qcqs square, affine S and S', Tor independence, perfect M, and quasi-coherent K. The helper statement was checked against the Tor-independent base-change reduction in the same proof and is strictly an auxiliary tensor-factor comparison. Small cases checked were the identity square, an affine identity morphism, zero K, and M equal to the unit perfect complex; each gives the identity comparison.

Step 1 uses the tensor-Hom comparison, the global-derived-Hom definition, and affine derived equivalence; their statements provide the dual-tensor identification and the affine global-sections interpretation. Step 2 uses the helper's stated Tor-independent tensor base-change isomorphism and the existing perfectness clause for the dual. Step 3 uses the existing pullback-of-the-perfect-dual clause and reapplies the tensor-Hom comparison on X'. Step 4 uses the affine equivalence and derived-pullback definition to identify the resulting map with the displayed R-module comparison. No step is marked elementary, and every non-elementary dependency is cited.

The helper is statement-only, self-contained, defines all objects through the cited definition nodes, uses TeX once, and records its Stacks source and three Mathlib searches in `searches.jsonl`. A whole-DAG search found no existing node for this Tor-independent perfect-tensor base-change statement. I changed only the helper's blueprint provenance: its earlier `via` entry pointed to the item itself, which would create an invalid provenance cycle; it now points directly to the ancestor proof place. The item metadata is left to the delivery tool's maintainer-field handling.
lem-pc-tor-independent-perfect-tensor-base-change vs lem-sc-affine-derived-cohomology: the existing node identifies cohomology sheaves of affine derived pushforward, while the new node identifies pullback of a pushforward with pushforward after base change.

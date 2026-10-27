## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dolbeault-laplacian-elliptic.json`: split the unchanged item into six proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-coordinate-weighted-adjoint.json`: new statement-only analytic lemma; not a Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-subordinate-partition.json`: new Mathlib leaf, `SmoothPartitionOfUnity.exists_isSubordinate`, `Mathlib/Geometry/Manifold/PartitionOfUnity.lean:554`.
- `citations.json`: the actual statements used by steps 2 and 3, copied verbatim.

The sandbox also retains the actual search outputs `search-00.txt` through `search-14.txt` and the command's `searches.jsonl`. The exact declaration grep subsequently located line 554. Concurrent search logs were matched by query rather than their append order. The existing item's earlier search records were retained and the searches of this run appended.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item id, Dolbeault, Laplacian, formalAdjoint, principalSymbol, principal_symbol and differential operator found no project declaration stating this item. Algebraic elliptic-curve occurrences are unrelated. Neither new statement is supplied by a project declaration. The partition result is a Mathlib leaf, not a project attachment.

## Wanted literature

WANTED: Wenrui Kong, *Notes on Complex Geometry*, April 9, 2025, §§6.1--6.2, Lemmas 6.2 and 6.4, printed pp.21 and 23, for lem-sfb-dolbeault-laplacian-elliptic and the local integration input. The PDF is absent locally; I read the original online at https://cims.nyu.edu/~wk805/files/Complex_Geometry_Notes.pdf (PDF pages 21 and 23). Nothing was downloaded or written to the repository. Kong states the adjunction and the scalar symbol but does not print this coordinate matrix argument. Accordingly the expanded proof is marked agent-written. The new coordinate formula is honestly identified as an agent-supplied input motivated by Lemma 6.2, rather than a purported quotation of that lemma.

The smooth-partition node's primary source is the Mathlib file itself, which was read. No Stacks tag is asserted for these analytic statements, and no SGA source is used.

## Corrections and scope

The statement is correct as imported and was not changed. Its unsplit proof had no steps. The replacement uses no Kähler hypothesis, closedness of the fundamental form, harmonic representatives, elliptic regularity, or Hodge decomposition. In particular it cannot create a cycle through the parent orthogonal decomposition. The symbol convention is explicitly the derivative symbol with no factor i; the sign is negative in accordance with Kong's convention. The proof uses the positive scalar norm of the (0,1) component and does not rely on a convention-dependent numerical metric normalization.

I read the chapter and unit records and the current latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof, especially paragraph (3). The already recorded analytic prerequisite route is retained. `tools/blueprint_refs.py ancestor lem-sfb-dolbeault-laplacian-elliptic` returns None. The item's existing null ancestor and detailed place are retained; each new node has that null ancestor and the item prepended to the inherited via list. No chapter or unit record was changed.

## Not duplicates

Whole-DAG keyword searches for formal adjoints, principal symbols, variable-matrix integration, smooth subordinate partitions and the Mathlib declaration found no node stating either proposed input. Whole-blueprint searches for Dolbeault, formal adjoint, integration by parts, partition of unity, smooth partition, exterior algebra and weighted coordinate adjoint all returned zero matches.

lem-sfb-coordinate-weighted-adjoint vs lem-sfb-dolbeault-laplacian-elliptic: the new lemma is an explicit coordinate-domain integration identity for arbitrary smooth rectangular matrix operators with arbitrary variable weights and one compactly supported test section. It neither constructs a global adjoint on a manifold nor asserts any ellipticity. The item's global construction and full symbol computation stay in its proof.

lem-sfb-smooth-subordinate-partition vs lem-sfb-smooth-presentation-closed-subsets: the latter concerns the topological space of an algebraic stack and reduced closed substacks, not partitions of unity on real manifolds. Its Mathlib name occurrence is a search record, not its statement.

lem-sfb-smooth-subordinate-partition vs lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci: the latter concerns open-and-closed fibre dimension loci of a proper smooth scheme morphism, not smooth real functions. Its declaration-name occurrence likewise supplies no such statement.

The existing Kähler first-order commutator and Kähler Laplacian nodes have different conclusions and stronger metric hypotheses; the Fredholm and Hermitian decomposition nodes are downstream uses, not coordinate-adjoint or partition theorems. The elementary exterior insertion/removal identity is proved in step 5, not made into a redundant node.

## Review by Q123

I read Kong's original Lemma 6.2 on printed p.21 and Lemma 6.4 on printed p.23, including the immediately preceding symbol convention. They cover a compact complex manifold with a Hermitian metric; Lemma 6.4 permits even a bundle twist, whereas this item only needs ordinary type forms. The metric is positive definite and smooth, and compactness and absence of boundary give the intended global L2 adjunction. No source error or statement dispute was found.

Step 1 computes the actual (0,1) component of exterior differentiation in holomorphic frames. It keeps left wedge order, so the sign from passing the p holomorphic factors is present. This is an expansion of the definitions in the statement, not an invocation of another Hodge-theoretic result.

Step 2 cites only the new coordinate weighted-adjoint statement. I opened that statement and checked that its formula uses real coordinate derivatives, the correct rectangular matrix sizes, conjugate transpose, separate source/target Gram matrices, and positive density. It gives exactly the integration identity and smooth first-order expression taken here. For in-range adjacent types these ranks are positive; zero target types are handled separately in step 4. Reading off its highest derivative gives minus the pointwise adjoint; derivatives of density and Gram matrices contribute only lower order. In particular this does not assume normal coordinates with vanishing metric derivatives, which would be unjustified for an arbitrary Hermitian metric.

Step 3 cites that same identity and the smooth subordinate-partition theorem. I read the leaf's exact Mathlib statement at lines 554--555 and its hypotheses at 484--485 and 550. The structure at 122--132 gives all the stated function properties and IsSubordinate at 267--271 gives closed support contained in the open set, which is essential for zero extension. On our compact Hausdorff finite-dimensional smooth manifold the sigma-compactness hypothesis holds, and the finite subcover is available. The construction is the explicit sum of Q_a(phi_a v), with the cutoff inside Q_a. Thus the local identity applies with a compactly supported second argument and arbitrary first argument; it does not incorrectly move a cutoff through the derivative. Smooth zero extension follows because the closed support is compactly contained in its chart. Summing the local identities proves global adjunction, and summing the top coefficients uses sum phi_a = 1. The source formulas use the coordinate expression of the same globally defined metric density.

Step 4 proves uniqueness using the difference applied to v as a test form. Zero L2 norm implies zero for a smooth section because the positive volume density assigns positive volume to coordinate balls. The missing types are zero by the item's convention; D at q=n and the adjoint entering q=0 are set to zero directly. This avoids applying the positive-rank coordinate lemma to a zero bundle.

Steps 5 and 6 have no cited black boxes. Step 5 checks insertion and its Hermitian transpose on every exterior basis monomial: precisely one of the two products is norm squared and the other is zero. The same computation includes p=0,n and q=0,n. The (0,1) projection of a nonzero real covector cannot vanish, by conjugation. Step 6 expands the product rule to isolate exactly the second derivatives, obtains the scalar symbol, writes its inverse explicitly, and observes that the same inverse works on the underlying real vector space. This is not an appeal to the item's ellipticity clause under a new name. All six steps have fewer than 1000 characters, so none hides a long comparison argument.

For the coordinate lemma I tested m=r=s=1, rho=H_E=H_F=1, B=0, which gives Q=-conjugate(A) d/dx - d(conjugate(A))/dx. With A=1 and variable positive rho,H the density/metric logarithmic derivative appears in the zero-order term as required. With A=0 the formula is the weighted pointwise adjoint of B. An empty U makes the integral identity vacuous. The assumption that at least one section has support compactly contained in U is necessary to remove boundary terms and is explicitly present. These are tests of a genuine local integration lemma, not of a copied clause about a Dolbeault Laplacian. The proof idea for its later worker is ordinary compact-support integration by parts in each real coordinate, then collecting coefficients; its unsplit JSON carries no proof or proof sketch.

For the partition node I checked the empty closed set and empty cover (zero functions satisfy the assertion), the single full-open cover (constant one), and covers of the whole compact manifold, the exact case used. It has no proof steps and is an exact Mathlib leaf. For the item, a one-dimensional flat complex torus has symbol -norm(xi^(0,1))^2 on functions and top anti-holomorphic forms alike, confirming both the sign and the endpoint computation. Empty M is vacuous. An invertible complex-linear map remains invertible as a real-linear map by exactly the same inverse; no real cotangent vectors are dropped.

Every recorded search was run with the required msearch command and its actual outputs were read. In particular the abstract LinearPMap adjoint hit does not give differential-operator coefficients. I also read Mathlib's candidate bilinear integration-by-parts statement at Analysis/Calculus/LineDeriv/IntegrationByParts.lean:195--204; passing to a coordinate open set, arranging compact cutoffs/extensions, and collecting variable weights needs more than one specialization, so I retained the local node as unsplit. Conversely the exact partition theorem was found and is recorded as a leaf. Neither new node has proof dependencies; the item's only proof dependencies are these two nodes, and citations.json quotes the actual relevant statements. All other calculations are written out in the item. No inherited metadata or statement was deleted.

## Outstanding work

The local coordinate integration lemma remains unsplit for a later worker, as required by the one-level delivery contract. This delivery writes no Lean and runs no compiler, Lake, or library build. Server preflight and dry-run results are recorded after validation below.

## Validation

The required `deliver.py Q123 lem-sfb-dolbeault-laplacian-elliptic --no-push` exited successfully and printed `OK (not pushed)` at f8329b51bb8, with server preflight passed. This includes the server DAG and split checks. No checker or preflight was run directly on this machine. The only subsequent content change was adding this validation record to the report.

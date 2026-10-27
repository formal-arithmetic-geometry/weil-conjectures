## What changed

Replaced the hole in `CategoryTheory.SignedDoubleRoos.signed_double_roos_tensor_exchange`
by a complete conjunction assembly from two independent, strictly smaller parts of its
existing eight-step proof. This is a decomposition, not a complete proof of the exchange
constructions. The existing theorem statement and docstring stay unchanged.

The original 18 coordinate, Roos, tensor and augmentation declarations move verbatim to
`Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeDefinitions`; the original module
publicly imports that module. Declaration-table comparison checked all 18 signatures
and bodies were identical. The original public dependencies are reexported through the
definitions module. This extraction permits the two new proof modules to import the
constructions without importing the theorem that uses them.

The interchange module states the signed strict interchange. The tensor module takes
any signed interchange as input and states only the tensor and augmentation conclusions.
The proof in the parent constructs the derived isomorphism using `derivedInterchange`,
then cancels the two comparison isomorphisms. It uses no uniqueness of derived cone maps
and no data chosen from a mere unproved existence theorem.

The interface extraction is recorded in
`coord/changes/signed-double-roos-definitions-extraction.md`. No source-library file is
changed. There are no forced adaptations of modules held by other groups.

## Proved and sorry left

Closed one original textual hole:
`CategoryTheory.SignedDoubleRoos.signed_double_roos_tensor_exchange`
(node `lem-sp-signed-double-roos-tensor-exchange`), with a complete assembly proof.
The derived comparison clause is proved directly by conjugation and cancellation.

Added two named lower holes, each in its own module, with source and complete coordinate
proof in words in its docstring and DAG node:

- `CategoryTheory.SignedDoubleRoos.signed_double_roos_interchange_core`
  (`lem-sp-signed-double-roos-interchange-core`): the strict double-cone interchange.
- `CategoryTheory.SignedDoubleRoos.signed_double_roos_tensor_core`
  (`lem-sp-signed-double-roos-tensor-core`): principal Koszul tensor exchange and its
  augmentation coherence for a supplied signed interchange.

Validation: `lcompile.py --all` compiled all four modules with exit code 0 and no
warnings or errors. Individual times were 17.8 s (definitions), 7.5 s (interchange),
12.3 s (tensor), and 36.3 s (parent assembly), all below the single-file limit.

The item module and the definitions module have zero holes. Two holes remain in the
whole delivery, so the ledger net is -1 before any closure pruning, not +1.

Edge cases checked in the coordinate argument: the zero complex and zero tower give
zero coordinates; Boolean pairs (false,false), (false,true), and (true,false) have
positive sign and only (true,true) is negated. In a constant double tower A=B=0, the
four-coordinate differential still commutes with the signed swap. Degree transports
use k-p-q = k-q-p for every integer k. For t=0, t a unit, and the first Koszul level
j=0 (exponent 1), both terms of the Koszul complex and its strict inclusion still
have the stated differential and transition formulas. Unbounded input causes only
two tensor summands in each degree. The tensor lemma asks no existence claim about beta
and uses its full signed coordinate hypothesis to obtain the last two equalities.

## No longer needed

Removed the private proof import `Sheaf.CategoryTheory.StrictRoosComparison`:
the parent theorem only asks for an explicit conjugate under any supplied comparisons,
which is exactly `derivedInterchange`. It does not require proving that those comparisons
come from derived limits. Accordingly the old parent proof step 5 is replaced by a
complete functorial cancellation calculation, and that node is removed from the parent's
proof dependencies and obsolete tool approvals. The parent's unchanged statement
dependencies still record the normalized-comparison context; no external module is
withdrawn or claimed globally unused.

Removed the old private imports
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`Mathlib.CategoryTheory.Limits.Shapes.Products`, and
`Mathlib.CategoryTheory.Abelian.Basic`. The constructions already receive their required
interfaces through the retained public imports. The tensor node still explicitly
retains the sheafification definition dependency for its natural-language proof.

No other old proof dependency is globally pruned: the product, abelian, strict Roos,
sheaf tensor, total tensor and principal Koszul nodes remain required by the two cores.
No old Lean module or DAG node is deleted. Zero current Lean importers is not used as
an argument for withdrawing the item: `lem-sp-power-torsion-sheaf-limit-complete`
still cites it in its proof.

## Where the brief, the DAG or earlier work was wrong

The dependency statements are available, but most are definitions, not the constructed
signed interchange or normalized principal tensor interchange. The nearby
`KoszulRoosProjectionComparison` is specialized to pro-etale schemes and regular
coefficients, while this item allows arbitrary essentially small sites and arbitrary t;
it cannot simply be applied. Mathlib's cone, shift and tensor APIs provide ingredients
but not these two core statements.

No mathematical error in the statement or the existing coordinate proof was found.
The recorded strictRoosComparison proof dependency is unnecessary for the actual Lean
derived clause, whose arbitrary comparison isomorphisms are supplied by its binders.
The unit route is unchanged. `dag/units/sk-lem-sp-tower.json` currently has empty realized
lists; this delivery changes none of the unit text, steps or route.

Ownership of the original plan: old steps 1--4 belong to the interchange core;
old step 5 is proved in the parent; old steps 6--8 belong to the tensor core.
The definitions node only records the original constructions needed by both cores.
For review, the full original proof steps are retained below, without shortening:

Original step 1: Put $P^a=\prod_n\prod_jX_{n,j}^a$ and let $A=1-s_n$, $B=1-s_j$ on $P$. Define the product interchange by requiring its $(j,n)$ projection to equal the original $(n,j)$ projection. The reversed prescription is inverse, since every projection of either composite is the corresponding projection of the identity. Strict commutation of the transitions gives $AB=BA$ by the same projection test. We also use the canonical identification $\prod_i(M_i\oplus N_i)\cong(\prod_iM_i)\oplus(\prod_iN_i)$: send a pair of product vectors to its pairs of projections; the inverse has first and second components the products of the two biproduct projections. Both composites are identities on all components. These constructions commute with component maps and differentials. Thus the two iterated Roos complexes may be expanded using the same $P$.

Original step 2: In total degree $k$, expand the source $\mathsf R_n\mathsf R_jX$ in the order $(a,b,c,h)$ of Roos degrees $(0,0),(0,1),(1,0),(1,1)$. Its four summands are $P^k,P^{k-1},P^{k-1},P^{k-2}$. Apply the differential $(dv,-du-(1-s)v)$ twice. The result is
$$D(a,b,c,h)=(da,-db-Ba,-dc-Aa,dh+Bc-Ab).$$
For example the last component is the negative of the second component of the inner differential on $(c,h)$, minus $A$ applied to $b$, namely $dh+Bc-Ab$. This also fixes the sign of the doubly shifted coordinate without any totalization convention left implicit.

Original step 3: The target order is $(j\text{-degree},n\text{-degree})$. Define $\beta(a,b,c,h)=(a,c,b,-h)$ after the product interchange. Using step 2 with $A,B$ exchanged, both $D\beta$ and $\beta D$ have components
$$(da,-dc-Aa,-db-Ba,-dh-Bc+Ab).$$
Thus $\beta$ is a chain map. Its reversed-coordinate formula is its inverse. It is exactly multiplication by $(-1)^{pq}$ on bidegree $(p,q)$, with no sign on the other three coordinates.

Original step 4: For a strict double-tower map, the induced maps on the four coordinates are the respective product maps; these commute with permutation, negation, and both shifts. This proves naturality. Evaluation at $n$ in the outer source retains $(a,b)$ and projects their $n$ index. In the target it retains the coordinates with $n$-Roos degree zero, also $(a,b)$ after $\beta$. Evaluation at $j$ likewise retains $(a,c)$ on either side. The sign on $h$ never enters either evaluation. Hence both evaluation squares commute as chain-map squares.

Original step 5: Localize $\beta$ and its inverse; the two composite identities remain identities under the localization functor. For each iterated limit use the inner and then outer normalized comparison $\rho$ of [lem-weil-strict-roos-comparison], with the strict inner Roos complexes as the outer representatives. The induced map on iterated total derived limits is the conjugate $\rho_{jn}\,Q(\beta)\,\rho_{nj}^{-1}$. Naturality of $\rho$ identifies this conjugate on strict maps, and its projection normalization identifies its evaluation squares with those of step 4. In particular this is the signed comparison induced by the specified Roos models; no uniqueness claim about maps between unspecified cones is used.

Original step 6: The tensor definition gives $M\otimes_RR\cong M$ by $x\otimes r\mapsto rx$, with inverse $x\mapsto x\otimes1$: balancing gives $x\otimes r=rx\otimes1$. These sectionwise inverse maps are natural in restrictions, and hence sheafify to inverse maps. Consequently $(V\otimes L_j)^k\cong V^{k+1}\oplus V^k$, with coordinates from Koszul degrees $-1,0$. Only these two summands occur, even when $V$ is unbounded. The product/biproduct maps of step 1 therefore identify $(\prod_nQ_n)\otimes L_j$ and $\prod_n(Q_n\otimes L_j)$ degreewise, and identify the two Roos copies as well. Define $\gamma_j$ by these coordinate maps, leaving each $Q_n^a\otimes L_j^b$ coordinate unchanged; the inverse assembles its two product coordinates. This constructs inverse graded maps without asserting that arbitrary tensor products preserve products.

Original step 7: Check the differentials on a coordinate of intrinsic $Q$ degree $a$, Roos degree $p\in\{0,1\}$, and Koszul degree $b\in\{-1,0\}$. On $H_0\otimes L_j$ the internal $Q$ differential has coefficient $(-1)^p$, the Koszul differential has coefficient $(-1)^{a+p}$, and the Roos arrow from $p=0$ to $p=1$ is $-(1-s_n)$. On $\mathsf R_n(Q\otimes L_j)$ they are respectively $(-1)^p$, $(-1)^p(-1)^a$, and $-(1-s_n)$. The coefficients agree, so the graded maps in step 6 are chain isomorphisms. The same coordinate test shows naturality in $Q$, commutation with the Koszul transition $(t,1)$, the degree-zero Koszul inclusion, and evaluation at $n$: all are the same component maps before and after $\gamma_j$.

Original step 8: The map $u_P$ is a chain map because $p\mapsto p\otimes1$ is the degree-zero Koszul inclusion, its components are fixed by the $j$-transition, and its shifted $j$-component is zero. Write an input to $H_0$ as $(v,u)$, of $n$-Roos degrees $0,1$. The coordinates of $\mathsf R_n(u_{Q_n})(v,u)$ in the order of step 2 are $(v\otimes1,0,u\otimes1,0)$, with the indicated entries repeated for all $j$. Applying $\beta$ gives $(v\otimes1,u\otimes1,0,0)$ in target order. Thus every $j$-Roos-degree-one coordinate is zero, and the degree-zero ones are precisely the two coordinates of $H_0$ inserted in Koszul degree zero. Step 7 identifies their images under $\mathsf R_j(\gamma^{-1})$ with $u_{H_0}(v,u)$. This proves the asserted strict equality, and therefore its derived equality. All calculations use finite biproducts and specified countable products only; no boundedness or condition on $t$ or $Q$ was used.

## New nodes

`def-sp-signed-double-roos-tensor-exchange-data` records the 18 unchanged constructions
in their extracted definitions module; it introduces no alternative tensor or cone.

`lem-sp-signed-double-roos-interchange-core` records original proof steps 1--4 with the
signed coordinate and strict evaluation conclusions, without any tensor data or derived
comparison clause.

`lem-sp-signed-double-roos-tensor-core` records original proof steps 6--8, assuming only
the coordinate property of a supplied beta, with no construction or evaluation-square
claim about beta. Both statement nodes are strictly parts of the parent's argument.

Change record: `coord/changes/signed-double-roos-definitions-extraction.md`.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

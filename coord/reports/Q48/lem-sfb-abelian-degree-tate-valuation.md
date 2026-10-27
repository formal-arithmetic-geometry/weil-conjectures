# Stage-1 delivery: lem-sfb-abelian-degree-tate-valuation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-degree-tate-valuation.json`: item, six-step split, statement unchanged; not a Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-group-scheme-primary-order.json`: one new statement-only node, unsplit; no Mathlib match.
- Sandbox `citations.json`: every proof-step citation backed by the full verbatim statement read. `searches.jsonl` is the original msearch log. Text extractions and the writing script are sandbox research files, not delivery nodes.

## Attachments

None. Searched the entire live `lean/WeilConjectures/` by blueprint tag and by Tate-module, determinant, degree, isogeny and primary-order notions. The abelian-variety Tate files supply rank results, and GroupScheme/Finite supplies connected order and finite-etale point counting, but none states this complete item or the new primary-order comparison. In particular a sorry-free rank theorem is not an attachment for a degree comparison. No Lean was written or compiled.

## WANTED

None. Both Milne PDFs used are present in literature.

## Findings and changes

The imported item had no proof. I kept its statement and its source metadata. Milne AV I Proposition 10.20, printed p.52, is the intended route: scheme kernel order, primary torsion, Tate cokernel/index, determinant. The displayed chain abbreviates the non-isogeny case, where an unqualified finite cardinality of the kernel/cokernel is not available. The delivered proof separates that case explicitly. It computes the isogeny index by finite-level kernels and existing Smith form, so it does not need a new cokernel comparison theorem.

The new lemma supplies only the scheme-order/points comparison, for arbitrary finite commutative group schemes over an algebraically closed field. Its statement does not mention abelian varieties, Tate modules or determinants, and it is neither a clause of this item nor a relabeling of it. Its future proof is the connected-etale splitting of Milne Algebraic Groups 11.3: over an algebraically closed field the etale factor is constant; the connected factor has order a power of the characteristic exponent by 11.30 (and order one in characteristic zero by Cartier/11.31). Thus the prime-to-characteristic part of the scheme order is the corresponding part of the finite group of points. The primary decomposition of a finite abelian group then gives the stated cardinality and stabilization at n >= max(1,e). This argument is recorded here, not inserted in the statement-only node.

No statement dispute was found. No unit or chapter route was changed. The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` was read. This item is the inherited lower-level abelian input, and no claim is made that current clause (3) itself discusses Tate modules. `blueprint_refs.py ancestor` returns None for the inherited created-node chain; the null ancestor and via chain are retained rather than inventing an imported ancestor.

## Not duplicates

- lem-sfb-finite-group-scheme-primary-order vs lem-sc-connected-finite-order: the existing node gives a connected group's characteristic-power scheme order, not the primary order of geometric points of an arbitrary disconnected possibly nonreduced group.
- lem-sfb-finite-group-scheme-primary-order vs lem-sc-fg-order-prime-etale: the existing node assumes the entire group order is prime to the characteristic; the new node permits an inseparable characteristic-primary factor and measures any other primary factor.
- lem-sfb-finite-group-scheme-primary-order vs lem-sc-finite-etale-points: the existing node assumes etaleness and counts all points; the new node has no etaleness hypothesis and compares one primary part of scheme order and points.
- lem-sfb-finite-group-scheme-primary-order vs lem-sfb-finite-group-scheme-order-annihilator: annihilation by scheme order on all algebra-valued points does not count its geometric primary subgroup.
- lem-sfb-finite-group-scheme-primary-order vs lem-sfb-abelian-degree-tate-valuation: the item compares a geometric endomorphism degree with a Tate determinant; the new node has neither endomorphisms nor Tate action nor determinants.

Whole DAG and whole imported-blueprint searches were run for Tate, Tate module determinant, Tate cokernel, Smith, finite group scheme, connected-etale, finite group order, primary and isogeny. I also searched the current latest abelian-variety blueprint for the comparison notions. The existing finite-kernel/equal-dimension theorem and rectangular DVR Smith form were reused rather than duplicated. Mathlib searches were exclusively through msearch.py; semantic results concerned abstract finite groups, finite fields and integer lattice indices, which do not state the geometric comparison. The second phrasings and exact service results are recorded without inventing queries. All services used for the new node answered; none was recorded as absent when unavailable.

## Review by Q48

I read Milne AV I printed pp.32 (Proposition 7.1), 34 (torsion lifting), 43 (kernel abelian part), 44–45 (Tate construction and rank), and 52 (Proposition 10.20 proof). For the new node I read Milne Algebraic Groups printed p.210, Proposition 11.3 and its proof, and pp.219–221, Theorem 11.29 and Corollaries 11.30–11.31; the connected-etale splitting is applicable because the stated base field is algebraically closed, hence perfect. These facts go beyond a two-line manipulation of the cited existing statements, so the missing scheme-order comparison is a real new lemma. There is no SGA source.

Step 1 uses exactly the integral and rational rank assertions of prop-av-tate-rank and the componentwise action in sk-def-av-tate. The hypotheses are an abelian variety over an algebraically closed field and ell different from its characteristic. I checked both, and chose an integral basis so its scalar extension really computes the rational determinant.

Step 2 uses the statement of lem-sc-isogeny-surjective only for multiplication by the positive integer ell on the points of C over the given algebraically closed field. The compatible lifting and kernel formula are written out from sk-def-av-tate, rather than attributed to a rank node. If the nth coordinate is zero, shifting the sequence by n gives the required divisor by ell^n; the zero earlier coordinates follow by compatibility. This also proves naturality with a by inspecting coordinates. It is an elementary sequence argument and was not made a new node.

Step 3 uses def-sc-isogeny for the finite kernel and its order, lem-sc-av-commutative for commutativity, and the full new primary-order statement for all sufficiently large n. The new node allows nonreduced kernels; the proof never substitutes number of all geometric kernel points for scheme degree. I checked this especially for inseparable isogenies.

Step 4 uses exactly the diagonal form provided by lem-sfb-dvr-matrix-smith-powers, not a theorem about continuous families or its proof. The hypotheses hold because def-weil-l-adic-numbers explicitly supplies the DVR, ell as uniformizer, and quotients by ell^n. I wrote the scalar kernel count, including exponent zero, exponents at least n, and zero pivots. Constant finite kernel cardinality for arbitrarily large n excludes a zero pivot, and n beyond all exponents identifies the sum of exponents with v_ell(d). This provides both full rank and determinant norm without assuming injectivity of Tate action or a rational inverse in advance. Determinants of the two integral invertible basis matrices are units, so the norm comparison is legitimate.

Step 5 uses the closed-subgroup assertion of lem-sc-kernel-subgroup; the abelian reduced identity component, its dimension equality and its dimension-zero finiteness assertion in lem-sfb-abelian-closed-subgroup-reduced-component; and the exact conclusion of lem-sfb-finite-kernel-equal-dimension-isogeny. All are applied over the algebraically closed field in the item. A=A gives the equal-dimension hypothesis. The supposed finite kernel would imply surjectivity, and hence the definition of isogeny, contradicting the case assumption. Thus B has positive dimension, and prop-av-tate-rank gives a nonzero integral Tate vector. Its inclusion is injective directly coordinate by coordinate and its image is killed because B is contained in the actual kernel. No unsupported exactness theorem for inverse limits is used.

Step 6 uses the actual inclusion of the integral coefficient ring in its fraction field, supplied by def-weil-l-adic-numbers. A nonzero free-coordinate vector stays nonzero after that inclusion, so the rational matrix has dependent columns and determinant zero. This elementary determinant argument completes the degree-zero case. I checked the cited statement rather than inferring anything from a definition of degree alone.

Small cases checked: a=0 on positive-dimensional A, a=id, multiplication by ell^s, projection on a product B x C, a purely inseparable isogeny in characteristic p different from ell, finite group schemes alpha_p and mu_p in characteristic p, a constant cyclic group of order ell^e, a mixed product with a characteristic-primary nonreduced factor, e=0 (trivial ell-primary subgroup), zero Smith pivots, and exponent-zero unit pivots. In particular inseparability contributes only a p-power to degree, with ell-adic absolute value one. The item excludes dimension zero; no step uses a nonzero vector in that excluded case.

I checked delivery-errors B through E against the written files. The new node introduces all objects and needed notions, carries only a statement, has an honest source and logged searches, and is smaller than the item. Every non-elementary input has a cited node, every citation was opened and copied verbatim into citations.json, the finite-level and zero-determinant computations are explicit, and no proof step is longer than 2000 characters. I avoided the available stronger relative determinant and characteristic-polynomial nodes, which are downstream of this item and would make a circular argument. Tool uses of the Tate-rank, multiplication, commutativity, kernel and Smith-form statements are declared in split_report; they are general tools, not replacements for the unit's route.

## Unfinished

The new primary-order lemma is intentionally unsplit, as required for a one-level split. No item proof case remains open. Delivery validation is recorded by the required dry run and push.

# Q31 repair: lem-sfb-augmented-etale-associated-graded

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-augmented-etale-associated-graded.json`: statement unchanged, parent proof shortened by extracting arguments, not by discarding them; 4 steps, 2576 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-formally-etale-power-step.json`: statement, unsplit; no exact Mathlib match. One successor-stage inverse construction, including factorization, both inverse identities, and compatibility.
- `dag/nodes/sec-six-functors-basics/lem-sfb-power-quotient-graded-comparison.json`: statement, unsplit; no exact Mathlib match. General comparison from quotient isomorphisms to graded algebras, including all canonical map functoriality.
- `citations.json`: actual verbatim statements for every citation of all four parent steps.
- `searches.jsonl`: actual msearch query logs. `original.json` retains the complete starting node. `repair.py` and `write_report.py` are sandbox-only generation scripts.

## Attachments

None. Searched the blueprint tag and the notions in `lean/WeilConjectures/`. Read `lean/Sheaf/RingTheory/FormallyEtaleAssociatedGraded.lean`: the principal declaration at line 91 has `sorry`; the naturality, composition, identity and affine-etale declarations also have `sorry`. Thus these are interfaces, not completed proofs or attachments. Existing associated-graded structure declarations in `WeilConjectures/RingTheory/AssociatedGradedRing.lean` supply ring structure, not the two new comparisons.

## WANTED

None: both source places are present in `literature/stacks-project/algebra.tex`.

## What was wrong, and repair of the return

The only return point is the human's re-split request: the previous proof had 5468 characters across seven steps. No statement correction is needed. There was no retained sandbox node or report on this retry: the sandbox contained only dispatcher brief markers. I copied the current repository node to `original.json` and used it as the delivered/returned text. Its seven steps have exactly the lengths listed in the return. Maintainer fields, Lean interfaces, statement and statement dependencies are retained; delivery.py rebases the split-owned fields onto current server main.

The original substantial arguments now divide into two independent tasks of comparable proof size. The first new node carries the old Steps 3-4 (1647 characters of the old proof); the second carries old Steps 5-7 (2264 characters). The old Steps 1-2 remain as the parent's hypothesis bridge and elementary base case. The parent now assembles these by induction. Neither new node concludes the parent: the successor lemma requires an existing inverse at a fixed level and proves no graded assertion; the graded comparison assumes all quotient isomorphisms and assumes no formal etaleness. Both are delivered statement-only, with empty proof, empty proof_deps and null proof_origin, so separate workers can start their proofs independently. The original full arguments are reproduced below for handoff; none were summarized away.

## Not duplicates

lem-sfb-formally-etale-power-step vs lem-sfb-augmented-etale-associated-graded: same source tag 0H1D, but the new lemma assumes an inverse at one fixed n and constructs the successor inverse with its lift/factorization/compatibility. It asserts neither all-level existence nor a graded comparison; the parent still supplies the base case and induction.

lem-sfb-power-quotient-graded-comparison vs lem-sfb-augmented-etale-associated-graded: same source tag 0H1D, but the new lemma is a general ideal-preserving-map criterion conditional on all positive quotient isomorphisms, with no formal-etale or augmentation hypothesis. It proves the independent homogeneous-piece, direct-sum, product/scalar and functoriality arguments rather than the existence of quotient isomorphisms.

lem-sfb-power-quotient-graded-comparison vs lem-weil-pbc-associated-graded-ring-structure: the existing node constructs the ring and scalar structure on a single associated graded abelian group; it does not construct a graded map for an arbitrary ring homomorphism, deduce its bijectivity from quotient comparisons, or establish its naturality.

Whole-DAG searches by tag and by associated-graded/isomorphism/functoriality and square-zero inverse terminology found no existing statement of either new argument. The only other textual 0H1D hit was the parent's citer `lem-sfb-nodal-branch-double-cover`, whose source is the nodal-family charts and whose statement concerns a degree-two scheme cover, not this algebra. Read the nearby candidates `lem-trf-smooth-local-tangent-cone-extension` and `lem-trf-smooth-rational-point-completion`: their additional local, characteristic-zero, smooth, finite-type and Noetherian hypotheses and polynomial-variable conclusions do not give the general criterion here. The nodal tangent-normalization and quasi-regular-sequence graded nodes likewise compare different objects. `lem-weil-pbc-etale-infinitesimal-neighbourhoods` proves etaleness near a closed fibre, not an inverse between quotient rings.

Blueprint-wide searches run with `tools/blueprint_refs.py`: `associated graded`, `formally etale`, `formally`, `infinitesimal`, `graded ring`, `lifting`, `0H1D`, `ideal power`. No duplicate. The ancestor command returns None, matching the parent's inherited null from.node; new ancestry prepends this item to its existing via chain and records the exact old proof steps and the tangent-cone use in the original blueprint route. Chapter and unit records were read; no chapter, unit route or realized fields are changed (this item is not a unit key statement).

## Mathlib searches read

Each new node has LeanFinder, LeanSearch, Loogle and source-grep searches, with a second semantic phrasing and a broader grep before concluding absence. Exact queries and responses are in searches.jsonl and the new nodes. The first Loogle request for `Algebra.FormallyEtale, Ideal.Quotient` rejected the namespace as an unknown identifier; I retained that actual result and ran the meaningful substring query `"Algebra.FormallyEtale", "comp"` afterwards.

For the power-step node, the real hits are `Algebra.FormallyEtale.comp_bijective` and `.iff_comp_bijective` (`Mathlib/RingTheory/Etale/Basic.lean`, lines 77 and 86). Read those declarations: they give unique lifting through a square-zero ideal. They do not show that the lift kills J^(n+1), factor it, or establish the two inverse identities. Standard-etale-pair hits are more specialized. Formally-smooth lifting hits do not provide uniqueness. Thus no one-line specialization states the new node.

For the graded comparison node, `Ideal.quotientEquiv` assumes an equivalence of the original rings, which is absent here, while `Ideal.powQuotPowSuccEquivMapMkPowSuccPow` and its linear version identify a single quotient with an ideal image; neither assembles or compares graded rings. Adic-completion transition maps assume/construct different objects; cotangent extension hits concern first-order cotangent modules. The source-wide associated-graded grep returns only a homological bicomplex associated-graded functor. Read the quotient-map declarations in `Ideal/Quotient/Operations.lean` as well: they supply quotient functoriality but not the criterion and graded direct-sum algebra map. Neither new node is a Mathlib leaf. Existing item searches were retained as existing evidence; they were not invented or rerun unchanged.

## Review by Q31

I read Stacks 0H1D, `lemma-formally-etale-lift-infinitesimal`, including its successive lifting diagrams and the uniqueness argument (algebra.tex lines 41257-41288), and Stacks 00UR, `lemma-formally-etale-etale`, including both directions (starting at line 41199). The local tag table identifies exactly those labels. These are the sources of both new nodes: the first isolates one dotted-arrow/inverse argument, the second makes precise the associated-graded consequence and the canonical maps. No SGA source or trace route is used.

For parent Step 1 I opened all six cited statements. `def-weil-etale-morphism` supplies flatness and unramifiedness. `lem-weil-pbc-flat-unramified-formally-etale` supplies formal smoothness (and a unique scheme lift); `def-sbc-formally-smooth` fixes that meaning. `lem-weil-pbc-affine-formally-smooth-iff-ring-lifting` supplies exactly existence for every square-zero ideal in an arbitrary A-algebra. `lem-weil-pbc-etale-ring-map-iff-etale-affine` supplies Omega_(C/A)=0, and direction (2)=>(1) of `lem-weil-pbc-formally-unramified-ring-iff-kahler-zero` supplies uniqueness for the very same ring lifting problem. Combining surjectivity and injectivity proves the desired bijection; the later argument uses that hypothesis directly. This preserves the previous reviewer's repair rather than reinstating the dropped cotangent node.

For Step 2 I read `def-weil-pbc-algebra-hom-quotient`: it states the quotient map's surjectivity and kernel, the algebra-map meaning, ideal products and powers. Preservation of powers follows by products and sums. The base inverse follows from the stated kernel and surjectivity; commutation of the quotient maps is equality on representatives, so elementary is justified.

Step 3 cites the new power-step statement, not its proof. Its hypotheses are exactly in force: the same A,C,I,J, the stated formal-etale lifting bijection, n>=1, and the inverse from the induction hypothesis. Its conclusion explicitly includes both inverse equations and immediate reduction compatibility. Repeated composition gives all earlier compatibility. The induction has the base in Step 2, so it is not circular. There is no dependency from the new node back to this item (created.item and blueprint.via are provenance only).

Step 4 cites the new comparison statement. The ideal-image inclusion was checked in Step 2; Step 3 establishes every positive quotient-isomorphism hypothesis. The conclusion names the actual degree-preserving representative map and the scalar identity, not an unspecified ring equivalence. It explicitly includes commuting-square, composition and identity laws for both Q and G, without demanding that comparison maps be formally etale. This supplies every clause of the parent, with no implicit identification or missing fact. Citations.json quotes the actual statement in full for each use.

I checked the internal successor argument needed by the first new statement even though its proof is reserved for another worker. At n>=1, both kernels I^n/I^(n+1) and J^n/J^(n+1) are square zero since 2n>=n+1. The existing inverse is an A-algebra map. For j in J, choose a representing g_n([j]); then phi(a)-j is in J^n, so phi(a) is in J and a is in I. Thus g_n pi_(J,n) sends J into I/I^n even when only the fixed-level inverse, not all lower inverses, is given. Its lift sends J into I/I^(n+1), kills J^(n+1), and the two inverse identities follow by the distinct arguments reproduced below. This is why extracting a fixed-step lemma is sound; compatibility with an earlier chosen g_1 is not an unstated hypothesis.

For the second new statement, I checked the degree-r inverse argument using f_(r+1) and f_r; r=0 instead uses f_1, avoiding any reliance on level zero. The direct-sum inverse has finite support, products are the homogeneous product formula of `lem-weil-pbc-associated-graded-ring-structure`, and the scalar equality is the same representative identity. Its hypotheses do not include formal etaleness or I=phi^(-1)(J), which are unnecessary once all Q_n are isomorphisms. Naturality is valid for arbitrary ideal-preserving squares; composition and identity are verified on each homogeneous representative and extended by finite sums.

Edge cases: identity maps; I=J=0; I=A,J=C; zero source/target rings when a unital map exists; n=1 (the square-zero inequality is equality); degree zero; and k -> k x k with J=0 x k, I=0. The last example has J!=IC and both new conclusions remain correct. Formal smoothness alone is inadequate: k -> k[t], J=(t), I=0 has a level-one inverse but k -> k[t]/(t^2) is not an isomorphism. This confirms the need for uniqueness in the new power-step node, rather than a silently weakened lifting hypothesis.

Checked delivery-errors B1-B10: both statements introduce all their objects, cite the definitions of quotient/graded notions, have actual tag-label sources, no proof sketches inside statements, no fake search results or unsupported leaves, and completed blueprint provenance. Checked C1-C8: the parent uses only exact cited statement clauses and explicit elementary manipulations, has no hidden source lemma, no cycle, and retains the existing approved etale route. Checked D1-D5: neither node is the parent or an unconditioned copy of its clauses, neither carries the whole proof, and all old arguments are allocated below. The two new proofs have different inputs and can be developed independently. Checked E1-E7 as above: no extra finiteness hypothesis or dropped scalar/naturality clause, wrong quotient, false edge case, or source error. Every parent proof step is under 2000 characters; total is 2576.

## Full retained arguments and allocation

This section retains the complete previous seven-step proof for the next workers; it is not a proof field of either unsplit node.

### Original Step 1 -> parent hypothesis bridge

For the parenthetical etale case, suppose $\operatorname{Spec}\varphi:\operatorname{Spec}C\to\operatorname{Spec}A$ is etale. By [def-weil-etale-morphism] it is flat and unramified, so [lem-weil-pbc-flat-unramified-formally-etale] makes it formally smooth in the sense of [def-sbc-formally-smooth]. Applying [lem-weil-pbc-affine-formally-smooth-iff-ring-lifting] to $\varphi$: for every $A$-algebra $E$ and square-zero ideal $N\subset E$, every $A$-algebra map $C\to E/N$ lifts to an $A$-algebra map $C\to E$, i.e. the reduction map of the item is surjective. By [lem-weil-pbc-etale-ring-map-iff-etale-affine], $\Omega_{C/A}=0$; the implication (2)$\Rightarrow$(1) of [lem-weil-pbc-formally-unramified-ring-iff-kahler-zero], with base ring $A$ and algebra $C$, says that such a lift is unique, i.e. the reduction map is injective. Hence the stated lifting hypothesis holds. In the rest of the proof use that lifting hypothesis directly; no finite-presentation assumption is needed there.

Cited nodes: def-weil-etale-morphism, lem-weil-pbc-flat-unramified-formally-etale, def-sbc-formally-smooth, lem-weil-pbc-affine-formally-smooth-iff-ring-lifting, lem-weil-pbc-etale-ring-map-iff-etale-affine, lem-weil-pbc-formally-unramified-ring-iff-kahler-zero.

### Original Step 2 -> parent elementary base case and quotient notation

Write $\pi_{I,n}:A\to A/I^n$ and $\pi_{J,n}:C\to C/J^n$ for the quotient maps [def-weil-pbc-algebra-hom-quotient]. If $a\in I$ then $\varphi(a)\in J$, so a product of $n$ elements of $I$ maps into $J^n$; sums and multiples give $\varphi(I^n)\subseteq J^n$. Thus $f_n([a])=[\varphi(a)]$ is a well-defined $A$-algebra homomorphism. These maps commute with every reduction map, since both composites send $[a]$ to $[\varphi(a)]$. For $n=1$, $f_1$ is surjective by assumption, and $f_1([a])=0$ means $a\in I$, so it is injective. Set $g_1=f_1^{-1}$ and $\ell_1=g_1\pi_{J,1}$.

Cited nodes: def-weil-pbc-algebra-hom-quotient.

### Original Step 3 -> lem-sfb-formally-etale-power-step

Induct on $n\ge1$ with claim: $f_n$ has an inverse $g_n$ and the maps $\ell_n=g_n\pi_{J,n}:C\to A/I^n$ are compatible with reduction at all already constructed levels. Suppose this holds through $n$. In $E=A/I^{n+1}$ the kernel $N=I^n/I^{n+1}$ of reduction to $A/I^n$ is square zero: a product of representatives in $I^n$ lies in $I^{2n}\subseteq I^{n+1}$, since $2n\ge n+1$. The quotient $E/N$ identifies with $A/I^n$ by $[[a]]\mapsto[a]$ (surjective with zero kernel). The existence part of the stated lifting hypothesis therefore gives an $A$-algebra map $\ell_{n+1}:C\to A/I^{n+1}$ reducing to $\ell_n$. This also preserves compatibility with every earlier $\ell_r$.

Cited nodes: def-weil-pbc-algebra-hom-quotient.

### Original Step 4 -> lem-sfb-formally-etale-power-step

The reduction of $\ell_{n+1}$ modulo $I$ is $\ell_1$, which vanishes on $J$. Hence $\ell_{n+1}(J)\subseteq I/I^{n+1}$, and products of $n+1$ such images vanish. Thus $\ell_{n+1}$ kills $J^{n+1}$ and induces $g_{n+1}:C/J^{n+1}\to A/I^{n+1}$, $[c]\mapsto\ell_{n+1}(c)$. It satisfies $g_{n+1}f_{n+1}([a])=\ell_{n+1}(\varphi(a))=[a]$, because $\ell_{n+1}$ is an $A$-algebra map. To check the other identity, compare the $A$-algebra maps $u=f_{n+1}\ell_{n+1}$ and $v=\pi_{J,n+1}$ from $C$ to $C/J^{n+1}$. Their reductions to $C/J^n$ are respectively $f_n\ell_n=f_ng_n\pi_{J,n}=\pi_{J,n}$ and $\pi_{J,n}$. The kernel $J^n/J^{n+1}$ is square zero by the same product calculation as in Step 3. The uniqueness part of the lifting hypothesis, applied with $E=C/J^{n+1}$, gives $u=v$. Evaluating on every $c\in C$ gives $f_{n+1}g_{n+1}=\mathrm{id}$, completing the induction. Compatibility of the $g_n$ follows by evaluating on $[c]$ the already constructed compatibility of the $\ell_n$.

Cited nodes: def-weil-pbc-algebra-hom-quotient.

### Original Step 5 -> lem-sfb-power-quotient-graded-comparison

For $r\ge1$ let $\theta_r:I^r/I^{r+1}\to J^r/J^{r+1}$ send the class of $a$ to that of $\varphi(a)$; it is well defined by Step 2. If $\theta_r([a])=0$, then $f_{r+1}([a])=0$, so $a\in I^{r+1}$ by injectivity of $f_{r+1}$. For $c\in J^r$, choose $a\in A$ with $\varphi(a)-c\in J^{r+1}$ using surjectivity of $f_{r+1}$. Then $f_r([a])=0$, so $a\in I^r$ by injectivity of $f_r$, proving surjectivity of $\theta_r$. For $r=0$, set $\theta_0=f_1:A/I\to C/J$; this treats degree zero without using $f_0$. These are precisely the homogeneous-piece maps in [def-weil-pbc-associated-graded-ring].

Cited nodes: def-weil-pbc-algebra-hom-quotient, def-weil-pbc-associated-graded-ring.

### Original Step 6 -> lem-sfb-power-quotient-graded-comparison

Take the direct sum of the $\theta_r$ using [def-weil-pbc-associated-graded-ring]. An element has finitely many nonzero components, so applying $\theta_r^{-1}$ componentwise defines a two-sided inverse on the direct sum; its support is still finite. The ring structures, homogeneous product formula and scalar action are given by [lem-weil-pbc-associated-graded-ring-structure]. For $a\in I^r$ and $b\in I^s$, multiplicativity is the identity $[\varphi(ab)]=[\varphi(a)\varphi(b)]$ in $J^{r+s}/J^{r+s+1}$. Biadditivity and finite sums give multiplicativity for arbitrary elements; the unit maps to $[1]$ in degree zero. For $a\in A$ and $x\in I^r$, the scalar identity is $[\varphi(ax)]=[\varphi(a)\varphi(x)]$. Thus, identifying $A/I$ with $C/J$ by $f_1$, this is an isomorphism of graded $A/I$-algebras.

Cited nodes: def-weil-pbc-associated-graded-ring, lem-weil-pbc-associated-graded-ring-structure.

### Original Step 7 -> lem-sfb-power-quotient-graded-comparison

For naturality, take a second datum $\varphi':A'\to C'$, $I'$, $J'$ and ring maps $\alpha:A\to A'$, $\gamma:C\to C'$ with $\gamma\varphi=\varphi'\alpha$, $\alpha(I)\subseteq I'$ and $\gamma(J)\subseteq J'$. Products give preservation of every ideal power. On the quotient by the $n$th power, the two routes around the square send $[a]$ respectively to $[\gamma(\varphi(a))]$ and $[\varphi'(\alpha(a))]$, which are equal. For a homogeneous class $a\in I^r$ the identical calculation holds modulo $(J')^{r+1}$, so summing the components proves naturality of the graded map. For composable homomorphisms, successive images of a representative equal its image under the composite, and the identity homomorphism fixes every representative. These formulas establish all stated compatibility assertions, without choices or assumptions $J=IC$, Noetherianity or finite generation.

Cited nodes: def-weil-pbc-algebra-hom-quotient, def-weil-pbc-associated-graded-ring.

## What could not be finished

No unresolved stage-1 obligation. The two new statements intentionally remain unsplit, with no Lean implementation or compiler run, as required for parallel proof work. Dry-run and push results are recorded by the delivery tool.

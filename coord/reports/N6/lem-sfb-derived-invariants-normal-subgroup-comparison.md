# Worker report: repair of the returned split

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-derived-invariants-normal-subgroup-comparison.json`: statement unchanged; four-step assembly of four separate arguments, 1707 proof-text characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-open-normal-action-injective-models.json`: statement; unsplit; no Mathlib match. Carries old steps 1–4 (3043 original proof characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-inflation-resolution-naturality.json`: statement; unsplit; no Mathlib match. Carries old steps 5–9 (3761 original proof characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-action-topos-coefficient-coherence.json`: statement; unsplit; no Mathlib match. Carries old steps 10–11 (2926 original proof characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-quotient-tower-resolution-coherence.json`: statement; unsplit; no Mathlib match. Carries old steps 12–14 (2067 original proof characters).
- `citations.json`: exact statement quotes for each parent proof citation.

## Attachments

None. I searched the read-only upstream `WeilConjectures/` by notion and blueprint tag. The matching project declaration `Profinite.CondensedAction.normal_subgroup_comparison`, in `lean/Sheaf/CategoryTheory/CondensedNormalSubgroupComparison.lean:685`, ends in `sorry` on line 686. Its docstring retains the same fourteen-step argument. Abstract/discrete representation declarations cover different coefficient/action categories.

## WANTED

WANTED: a human-written reference for this precise ordinary unbounded internal-condensed normal-subgroup comparison, including kernel restriction and normalized coefficient compatibility. As in the inherited source field, main-20261015 direct-images paragraph (3) motivates the tame-boundary application but does not state this formal lemma. The constructions remain explicitly agent-formulated; no new source is claimed to prove them verbatim.

## What was wrong and what changed

The return demands distribution of a proof of 11797 characters, rather than a shortened rendering of the same single task. I copied the current read-only repository item because the retained sandbox contained only dispatcher markers and no node or report. Four new statement-only nodes now expose the independent arguments and their precise resolution outputs. No new node has proof steps or proof dependencies; the original arguments are retained below as work allocations, not smuggled into their statements as proofs. The parent keeps its exact statement and all maintainer-owned fields. New statements specify actual derived isomorphisms, arrows, homotopy classes and their normalizations, rather than only cohomology groups. No Lean, compiler, repository writes or git command was used.

## What remains unfinished

The four new nodes are intentionally unsplit: future workers prove them independently. Their sizes are the original argument sizes, not an estimate from shorter statement text. The parent task is only their assembly. No source error or statement dispute was found.

## Review by N6

I read the current node, its Lean theorem and full proof docstring, the current blueprint unit and direct-images proof paragraph (3), the chapter record and all statements cited by the returned proof. I also read Stacks `derived.tex` at lemma-derived-adjoint-functors (09T5), lemma-K-injective (070I), lemma-K-injective-defined (070Y), lemma-enough-K-injectives-implies (070K), and lemma-adjoint-preserve-K-injectives (08BJ), and `sites-cohomology.tex` lemma-derived-pushforward-composition (0D6E). These are the supporting categorical inputs, not a claim that Stacks states the condensed result. No SGA route is used.

The first new node carries old steps 1–4: the action-site presentation and ringed-site Grothendieck theorem have small-site hypotheses satisfied by the size convention; the quotient has finitely many open cosets, hence a continuous set section. The normalized adjunction has the correct direction (inflation left, invariants right). For restriction to K, H=K×1 in P=G×L has quotient Q×L and continuous section (s,1), so the split-coset induction theorem applies even for infinite L. The exact-left-adjoint criterion applies to r, T and full invariants. The exact-square theorem has r=Res_K, s=U, H'=T and H=Γ_K, so it gives the stated derived β. None of these ingredients was replaced by a definition that merely specifies their desired existence.

The second node carries old steps 5–9: exact trivial inflation followed by quotient inflation is the left functor in the normalized adjunction-composition theorem. Its conjugate is c, with the identity on invariant complexes, not an arbitrary isomorphism. Since TI is K-injective, the Hom bijection gives precisely the lift b and its uniqueness up to homotopy. Its normalized transpose composes with the invariant inclusion, so the inflation arrow has the displayed direction and c inf=RΓ(η). Equivariant maps preserve the fixed-section identities and homotopies. For a continuous h:L'→L, I specifically kept the extra resolution of r_h I: no preservation of K-injectives by arbitrary group restriction is used. I wrote the actual c square in the new statement to remove any ambiguity in “naturality”.

The third node carries old steps 10–11: the action-site formula extends to set-valued sheaves and its covering-sieve criterion gives a small-site presentation of the action topos. Inflation is finite-limit preserving on underlying sheaves; its right adjoint is kernel invariants. This gives geometric morphisms with the correct module direct images. For a ring map the underlying topos is the identity and the direct image is exact scalar restriction, so the two composites with a projection really are the same ringed-topos morphism. The composition theorem produces θ, and its normalized inverse is f_*(a). The cocycle statement explicitly includes changes on identity topoi and therefore applies to all coefficient squares. The new statement keeps the inverse representative (sI')^K→J^K and its full-invariant counterpart, the derived-unit square, arbitrary v, and absence of any flatness assumption.

The fourth node carries old steps 12–14: the kernel of a composite projection gives the successive fixed-section identity with the composite inclusion, and K-injective preservation makes the two factorizations compute the same derived functor. I checked the actual arrows: b a≃T₁i, d z≃T₂a and hence T₂(b)d z≃T₂T₁i. The unique extension class, after full invariants, gives inf₀₂=inf₁∘inf₂ with the correctly typed sources. The identity kernel has T=id; η is a resolution quasi-isomorphism viewed under the canonical localization identification and β,c are termwise identities. This is the unit/identity coherence of the same tower calculation.

For the repaired parent, step 1 cites the first new statement for precisely the action-category structures, kernel model and β that it states. Step 2 cites the second for c, the normalized resolution unit, the actual inflation formula and both naturalities. Step 3 cites the third for θ and its squares with those same normalized arrows. Step 4 cites the fourth for the actual transitivity arrow and identity kernel. All hypotheses are the parent’s own ring/site/profinite/open-normal hypotheses. The quotes in citations.json are literal substrings of these statements. Every non-elementary parent inference is accounted for by that step’s new node.

I tested the statements at K=1, K=G, L=1, the zero ring, zero module, an identity projection and towers having either identity stage. In particular K=1 makes β compare U with the same exact forgetting functor; K=G still allows arbitrary profinite L, covered by Q×L in the split-coset input. Scalar tests include identity ring maps and nonflat maps: the argument uses ringed-topos composition, not scalar preservation of K-injectives. The assembly has no step exceeding 2000 characters. The earlier fourteen arguments are preserved verbatim below, each assigned to the statement that now owns its proof obligation.

## Not duplicates

The new nodes were searched across the whole DAG by quotient/invariants, action-topos, normal-subgroup, scalar-restriction and tower terms, and across all blueprint chapters with `blueprint_refs.py search` for open normal invariant K-injective, normalized inflation, action topos coefficient, quotient tower, invariants and inflation. The ancestor tool reports null, just as in the current parent; I retained the inherited via chain and prepended the item for each child. No source tag is used as a substitute for a statement.
lem-sfb-open-normal-action-injective-models vs lem-sfb-condensed-product-action-inflation: product projections with split product kernel; it does not give arbitrary open-normal quotient residual actions or kernel K-injective restriction.

lem-sfb-open-normal-action-injective-models vs lem-sfb-condensed-derived-restriction-calculus: has general full-invariant group restriction and coefficient maps, but no normal-kernel residual functor, β/c compatibility, or transitivity of normalized quotient inflation.

lem-sfb-open-normal-action-injective-models vs lem-sfb-internal-action-site-presentation: presents module action sheaves and their kernels/cokernels, but has no derived normal-quotient or scalar-cocycle assertion.

lem-sfb-open-normal-action-injective-models vs lem-sfb-condensed-split-coset-induction: constructs exact induction for a split coset space; it does not give the derived invariant comparison or any of the compatibility diagrams.

lem-sfb-open-normal-action-injective-models vs lem-sfb-successive-derived-quotient-normalization: concerns scalar extension along ring maps, not invariants along group quotient projections.

lem-sfb-normal-inflation-resolution-naturality vs lem-sfb-condensed-product-action-inflation: product projections with split product kernel; it does not give arbitrary open-normal quotient residual actions or kernel K-injective restriction.

lem-sfb-normal-inflation-resolution-naturality vs lem-sfb-condensed-derived-restriction-calculus: has general full-invariant group restriction and coefficient maps, but no normal-kernel residual functor, β/c compatibility, or transitivity of normalized quotient inflation.

lem-sfb-normal-inflation-resolution-naturality vs lem-sfb-internal-action-site-presentation: presents module action sheaves and their kernels/cokernels, but has no derived normal-quotient or scalar-cocycle assertion.

lem-sfb-normal-inflation-resolution-naturality vs lem-sfb-condensed-split-coset-induction: constructs exact induction for a split coset space; it does not give the derived invariant comparison or any of the compatibility diagrams.

lem-sfb-normal-inflation-resolution-naturality vs lem-sfb-successive-derived-quotient-normalization: concerns scalar extension along ring maps, not invariants along group quotient projections.

lem-sfb-action-topos-coefficient-coherence vs lem-sfb-condensed-product-action-inflation: product projections with split product kernel; it does not give arbitrary open-normal quotient residual actions or kernel K-injective restriction.

lem-sfb-action-topos-coefficient-coherence vs lem-sfb-condensed-derived-restriction-calculus: has general full-invariant group restriction and coefficient maps, but no normal-kernel residual functor, β/c compatibility, or transitivity of normalized quotient inflation.

lem-sfb-action-topos-coefficient-coherence vs lem-sfb-internal-action-site-presentation: presents module action sheaves and their kernels/cokernels, but has no derived normal-quotient or scalar-cocycle assertion.

lem-sfb-action-topos-coefficient-coherence vs lem-sfb-condensed-split-coset-induction: constructs exact induction for a split coset space; it does not give the derived invariant comparison or any of the compatibility diagrams.

lem-sfb-action-topos-coefficient-coherence vs lem-sfb-successive-derived-quotient-normalization: concerns scalar extension along ring maps, not invariants along group quotient projections.

lem-sfb-normal-quotient-tower-resolution-coherence vs lem-sfb-condensed-product-action-inflation: product projections with split product kernel; it does not give arbitrary open-normal quotient residual actions or kernel K-injective restriction.

lem-sfb-normal-quotient-tower-resolution-coherence vs lem-sfb-condensed-derived-restriction-calculus: has general full-invariant group restriction and coefficient maps, but no normal-kernel residual functor, β/c compatibility, or transitivity of normalized quotient inflation.

lem-sfb-normal-quotient-tower-resolution-coherence vs lem-sfb-internal-action-site-presentation: presents module action sheaves and their kernels/cokernels, but has no derived normal-quotient or scalar-cocycle assertion.

lem-sfb-normal-quotient-tower-resolution-coherence vs lem-sfb-condensed-split-coset-induction: constructs exact induction for a split coset space; it does not give the derived invariant comparison or any of the compatibility diagrams.

lem-sfb-normal-quotient-tower-resolution-coherence vs lem-sfb-successive-derived-quotient-normalization: concerns scalar extension along ring maps, not invariants along group quotient projections.

## Mathlib search assessment

Every new node has logged leanfinder, loogle, leansearch and source-grep searches, with a different semantic phrasing in leansearch. The log is searches.jsonl; records are copied only from executed calls. I read the results and candidate source: RepresentationTheory/Invariants.lean:150–176 and :246–270 defines abstract-group quotient invariants; GroupCohomology/Functoriality.lean:161 and :558 gives per-degree maps and abstract inflation, not the unbounded internal-condensed result; Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:139 gives underived composition for continuous site functors, and Sheaf/ChangeOfRings.lean:36 defines scalar restriction. None is a one-line specialization of any of the four new statements. The first coefficient grep used a nonexistent likely directory and returned no hits; I corrected it with a logged grep under Algebra/Category/ModuleCat/Sheaf and inspected its hits. The earlier empty query is retained honestly and is not relied upon as evidence of absence. No service failures were reclassified as no match.

## Preserved argument allocations

The following is the returned proof verbatim. These are instructions/material for the four future proof tasks, not proof fields of any unsplit node. Their source and old citations are retained so that none of the 11797-character argument is lost by the re-split.

### lem-sfb-open-normal-action-injective-models — old steps 1–4

Old step 1. Apply the internal action-site presentation with the sheaf of groups $S\mapsto C(S,P)$ and the trivial action on $A$, for each $P=1,K,G\times L,Q\times L$. Its small ringed action site presents $\mathcal A_P(A)$ as a module-sheaf category. The ringed-site Grothendieck theorem therefore makes all these categories Grothendieck abelian. The presentation creates kernels and cokernels after forgetting actions. Changing an action by precomposition leaves the underlying module and its morphisms unchanged, so restriction, inflation and forgetting are additive and exact. These assertions also hold after a change of coefficient ring: scalar restriction leaves the underlying abelian sheaf, its kernels, and its sheaf-cokernels unchanged.

Cited nodes: lem-sfb-internal-action-site-presentation, lem-pur-ringed-site-grothendieck-abelian.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent action-category foundation; Grothendieck input: Stacks 03DA, 03DB, 03EW (sites-modules.tex) and 07A5 (sites-cohomology.tex).

Old step 2. The disjoint open cosets of $K$ cover compact $G$, so a finite subcover exhausts them. Choose one representative of each of the finitely many cosets of the open subgroup $K$ in $G$. This gives a continuous set section $s:Q\to G$. Define $T(M)$ by the sections fixed by $K$ after every profinite base change. The condition is local and preserved by restriction, so this is an internal submodule. Normality makes it $G\times L$-stable: $k(gm)=g((g^{-1}kg)m)=gm$. Every map into $Q\times L$ lifts using $(s,1_L)$, so its action on these sections is independent of the lift and defines the residual condensed $Q\times L$-action. A map from an inflated module lands in $T(M)$, since its source is $K$-fixed; conversely the invariant inclusion makes every map into $T(M)$ equivariant after inflation. These inverse operations give precisely the normalized adjunction. Applying the same fixed-section definition gives the identity $\Gamma_{G\times L}=\Gamma_{Q\times L}T$ on objects and maps, since every $(g,l)$ is a lift of $(\bar g,l)$ and the kernel is $K$.

Cited nodes: def-sfb-condensed-action-module.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent quotient-action and normalized transpose calculation.

Old step 3. Put $P=G\times L$ and identify $H=K\times\{1\}$ with $K$. The coset space $P/H$ is $Q\times L$; $(q,l)\mapsto(s(q),l)$ is a continuous section of its projection. The exact condensed induction lemma supplies an exact left adjoint to $\operatorname{Res}_K:\mathcal A_{G\times L}(A)\to\mathcal A_K(A)$, without requiring $L$ finite. Consequently restriction to $K$ preserves K-injective complexes by the exact-left-adjoint criterion. The same criterion applied to exact quotient inflation shows that $T$ preserves K-injectives. Applied to exact trivial inflation, it also shows that every invariants functor $\Gamma_P$ carries K-injectives to K-injectives.

Cited nodes: lem-sfb-condensed-split-coset-induction, lem-weil-pbc-right-adjoint-preserves-kinjective.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent kernel restriction; Stacks Tag 08BJ, lemma-adjoint-preserve-K-injectives.

Old step 4. There are enough K-injectives by the Grothendieck K-injective theorem. In the exact-square comparison theorem take $H'=T$, $H=\Gamma_K$, $r=\operatorname{Res}_K$, and $s=U_{Q\times L}$. The square $sH'=Hr$ is the fixed-section identity, and $r$ is exact and preserves K-injectives by step 3. Its normalized isomorphism is the required $\beta:D(U_{Q\times L})RT\cong R\Gamma_K D(\operatorname{Res}_K)$. Explicitly, on a resolution $N\to I$ both sides are represented by the identical complex $(I|_K)^K=U(TI)$; the comparison is its identity. This also fixes the comparison independently of all choices.

Cited nodes: lem-sfb-grothendieck-k-injective, lem-weil-pbc-kinjective-exact-square-comparison.
Source: literature/stacks-project/derived.tex, Tags 070I (lemma-K-injective), 070Y (lemma-K-injective-defined), 070K (lemma-enough-K-injectives-implies); normalized exact-square application.

### lem-sfb-normal-inflation-resolution-naturality — old steps 5–9

Old step 5. Apply the normalized derived adjunction-composition theorem to the exact trivial inflation from $\mathcal A_1(A)$ to $\mathcal A_{Q\times L}(A)$, followed by exact quotient inflation to $\mathcal A_{G\times L}(A)$. Their composite is trivial inflation to $G\times L$, and step 2 identifies the conjugate right adjoints by $\Gamma_{G\times L}=\Gamma_{Q\times L}T$, with the specified invariant inclusions. The theorem gives $c:R\Gamma_{G\times L}\cong R\Gamma_{Q\times L}RT$ as the conjugate of this exact inflation identity. On a K-injective $I$, the intermediate $TI$ is K-injective by step 3, so $c$ is represented by the identity $I^{G\times L}=(TI)^{Q\times L}$. Thus it has precisely the required adjunction normalization.

Cited nodes: lem-sfb-derived-composition-adjunction-normalization.
Source: literature/stacks-project/derived.tex, Tag 09T5, lemma-derived-adjoint-functors; exact-left-adjoint composition extraction of Tag 0D6E, sites-cohomology.tex, lemma-derived-pushforward-composition.

Old step 6. For a module $N$, choose a K-injective resolution $i:N[0]\to I$ in the action category. The unit of $RT$ is represented by $T(i):T(N)[0]\to TI$. The first comparison of step 4 takes its underlying map to $(i|_K)^K$, which is the usual invariant-to-derived-invariant map, since $I|_K$ is K-injective. Let $a:T(N)[0]\to J$ be a K-injective resolution in the quotient-action category. As $TI$ is K-injective, precomposition with $a$ gives a bijection of homotopy classes of maps into $TI$. Hence there is a unique homotopy class $b:J\to TI$ with $ba=T(i)$. Applying quotient invariants represents $R\Gamma_{Q\times L}(\eta_N)$ by $\Gamma_{Q\times L}(b)$.

Cited nodes: def-sfb-right-derived-functor, lem-weil-pbc-kinjective-hom-derived.
Source: literature/stacks-project/derived.tex, Tags 070I and 070Y; resolution unit and extension of a map to a K-injective target.

Old step 7. Under the normalized inflation adjunction, $b:J\to TI$ transposes to the chain map from the inflation of $J$ into $I$ obtained by composing with $TI\hookrightarrow I$. On invariant complexes its map is exactly $\Gamma_{Q\times L}(b):J^{Q\times L}\to I^{G\times L}$, using $I^{G\times L}=(TI)^{Q\times L}$. This is the derived inflation attached to the projection and the original inclusion $\operatorname{Inf}T(N)\hookrightarrow N$: its composite with the inflated resolution map agrees up to homotopy with $i$ composed with that inclusion, by $ba=T(i)$. Since $c_N$ is the identity on the target invariant complex, this gives $c_N\operatorname{inf}_N=R\Gamma_{Q\times L}(\eta_N)$. The Hom bijection in step 6 and the derived adjunction normalization show that this description is independent of $i,a,b$.

Cited nodes: def-sfb-condensed-action-module, lem-sfb-derived-composition-adjunction-normalization, lem-weil-pbc-kinjective-hom-derived.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent normalized inflation calculation on resolutions, using Stacks 070I and 09T5.

Old step 8. For a morphism of complexes, maps between K-injective resolutions representing it are unique up to homotopy, by the K-injective Hom bijection. Applying $T$, restriction and invariants preserves homotopies. The identities of fixed-section submodules in steps 2, 4 and 5 commute with every equivariant linear map. Thus $\beta,c,\eta$ and the displayed inflation equation are natural in module maps (and $\beta,c$ are natural on the unbounded derived category). In later steps, equality of natural derived maps may be checked on K-injectives: every object is isomorphic to one, and their derived Hom sets equal their homotopy Hom sets.

Cited nodes: lem-weil-pbc-kinjective-hom-derived.
Source: literature/stacks-project/derived.tex, Tag 070I, lemma-K-injective, (1) implies (3); homotopy-natural fixed-section identities.

Old step 9. For a continuous $h:L'\to L$, write $r_h$ for action restriction and use the analogous quotient restriction. There is an equality $T' r_h=r_hT$ of underlying invariant submodules with residual action. Full invariants have the natural inclusion $M^{G\times L}\to(r_hM)^{G\times L'}$, and likewise for $Q$; the $K$-invariant submodule itself is unchanged. To derive these maps on a K-injective source $I$, resolve $r_hI\to J$ in the new action category and apply these inclusions followed by the corresponding invariant map to $J$. The target $T'J$ and $J|_K$ are K-injective by step 3 for $L'$. All paths through $\beta$ or $c$ are therefore the same maps of invariant complexes: use $I^{G\times L}=(TI)^{Q\times L}$, then $T'(r_hI)\to T'J$. This proves the two naturality squares and, with $T(N)\to TI$, the inflation equation after $h$. Resolution-independence follows from the Hom bijection; no preservation of K-injectives by $r_h$ is asserted.

Cited nodes: def-sfb-right-derived-functor, lem-weil-pbc-kinjective-hom-derived.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent continuous-homomorphism naturality via invariant inclusions and Stacks 070I/070Y.

### lem-sfb-action-topos-coefficient-coherence — old steps 10–11

Old step 10. Use the action sites also for sheaves of sets: the same formulas as in the action-site presentation identify a $P$-set sheaf $X$ with the sheaf having restriction $x\mapsto a f^*x$ along $(f,a)$. Restricting to $(f,1)$ is the inverse; twisting by $(1,a)$ is invertible, so the covering-sieve criterion in that presentation identifies the two sheaf conditions. Thus the category $B_P$ of internal $P$-set sheaves is a small-site topos. Inflation along $P\to1$ or $G\times L\to Q\times L$ preserves finite limits, computed on underlying sheaves, and is left adjoint to kernel invariants by the fixed-section formulas of step 2 (with sets in place of modules). These are geometric morphisms; with the trivially acted-on ring $A$ their module direct images are $\Gamma_P$ and $T$. A ring map $A\to A'$ is a ringed-topos morphism on the identity underlying $B_P$, with exact module direct image scalar restriction $r_P$. For either projection $f:B_P\to B_R$, the two composites of the coefficient-change and projection morphisms agree, since the ring structural map is the same $A\to A'$. The ringed-topos composition theorem gives the canonical isomorphism
$$\theta_f:Rf_{*,A}D(r_P)\xrightarrow{\sim}D(r_R)Rf_{*,A'}.$$
Indeed composition identifies both sides with the direct image of that common composite. Its normalization says: for $A'$-K-injective $I'$ and a resolution $a:r_PI'\to J$ over $A$, the map $f_{*,A}(a)$ from $r_R f_{*,A'}I'$ to $f_{*,A}J$ is a quasi-isomorphism and represents $\theta_f^{-1}$. Thus no scalar restriction is assumed to preserve K-injectives.

Cited nodes: lem-sfb-internal-action-site-presentation, def-weil-pbc-ringed-topos-morphism, lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
Source: literature/stacks-project/sites-cohomology.tex, Tag 0D6E, lemma-derived-pushforward-composition; agent realization of invariants on action topoi and its coefficient-change composition square.

Old step 11. Let $\sigma:A\to A'$ and $v:N\to r_{G\times L}N'$ be an equivariant coefficient map. The required coefficient transformation for invariants is explicitly $R\Gamma_A(v)$ followed by $\theta_\Gamma$ of step 10; it derives the equality of invariants with scalar restriction. Use the analogous $\theta_T$ for $T$. On an $A'$-K-injective $I'$ choose $a:rI'\to J$ over $A$. The inverses of all these coefficient comparisons are represented by the invariant maps of $a$. The square for $\beta$ is the single map $(rI')^K\to J^K$, since $T_A(a)$ has that underlying map and $J|_K$ is K-injective. The square for $c$ is the single map $(rI')^{G\times L}\to J^{G\times L}$, written also as quotient invariants of $T_A(a)$. The ringed-topos composition cocycle states exactly that resolving after either of these two factorizations gives the same canonical comparison, including coefficient changes on identity topoi. Its unit normalization agrees with the normalization in step 5, so these are the specified $c,\theta$ rather than arbitrary isomorphisms. Naturality of the derived unit for $N'[0]\to I'$ gives the same square for $\eta$; composing the original invariant inclusions with $a$ gives it for inflation by step 7. Finally compose with $R\Gamma_A(v)$. This proves every coefficient square for arbitrary $v$, without a flatness assumption on $A'$ over $A$.

Cited nodes: def-sfb-right-derived-functor, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-pur-ringed-derived-composition-cocycle, lem-sfb-derived-composition-adjunction-normalization.
Source: literature/stacks-project/sites-cohomology.tex, Tag 0D6E, lemma-derived-pushforward-composition; normalized cocycle for coefficient changes on identity topoi and agent invariant-inclusion calculation.

### lem-sfb-normal-quotient-tower-resolution-coherence — old steps 12–14

Old step 12. Consider successive quotient projections $P_0\to P_1\to P_2$ with open normal kernels, retaining any factor $L$. Write $T_1,T_2$ for their invariant functors. A section is fixed by the composite kernel exactly when it is $\ker(P_0\to P_1)$-fixed and its residual section is $\ker(P_1\to P_2)$-fixed; quotient maps have the continuous set sections used in step 2. Consequently $T_{02}=T_2T_1$ and the invariant inclusion for the composite is the composite of the two inclusions. For a K-injective resolution $N\to I$, both $T_1I$ and $T_2T_1I$ are K-injective. The derived composition comparisons, in either parenthesization, are the identity on $I^{P_0}=(T_1I)^{P_1}=(T_2T_1I)^{P_2}$, by their adjunction-normalization theorem. Step 8 extends this equality to all derived objects.

Cited nodes: def-sfb-condensed-action-module, lem-sfb-derived-composition-adjunction-normalization.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent successive quotient and compositor identity calculation.

Old step 13. To check inflation itself under those projections, resolve $T_1N\to J$ in the $P_1$-action category and extend $T_1(N\to I)$ to $b:J\to T_1I$ using the Hom bijection. Resolve $T_2T_1N\to Z$ in the $P_2$-action category. Extend $T_2(T_1N\to J)$ to $d:Z\to T_2J$; this is possible because $T_2J$ is K-injective. The map $T_2(b)d:Z\to T_2T_1I$ extends $T_2T_1(N\to I)$. The direct inflation uses the unique homotopy class with exactly this extension property, so it agrees with $T_2(b)d$. Taking $P_2$-invariants identifies this map with the composite of the two inflations, since the invariant inclusions compose as in step 12. This proves the asserted transitivity, including its actual arrow.

Cited nodes: lem-weil-pbc-kinjective-hom-derived, def-sfb-condensed-action-module.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent two-resolution calculation of successive inflation; Stacks 070I.

Old step 14. If $K=1$, the quotient is $G$, $T$ is the identity functor, and $\Gamma_K$ is the identity on underlying modules. Its derived unit is the class of a quasi-isomorphism $N\to I$, hence is the identity under the exact-functor resolution identifications. The termwise fixed-section identities defining $\beta$ and $c$ are identities too, so their normalized derived comparisons are identities under the same identifications. The zero ring, zero module, $K=G$, and trivial $L$ require no changes: all constructions are submodules, exact adjunctions and resolutions, with no division by a group order.

Cited nodes: def-sfb-right-derived-functor, lem-sfb-derived-composition-adjunction-normalization.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, Paragraph (3), agent identity and degenerate-case check.

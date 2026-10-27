# Q32 repair: lem-trf-valuation-general-mod-injective

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-general-mod-injective.json`: statement unchanged; four-step assembly, 1979 characters, status split.
- `dag/nodes/sec-trace-formula/lem-trf-eventual-residue-tensor-comparison-injective.json`: statement, unsplit; no Mathlib match. Carries old steps 3--5 (2286 characters of argument).
- `dag/nodes/sec-trace-formula/lem-trf-noetherian-arrow-eventual-injective-flat-cokernel.json`: statement, unsplit; no Mathlib match. Carries old steps 2, 6, 7 (1785 characters of argument).
- `dag/nodes/sec-trace-formula/lem-trf-localized-arrow-injective-flat-cokernel-limit.json`: statement, unsplit; no Mathlib match. Carries old steps 8--9 (1223 characters of argument).

`citations.json` quotes the complete statement of each cited node at each assembly step. `searches.jsonl` and the search-output files retain the actual queries and answers. No new node contains proof steps or proof dependencies. This delivery creates three parallel tasks of comparable argument size; it does not move the theorem wholesale into one helper. The independent claims concern a source comparison diagram, eventual properties at finite stages, and passage from stage properties to the limit, respectively.

## Attachments

None. I searched `lean/WeilConjectures/` by the item's blueprint tag and the module/injectivity notions. The only full item declaration found is `Algebra.local_essentially_finite_presentation_mod_injective` in `lean/Sheaf/RingTheory/LocalEssentiallyFinitePresentationModInjective.lean:99`; its proof ends with `sorry`. Related source declarations prove the Noetherian local criterion, not 046Y in its non-Noetherian essentially finitely presented generality. No attachment is claimed, and no Lean file was written or compiled.

## WANTED

None. All sources needed for this split are present under `literature/stacks-project/`.

## What was wrong and what changed

The returned nine-step proof has 5846 characters and was explicitly returned for spreading its work into new unsplit tasks. The item keeps exactly its original statement. Old step 1 remains verbatim. Every other original argument has an assigned new node, and is preserved verbatim below for its future worker. The new assembly only checks the hypotheses of these three statements and composes their conclusions.

At startup this sandbox contained only `.brief2` through `.brief5`, with no node, report, citations or search log to recover. I therefore copied the current repository item and preserved that version as `original-item.json`. It has precisely the nine returned steps and their returned lengths; this is the returned argument used for the repair. The delivery tool overlays the split onto current server main and preserves maintainer-owned metadata and the existing Lean attachment. No git command was run in the shared repository.

The item is below the fixed `sec-trace-formula` / `sk-i-curve-zero` route. I read those records and the current main-20261015 unit and locality proof. The nearest blueprint ancestor remains `lem-trf-local-term-locality`, reached by the existing valuation-ring / Tag 0GSG branch; its via chain is retained and prefixed by this item for the new nodes. This is an algebraic re-split beneath that route, not a change to the chapter or unit. The three stages continue the exact Tag 046Y argument. No SGA source is used.

## Searches and existing material

Before creating nodes I searched the whole DAG by 046Y, finite fibre kernels, residue/fibre comparison, localization-system kernels, injectivity and flat cokernels, and inspected relevant statement candidates. Whole-blueprint searches (`tools/blueprint_refs.py search`) for `046Y`, `fibre comparison`, `flat cokernel`, `residue field`, `kernel stabilization`, `cokernel`, `localization system`, `injective flat` and `Noetherian fibre` found no equivalent statement. I checked the ring-theory Lean source by the same notions. Existing simultaneous approximation and generic localization-kernel stabilization remain available; neither states the residue-tensor construction. Existing flatness descent, tensor right exactness and the local injectivity criterion are ingredients, and do not state these new stage/limit assertions.

Each new node has two separately phrased LeanFinder searches, a Loogle query, a Mathlib grep and a LeanSearch request, run exclusively through the prescribed msearch command, with exact queries in the JSON and the original output retained. LeanSearch returned HTTP rate-limit errors and is recorded as unavailable. The other three kinds ran. The search results include `IsLocalRing.split_injective_iff_lTensor_residueField_injective` (Mathlib/RingTheory/LocalRing/Module.lean:334), whose hypotheses require finite modules over one ring and a free target; it does not apply to varying local base rings and finite modules over their auxiliary algebras. `IsLocalization.tensorProduct_tensorProduct` supplies only localization/base-change compatibility. `Module.DirectLimit.lift_injective` concerns a compatible family of already injective maps over a fixed base and does not identify stage cokernels or prove their flatness over a new base. `Module.Flat.ker_lTensor_eq` and `LinearMap.lTensor_injective_of_exact_of_flat` preserve exactness under a flat tensor factor; they do not descend flatness or prove the new varying-ring statements. I read these candidate source declarations, including the free-target assumptions and tensor-kernel formulas, before recording no match. The completions, quasi-finite algebras, and local-detection results among the remaining hits likewise have different hypotheses or conclusions. There is no one-line specialization giving a complete new node.

## Review by Q32

I read Algebra Tag 046Y (`lemma-mod-injective-general`) in full, including its construction of Psi, finite-kernel denominator argument, final fibre square and Noetherian criterion. For the new comparison node I also read the approximation statement and presentation-matrix proof of Tag 00QX. Its statement is restricted to diagrams with the actual localized base-change transitions and module base-change identifications, so tensoring with the fixed limit field really gives localization transitions. The source of Psi is the finite module over the essentially finite type k-algebra, and that ring is Noetherian; the finite kernel is taken over this ring, not over the original non-Noetherian base. Tensor/colimit commutation is applied to the constant diagram k with its compatible R_i-actions. I opened the existing tensor-over-quotient, localization-tensor, varying-ring-colimit, Noetherian permanence, finite-submodule and kernel-stabilization nodes and checked their statements support those precise ingredients.

For the new arrow-stage node I read the first and final paragraphs of 046Y, Tag 00R6 (`lemma-colimit-eventually-flat`), Tag 00ME (`lemma-mod-injective`) and the quotient-flatness paragraph of 00MO (`lemma-another-variant-local-criterion-flatness`). Its hypotheses explicitly provide both Noetherian rings, finite stage modules, semilinear maps, commuting arrows, algebraic ring and additive colimits, transition localizations and target base-change isomorphisms. These give every hypothesis of the existing eventual-flatness node, including preservation of the base colimit on sets. At I=0 the existing localized-base-change quotient-flatness statement propagates one flat target stage to its tail. Local R_j to R gives an embedding of fields k_j to k. Faithful field extension embeds the source fibre into its scalar extension; Psi injectivity then embeds it into the limit source fibre. In the commuting fibre square, injectivity of the limit u implies injectivity of the stage u. No injectivity of the target comparison is assumed. In 00ME the source is finite over S_j and the target is R_j-flat; the symbols M,N there are swapped relative to our item, as the old proof correctly does. I opened and read the statements of the field-extension faithful-flatness, universal-injectivity, eventual-flatness, localized-quotient-flatness and Noetherian-injectivity nodes used by these retained arguments.

For the new limit node I read the last sentence of 046Y alongside 00D7 (`lemma-zero-directed-limit`), 00DF (`lemma-tensor-product-exact`) and the initial quotient-flatness argument of 00MO. The new statement assumes actual additive colimits, not an identification of a finite stage with the limit. A representative of a kernel element moves to a later stage where its image is zero, and that later stage is still in the injectivity tail. The stated canonical base-change maps identify the tensor of u_i with the actual limit map u. Tensor right exactness therefore gives the explicit map [y] tensor s to s[nu_i(y)] on cokernels. Flatness uses the LIMIT localization S_i tensor_(R_i) R to S and the zero ideal, not merely the transition localizations. I checked the existing elementwise module-colimit, tensor-right-exact and localized-base-change quotient-flatness statements; they assert exactly these ingredients without additional locality or finiteness assumptions.

I then checked each assembly citation against its statement. Step 1 cites simultaneous arrow approximation: its hypotheses are exactly the item's local essentially finitely presented algebra, finite presentations of M,N and S-linear u, and its statement gives Noetherian stages, finite modules, the compatible arrow cocones, both kinds of localization, both module base-change maps and the elementwise colimit properties. Step 2 cites the new residue-comparison node: all its diagram hypotheses come from Step 1, including essential finite type of every S_i, and its conclusion gives precisely the scalar-extended source comparison injection required in Step 3. Step 3 cites the new arrow-stage node: Step 1 supplies its Noetherian diagram, Step 2 its eventual Psi injection, and the item's assumptions supply flat N and injective limit closed fibre. Its conclusion is the eventual injectivity and flat C_j needed in Step 4. Step 4 cites the new limit node: Step 1 clause (4) supplies the actual LIMIT localization and the base-change identifications carrying u_j to u, and Step 3 supplies the tail assumptions. Its conclusion is exactly the item's two conclusions. The full verbatim statements in citations.json let the delivery check every citation, and I checked the hypotheses myself rather than relying only on matching quotes.

I checked B--E of delivery-errors point by point. All new statements introduce their rings, modules, arrows, index set and canonical maps, define locality/localization inline and cite definition nodes for non-elementary notions. They contain statements only, no circular proof, no reference to a source proof as data, and no new custom definition. They have sources with Stacks tags and labels, genuine logged searches, concrete blueprint places, and single TeX escaping. The assembly has four non-elementary applications, each supported by the exact cited statement; none conceals an additional non-elementary argument. The old arguments are fully allocated below. The duplicate comparisons below come from opening each same-tag statement, not just comparing titles. New nodes have no proof dependencies and depend only on existing definitions, so no new proof cycle can close through the item. The original item statement and its Lean declaration remain untouched.

Small cases: with M=0 the comparison map has zero source and the residue argument applies immediately; the eventual-stage conclusion reduces to eventual target flatness, and the limit assertion gives the assumed flat target as cokernel. With u an identity the cokernels vanish and every formula sends zero to zero. A singleton diagram satisfies each statement whenever its hypotheses do; in the stage lemma it reduces to the genuine Noetherian criterion, and in the comparison lemma to the identity scalar extension. Over a field base, the maximal ideal is zero and the faithful-extension argument is the ordinary vector-space injection. The limit lemma permits a zero limit ring/module and noninjective cocone maps: elementwise eventual vanishing still proves injectivity of the limit arrow, so it does not accidentally assert any stage-to-limit injection. The comparison lemma requires only the source comparisons; taking a noninjective target comparison does not affect the fibre-square proof. Local rings here have proper maximal ideals, so the zero ring is not silently used as a residue-field source. I found no false statement or missing hypothesis requiring a dispute.

## No original argument removed

The exact returned text is reproduced below and assigned to independent tasks. The future workers can use these complete arguments and their original dependencies; none is hidden in the shortened assembly. This report preservation is not a proof field of any new node: those nodes are deliberately statement-only for parallel splitting.

### Old step 1 → parent assembly Step 1

Apply simultaneous Noetherian approximation to $R\to S$, $M,N,u$. Obtain one directed system $R_i\to S_i$, modules $M_i,N_i$ and maps $u_i$, with local transitions and cocones, algebraic ring/group colimits, and the transition and limit localization and module base-change identifications. In particular both $R_i$ and $S_i$ are Noetherian, $M_i,N_i$ are finite, and every comparison carries the stage map to the later map. The approximation lemma requires neither flatness nor fibre injectivity, so all its hypotheses come directly from the statement.

Dependencies: `lem-trf-local-module-arrow-noetherian-descent`.

Source: Tag 046Y, first proof paragraph; Tags 00QV/00QX simultaneous presentation construction.

### Old step 2 → lem-trf-noetherian-arrow-eventual-injective-flat-cokernel

Apply eventual flatness with $A_i=R_i$, $B_i=S_i$ and target module $N_i$. Step 1 supplies Noetherian local stages, finite modules, local commuting transitions, the transition localizations, module base-change isomorphisms and algebraic colimits (in particular preservation of the base colimit by forgetting to sets); the limit module $N$ is $R$-flat by hypothesis. Thus some $N_{i_1}$ is $R_{i_1}$-flat. For every $j\ge i_1$, apply localized-base-change quotient flatness with $I=0$, $(R,S,R',S')=(R_{i_1},S_{i_1},R_j,S_j)$ and module $N_{i_1}$. Its conclusion, together with $N_j=N_{i_1}\otimes_{S_{i_1}}S_j$, gives $R_j$-flatness of $N_j$. Restrict to this tail; a tail of a directed set is cofinal.

Dependencies: `lem-weil-pbc-colimit-eventually-flat`, `lem-weil-pbc-localized-base-change-quotient-flat`.

Source: Tag 046Y, first proof paragraph, invoking 00R6; Tag 00MO localized quotient flatness at I=0.

### Old step 3 → lem-trf-eventual-residue-tensor-comparison-injective

Put $k=R/\mathfrak m_R$, $k_i=R_i/\mathfrak m_i$, $D_i=S_i\otimes_{R_i}k$, $P_i=M_i\otimes_{R_i}k$ and $P=M\otimes_Rk$. Locality makes $k_i\to k$ a field embedding. We have $P_i=(M_i/\mathfrak m_iM_i)\otimes_{k_i}k$, $D_i=(S_i/\mathfrak m_iS_i)\otimes_{k_i}k$ and $P=M/\mathfrak m_RM$: the identifications send $x\otimes c$ to $[x]\otimes c$ and $x\otimes[r]$ to $[rx]$. Tensor-over-quotient gives these identifications. Since $S_i$ is a localization of a finite type $R_i$-algebra, localization commuting with tensor identifies $D_i$ with a localization of a finite type $k$-algebra (base change its finitely many polynomial generators and relations). A field is Noetherian, so finite-type Noetherianity followed by localization Noetherianity makes $D_i$ Noetherian. A finite generating family of $M_i$ gives the generating family $x_a\otimes1$ of $P_i$ over $D_i$. Consequently the kernel of the $D_i$-linear comparison $\Psi_i:P_i\to P$, $x\otimes c\mapsto\mu_i(x)\otimes c$, is finite by the Noetherian submodule theorem.

Dependencies: `lem-weil-pbc-tensor-over-quotient-ring`, `lem-weil-pbc-localization-tensor-over-base`, `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-localization-noetherian`, `lem-weil-pbc-noetherian-submodule-finite`.

Source: Tag 046Y, middle proof paragraph, Noetherian fibre ring and finite kernel.

### Old step 4 → lem-trf-eventual-residue-tensor-comparison-injective

For $i\le j$, write $C_{ji}=S_i\otimes_{R_i}R_j$ and $S_j=W_{ji}^{-1}C_{ji}$ as in Step 1. Tensor the ring localization and the corresponding localization $M_i\otimes_{R_i}R_j\to M_j$ over $R_j$ with $k$. The localization-tensor theorem identifies $D_j$ with the localization of $D_i=C_{ji}\otimes_{R_j}k$ at the image of $W_{ji}$, and identifies $P_j$ with that localization of $P_i$. These maps are the actual transitions, since their pure-tensor formulas are $s\otimes c\mapsto s_{ji}(s)\otimes c$ and $x\otimes c\mapsto m_{ji}(x)\otimes c$. Apply varying-ring tensor/colimit commutation to the system $R_i$, the modules $M_i$, and the constant additive diagram $k$ with its compatible $R_i$-actions. It gives $\varinjlim P_i=M\otimes_Rk=P$ with precisely the maps $\Psi_i$. All rings, modules and the small index set are taken in one common containing universe.

Dependencies: `lem-weil-pbc-localization-tensor-over-base`, `lem-weil-pbc-filtered-colimit-tensor-varying-rings`.

Source: Tag 046Y, middle proof paragraph, comparison maps and localization identification; Tag 00DD tensor/colimit commutation.

### Old step 5 → lem-trf-eventual-residue-tensor-comparison-injective

Fix any index $i_0$. Step 3 makes $\ker\Psi_{i_0}$ finite over $D_{i_0}$; Step 4 supplies the localization transitions and the additive colimit required by kernel stabilization. That lemma gives $i_2\ge i_0$ for which $\Psi_j$ is injective for every $j\ge i_2$. Its finite-kernel hypothesis concerns the source module $M_j$; no injectivity assertion about a target comparison for $N_j$ is needed.

Dependencies: `lem-trf-localization-system-kernel-stabilization`.

Source: Tag 046Y, middle proof paragraph, conclusion that all sufficiently late Psi have zero kernel.

### Old step 6 → lem-trf-noetherian-arrow-eventual-injective-flat-cokernel

For $j\ge i_2$ set $F_j=M_j/\mathfrak m_jM_j$. The map $k_j\to k=k_j\otimes_{k_j}k$ is faithfully flat by the field-extension base-change theorem with $D=k_j$. Universal injectivity for faithfully flat maps gives an injective map $F_j\to F_j\otimes_{k_j}k$, $x\mapsto x\otimes1$. Compose it with the injective $\Psi_j$ from Step 5. Thus the actual map $a_j:F_j\to M/\mathfrak m_RM$ is injective. In the fibre square, $b_j\overline{u_j}=\overline u\,a_j$, where $b_j:N_j/\mathfrak m_jN_j\to N/\mathfrak m_RN$ is the cocone map. If $\overline{u_j}(x)=0$, this equality and injectivity of $\overline u$ give $a_j(x)=0$, hence $x=0$. This proves injectivity of $\overline{u_j}$ without assuming $b_j$ injective.

Dependencies: `lem-weil-pbc-field-extension-base-change-faithfully-flat`, `lem-weil-pbc-faithfully-flat-universally-injective`.

Source: Tag 046Y, end of middle paragraph and start of final paragraph, faithful field extension and fibre square.

### Old step 7 → lem-trf-noetherian-arrow-eventual-injective-flat-cokernel

Apply the Noetherian local injectivity criterion at every $j\ge i_2$ on the tail chosen in Step 2. Its base is $R_j$, its Noetherian local auxiliary ring is $S_j$, its finite source is $M_j$ and its flat $R_j$-module target is $N_j$; $u_j$ is $R_j$-linear. Step 6 supplies injectivity modulo $\mathfrak m_j$. Hence $u_j$ is injective and $C_j=N_j/u_j(M_j)$ is flat over $R_j$.

Dependencies: `lem-weil-pbc-flat-mod-injective`.

Source: Tag 046Y, final paragraph, application of Tag 00ME.

### Old step 8 → lem-trf-localized-arrow-injective-flat-cokernel-limit

Let $x\in M$ with $u(x)=0$. Represent $x=\mu_j(x_j)$ at a stage $j$ in the eventual-injectivity tail. Compatibility gives $\nu_j(u_j(x_j))=0$ in $N$. Apply the elementwise colimit vanishing criterion to the underlying abelian groups (equivalently $\mathbf Z$-modules): there is $l\ge j$ with $n_{lj}(u_j(x_j))=0$. This equals $u_l(m_{lj}(x_j))$, so Step 7 implies $m_{lj}(x_j)=0$ and therefore $x=0$. Thus $u$ is injective. This argument uses a later stage for each kernel element, never an identification $M_j=M$.

Dependencies: `lem-weil-pbc-filtered-colimit-modules-elementwise`.

Source: Tag 046Y, final sentence, injectivity of the colimit map.

### Old step 9 → lem-trf-localized-arrow-injective-flat-cokernel-limit

Fix one $j$ in that tail. Apply tensor right exactness over $S_j$ to $M_j\xrightarrow{u_j}N_j\to C_j\to0$ and the $S_j$-algebra $S$. The compatible limit base-change identifications in Step 1 identify its first map with $u:M\to N$; hence they give a canonical isomorphism $C_j\otimes_{S_j}S\cong N/u(M)$, sending $[y]\otimes s$ to $s[\nu_j(y)]$. Apply localized-base-change quotient flatness at $I=0$ with $(R,S,R',S')=(R_j,S_j,R,S)$ and module $C_j$. Its localization hypothesis is the LIMIT localization $S_j\otimes_{R_j}R\to S$ in Step 1, and its flatness hypothesis is Step 7. Its conclusion is that $C_j\otimes_{S_j}S$ is flat over $R$. The displayed isomorphism proves the required flatness of $N/u(M)$.

Dependencies: `lem-weil-pbc-tensor-right-exact`, `lem-weil-pbc-localized-base-change-quotient-flat`.

Source: Tag 046Y, final sentence, flatness of the limit cokernel; Tag 00MO at I=0.

## Not duplicates

lem-trf-eventual-residue-tensor-comparison-injective vs lem-trf-local-module-arrow-noetherian-descent: constructs the simultaneous Noetherian approximation diagram but proves neither residue comparison stabilization nor arrow-stage descent nor the limit transfer theorem.

lem-trf-eventual-residue-tensor-comparison-injective vs lem-trf-localization-system-kernel-stabilization: assumes an already constructed module-localization diagram and a finite comparison kernel; it neither constructs the residue diagram nor proves the arrow-stage or flat-cokernel limit statements.

lem-trf-eventual-residue-tensor-comparison-injective vs lem-trf-valuation-general-mod-injective: asserts the original local essentially finitely presented closed-fibre criterion, without assuming a supplied approximation diagram or eventual stage/comparison properties.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-trf-local-module-arrow-noetherian-descent: constructs the simultaneous Noetherian approximation diagram but proves neither residue comparison stabilization nor arrow-stage descent nor the limit transfer theorem.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-trf-fibre-module-localization: identifies a single residue fibre with a module localization and controls an annihilator, not a directed arrow limit.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-trf-localization-system-kernel-stabilization: assumes an already constructed module-localization diagram and a finite comparison kernel; it neither constructs the residue diagram nor proves the arrow-stage or flat-cokernel limit statements.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-trf-valuation-general-mod-injective: asserts the original local essentially finitely presented closed-fibre criterion, without assuming a supplied approximation diagram or eventual stage/comparison properties.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-pc-tensor-tail-colimit-elementwise: gives representatives and eventual vanishing for scalar extensions of one fixed module, with no cokernel flatness assertion.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-colimit-flat-relation-descent-elementwise: descends a finite linear relation using flatness of a limit module, not eventual injectivity or flat stage/limit cokernels.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-localization-ideal-kernel-generators: describes generators of an ideal-multiplication kernel after localization, not arrow cokernels or eventual arrow injectivity.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-tensor-over-quotient-ring: identifies tensors over quotient rings for one module, not stage injectivity or limit cokernel flatness.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-directed-colimit-base-change-elementwise: gives representative/vanishing criteria for one fixed-base scalar-extended module, not flat cokernels of arrows.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-filtered-colimit-rings-zero: is an equality/zero detection theorem for ring colimits and contains no module-arrow assertion.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-module-pullback-ideal-quotient: describes pullback of an ideal quotient on schemes and its natural isomorphism, not varying-ring arrow diagrams.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-etale-quotient-base-change: preserves etaleness after quotienting a ring map; it has no directed system or module arrow.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-base-change-ideal-kernel-generators: controls ideal-multiplication kernels under base change with quotient flatness, not eventual stage injectivity or flat cokernel transfer.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-affine-conormal-sections-existence: identifies affine conormal sections for a closed immersion, not colimits of flat module-arrow cokernels.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-directed-tensor-cocones-colimit-n3: recognizes two tensor cocones as ring colimits, without an arrow injection or flat cokernel assertion.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-colimit-eventually-flat: finds a flat target stage only, without a source module, comparison injection, injective arrow or flat cokernel conclusion.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-flat-another-variant-local-criterion: uses a proper ideal and vanishing of a change-of-rings multiplication kernel to prove one localized module flat, not stage arrow/cokernel properties or limit injectivity.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-tensor-quotient-base-change: identifies a ring ideal quotient with a tensor product for a single base change, not arrow colimit injectivity/flatness.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-filtered-colimit-modules-criterion: recognizes a fixed-ring module cocone as a colimit from element criteria, without localized-base-change flatness or arrow conclusions.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-tor-ideal-kernel-naturality: identifies Tor with ideal-multiplication kernels and its naturality for one map, not eventual arrow properties or a limit cokernel.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-base-change-diagram-elementwise: proves element representation and vanishing for one scalar-extension diagram, without an arrow or flat cokernel.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-filtered-colimit-modules-elementwise: supplies representative and eventual equality/zero criteria over a fixed ring, not flat cokernels over varying base rings.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-filtered-colimit-localization-at-prime: constructs a ring colimit of prime localizations, not injective module-arrow limits or flat cokernels.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-tensor-right-exact: preserves a single right-exact sequence under tensor, without proving limit injectivity or localized-base-change flatness.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-completion-tensor-quotient-separated: detects zero using all evaluations of one completed tensor product, not a directed system of module arrows.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-filtered-colimit-localization-at-prime-data: constructs the contracted-prime localization functor and colimit, not a module-arrow property.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-flat-quotient-presentation-intersection: bounds an intersection involving an extended relation module and an ideal, not eventual arrow injectivity or limit transfer.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-localized-base-change-quotient-flat: transfers flatness of one quotient module under one localized base change; it does not supply arrow colimit injectivity, identify its cokernel, or descend stage fibre injectivity.

lem-trf-localized-arrow-injective-flat-cokernel-limit vs lem-weil-pbc-localized-base-change-ideal-kernel-span: bounds an ideal-multiplication kernel by transported kernel elements under one localized base change, not arrow or cokernel conclusions.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-trf-local-module-arrow-noetherian-descent: constructs the simultaneous Noetherian approximation diagram but proves neither residue comparison stabilization nor arrow-stage descent nor the limit transfer theorem.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-trf-localization-system-kernel-stabilization: assumes an already constructed module-localization diagram and a finite comparison kernel; it neither constructs the residue diagram nor proves the arrow-stage or flat-cokernel limit statements.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-trf-valuation-general-mod-injective: asserts the original local essentially finitely presented closed-fibre criterion, without assuming a supplied approximation diagram or eventual stage/comparison properties.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-colimit-flat-relation-descent-elementwise: descends a finite linear relation using flatness of a limit module, not eventual injectivity or flat stage/limit cokernels.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-noetherian-local-model-tower-fiber-localization: constructs one transition localization for the quotient diagram of a model tower, not properties of module arrows.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-localization-ideal-kernel-generators: describes generators of an ideal-multiplication kernel after localization, not arrow cokernels or eventual arrow injectivity.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-flat-point-noetherian-model: constructs a single flat model at a prime of a finitely presented algebra, not a tail of injective module arrows.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-ideal-kernel-element-descent: kills an individual ideal-tensor kernel element at a later stage, not injectivity and flatness of arrow cokernels.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit: constructs the module action and fibre equivalence for the quotient diagram of a tower, not injective arrows or flat cokernels.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-base-change-ideal-kernel-generators: controls ideal-multiplication kernels under base change with quotient flatness, not eventual stage injectivity or flat cokernel transfer.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-integer-approximation-flat-point-stage: finds one prime-localized flat module stage in an integer approximation, without a source arrow, source-fibre injectivity or cokernel.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-noetherian-local-model-tower-fiber-diagram: constructs a quotient-ring/module diagram and comparisons for a tower; it does not assert eventual injectivity or flat cokernels.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-noetherian-local-model-tower-fiber-colimit: constructs the compatible module action and identifies a tower quotient colimit, with no flatness or arrow conclusion.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-colimit-eventually-flat: finds a flat target stage only, without a source module, comparison injection, injective arrow or flat cokernel conclusion.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-flat-another-variant-local-criterion: uses a proper ideal and vanishing of a change-of-rings multiplication kernel to prove one localized module flat, not stage arrow/cokernel properties or limit injectivity.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit: defines a tower quotient ring cocone/equivalence, and is no theorem about arrows or cokernels.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-colimit-maximal-kernel-descent: kills the ideal-multiplication kernel from one stage in a flat limit diagram, not arrow-stage injectivity or cokernel flatness.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-tor-ideal-kernel-naturality: identifies Tor with ideal-multiplication kernels and its naturality for one map, not eventual arrow properties or a limit cokernel.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-colimit-flat-relation-descent: descends coefficients in one finite relation using flatness of the limit, not injectivity or flat cokernels of arrows.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-flat-quotient-presentation-intersection: bounds an intersection involving an extended relation module and an ideal, not eventual arrow injectivity or limit transfer.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-finite-tensor-kernel-generators: gives a finite set of generators for one ideal-tensor multiplication kernel, without any directed-system arrow claim.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-finite-ideal-kernel-descent: kills a finite set in one stage ideal-multiplication kernel after passing to a later stage, not stage-arrow injectivity or flat cokernels.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-localized-base-change-quotient-flat: transfers flatness of one quotient module under one localized base change; it does not supply arrow colimit injectivity, identify its cokernel, or descend stage fibre injectivity.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-localized-base-change-ideal-kernel-span: bounds an ideal-multiplication kernel by transported kernel elements under one localized base change, not arrow or cokernel conclusions.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs lem-weil-pbc-flat-mod-injective: is the Noetherian single-stage local criterion, not a descent to a common tail from a flat limit with eventually injective source comparisons.

lem-trf-noetherian-arrow-eventual-injective-flat-cokernel vs def-weil-pbc-noetherian-local-model-tower-fiber-system: defines the quotient ring and module diagrams of a tower, and does not prove eventual arrow-stage injectivity or flat cokernels.

Additional concept-search candidates were also opened: `lem-weil-pbc-fibre-ring-noetherian` gives Noetherianity of one ordinary fibre of a Noetherian ring, not its arbitrary extension to the limit field or a localization-colimit diagram; `lem-trf-valuation-closed-fibre-noetherian` is specific to valuation bases and has no comparison system; `lem-sfb-arrow-exact-colimits` is an abstract exact-colimit tool and contains no varying-base module flatness; `lem-pc-finite-relation-cokernel-colimit` descends a presentation matrix, not injectivity or flat cokernels; `lem-weil-pbc-noetherian-flat-closed-fiber-model` and `lem-weil-pbc-noetherian-local-model-tower-fiber-flat` concern flatness of a single module/closed fibre with no source comparison or arrow; `lem-sfb-finite-type-local-closed-fibre-approximation` constructs a local surjective approximation with unchanged fibre; `lem-trf-local-ui-flat-cokernel` concerns one universally exact sequence; and `lem-kun-tor-cokernel-flat` is a module-sheaf complex criterion. None states one of the three new diagram lemmas.

## Nodes no longer cited directly by the item

The fifteen original proof dependencies are all assigned in the preserved argument above. Simultaneous approximation is still cited directly. The other fourteen are ingredients for the new unsplit tasks, not deleted or claimed proved. The item's proof_deps is exactly the union of the four assembly uses. No Lean import was edited. The existing accepted tool_uses metadata is preserved; the assembly itself cites only nodes in the item's own unit. Any later split of a new node must declare its off-unit algebra tool uses in its own split_report as usual.

## Unfinished work and validation

The three new nodes remain unsplit intentionally, exactly as requested, so that separate workers can begin them. Their full retained arguments above and precise source places carry every piece of old work forward. There is no mathematical blocker or statement change. The first required server dry run rejected only the phrase “the item’s hypotheses” in assembly Step 3 under its self-containedness check. I replaced it by “by hypothesis”, leaving the explicit statements of R-flatness of N and injectivity of the closed-fibre map in that sentence. The run also recorded the existing route warning from lem-pur-relative-regular-equations-base-change to this item, explicitly as not refused. The corrected files are submitted to the required final server dry run and push.

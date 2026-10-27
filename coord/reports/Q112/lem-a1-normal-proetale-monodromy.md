## Worker report

Files written:
- dag/nodes/sec-purity-real-sheaves/lem-a1-normal-proetale-monodromy.json — repaired split; statement unchanged.
- dag/nodes/sec-purity-real-sheaves/lem-a1-normal-lattice-finite-cover-presentation.json — statement, unsplit; no Mathlib match.
- dag/nodes/sec-purity-real-sheaves/lem-a1-integral-fibre-monodromy-reconstruction.json — statement, unsplit; no Mathlib match.
- citations.json — verbatim statements supporting every citation of the assembly.

Attachments: none. The project tag search finds only Sheaf.Paper.NormalProEtaleMonodromy, whose theorem at line 107 ends in sorry. The upstream WeilConjectures tree has no declaration of the exact item. Its exists_lisseMonodromy is for regular bases and algebraically closed coefficients, and does not give this finite-extension normalization for all normal schemes. No Lean was written or compiled.

WANTED: none. Read the available Bhatt–Scholze PDF, pp. 59–61 and 70–71, and Stacks properties.tex, lemma-normal-geometrically-unibranch (0BQ3).

The sandbox initially contained only brief markers: there was no retained node, report or search log. The current live node supplies the returned ten-step proof. coord/repair-notes/lem-a1-normal-proetale-monodromy.json explicitly releases stage 1 with keep_plan. This repair does not change its statement, statement dependencies, imported fields or Lean. No statement dispute was found. The defect is the granularity of the proof. Nothing is left unresolved for this stage-1 split; proofs of the two new unsplit nodes are intentionally tasks for other workers.

## Repair of the return

The return has one re-split order. The new finite-cover presentation carries old steps 1–4, including all coefficient comparisons and the qcqs check, not just the existence of a cover. The reconstruction node carries old steps 6–8, including finite-level compatibility, inverse-limit torsion-freeness, both continuity arguments and recovery by the same normalized functor. Both are statement-only, status unsplit, with no proof steps or proof dependencies. Old step 5 remains the direct finite-etale descent citation in assembly step 3. Old steps 9–10 remain the explicit quasi-inverse, linearity, unit normalization and lifting in assembly step 5. Old step 2's fully faithful J remains assembly step 2. The complete old arguments are preserved below for the future workers; they have not been discarded or replaced by an assertion of the whole theorem. The new nodes have comparable work loads (old text about 2600 and 2558 characters) and neither states the item's equivalence.

## Not duplicates

lem-a1-normal-lattice-finite-cover-presentation vs lem-a1-normal-locally-constant-finite-section: the existing result concerns arbitrary set-valued local systems; the new task identifies completed/continuous coefficients, verifies qcqs, constructs the lattice-class sheaf and obtains an actual lattice pair over a finite etale cover.
lem-a1-normal-lattice-finite-cover-presentation vs lem-weil-pbc-lattice-sheaf-locally-constant: the existing result gives the continuous-coefficient coset sheaf over an arbitrary scheme, but no normal finite-cover section or completed coefficient/topological comparisons.
lem-a1-normal-lattice-finite-cover-presentation vs lem-a1-normal-completed-integral-model: the existing result asserts a global integral model, not the finite-cover lattice-class presentation; it depends on the present item, so citing it here would be circular.
lem-a1-normal-lattice-finite-cover-presentation vs lem-weil-pbc-lisse-lattice-finite-etale-descent: the existing result assumes a supplied finite-cover lattice and descends existence; the new node constructs the supplied cover and lattice and does not descend it.
lem-a1-normal-lattice-finite-cover-presentation vs det-lem-stratified-lattice-scheme: the existing blueprint statement is representability of lattice classes for pulled-back condensed coefficients, not the completed-coefficient normal finite-cover presentation.
lem-a1-integral-fibre-monodromy-reconstruction vs lem-per-normalized-tower-finite-free: that node proves freeness of an abstract normalized tower only; the new task constructs the equivariant fibre tower, joint continuity on its limit and rationalization, and its comparison with a fixed normalized realization.
lem-a1-integral-fibre-monodromy-reconstruction vs cor-galois-lisse-representations: clause (1) is used at finite level; clause (2) concerns the previously defined adic sheaf category, not the comparison with arbitrary integral pro-etale B-modules and a specified continuous-coefficient realization functor.
lem-a1-integral-fibre-monodromy-reconstruction vs new-e4-galois-adic-from-finite: that node constructs a complete adic/tensor correspondence in the adic-system category; it does not state recovery of a given completed pro-etale module under a chosen normalized rational realization.
lem-a1-integral-fibre-monodromy-reconstruction vs lem-sfb-normalized-monodromy-functor: the existing result constructs a functor and its lattice normalizations from representations; the new result starts with an integral pro-etale sheaf and reconstructs the lattice and its realization. It assumes the functor, not its essential surjectivity.

Whole DAG searches used lattice/monodromy titles, normal+lattice, integral+monodromy, inverse-limit freeness, and source places 7.4.7, 7.4.10 and 6.8.4(6). Opened the nodes above, all thirteen returned proof dependencies, the two generic Noetherian topology nodes and the coefficient definitions. Whole-blueprint searches used lattice normal, integral monodromy, monodromy, lattice finite, integral fibre, lisse inverse, lattice class and normalized fibre. The reported matches are broader packaging, different coefficient categories or generic ingredients; no blueprint statement equals either new node. The ancestor is lem-a1-affine-hc0; from.place ties each task to its first support/global-section sentence, through the retained lattice realization chain.

Mathlib searches are exactly the msearch.py queries in searches.jsonl. Both nodes have LeanSearch, Loogle, LeanFinder, grep and a second semantic phrasing. The finite-cover queries found etale-site definitions, ordinary Z-lattices, and condensed locally constant functors. The fibre queries found finite Galois categories and profinite group limits, and discrete condensed functors. None states either new task or supplies it by one-line specialization. Read Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean in full: it defines the Z_l coefficient sheaf and cohomology, not monodromy or lattice reconstruction. The grep's 'lisse' substring also matches relIsSeparated; these hits define metric/set-relation separation and are irrelevant. The new nodes are not Mathlib leaves.

## Review by Q112

I read BS Definition 6.8.3 and Proposition 6.8.4(1),(4),(6) on pp. 59–60, Lemma 6.8.13 on p. 61, and Lemmas 7.4.7 and 7.4.10 on pp. 70–71. For the normal finite-cover node the source is the lattice-class sheaf in the proof of 6.8.4(6), coupled with 7.4.10's finite connected geometric coverings and 7.3.9 as exposed by the existing finite-section node. Stacks 0BQ3 says exactly that a normal scheme is geometrically unibranch; its normal-ring meaning agrees with the hypotheses. The source's normality argument remains in the existing finite-section dependency, not silently assumed for nonnormal X. For the fibre reconstruction node the source is the integral case of 7.4.7 and 6.8.4(1),(4); the returned proof's extra freeness and continuity verifications are copied below as the future worker's argument. No SGA source is used.

Assembly step 1 cites the new presentation statement, whose conclusion literally supplies both coefficient isomorphisms, topological Noetherianity/quasi-separatedness, the finite etale surjection and its integral lattice pair. The old coefficient input lem-sfb-integral-lisse-reduction-equivalence gives A_cts = lim constant(A/pi^n), A_cts[1/l] = E_cts; lem-weil-l-adic-extension-integers-dvr gives l = unit*pi^e. These are sheaf limits and localization, never a discrete constant A substituted for completion. Noetherian closed-subset minimality and compactness of all subsets give the quasi-separatedness check used by J. They remain part of the first new task's handoff.

Assembly step 2 cites the existing etale-local-monodromy statement's first assertion: its functor is E-linear, fully faithful, has lisse values and simultaneous normalization on every invariant lattice, naturally for maps. Connectedness and the point are given; qc follows from Noetherianity and qs/topological Noetherianity from step 1. It does not use the etale-local clause as global surjectivity. This is a generic monodromy tool from another unit, declared in split_report.tool_uses with the reason.

Assembly step 3 cites the existing finite-etale lattice descent statement. Its required topologically Noetherian base comes from step 1, its cover is finite etale and surjective, and its lattice is supplied with the correct rational identification. The statement explicitly requires no descent datum and does not identify the descended lattice's pullback with M. Its continuous coefficient notation is identified by step 1. This off-unit lattice-descent tool is retained and declared.

Assembly step 4 cites the new reconstruction statement for exactly M_0 and the same fixed J. All separated, Noetherian and invertibility hypotheses are the item's, and the extra topological hypotheses were checked. Normality is not needed by this new task. Its conclusion gives a jointly continuous representation and J(V) = M_0[1/pi], so this is essential surjectivity of the chosen functor, not unrelated realizations. The normalized integral comparison, finite coefficient correspondence and adic-limit module statements were each opened: the former provides M = lim nu*F_n and quotient compatibility, the finite correspondence is compatible with coefficient extension and morphisms, and the module statement provides finite generation, quotient identities and the adic topology. The returned torsion calculation then justifies freeness rather than inferring it from finite generation alone.

Assembly step 5 is elementary assembly using the preceding fully faithful functor and its normalization. It defines the inverse on arrows by the displayed conjugation formula; full faithfulness proves functoriality, E-linearity, natural inverse maps and lifting of inverse isomorphisms. The sole new citation at this step, lem-per-lisse-completed-system-comparison, literally makes N_Lambda = lim nu*F_n integral lisse. Normalization and naturality are already provided in step 2 and localization comparison in step 1. I checked the statement of every cited node and wrote its verbatim supporting text in citations.json. The longest assembly step is below 2000 characters and the total below 3000.

Small cases: rank zero has the unique GL_0 coset, zero normalized tower and zero representation; constant rank-one sheaves give the standard lattice and usual finite quotients. The connected base forces a common rank without asserting a global basis. A ramified E/Q_l still has l = u*pi^e, e positive, so either localization gives E. The pi-torsion argument must use n>k: a pi-annihilated element of a free A/pi^n-module lies in pi^(n-1), which reduces to zero at every fixed lower k. This excludes all torsion by the DVR factorization. Joint continuity is checked on each finite discrete coordinate and on the open sets pi^(-k)Lambda exhausting V. Nonnormal nodal curves are excluded (BS Example 7.4.9); none of the new claims drops normality where the finite-cover argument needs it. A geometric point already excludes the empty scheme for this item and both new tasks. No unverified global lattice statement is used to prove its ancestor.

Correction made in this repair: the long item proof is now distributed into two independent statement-only nodes; coefficient, topology, inverse-limit freeness and joint continuity claims have explicit conclusions and complete retained handoff arguments. Neither new node has a proof hidden in its statement; their argument is recorded only in this report. No statement or definition was weakened, no cycle introduced intentionally, and no unrelated route added.

## Retained returned proof and work allocation

The paragraphs below are the complete returned arguments, preserved verbatim. They are handoff material for the new statement-only tasks, not extra proof steps in their node files.

### Old step 1 — finite-cover presentation

First compare the coefficient conventions, rather than treating a discrete constant $A$-sheaf as completed coefficients. By [lem-sfb-integral-lisse-reduction-equivalence], the continuous-function coefficient sheaf $A_X$ is canonically $\varprojlim_n(A/\varpi^n)_X=B_X$, and $A_X[1/\ell]=E_X$ in the continuous-function convention. Since $\ell$ and $\varpi$ are nonzero elements of the maximal ideal of the discrete valuation ring $A$, [lem-weil-l-adic-extension-integers-dvr](5) writes $\ell=u\varpi^e$ with $u$ a unit and $e>0$. Thus localization at either element gives the same sheaf, and the present $B_X[1/\varpi]$ agrees with that $E_X$. All subsequent coefficient changes use these canonical isomorphisms.

Cited statements: lem-sfb-integral-lisse-reduction-equivalence, lem-weil-l-adic-extension-integers-dvr.

### Old step 2 — finite-cover presentation

The scheme is quasi-compact by hypothesis. By [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal], its closed subsets satisfy the descending-chain condition. Consequently [lem-sfb-noetherian-space-compact-subsets] makes every subset of $|X|$ quasi-compact; in particular intersections of affine opens are quasi-compact, which verifies quasi-separatedness. Apply the first assertion of [lem-sfb-etale-local-monodromy-realization] to this connected qcqs, topologically Noetherian $X$ and the specified geometric point. It gives an $E$-linear fully faithful functor $J_X$ from the required continuous representations into lisse $E_X$-modules. Its integral normalization uses precisely the finite-level equivalence in the question. It remains to prove essential surjectivity; the etale-local realization clause of that node alone would not suffice.

Cited statements: lem-weil-pbc-noetherian-scheme-closed-subsets-minimal, lem-sfb-noetherian-space-compact-subsets, lem-sfb-etale-local-monodromy-realization.

### Old step 3 — finite-cover presentation

Fix a lisse $E_X$-module $L$. Apply [lem-weil-pbc-lattice-sheaf-locally-constant] using step 1's coefficient identifications. Its sheaf $\mathscr L_L$ parametrizes integral lisse lattices together with their specified rational identification with $L$. On a pro-etale trivialization $L=E^r$, this sheaf is the constant sheaf with set $\operatorname{GL}_r(E)/\operatorname{GL}_r(A)$. This set contains the identity coset, including for $r=0$. Thus $\mathscr L_L$ is locally constant and has sections on a pro-etale covering. No global basis of $L$ is chosen.

Cited statements: lem-weil-pbc-lattice-sheaf-locally-constant.

### Old step 4 — finite-cover presentation

Apply [lem-a1-normal-locally-constant-finite-section] to $F=\mathscr L_L$. Its normal-local-ring, connectedness, nonemptiness and Noetherian hypotheses are exactly assumptions on $X$; local constancy and local nonemptiness were proved in step 3. We obtain a finite etale surjection $p:Y\to X$ and a section of $\mathscr L_L(Y)$. By the definition of that sheaf's sections, this section is an isomorphism class with a representative $(M,\alpha)$, where $M$ is integral lisse on $Y$ and $\alpha:M[1/\varpi]\simeq p^{-1}L$.

Cited statements: lem-a1-normal-locally-constant-finite-section.

### Old step 5 — retained assembly

Use [lem-weil-pbc-lisse-lattice-finite-etale-descent] for this $p$ and $(M,\alpha)$. The space $|X|$ is Noetherian by step 2, $p$ is finite etale and surjective by step 4, and $L,M$ are locally finite free with the specified rational identification. That theorem supplies an integral lisse $B_X$-module $M_0$ and $M_0[1/\varpi]\simeq L$. It does not require the specified lattice $M$ to carry descent data, and we do not assert that $M_0$ pulls back to $M$.

Cited statements: lem-weil-pbc-lisse-lattice-finite-etale-descent.

### Old step 6 — integral fibre reconstruction

By [lem-per-lisse-completed-system-comparison], $M_0$ corresponds to a normalized tower $(F_n)$ of finite locally free $A/\varpi^n$-module sheaves on $X_{\mathrm{et}}$, with $M_0\simeq\varprojlim_n\nu_X^*F_n$. Apply [cor-galois-lisse-representations](1) to each finite ring $A/\varpi^n$ (finiteness is part of [def-weil-l-adic-coefficient-extension]). Let $\Lambda_n=(F_n)_{\bar x}$ with its finite discrete continuous $\Pi$-action. The finite-level equivalence is compatible with coefficient extension, so normalization gives $\Lambda_{n+1}/\varpi^n\Lambda_{n+1}\simeq\Lambda_n$, equivariantly. Each $\Lambda_n$ is finite free, since $F_n$ is finite locally free. By [lem-pod-adic-limit-finite-modules](1), $\Lambda=\varprojlim_n\Lambda_n$ is finitely generated, $\Lambda/\varpi^n\Lambda\simeq\Lambda_n$, and its inverse-limit topology is its adic topology. The coordinatewise $\Pi$-action is jointly continuous: each coordinate of $\Pi\times\Lambda\to\Lambda$ factors through the continuous action on the finite discrete $\Lambda_n$.

Cited statements: lem-per-lisse-completed-system-comparison, cor-galois-lisse-representations, def-weil-l-adic-coefficient-extension, lem-pod-adic-limit-finite-modules.

### Old step 7 — integral fibre reconstruction

The module $\Lambda$ is torsion-free. Indeed, if $\varpi\lambda=0$, its image in the free $A/\varpi^n$-module $\Lambda_n$ lies in $\varpi^{n-1}\Lambda_n$. For every fixed $k$, reducing from any $n>k$ makes that image zero in $\Lambda_k$; hence all coordinates of $\lambda$ vanish. Repeating this rules out $\varpi$-power torsion, and every nonzero element of $A$ is a unit times a power of $\varpi$ by [lem-weil-l-adic-extension-integers-dvr]. This node also says $A$ is a DVR. Apply [lem-sc-dvr-fg-torsionfree-free] to conclude that $\Lambda$ is finite free. Put $V=E\otimes_A\Lambda$. A basis of $\Lambda$ identifies $V$ with $E^r$ and $\Lambda$ with $A^r$; the sets $\varpi^{-k}\Lambda$ are open and exhaust $V$. On each such set the action is the rescaled continuous action on $\Lambda$, so the action $\Pi\times V\to V$ is jointly continuous. The submodule $\Lambda\subset V$ is therefore an invariant finite free lattice of the kind in the question.

Cited statements: lem-weil-l-adic-extension-integers-dvr, lem-sc-dvr-fg-torsionfree-free.

### Old step 8 — integral fibre reconstruction

The finite-level equivalences identify $F_n$ with the sheaf corresponding to $\Lambda/\varpi^n\Lambda$, with the quotient transition maps. Thus the normalization of [lem-sfb-etale-local-monodromy-realization] gives $J_X(V)\simeq (\varprojlim_n\nu_X^*F_n)[1/\ell]\simeq M_0[1/\varpi]\simeq L$. The middle isomorphism is the inverse of reduction in [lem-per-lisse-completed-system-comparison], and step 1 identifies the two localizations. This proves essential surjectivity for the same fully faithful $J_X$, rather than constructing a separate functor for each lattice.

Cited statements: cor-galois-lisse-representations, lem-sfb-etale-local-monodromy-realization, lem-per-lisse-completed-system-comparison.

### Old step 9 — retained assembly

Construct an inverse $\Phi_X$ explicitly: for each $L$ choose $V_L$ and $a_L:J_X(V_L)\xrightarrow{\sim}L$ as above, and define $\Phi_X(f)$ to be the unique map whose image under $J_X$ is $a_{L'}^{-1}fa_L$. Full faithfulness gives uniqueness, preserves identities and composition, and makes this functor $E$-linear. The $a_L$ give one natural inverse isomorphism; full faithfulness gives the other. Hence $\Phi_X$ is the required $E$-linear equivalence.

Cited statements: .

### Old step 10 — retained assembly

Finally let $(V,\Lambda)$ be any representation and stable lattice as in the question. The normalization of [lem-sfb-etale-local-monodromy-realization] is $J_X(V)\simeq N_\Lambda[1/\ell]$, naturally for lattice-preserving equivariant maps, and [lem-per-lisse-completed-system-comparison] ensures $N_\Lambda$ is integral lisse. Step 1 replaces $1/\ell$ by $1/\varpi$. Applying the inverse equivalence and its unit gives $\Phi_X(N_\Lambda[1/\varpi])\simeq V$ with exactly that naturality. If $\Phi_X(L)\simeq V$, full faithfulness lifts this isomorphism and its inverse to mutually inverse sheaf morphisms $N_\Lambda[1/\varpi]\simeq L$. All constructions include the zero module and the unique rank-zero lattice.

Cited statements: lem-sfb-etale-local-monodromy-realization, lem-per-lisse-completed-system-comparison.

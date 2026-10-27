## Worker report

Repair of the released stage-1 order dated 2026-10-22. The assigned sandbox initially contained only dispatcher marker files, so the current live item was copied as the returned proof. The live repair note explicitly reopens the previously reviewed split. No retained sandbox split or searches were discarded. The old item, its searches, statement, statement dependencies, Lean metadata, import fields and maintainer records were preserved. Only stage-1 proof/report fields change.

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibrewise-flatness-criterion.json`: unchanged statement; three assembly steps, 1622 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibre-flatness-compatible-stalk-data.json`: statement-only, status unsplit, no Mathlib match for the complete compatible construction. Carries old steps 1-4.
- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-closed-fibre-approximation-rigidity.json`: statement-only, status unsplit, no Mathlib match. Carries the scalar relabelling, the 00R7 application with M=C, and the faithful-flatness kernel argument in old steps 5-7.
- `citations.json`: a verbatim quote for every assembly citation. `searches.jsonl` contains the actual wrapper logs; the prior item's historical records remain untouched.

Attachments: none. The item tag has no declaration in `lean/WeilConjectures`; its live `Sheaf.AlgebraicGeometry.FibrewiseFlatnessCriterion` theorem ends in `sorry`. The project algebraic declaration `Module.flat_of_flat_closedFiber` assumes both local algebras essentially finitely presented and does not state the approximation-rigidity result. Fibre-map and smoothness declarations do not state either new node. No Lean files were written and no compiler or Lake was run.

WANTED: none.

The item statement agrees with Stacks 039C (1) implies (2) for the structure sheaf, which is free of rank one and nonzero at an actual point. No statement correction is needed. The return concerns granularity: all eight old arguments now have explicit ownership, and the two new lemmas are independent tasks of similar proof workload. The first builds geometry-to-algebra data without assuming any flatness; the second starts from arbitrary four local rings and a supplied approximation, with no scheme or finite-type construction. Neither states the item or one of its flatness conclusions alone.

Nothing remains unfinished in the authorized one-level split. The proofs of the two new statement-only nodes belong to their future workers. All writes are in this sandbox. No agents, repository git commands, SGA sources or local checker executions were used.

## Review by Q61

I read the item and all eight live proof steps, the released repair note, Stacks `more-morphisms.tex` Tag 039C (`theorem-criterion-flatness-fibre`, lines 4588-4624), and the current blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`. The inherited blueprint ancestry has `from.node = null`, as the prescribed ancestor tool reports; this is retained, with explicit original-step places and the inherited via chain on each new node. The latest blueprint now phrases its direct-image route through compactification; this delivery repairs the existing local prerequisite and does not claim a new blueprint identity or silently replace its inherited route.

For the compatible-stalk-data node I read Schemes 0HA1 (`lemma-local-ring-fibre`, lines 3544-3565), Algebra 00QM (`definition-essentially-finite-p-t`, lines 12835-12846), and the actual statements of the affine-open stalk, stalk-map composition, finite-presentation base-change and localization-transitivity nodes. The new statement exposes the affine charts and maps rather than saying only that finiteness transports. It includes the actual induced fibre stalk map, not just abstract ring isomorphisms. The chart map U to S need not land in W: only U and W mapping into the common V is asserted. Because p's finite-presentation chart first fixes V, q's definition supplies E over that same V. The tensor/fraction calculation shows R tensor_A D is D localized at A minus a; that set avoids c, so transitivity gives P to C. The same argument with E gives Q to B, with finite generators carried to pure tensors. Source flatness is not assumed by this lemma. This is larger than the affine-only existing stalk-localization lemma and the one-map fibre quotient theorem: those do not give the joint chart data and commuting induced fibre map asserted here.

For approximation rigidity I read Algebra 05UV (`lemma-criterion-flatness-fibre-fp-over-ft`, lines 33119-33178), 00R7 (`lemma-criterion-flatness-fibre`, lines 32992-33014), 00HR (`lemma-local-flat-ff`, lines 9183-9191), and 05CK (`lemma-faithfully-flat-universally-injective`, lines 20254-20273). I also opened the statements of the existing 00R7 criterion, local-flat-faithfully-flat lemma, and universal tensor-injectivity lemma. The tower R to T to B to C supplies every scalar action. The closed-fibre isomorphism induced by u, not an arbitrary residue-ring isomorphism, makes C/mC flat over T/mT. In applying 00R7 to R to T to C, both T and C are essentially finitely presented by explicit assumptions; M=C is finitely presented over C (free of rank one) and nonzero. Thus T is R-flat and C is T-flat. T to C is local because its two factors are local. By 00HR it is faithfully flat, and 05CK with N=T and T tensor_T C identified with C makes T to C injective. Its factorization through u forces ker u=0; together with the assumed surjectivity this is an R-algebra isomorphism. This is a real argument involving the fibre criterion, not merely the elementary fact that a surjection through an injective map is an isomorphism. It does not construct u, duplicate the approximation lemma, or assume B essentially finitely presented.

Assembly step 1 cites compatible-stalk-data for precisely the tower, the two essential finiteness properties, and the formula for the fibre map; its entire statement is quoted in citations.json. `def-weil-flat-morphism` identifies both flatness hypotheses with the indicated scalar actions. No nonzero-stalk or finite-presentation fact is silently obtained from a definition that lacks it: those are conclusions of the new construction node.

Assembly step 2 cites the existing `lem-sfb-finite-type-local-closed-fibre-approximation`, whose statement explicitly supplies local R to T to B, nonzero T, essential finite presentation, surjectivity, and the exact quotient isomorphism. Its hypotheses (local R to B and essential finite type of B) are in step 1. I read that statement in full; it is not being used for flatness. Composing the new local maps with the already given B to C only forms the tower and is elementary.

Assembly step 3 cites rigidity for its exact conclusion: T R-flat, C T-flat and u an R-algebra isomorphism. Its four-ring hypotheses have been checked separately above. The remaining scalar transfer is written out: u identifies the coefficient rings, and the original B-action on C agrees with the transported action because the T-action is through u. Identifying tensor-injectivity tests proves the two flatness statements, using `def-weil-pbc-flat-ring-map`; `def-weil-flat-morphism` translates them back to q at y and f at x. This step introduces no unproved descent or additional flatness theorem.

I checked B1-B10: both new nodes introduce every object, use single-escaped TeX, cite definition nodes for stalks, fibres, finiteness, localization, tensor and flatness, and have empty proof/proof_deps and null proof_origin. The sources name tags and exact tex labels, and contain no proof sketch in the new statement. Actual searches (LeanFinder in two phrasings, Loogle, LeanSearch and grep) were inspected. FiniteType.stalkMap is already in Mathlib (FiniteType.lean:102-108), but supplies only one component of the geometric construction. The affine stalk-map hits do not give its fibre quotient compatibility or essential finite-presentation chart; faithfully flat injectivity hits assume flatness and do not prove rigidity from the closed-fibre criterion. Thus neither complete new node is a Mathlib leaf. I read the inherited historical item searches rather than claiming new runs for them.

I checked C1-C8, D1-D5 and E1-E7: every non-elementary assembly input is a cited node, all cited statements are opened and quoted, and no new node depends on this item. The new statement dependencies are definition nodes only, so the extraction creates no proof cycle. No new off-unit proof citation is introduced in the item. The two tasks are neither clause restatements nor the whole item relabelled. The original source's finite-type/finite-presentation distinction is preserved, including over a non-Noetherian base; no finite-presentation hypothesis on B and no global flatness hypothesis appear.

Small cases: an empty X has no x, so the pointed statement is vacuous; identity maps give the usual stalk and quotient maps; nonclosed x and s are allowed and fibre projections still have the unique points used. With R a field, the quotient isomorphism in rigidity is u itself, so its isomorphism conclusion is immediate; with u the identity, the argument reduces to 00R7. With R=T=B=C any nonzero local ring, all conclusions hold, including nonreduced and non-Noetherian choices. For a deliberately noninjective u such as k[epsilon]/epsilon^2 to k, the prescribed closed-fibre isomorphism over R=k fails, so there is no false kernel conclusion. A zero C is explicitly excluded (and cannot be an actual scheme-point stalk), avoiding the vacuous flat module counterexample. Zero-generator affine presentations and finite-type maps not finitely presented over non-Noetherian bases are included. No openness assertion is added.

The repair changes exactly the return's requested granularity: two new unsplit nodes, each with real logged searches and self-contained statements, retain all old arguments; the assembly is below 3000 characters and has no step over 2000 characters. No old argument is deleted or blurred. The original eight steps are reproduced below to make their assignment reviewable. No other fault required correction.

## Source error

The inherited report correctly notes two proof-text typos in 05UV: its first proof sentence says essentially finite presentation where the hypothesis and construction need only essentially finite type, and a later nested-ideal sentence repeats J' where J'' is intended. Neither affects the statements here. Rigidity uses the initial 00R7 application plus faithful flatness for M=C; it does not use the later ideal-stabilization paragraph. No statement dispute is introduced.

## Not duplicates

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-sfb-fibrewise-flatness-criterion: the item assumes base and fibre flatness and concludes flatness; the new node assumes no flatness and constructs compatible affine models and quotient maps.

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-trf-lci-pointwise-criterion: the existing node concerns Pointwise local-ring criteria for local complete intersections; it does not construct simultaneous base-localized affine models and compatible induced fibre stalk maps for an arbitrary three-scheme diagram.

lem-sfb-fibre-flatness-compatible-stalk-data vs def-weil-pbc-essentially-smooth-ring-map: the existing node concerns Essentially smooth ring maps; it does not construct simultaneous base-localized affine models and compatible induced fibre stalk maps for an arbitrary three-scheme diagram.

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-weil-pbc-essentially-smooth-small-local-model: the existing node concerns Small local model of an essentially smooth algebra; it does not construct simultaneous base-localized affine models and compatible induced fibre stalk maps for an arbitrary three-scheme diagram.

lem-sfb-fibre-flatness-compatible-stalk-data vs def-weil-pbc-essentially-finite-type-algebra: the existing node concerns Essentially of finite type ring maps; it does not construct simultaneous base-localized affine models and compatible induced fibre stalk maps for an arbitrary three-scheme diagram.

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-sbc-scheme-fibre-stalk-quotient: the existing statement treats one morphism and one quotient projection, without a tower, finiteness charts or compatibility with an induced fibre morphism.

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-sbc-composite-fibre-local-models: the existing statement concerns Noetherian local rings on nested fibres of two locally finite-type maps; it gives neither the original stalk R to B to C nor its essential finite-presentation chart.

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-trf-flat-association-stalk-dictionary: the existing statement assumes a flat morphism with locally Noetherian base and gives associated-point formulas; it does not give general finite-presentation charts or a fibre morphism of a three-scheme diagram.

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-trf-finite-presentation-stalk-fibre-data: the existing statement supplies a single map with a finitely presented module, an unspecified finitely presented stalk algebra and module quotient comparison; it does not supply the joint A,D,E charts, P,Q localization maps, or induced fibre morphism formula.

lem-sfb-fibre-flatness-compatible-stalk-data vs lem-sbc-finite-presentation-stalk-localization-model: the existing affine-only statement supplies one localization model; the new construction is for arbitrary schemes and includes the common-base chart, finite-type target and actual fibre map.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-trf-valuation-separable-closure-extension: the existing node concerns Finite-height faithfully flat valuation extension to a separable closure; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-trf-diagonal-taylor-faithful-flatness: the existing node concerns Faithfully flat Taylor realization at the residue-field diagonal point; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-trf-flat-local-component-dimension-difference: the existing node concerns Dimension difference on minimal components of a flat local map; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-trf-flat-localized-field-descent: the existing node concerns A field localization upstairs identifies the base localization with its residue field; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-pc-local-flat-faithful-flat-reflects-surjective: the existing node concerns Faithfully flat local stalk maps reflect surjectivity; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-weil-pbc-finite-projective-descends-flat-local: the existing node concerns Finite projective modules descend along flat local homomorphisms; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-weil-pbc-flat-local-hom-faithfully-flat: the existing node concerns A flat local homomorphism of local rings is surjective on spectra; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-ring-bridge: the existing node concerns Algebraic ring bridge for polynomial chart stalk flatness; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-sbc-polynomial-chart-stalk-flat-comparison: the existing node concerns Flatness comparison of a chart stalk and its closed fibre; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-sbc-polynomial-chart-stalk-flat-comparison-reverse: the existing node concerns Reverse flatness comparison for polynomial chart stalks; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-sbc-cohen-macaulay-flat-quasi-finite-chart: the existing node concerns Flat quasi-finite chart near a Cohen-Macaulay fibre point; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood: the existing node concerns Constant local fibre dimension near one Cohen-Macaulay fibre stalk; it has no general four-local-ring approximation with a closed-fibre isomorphism and no deduction that the supplied surjection is an isomorphism from the R-flat and closed-fibre-flat hypotheses.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-weil-pbc-faithfully-flat-universally-injective: the existing node assumes faithful flatness; the new lemma must establish flatness from the R-flat and closed-fibre-flat hypotheses before using injectivity.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-weil-pbc-criterion-flatness-fibre: 00R7 gives flatness for R to T to C and a finite module, without the extra surjection T to B or the claim that it is an isomorphism; the new lemma also handles the quotient-ring scalar identification and kernel argument.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-sfb-finite-type-local-closed-fibre-approximation: the existing node constructs a surjective approximation with identical closed fibre from essential finite type alone, assumes no C, and asserts no flatness or isomorphism; the new node takes that approximation as input and proves its rigidity using a flat test algebra.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-sfb-finite-type-local-closed-fibre-approximation: the existing node constructs a surjective approximation with identical closed fibre from essential finite type alone, assumes no C, and asserts no flatness or isomorphism; the new node takes that approximation as input and proves its rigidity using a flat test algebra.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-weil-pbc-criterion-flatness-fibre: 00R7 gives flatness for R to T to C and a finite module, without the extra surjection T to B or the claim that it is an isomorphism; the new lemma also handles the quotient-ring scalar identification and kernel argument.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-weil-pbc-faithfully-flat-universally-injective: the existing node assumes faithful flatness; the new lemma must establish flatness from the R-flat and closed-fibre-flat hypotheses before using injectivity.

lem-sfb-flat-closed-fibre-approximation-rigidity vs def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit: the existing node defines a colimit comparison for the middle closed-fibre functor of an already supplied directed model tower; it neither supplies the four-ring approximation hypotheses nor proves its surjection an isomorphism.

lem-sfb-flat-closed-fibre-approximation-rigidity vs def-weil-pbc-noetherian-local-model-tower-fiber-system: the existing node defines quotient diagrams and semilinear tensor maps for a supplied model tower; rigidity concerns one fixed four-ring tower and deduces flatness and an isomorphism, without directed systems.

lem-sfb-flat-closed-fibre-approximation-rigidity vs def-weil-pbc-noetherian-local-model-tower: the existing node defines directed Noetherian models, localizations and module comparisons without flatness; the new node assumes a supplied single approximation and flatness conditions and concludes its rigidity.

lem-sfb-flat-closed-fibre-approximation-rigidity vs lem-limit-module-colimit-part: the existing node asserts existence of a tail module diagram and its colimit under module descent data; the new node concerns no module colimit and proves a supplied local-ring surjection is an isomorphism.

## Preservation of the returned proof

Old step 1 → lem-sfb-fibre-flatness-compatible-stalk-data.

Put $R=\mathcal O_{S,s}$, $B=\mathcal O_{Y,y}$, and $C=\mathcal O_{X,x}$. These are nonzero local rings. The stalk maps form local homomorphisms $R\to B\to C$, whose composite is the stalk map of $p$, since $qf=p$. The definition of flatness at a point translates the hypothesis on $p$ into flatness of $C$ as an $R$-module.

Old step 2 → lem-sfb-fibre-flatness-compatible-stalk-data.

The fibre-stalk quotient theorem, applied to $p$ and $q$, identifies the local rings of $X_s$ and $Y_s$ at the corresponding points with $C/\mathfrak m_RC$ and $B/\mathfrak m_RB$. These are identifications of the actual projection stalk maps: the class of $c$, respectively $b$, maps to its projection germ. By the definition of the induced morphism of fibre products [def-pc-fibre-product] (here $f_s=f\times_S\mathrm{id}_{\operatorname{Spec}\kappa(s)}$), the projections satisfy $f\circ\iota_X=\iota_Y\circ f_s$; since $\iota_Y$ maps the point of $Y_s$ over $y$ to $y$ and that point is unique, $f_s$ sends the point $x$ of $X_s$ to the point of $Y_s$ over $y$. Taking stalk maps gives $\iota_X^\sharp f^\sharp=f_s^\sharp\iota_Y^\sharp$, so the fibre stalk map sends $[b]$ to $[f^\sharp(b)]$. Thus the hypothesis on $f_s$ says precisely that $C/\mathfrak m_RC$ is flat over $B/\mathfrak m_RB$, with its quotient action.

Old step 3 → lem-sfb-fibre-flatness-compatible-stalk-data.

Choose the affine finite-presentation chart for $p$ at $x$: $U=\operatorname{Spec}D\subset X$ and $V=\operatorname{Spec}A\subset S$, with $D$ finitely presented over $A$. Write $\mathfrak a\subset A$ and $\mathfrak c\subset D$ for $s$ and $x$. The affine-open stalk theorem identifies $R=A_{\mathfrak a}$ and $C=D_{\mathfrak c}$ through germs. Its germ formulas, together with the stalk-map germ formula, identify the structural map with the extension of $A\to D$. The algebra $P=R\otimes_A D$ is finitely presented over $R$ by base change. It is $D$ localized at the image of $A\setminus\mathfrak a$: the mutually inverse maps are $r\otimes d\mapsto rd$ and $d/a\mapsto(1/a)\otimes d$, whose relations are exactly the tensor and fraction relations. Since that multiplicative set lies in $D\setminus\mathfrak c$, localization transitivity makes $C$ a localization of $P$. Thus $C$ is essentially of finite presentation over $R$.

Old step 4 → lem-sfb-fibre-flatness-compatible-stalk-data.

On the same affine base $V=\operatorname{Spec}A$, take a finite-type affine chart $\operatorname{Spec}E\subset q^{-1}(V)$ containing $y$, available by local finite type. Write $\mathfrak b$ for its point $y$. Then $B=E_{\mathfrak b}$, compatibly with $R=A_{\mathfrak a}\to B$, by the affine-open stalk and germ formulas. If $e_1,\ldots,e_n$ generate $E$ over $A$, their images generate $R\otimes_A E$ over $R$: rewrite each pure tensor $r\otimes e$ by expressing $e$ as a polynomial in the $e_i$. As in step 3, $R\otimes_A E$ is the localization of $E$ at the image of $A\setminus\mathfrak a$, and localization transitivity identifies $B$ as a further localization. Hence $B$ is essentially of finite type over $R$. No finite presentation of $B$ has been assumed.

Old step 5 → assembly step 2 (existing approximation construction) and lem-sfb-flat-closed-fibre-approximation-rigidity (quotient scalar action).

Apply the closed-fibre approximation to $R\to B$. It supplies a local ring $T$, a factorization by local maps $R\to T\xrightarrow{u}B$, with $T$ essentially of finite presentation over $R$, $u$ surjective, and $\bar u:T/\mathfrak m_RT\xrightarrow{\sim}B/\mathfrak m_RB$. Compose with $B\to C$. The resulting map $T\to C$ is local since each factor sends the maximal ideal into the next. Its reduction acts on $C/\mathfrak m_RC$ through $\bar u$, so step 2 gives flatness of this quotient as a $T/\mathfrak m_RT$-module: the tensor functors for the two isomorphic coefficient rings are identified by relabelling scalars.

Old step 6 → lem-sfb-flat-closed-fibre-approximation-rigidity.

Apply the existing algebraic fibre criterion to the local tower $R\to T\to C$ and the $C$-module $M=C$. Both $T$ and $C$ are essentially of finite presentation over $R$ by steps 5 and 3. The module $C$ is finitely presented over itself (free on $1$, with no relations) and is nonzero since it is the local ring at a point. Its $R$-flatness is step 1, and its closed-fibre flatness over $T/\mathfrak m_RT$ is step 5. The criterion gives that $T$ is flat over $R$ and $C$ is flat over $T$.

Old step 7 → lem-sfb-flat-closed-fibre-approximation-rigidity.

The map $T\to C$ is a flat local map of local rings, so it is faithfully flat. Apply universal injectivity with the module $N=T$. Under $T\otimes_T C\cong C$, $t\otimes c\mapsto tc$ with inverse $c\mapsto1\otimes c$, its injective map $t\mapsto t\otimes1$ becomes the map $T\to C$. Hence $T\to C$ is injective. If $u(t)=0$ in $B$, its image in $C$ is zero, and this injectivity implies $t=0$. Thus $u:T\to B$ is injective as well as surjective, and is an $R$-algebra isomorphism.

Old step 8 → assembly step 3.

Transfer the two flatness conclusions of step 6 along the $R$-algebra isomorphism $u:T\xrightarrow{\sim}B$. The resulting scalar action on $C$ is its original $B$-action because the map $T\to C$ was defined to factor through $u$. This transfer is just identification of the tensor-injectivity tests for isomorphic coefficient rings. We obtain $B$ flat over $R$ and $C$ flat over $B$, which by the definition of pointwise flatness say respectively that $q$ is flat at $y$ and $f$ is flat at $x$.

## Retained earlier report and searches

The earlier delivered report is retained here as history, including its citations and logged-search descriptions; its original delivery and stage-2 validation claims belong to that earlier delivery. Current validation is recorded separately below.

## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibrewise-flatness-criterion.json`: item, statement unchanged, split into eight steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-local-closed-fibre-approximation.json`: new statement, unsplit; no Mathlib match after LeanFinder in two phrasings, Loogle, LeanSearch and source grep.
- `citations.json`: one verbatim statement quote for each of the 23 step citations.

Attachments: none. Searched `lean/WeilConjectures/` for the item tag, fibrewise/fiberwise flatness, and flat/fibre criteria; the existing `Module.flat_of_flat_closedFiber` is the algebraic criterion with an essentially finitely presented intermediate ring, not the requested scheme statement with only a finite-type target. Its DAG node is reused. The polynomial-chart and Noetherian criteria do not state this item either.

WANTED: none.

The imported item has the correct hypotheses and conclusions for the structure-sheaf specialization of Stacks 039C (1) to (2), so I did not change its statement. Its proof and dependencies were empty. The essential issue is that local finite type of Y/S does not give an essentially finitely presented target stalk over a non-Noetherian base. Step 5 introduces a genuine approximation, and steps 6–7 prove it is already the target stalk using the structure-sheaf hypothesis. This avoids assuming the missing finite presentation. The approximation lemma asserts no flatness and no conclusion of the item; it is only the preliminary construction from 05UV. It is deliberately left statement-only.

Nothing required for this one-level split remains unfinished. The new node's own proof belongs to a later stage-1 item. No Lean source was written, and no compiler, Lake, local checker, git command in the shared repository, or subagent was used. The only writes are in the assigned sandbox; delivery uses the authorized delivery tool.

## Source error

The local source of Tag 05UV (`algebra.tex`, `lemma-criterion-flatness-fibre-fp-over-ft`, beginning at line 33119) starts its proof “As S is essentially of finite presentation over R”, although its hypothesis is only essentially of finite type. The construction immediately following it requires only finite type: write the local algebra as a localization of a finite-type algebra, then as a quotient of a localized polynomial ring. I use this correct reading. The source also has the repeated J' in its line introducing nested ideals; that unused stabilization paragraph is unnecessary here. These are proof-text errors, not changes to the item or its source theorem. In the structure-sheaf case, flatness of the local algebra C over the approximation T makes T→C faithfully flat and injective, immediately forcing the surjective T→B to be an isomorphism.

## Not duplicates

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-sfb-relative-flat-locus-base-change: the latter mentions Tag 05UV in the proof of an openness/base-change theorem for the flat locus of a scheme morphism. It does not state an algebraic surjective finite-presentation approximation with an unchanged closed fibre.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-criterion-flatness-fibre: the existing 00R7 node assumes both intermediate and final local rings essentially finitely presented and concludes flatness. The new lemma assumes only essential finite type of one local algebra and constructs an intermediate essentially finitely presented local algebra with the same closed fibre; it assumes and concludes no flatness.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-trf-valuation-finite-module-fp-reduction: that node concerns a filtered system of finitely presented modules over a valuation-base algebra. The new lemma concerns a surjection of local algebras over an arbitrary local base, with no valuation hypothesis and no module approximation assertion.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-noetherian-flat-closed-fiber-model: that node constructs a simultaneous Noetherian model for a tower of essentially finitely presented rings and a flat module. The new lemma constructs a local algebra over the original arbitrary base, starting from only essential finite type, with no flatness assumptions.

lem-sfb-finite-type-local-closed-fibre-approximation vs def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit: defines the colimit and comparison equivalence for the middle closed-fibre system of an already supplied Noetherian model tower; the new statement constructs a surjective local approximation over the original base from only essential finite type, without any tower.

lem-sfb-finite-type-local-closed-fibre-approximation vs def-weil-pbc-noetherian-local-model-tower-fiber-system: defines the three closed-fibre diagrams and their actions for an already supplied Noetherian local model tower; it does not assert the existence of an essentially finitely presented algebra surjecting onto a given essentially finite-type local algebra with an identical closed fibre.

lem-sfb-finite-type-local-closed-fibre-approximation vs def-weil-pbc-noetherian-local-model-tower: defines data of a directed tower of three Noetherian local rings and finite modules with localization comparisons. It asserts no existence of the single local approximation over the unchanged arbitrary base in the new statement.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-limit-module-colimit-part: asserts the colimit property of a tail module diagram under supplied module-descent data; the new lemma constructs local algebras, not a module colimit, and needs no given directed system.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-essentially-finite-presentation-over-intermediate: assumes a final algebra already essentially finitely presented over R and changes its coefficient ring to an intermediate essentially finite-type algebra; the new lemma starts with only one essentially finite-type local algebra and constructs a different essentially finitely presented algebra surjecting onto it, with a closed-fibre isomorphism.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-core: descends an already essentially finitely presented local algebra and finitely presented module along a supplied local-ring colimit; the new lemma requires neither such input presentation nor a system or module and constructs a surjection preserving the closed fibre over the unchanged base.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module: descends an essentially finitely presented algebra and module to a tail of a supplied local-ring system, with tensor and colimit comparisons; the new lemma starts from only essential finite type and constructs a surjective local algebra approximation with a specified closed-fibre isomorphism, without changing the base.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-ring: assumes essential finite presentation of the limit algebra and a local-ring system, then produces stage algebras/modules and colimit comparisons. It does not approximate a merely essentially finite-type algebra by a surjective essentially finitely presented algebra over its original base.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-limit-module-essentially-finite-presentation-over-system: descends an essentially finitely presented local algebra and finitely presented module through a directed local-ring colimit. The new lemma has no module or colimit data and constructs an approximation of a merely essentially finite-type algebra with an unchanged closed fibre.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-limit-module-ring-data-core: produces a tail functor and local finite-type stage maps under the hypotheses of ring descent. It supplies no surjection onto a merely essentially finite-type local algebra over a fixed base and no closed-fibre isomorphism.

lem-sfb-finite-type-local-closed-fibre-approximation vs lem-weil-pbc-limit-module-small-over-system: is a universe-sensitive descent statement for an already presented algebra and module over a supplied colimit of essentially finite-type Z-algebras. The new lemma has no colimit or module and starts with only essential finite type over an arbitrary unchanged local base.

## Review by NO

I read Stacks `more-morphisms.tex`, Tag 039C (`theorem-criterion-flatness-fibre`), including its first stalk-reduction paragraph, and `algebra.tex`, Tags 05UV (`lemma-criterion-flatness-fibre-fp-over-ft`), 00QM (`definition-essentially-finite-p-t`), 00HR (`lemma-local-flat-ff`) and 05CK (`lemma-faithfully-flat-universally-injective`). I read the complete statement of the existing 00R7 node, the affine-open stalk localization node, localization transitivity, finite-presentation base change/composition, the fibre-stalk quotient theorem, and both faithful-flatness tools cited below. The chapter and unit records and the current blueprint stability unit were read; this is the inherited auxiliary flat-locus/Hilbert prerequisite, not a change to a six-functor unit step. The generic off-unit statements are declared in `split_report.tool_uses` where necessary.

For step 1, `def-weil-flat-morphism` explicitly identifies pointwise flatness with flatness of the structural local-ring map and says those maps are local; `lem-weil-pbc-scheme-stalk-map-composition` explicitly identifies the composite. Local rings at points are nonzero; this supplies the nonzero module later rather than silently dropping 039C's nonzero-stalk condition. Nothing beyond these definitions and the cited equality is asserted.

For step 2, `lem-sbc-scheme-fibre-stalk-quotient` gives both the quotient isomorphism and its value on every class as the actual projection stalk map, not just an abstract isomorphism. Applied to p and q, it gives exactly C/m_R C and B/m_R B. `def-pc-scheme-fibre` supplies the fibre projections. The composition formula makes the cartesian-square equality into the displayed equality of stalk maps. Surjectivity of the quotient map then checks the fibre action on every class [b]. Thus flatness of f_s is flatness for the particular quotient action needed by 00R7, not for an unrelated isomorphic ring.

For step 3, the local finite-presentation definition supplies the chosen affine p-chart. `lem-weil-pbc-affine-open-stalk-localization` states that its actual germs give A_a and D_c. The separate stalk-germ formula checks compatibility with p. `lem-weil-pbc-finite-presentation-base-change-composition` explicitly gives the finite presentation of R tensor_A D. The tensor/fraction maps proving that this is the base localization are written out, and clause (2) of localization transitivity applies because the image of A minus a avoids c. This is exactly the essentially finitely presented C needed in step 6.

For step 4, the local finite-type definition is quantified over every affine base open, so it applies to the same V chosen in step 3. It supplies E with finitely many algebra generators. I wrote out why the same generators work after replacing A by A_a; no theorem asserting finite type was taken from a definition of flatness. The same affine-open stalk and localization transitivity statements identify B as a localization of that finite-type R-algebra. The definition of essential finite type gives the conclusion. This is an elementary fraction/generator argument from the cited statements, and does not assert finite presentation.

For step 5, the new node is a complete standalone statement over arbitrary nonzero local rings. I checked it against the initial polynomial/finite-equation construction in 05UV, with the finite-type typo corrected as above. Here is the construction checked for its truth: represent B as C_q with C finite type over R, present C as R[z_1,...,z_n]/I, and set D=R[z]_Q for the prime above q and J=ID. The local finite-type presentation B=C_q follows even from an arbitrary localization presentation: elements outside the contraction of the maximal ideal become units in the local ring B, so the two localization universal properties give inverse maps. The ring D/m_R D is a localization of a polynomial ring over the residue field of R, hence Noetherian. Lift finitely many generators of the image of J to elements of J, and let J_0 be the ideal they generate. Then T=D/J_0 is local, is nonzero because it surjects onto B=D/J, and is essentially finitely presented over R: lift the finitely many fractions generating J_0 to polynomial numerators and localize the resulting finitely presented polynomial quotient. Both maps are local, and the image ideals modulo m_R agree, so the induced map T/m_R T→B/m_R B is an isomorphism sending [t] to [u(t)]. These arguments explain why the new statement is true; none is embedded as a proof in the unsplit node. Applying it in step 5 is legitimate by step 4, and its exact quotient-map formula gives the scalar action used in step 6.

For step 6, the existing `lem-weil-pbc-criterion-flatness-fibre` explicitly assumes local R→T→C, both T and C essentially finitely presented over R, a nonzero finitely presented C-module, flatness over R, and the specified closed-fibre flatness. I checked each: step 5 provides local T→B→C and T's presentation; step 3 provides C's presentation; M=C is nonzero and free of rank one over C; steps 1 and 5 provide the two flatness assumptions. Its conclusion is exactly R-flatness of T and T-flatness of C. The Noetherian-only criterion is not used.

For step 7, `lem-pc-local-flat-faithful-flat-reflects-surjective` explicitly includes that any flat local map of local rings is faithfully flat; only that clause is used, not its surjectivity-reflection clause. `lem-weil-pbc-faithfully-flat-universally-injective` explicitly gives N→N tensor_T C injective for every N. Taking N=T and writing the elementary tensor-unit isomorphism identifies its map with T→C. Because this map factors through u, every kernel element of u is zero; u is already surjective by the new lemma. This proves the approximation equals B, rather than relocating the item's conclusion to the new node.

For step 8, the R-algebra isomorphism respects the factorization into C. The definition of a flat ring map and the pointwise-flatness definition therefore translate both tensor-injectivity conditions without changing an action or a hypothesis. This supplies both requested conclusions, with no openness assertion.

I checked small cases of the new statement: R=B with identity map (take T=R); a field base with arbitrary finite-type local B (the closed fibre is B itself, and the lemma correctly forces T≅B, which is essentially finitely presented over a field); a finite polynomial quotient localized at a prime (take the finite equations themselves); n=0 and an empty lifted generating list; nonreduced R and non-finitely-generated defining ideals (only the closed-fibre image ideal needs finite generation). Locality prevents a zero closed fibre, and the existence of y excludes the zero target ring. For the item, empty X is vacuous because x is fixed, identity maps are immediate, and no closed-point, valuation, Noetherian, global flatness, or finite-presentation hypothesis on q was introduced.

Before creating the new node I searched the whole DAG for 05UV, the proof label, closed-fibre approximations and finite-type/local presentation statements, and searched all blueprint nodes using `blueprint_refs.py search` for flatness, 05UV and closed fibre. I also checked the live project source. The nearby nodes listed under Not duplicates do not state it. The new node's Mathlib hits give locality/localization, residue-field finite type, standard-smooth presentations, or the Noetherian finite-type/finite-presentation equivalence; each lacks this arbitrary-base approximation conclusion. Every new-node search record comes verbatim from an actual `msearch.py` log entry, with the actual successful-service status. Existing searches on the item were retained and new item searches appended. Every cited node statement was opened, and `citations.json` contains those actual statements, not paraphrases.

The B–E audit led to the finite-type approximation rather than an invalid direct application of 00R7, and to the explicit fibre-map compatibility. The new node is neither an elementary step nor a flatness clause of the item; its polynomial Noetherian closed-fibre construction is the independent non-elementary sublemma. Its JSON has no proof or proof dependencies, and its statement defines essential finite presentation inline via a localization. No proof step exceeds 2000 characters; the longest is under 1000, and no long step hides a further standard comparison.

The first delivery dry run requested explicit same-tag comparisons for the eleven additional 00R7 limit-system and intermediate-ring nodes listed above. I opened every statement and added the individual distinctions; none states the new closed-fibre approximation. No mathematical statement or citation was changed.


## Current validation

The required deliver.py --no-push completed with exit 0: OK (not pushed), preflight passed at be1770915d5. Its first attempt had requested four additional same-tag duplicate comparisons; I opened all four statements and added their specific distinctions above. The final report is submitted to the same dry run again before push. Both new nodes remain statement-only and the item statement is byte-for-byte unchanged as a JSON string. No local DAG checker or build tool was run.

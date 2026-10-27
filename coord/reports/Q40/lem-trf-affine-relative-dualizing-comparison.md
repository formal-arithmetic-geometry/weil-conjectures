# Worker report

1. Files written: the item JSON (unchanged statement; five-step assembly), and two new statement-only nodes:

- lem-trf-affine-relative-tor-diagonal-finiteness — statement, unsplit, no Mathlib match.
- lem-trf-affine-algebra-class-evaluation-comparison — statement, unsplit, no Mathlib match.

2. Attachments: none. The item tag and concept searches in WeilConjectures found no complete matching declaration. The existing Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison theorem is still `by sorry`; it is not an attachment. No Lean file was changed or compiled.

3. WANTED: none. All sources used below were read in the local Stacks source.

4. Repair: the sandbox initially contained only dispatcher marker files, no delivered node/report/search log. I copied the current repository's returned nine-step item, preserving its full statement, citations, searches, Lean binding and blueprint metadata. Its full proof is preserved below. The return asks for actual new parallel work, not compression: old steps 3--6 (2432 characters approximately) now specify the finiteness node; old steps 7--9 (3284 characters approximately) now specify the natural evaluation/class node. The tensor-square Noetherian calculation in old step 1 also belongs to the finiteness task. Neither node assumes a dualizing pair, neither proves the whole item, and neither has proof steps. The new parent merely applies these prerequisite results to the supplied pair.

5. Nothing remains unfinished within this stage-1 split. The two unsplit proofs are intentionally future work assigned by the DAG, as explicitly required by the return.

## Repair map and retained arguments

Old steps 1--2 are retained in parent steps 1--2 except that the tensor-square finite-generation calculation is allocated to the finiteness node. Old steps 3--6 are the first new node, and old steps 7--9 are the second new node. Empty/identity cases remain parent step 5. The new nodes state all of these conclusions as future proof obligations. The following original text is retained verbatim so the next workers have the full arguments and exact supporting node lists, rather than a compressed replacement.

### Returned step 1 → parent steps 1--2

Keep the affine opens $U=\operatorname{Spec}A$, $V=\operatorname{Spec}R$ specified in the statement. The affine flatness criterion gives flatness of $R\to A$, and the affine characterization of local finite presentation gives a finite presentation of $A$ over $R$ for these very opens. Every affine open of a locally Noetherian scheme has Noetherian coordinate ring, so $R$ is Noetherian; no shrinking of the given $V$ is needed. The presentation makes $A$ a finite-type $R$-algebra, and the Noetherian-algebra theorem makes $A$ Noetherian. If $t_1,\ldots,t_n$ generate $A$ over $R$, then $1\otimes t_1,\ldots,1\otimes t_n$ generate $B=A\otimes_R A$ over $A$ through its first factor. The same theorem therefore makes $B$ Noetherian.

Cited statements: lem-weil-pbc-flat-morphism-affine-criterion, lem-weil-pbc-lfp-affine-opens-finite-presentation, pqf-lem-affine-open-locnoeth, lem-weil-pbc-finite-type-algebra-noetherian.

Source: literature/stacks-project/duality.tex, Tag 0E2U, affine reduction; morphisms.tex Tags 01U5 and 01TQ; algebra.tex Tag 00FN.

### Returned step 2 → parent steps 1--2

Put $W=U\times_VU$. It is the open subscheme $U\times_SU$ of $Y$: both maps from $U$ factor through the open immersion $V\hookrightarrow S$, which is a monomorphism. The affine fibre-product theorem identifies $W$ with $\operatorname{Spec}B$ and its first projection with $a\mapsto a\otimes1$. The restricted diagonal is induced by $\mu:B\to A$, $a\otimes a'\mapsto aa'$, because composing either coprojection with $\mu$ is the identity. Its inverse image of $D(b)\subset\operatorname{Spec}B$ is $D(\mu(b))\subset\operatorname{Spec}A$. Thus the sections of $(\Delta_*\mathcal O_X)|_W$ on $D(b)$ are $A_{\mu(b)}$, with $B$ acting through $\mu$. The basic-open section formula for associated sheaves gives exactly the same sections for $\widetilde A$, with the same fraction restriction maps. They identify the sheaves, not just their global sections.

Cited statements: lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-spec-module-tilde-sections.

Source: literature/stacks-project/duality.tex, Tag 0E2U, diagonal affine comparison; schemes.tex Tags 01I4 and 01HV.

### Returned step 3 → lem-trf-affine-relative-tor-diagonal-finiteness

Let $E=K|_U$. Pseudo-coherence restricts to $U$ by its local definition. The pseudo-coherent quasi-coherence theorem gives $E\in D_{\mathrm{QCoh}}(\mathcal O_U)$, so the affine equivalence supplies $M\in D(A)$ with $\widetilde M\cong E$. The affine pseudo-coherence criterion supplies a bounded-above complex of finite free $A$-modules representing $M$; this is precisely pseudo-coherence over $A$. This also verifies that applying the affine equivalence was legitimate: membership in $D_{\mathrm{QCoh}}$ was established before its use.

Cited statements: def-pur-pseudo-coherent-complex, lem-sc-pseudo-coherent-qcoh, lem-pc-affine-qcoh-derived-equivalence, lem-pc-affine-pseudo-coherent-criterion, def-pc-ring-pseudo-coherent-complex.

Source: literature/stacks-project/duality.tex, Tag 0E2U, paragraph beginning Observe that relatively perfect objects; perfect.tex Tags 08E5, 06Z0, 08E7.

### Returned step 4 → lem-trf-affine-relative-tor-diagonal-finiteness

The local relative Tor hypothesis on $K$ restricts to $U$ and to the base open $V$. Its formulation using inverse images of $\mathcal O_S$-modules also tests all $\mathcal O_V$-modules: a module on $V$ extends by direct image along $V\hookrightarrow S$, and its restriction back is the original module, directly from the open direct-image formula. Apply the affine relative-Tor criterion to $R\to A$ and $E=\widetilde M$. Its local-finite clause (and its inverse-image-test clause) gives one finite interval $[a,b]$ with $H^i(M\otimes_R^{\mathbf L}N)=0$ for every $R$-module $N$ outside that interval. This is a relative $R$-Tor bound; the absolute $A$-Tor criterion is not being substituted. In particular taking $N=R$ shows $H^i(M)=0$ for $i<a$ and $i>b$.

Cited statements: lem-trf-affine-relative-tor-amplitude-criterion.

Source: literature/stacks-project/perfect.tex, Tag 0DHY, lemma-tor-dimension-rel-affine (2), including the finite-subcover argument on the affine source.

### Returned step 5 → lem-trf-affine-relative-tor-diagonal-finiteness

The affine pullback comparison, including its open-restriction clause, gives $(Lp_1^*K)|_W\cong\widetilde{M_1}$ with $M_1=M\otimes_{A,p_1}^{\mathbf L}B$. The $A$-module $B$ through $p_1$ is flat: it is base change of the flat $R$-module $A$ from Step 1. Hence $B[0]$ itself computes this derived tensor. Exactness of flat tensor on kernels and images gives $H^i(M_1)=H^i(M)\otimes_{A,p_1}B$, so $M_1$ is bounded below by $a$. These computations also verify the stated use of flat resolutions for the derived tensor.

Cited statements: lem-pc-affine-derived-pullback-tensor-tilde, lem-weil-pbc-flat-module-base-change, lem-weil-pbc-flat-tensor-exact, lem-pc-module-bounded-flat-kflat.

Source: literature/stacks-project/duality.tex, Tag 0E2U, pullback compatibility; perfect.tex Tag 08DW; algebra.tex Tags 00HI and 00HD.

### Returned step 6 → lem-trf-affine-relative-tor-diagonal-finiteness

The map $\mu:B\to A$ is surjective since $\mu(a\otimes1)=a$. Thus $A$ is a cyclic, hence finitely generated, $B$-module. Over the Noetherian ring $B$ of Step 1, the Noetherian pseudo-coherence criterion applied to $A[0]$ makes it pseudo-coherent: its only nonzero cohomology is the finite module $A$ in degree zero. By the definition of ring pseudo-coherence it has a bounded-above finite-free $B$-complex representative. This proves the finiteness condition on the first argument of the forthcoming internal-Hom comparison; neither regularity of the diagonal nor a bounded projective resolution is assumed.

Cited statements: lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion, def-pc-ring-pseudo-coherent-complex.

Source: literature/stacks-project/duality.tex, Tag 0E2U, pseudo-coherence condition for the diagonal; in the Noetherian case more-algebra.tex Tag 066E.

### Returned step 7 → lem-trf-affine-algebra-class-evaluation-comparison

Use open restriction of derived internal Hom to identify its restriction from $Y$ to $W$ with $R\mathcal Hom_W(\widetilde A,\widetilde{M_1})$. Step 6 gives a bounded-above finite-free (therefore finite-projective) representative for its first argument, and Step 5 gives bounded-below cohomology for its second. The affine pseudo-coherent RHom theorem, with coefficient ring $B$, now gives $R\mathcal Hom_W(\widetilde A,\widetilde{M_1})\cong\widetilde{R\operatorname{Hom}_B(A,M_1)}$. Finite freeness implies projectivity by the cited free-module theorem. All the hypotheses of this comparison have now been supplied, including the bounded-below hypothesis which would fail for an arbitrary unbounded second argument.

Cited statements: lem-sc-derived-internal-hom-restrict-open, lem-sc-affine-pseudo-coherent-rhom-qcoherent, lem-weil-pbc-free-module-projective.

Source: literature/stacks-project/duality.tex, Tag 0E2U, internal Hom compatibility; cohomology.tex Tag 08DL; perfect.tex Tag 0A6H (3)(a).

### Returned step 8 → lem-trf-affine-algebra-class-evaluation-comparison

Restrict $\xi$ to $W$ and use the full faithfulness of the affine derived equivalence for $B$ to define its inverse image $\xi_U:A\to M_1$. Check the induced multiplication map using tensor-Hom evaluation. On either side it is the transpose of the composite $A\otimes_B^{\mathbf L}A\to A\xrightarrow{\xi_U}M_1$, respectively its sheaf version, where the first arrow is the derived multiplication of the degree-zero algebra $A$. The canonical affine tensor comparison carries this multiplication to sheaf multiplication: on representative tensors its value is $x\otimes y\mapsto xy$. The Hom comparison in Step 7 respects this transposition. Concretely, a bounded-above finite-free resolution of $A$ and a bounded-below representative of $M_1$ compute it by the cited finite-free derived-Hom model. In each total degree only finitely many Hom summands occur, and the comparison is componentwise evaluation $h\otimes x\mapsto h(x)$ before and after associated sheafification; the functorial Hom-tensor identity and its cochain differentials are the same. Thus the sheafification of the multiplication map induced by $\xi_U$ is the restriction of the given multiplication isomorphism. The affine equivalence reflects isomorphisms, proving $A\xrightarrow{\sim}R\operatorname{Hom}_B(A,M_1)$.

Cited statements: lem-pc-affine-qcoh-derived-equivalence, lem-pc-affine-derived-pullback-tensor-tilde, lem-sc-derived-hom-finite-free-model, lem-sc-derived-hom-tensor-total, def-pc-canonical-derived-tensor-hom-bijection.

Source: literature/stacks-project/duality.tex, Tag 0E2U, final sentence recovering the algebraic conditions; perfect.tex Tags 08DX and 0A6H; cohomology.tex tensor-Hom evaluation.

### Returned step 9 → lem-trf-affine-algebra-class-evaluation-comparison

The same model formulas verify the final compatibility assertions. Multiplication by $c\in A$ on the coefficient complex and precomposition by multiplication on the diagonal commute with the comparisons: the former is $h\mapsto ch$, and evaluation gives $(ch)(x)=c\,h(x)$; the latter is the functorial first-variable Hom action. For a smaller pair of affine opens, its product is an open in $W$. Open restriction of pullback and RHom gives the operations there. The basic-open fraction map for $\widetilde A$ in Step 2 commutes with restriction. For the Hom comparison, restrict the finite-free/bounded-below representatives: the degreewise finite Hom sums restrict to the same finite Hom sums of the restricted terms, and the evaluation formula and differential are unchanged. This constructs the same comparison on the smaller open, so the two descriptions of the restricted class are equal by full faithfulness of its affine equivalence. This is compatibility of the constructed maps; it does not infer equality of arbitrary derived morphisms from local equality. If $U$ is empty, $A=B=0$, all module and sheaf objects are zero, and any finite interval works. For the identity map $R=A$ the diagonal and all these formulas reduce to the ordinary affine equivalence and evaluation.

Cited statements: lem-pc-affine-derived-pullback-tensor-tilde, lem-sc-derived-internal-hom-restrict-open, lem-weil-pbc-spec-module-tilde-sections, lem-sc-derived-hom-finite-free-model, lem-sc-derived-hom-tensor-total, lem-pc-affine-qcoh-derived-equivalence.

Source: literature/stacks-project/duality.tex, Tag 0E2U, restriction of the three affine comparisons; perfect.tex Tag 0A6H proof and cohomology.tex Tag 08DL.

## Review by Q40

I read Stacks duality.tex, lemma-relative-dualizing-complex-algebra (0E2U), including the reason its final internal-Hom comparison requires pseudo-coherence of the diagonal and boundedness below of the pullback. I read perfect.tex, lemma-pseudo-coherent-affine (08E7), lemma-tor-dimension-rel-affine (0DHY), and lemma-quasi-coherence-internal-hom (0A6H), as well as cohomology.tex, lemma-Rhom-complex-of-direct-summands-finite-free. The first new node isolates the finiteness checks preceding that Hom calculation, without requiring that E be perfect over A; the uniform interval is relative to R. The second isolates the Hom calculation and its actual evaluation maps, without assuming C has a bounded projective resolution. The multiplication transpose is explicitly part of the statement, not inferred from an arbitrary isomorphism of objects. Its localization clause names the canonical evaluation-defined map into Hom recomputed over the new coefficient ring.

For parent step 1 I read all four cited node statements: the affine flatness criterion applies to the very opens given, the finite-presentation criterion gives finite presentation there, the affine-open local-Noetherian statement gives R Noetherian, and the finite-type Noetherian-algebra theorem gives A Noetherian. I did not shrink the given chart. For step 2 the affine-fibre-product node gives Spec(B) and both coordinate maps; the associated-sheaf node gives sections A_{mu(b)} and the actual fraction restriction maps. The diagonal ring map is determined by its two composites, so these are the sections of its direct image, not just a global-sections identification.

For parent step 3 I read the full new finiteness statement. The hypotheses R Noetherian and A flat finitely presented come from step 1; pseudo-coherence and the local relative test come from the supplied K. Open direct image extends every base-open module and restricts back identically, so the new node's test by every inverse-image module is justified. Its conclusion gives the desired module, the relative R interval, and separately the pseudo-coherent B-module A and the lower bound on M1 needed in step 4. It does not replace relative R-Tor dimension by absolute A-Tor dimension. Its future proof is exactly returned steps 3--6: pseudo-coherent implies quasi-coherent, the affine pseudo-coherence criterion gives finite free models, the relative Tor criterion supplies the interval, N=R supplies a lower bound, flat base change preserves that bound, and cyclic A over Noetherian B is pseudo-coherent. The generation calculation for B is retained in returned step 1 above. I read each of these original supporting statements in full before assigning this task.

For parent step 4 I read the affine pullback/tensor node, the open-restriction RHom node, the affine equivalence node and the full new algebra-class statement. Step 3 supplies its exact hypotheses with C=A and T=M1 over B. Its evaluation normalization identifies the specified multiplication transpose, so reflection of isomorphisms under the equivalence proves the class-map assertion. Naturality for B scalars gives a tensor 1 scalar action; first-variable naturality also gives precomposition by A multiplication. For a smaller affine product chart the ring map B→D is an affine open immersion; the comparison theorem explicitly covers such maps and successive restrictions. Its diagonal is D tensor_B A by the basic-open description, and its coefficient object is derived scalar extension by tensor associativity. Thus the local class is recomputed using multiplication and evaluation, not an arbitrary identification or equality inferred from local equality of derived morphisms. I read the flat pseudo-coherent RHom base-change node too; it supplies invertibility of the localization comparison to the future worker, but does not already assert the sheaf/evaluation/class comparison in the new statement.

Step 5 checks zero rings, empty affine opens and the identity map directly. I also checked E=0 (choose [0,0]), shifts A[n] of flat modules, C=B (ordinary evaluation), and a nonperfect cyclic algebra over a singular Noetherian ring. The latter confirms why bounded-above finite free, rather than bounded projective, is essential; no regularity is being smuggled in. No claim was made for an arbitrary unbounded second Hom argument. All new object comparisons are derived-category isomorphisms, not merely per-degree assertions.

I checked delivery-errors B--E: statements introduce their own objects, have definition references or explicit meanings, use Stacks labels/tags, have no embedded proof, and were searched before creation; citations use statements rather than a construction hidden in a proof; neither new node depends on the parent; the parent still carries the ring/diagonal argument and assembly; no route change, existence claim, SGA citation, added hypothesis or statement weakening was introduced. The two new tasks account for comparable substantial pieces of the returned proof. No parent non-elementary step exceeds 2000 characters and the full assembly is below 3000 characters. I preserved old search records and recorded only actual msearch calls for the new nodes; LeanSearch rate limits are marked unavailable, and the two phrasings of LeanFinder, Loogle and source searches were read.

## Not duplicates

- lem-trf-affine-relative-tor-diagonal-finiteness vs def-trf-affine-diagonal-module-data: the existing node defines K-flat scalar extension and the affine diagonal module; it states no uniform relative-Tor, pseudo-coherence or boundedness theorem for an arbitrary E.

- lem-trf-affine-relative-tor-diagonal-finiteness vs def-trf-polynomial-duality-affine-atlas-comparison: the existing node defines Canonical affine realization of coinduced polynomial duality models; it states no uniform relative-Tor, pseudo-coherence or boundedness theorem for an arbitrary E.

- lem-trf-affine-relative-tor-diagonal-finiteness vs def-trf-polynomial-duality-affine-realization: the existing node defines Exact affine realization with original-unit normalizations; it states no uniform relative-Tor, pseudo-coherence or boundedness theorem for an arbitrary E.

- lem-trf-affine-relative-tor-diagonal-finiteness vs lem-trf-affine-relative-dualizing-comparison: the parent translates a supplied geometric dualizing pair and its canonical class; the new prerequisite has no pair or class, and establishes uniform relative Tor bounds, diagonal finiteness and a flat pullback lower bound for an arbitrary E.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-affine-finite-projective-hom-model: the existing node asserts Finite-free preparation of the affine module Hom complex; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-affine-pseudo-coherent-rhom-qcoherent: the existing node asserts Affine RHom of a pseudo-coherent complex is quasi-coherent; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-derived-locally-bounded-below-global: the existing node asserts A locally bounded-below derived object on a Noetherian scheme has a uniform lower bound; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-finite-free-hom-complex-qc-cohomology: the existing node asserts Quasi-coherent cohomology of Hom from a finite free complex; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-pseudo-coherent-rhom-qcoherent: the existing node asserts Derived internal Hom from a pseudo-coherent module preserves bounded-below quasi-coherence; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-rhom-supported-qcoherent-perfect-part: the existing node asserts Perfect internal Hom quasi-coherence; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-rhom-supported-qcoherent-pseudo-part: the existing node asserts Pseudo-coherent internal Hom quasi-coherence and local lower bounds; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-rhom-supported-qcoherent: the existing node asserts Internal Hom from a pseudo-coherent or perfect complex to a supported complex; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs lem-sc-single-supported-finite-free-hom-qc: the existing node asserts Quasi-coherent cohomology of one-column finite free Hom; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs new-lem-sc-rhom-supported-qcoherent-pseudo-part-bound: the existing node asserts Local lower-bound component of pseudo-coherent RHom; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology: the existing node asserts Degreewise quasi-coherence of pseudo-coherent RHom; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

- lem-trf-affine-algebra-class-evaluation-comparison vs new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc: the existing node asserts Quasi-coherence component of pseudo-coherent RHom; the new theorem asserts the evaluation-normalized affine isomorphism together with algebra multiplication-transpose and canonical affine-open localization diagrams. Those diagrams are absent from the existing statement.

Additional keyword candidates read: lem-pc-perfect-affine-module-preimage assumes E perfect and has no relative base-ring/diagonal bounds; lem-sc-flat-affine-global-hom-comparison assumes a perfect first argument and has no algebra class-map diagram. lem-sc-derived-restriction-tensor-hom-coherence and lem-pc-open-restriction-closed-monoidal compare two SHEAF derived categories under open restriction; they do not identify module derived Hom with affine sheaf Hom. lem-trf-pseudocoherent-rhom-flat-base-change gives the module scalar-extension isomorphism alone and is an input to, rather than a duplicate of, the new evaluation-and-class comparison. Blueprint searches for pseudo-coherent affine, relative Tor, affine Hom, tensor-Hom evaluation and multiplication internal Hom found no blueprint statement giving either new prerequisite package.


## Landing-refusal repair and current-DAG comparison

The return is: “approved by the reader, but the landing refused it: NOT MERGED lem-trf-affine-relative-dualizing-comparison: lem-trf-affine-relative-dualizing-comparison: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it). Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.”

I continued the retained sandbox rather than recreating the split. The retained `returned-proof.json` is identical, field for field, to the current repository item. Relative to that current item, the retained delivery changes only `proof`, `proof_deps` and `split_report`; the statement, statement dependencies, source, Lean binding, blueprint ancestry, import flags and existing review record agree exactly. I reapplied these three split fields to a freshly read current node, and amended the split summary and this report to record this specific landing refusal. The first required dry run completed successfully at `23de2c34c01`; the delivery tool fetched the current server DAG and rebuilt the delivery in its own worktree. The final dry run and push use that same supported mechanism, not an old delivery commit or an unchanged branch re-push. The maintainer L is responsible for the live-DAG promotion identified in the return; this report does not treat the older side-project completion as a new live landing.

I reread all current proof-citation statements, including those whose old supporting arguments are retained in the repair map above, rather than guessing which had changed. In step 1 the affine flatness and local-finite-presentation criteria apply to every given pair of affine opens; the locally-Noetherian affine-open theorem and finite-type algebra theorem give exactly the two ring conclusions. In step 2 the fibre-product theorem specifies both tensor coprojections, and the associated-sheaf theorem specifies basic-open localizations and their fraction restriction maps. This supplies the actual sheaf identification used by the assembly. In step 3 the new finiteness node assumes the flat finitely presented Noetherian base data already established and supplies the uniform relative R interval, the pseudo-coherent diagonal over B and the bounded-below first pullback. In step 4 the current affine pullback statement includes open restriction and tensor comparison, the RHom restriction statement allows arbitrary derived objects, the affine equivalence supplies full faithfulness and reflection of isomorphisms, and the new class-comparison statement explicitly includes evaluation normalization, multiplication transpose, scalar naturality and the affine-open localization diagrams. Thus no step borrows a result available only inside another node's proof, and no changed citation requires an additional hypothesis or replacement node. Step 5 remains the direct zero-ring and identity calculation.

I also reread the supporting pseudo-coherence, affine relative Tor, flat base-change, flat tensor exactness, bounded-flat K-flatness, Noetherian pseudo-coherence, finite-free Hom-model and tensor-Hom statements underlying the retained proof map. They still provide the claimed inputs. In particular the Tor bound is over R, not A; the diagonal needs pseudo-coherence, not a bounded projective resolution; and the second Hom argument is bounded below. These checks agree with Stacks duality.tex, lemma-relative-dualizing-complex-algebra (0E2U), perfect.tex, lemma-pseudo-coherent-affine (08E7), lemma-tor-dimension-rel-affine (0DHY), lemma-quasi-coherence-internal-hom (0A6H), and cohomology.tex, lemma-Rhom-complex-of-direct-summands-finite-free, which I reopened for this repair. Zero rings, E=0, C=B and a nonperfect cyclic diagonal over a singular Noetherian ring still satisfy precisely the stated hypotheses.

All 11 entries of the retained citations.json are still verbatim substrings of the current cited statements and cover every (step, cited-node) pair exactly. The retained new nodes remain statement-only unsplit tasks, and neither id occurs in the current repository DAG. The assembly has 2,890 characters in five steps, with no non-elementary step exceeding 2,000 characters. Existing logged searches and their unavailable-service verdicts are retained without inventing or repeating queries, since neither new statement nor its search question changed. This addresses the single landing-refusal point while preserving the previously approved mathematical split and its full retained arguments.

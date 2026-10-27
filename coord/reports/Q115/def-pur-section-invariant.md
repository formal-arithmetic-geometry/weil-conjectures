# Worker report: def-pur-section-invariant

## Files written

- dag/nodes/sec-smooth-purity/def-pur-section-invariant.json: definition; statement retained byte-for-byte; three assembly steps, 1624 characters of proof text.
- dag/nodes/sec-smooth-purity/lem-pur-varying-dimension-dualizing-inverse.json: statement, unsplit; no Mathlib match; finite-clopen reduction and reconstruction of the inverse of the dualizing object with varying relative dimension.
- dag/nodes/sec-smooth-purity/lem-pur-all-stage-ctf-pullback-unit.json: statement, unsplit; no Mathlib match; actual finite, integral, rational and algebraically closed pullback domains, fixed/uniform Tor bounds, and completed-unit isomorphisms.
- citations.json: one verbatim statement excerpt for every citation in every assembly step.
- searches.jsonl: the actual prescribed msearch.py search log. No search was fabricated or rewritten.

## Attachments

None. I searched lean/WeilConjectures for the blueprint id and section-invariant/dualizing terminology and read Conventions.lean, SectionInvariant.lean and SectionInvariantCtf.lean in EtaleCohomology/Purity/Smooth. The finite etale declarations include AlgebraicGeometry.Etale.sectionInvariant, isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant_of_smooth (SectionInvariantCtf.lean:238), and isInvertible_and_boundedConstructibleFiniteTor_dualizingComplex_of_smooth (line 166). They do not state the integral and field-level completed/common-stage pro-etale clauses. The finite-stage result is useful reference material, not an attachment of this entire item or the all-stage new nodes. The named sectionInvariantIntrinsic_invertible in lean/Sheaf/Paper/PuritySectionInvariantIntrinsic.lean still contains sorry; sectionInvariantFinite_invertible calls it. Neither is a completed proof of the item. No Lean file was edited or compiled.

## WANTED

None: the current/older blueprint, Stacks source and Bhatt--Scholze paper needed for this extraction are present.

## The returned problem and its repair

The supplied return asks for at least two independent next-level tasks, comparable in size, instead of 5193 characters in one node. The sandbox initially contained only dispatcher marker files: no node, report, citations or search log. I recovered the returned seven-step split from the current read-only repository, including its statement, proof, citations, recorded searches, blueprint fields and Lean metadata. The earlier review is available at coord/reports/Q40/def-pur-section-invariant.md; I read it. All existing metadata is retained, except the split-owned proof, proof origin and split report. The delivery tool rebases the overlay on current server state and preserves maintainer-owned fields.

The extraction boundary is mathematical, not a shortening trick. The first new task handles a smooth morphism without a section and with nonconstant relative dimension; its statement gives the finite dimension partition, the exact admissibility of each restriction, the derived exceptional restrictions and an inverse pair reconstructed in the finite-Tor category at each coefficient stage. The second task handles any separated finite-type morphism, without smoothness or an exceptional inverse image; its statement gives constructible finite-Tor pullback with unchanged finite/uniform integral intervals and the actual coefficient-unit isomorphisms. Neither restates the section-invariant assertion. Their statements are 2660 and 2896 characters, and their original argument allocations are respectively old steps 1-3 (2097 characters) and 4-6 (2265 characters). Both have status unsplit, proof=[], proof_deps=[], proof_origin=null. No proof sketch has been put inside a statement.

Old step 7 is the short final assembly, retained explicitly as current step 3, including the direction of the tensor comparison and both inverse maps. It cannot replace either new task: it assumes their dualizing inverse, pullback domains and unit comparison. The two new tasks are independent: neither cites the other or the parent. The parent keeps its original statement, its actual pullback construction and its lack of a Tate orientation.

The existing source error “invertible by def-pur-co-smoothness” is not revived. That node defines a property; the actual invertibility theorem used in the first task is thm-pur-cohomological-smoothness. This was already explained in the returned proof, and its full argument is preserved below. No new statement dispute or weakening was introduced.

## Sources and searches

I read the current main-20261015 blueprint file literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md, its conventions unit _section.md, the original chapter/unit records, def-pur-conventions, and the full returned split. The formula is the same actual pullback at every stage. Chapter and unit routes are unchanged; no SGA route is used.

For the first new node I opened the full statements of sbc-lem-smooth-relative-dimension-locally-constant, lem-pc-open-immersion-smooth-composition, lem-pur-finite-clopen-derived-decomposition, lem-pur-finite-clopen-exceptional-restriction and thm-pur-cohomological-smoothness. I also read Stacks Tag 02G1, morphisms-lemma-smooth-omega-finite-locally-free, in literature/stacks-project/morphisms.tex:7214: finite local freeness of differentials gives the dimension function. This is the geometric input, not a purported Stacks theorem on all-stage dualizing objects. The source field of the new task deliberately names the blueprint argument being extracted rather than falsely attributing the whole theorem to that tag.

For the second new node I opened the full statements of lem-sf-pullback-tor-amplitude, lem-pur-integral-operations-preserve-constructible, def-weil-finite-tor-amplitude, def-weil-derived-pullback-tensor-hom and lem-weil-constant-coefficient-objects-constructible. I read Bhatt--Scholze, literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemmas 6.5.3-6.5.5 and 6.5.9(5), including the pullback-followed-by-completion proof. The paper assumes qcqs schemes there; finite-type schemes over a field are noetherian and hence qcqs, without imposing separatedness over k. The Tor uniformity and field-stage clauses are precisely the existing definitions and representative constructions, not an additional conclusion claimed from Bhatt--Scholze alone.

For the assembly I read lem-pur-derived-pullback-tensor-iso in full and Stacks Tag 07A4, sites-cohomology-lemma-pullback-tensor-product, at literature/stacks-project/sites-cohomology.tex:3684. The finite-level comparison is ambient, and the cited node separately states the coherent integral, rationalized and common-stage comparisons. I did not claim that the Stacks lemma by itself proves those higher-coefficient extensions.

Before creating either node I searched the whole DAG by titles and statements for varying dimension/dualizing, clopen, inverse pair, constructible pullback, finite Tor and completed-unit terms. I ran tools/blueprint_refs.py ancestor def-pur-section-invariant (ancestor is the item itself), and searches for pullback, dualizing, unit, pullback finite Tor, pullback invertible, dualizing varying, pullback coefficient unit, dualizing invertible, finite Tor preservation, coefficient unit, relative dimension, completed unit, inverse pair, uniform Tor, constructible pullback and pullback unit. I read the closest matches listed below. Neither new statement is an existing imported node. Both new blueprint.from.node values are the item, via=[], their places identify the original arguments exactly, and same_as=[] records no identical blueprint statement.

Each new node has actual LeanFinder, Loogle, grep and LeanSearch results with exact query strings copied from searches.jsonl. I read the hits and tried a second formulation for each. The first searches return smooth relative-dimension definitions, ordinary invertible modules and scheme gluing; they do not construct relative dualizing complexes. The second searches return ordinary adic module completion, general underived sheaf pullbacks, and unrelated categorical pullback/unit references. I read Mathlib/RingTheory/PicardGroup.lean, including Module.Invertible, and Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:45-64, including SheafOfModules.pullback and pullbackPushforwardAdjunction. These have neither the needed derived constructible domains nor the uniform integral reduction assertion. No candidate states a new node or specializes to it in one line. All services used for the recorded new-node searches succeeded; no unavailable service is represented as a no-match. Existing item searches were retained, not rerun.

## Not duplicates

lem-pur-varying-dimension-dualizing-inverse vs thm-pur-cohomological-smoothness: the existing theorem assumes one relative dimension d; the new task allows different dimensions on different components and constructs the finite partition and the global inverse from the pure-dimensional inputs. The existing theorem remains its intended input, not a duplicate output.
lem-pur-varying-dimension-dualizing-inverse vs lem-sf-smooth-dualizing-complex-invertible: the existing result is finite-coefficient, pure-dimensional and etale; the new task includes varying dimension and the completed, rationalized and common-stage pro-etale categories.
lem-pur-varying-dimension-dualizing-inverse vs lem-pur-finite-clopen-derived-decomposition: that statement gives the coefficient-category equivalence for a supplied finite clopen cover, with no smooth morphism, dimension partition or inverse of a dualizing object.
lem-pur-varying-dimension-dualizing-inverse vs lem-pur-finite-clopen-exceptional-restriction: that statement identifies exceptional restrictions for a supplied clopen cover, with no smoothness, pure-dimensional invertibility or global inverse construction.
lem-pur-varying-dimension-dualizing-inverse vs cor-pur-smooth-admissibility: that statement is finite-level and pure-dimensional, and asserts exceptional amplitude preservation, not varying-dimension global tensor invertibility.
lem-pur-varying-dimension-dualizing-inverse vs def-pur-section-invariant: the new task has no section and concerns an inverse on V, not the actual section pullback or an object on B.
lem-pur-all-stage-ctf-pullback-unit vs lem-sf-pullback-tor-amplitude: the existing node is the finite-level fixed-interval theorem; the new task also gives uniform integral reductions, field-stage functors and actual completed-unit maps.
lem-pur-all-stage-ctf-pullback-unit vs lem-pur-integral-operations-preserve-constructible: the existing node gives integral bounded constructibility and reduction comparisons, not the uniform Tor test, finite/field-stage assertions or unit isomorphisms.
lem-pur-all-stage-ctf-pullback-unit vs lem-pur-completed-unit-pullback-tower: that node concerns the unit tower and assumes separated schemes; it does not assert fixed-interval pullback of arbitrary ctf inputs. The new task permits finite-type schemes not separated over k, as the parent does.
lem-pur-all-stage-ctf-pullback-unit vs det-thm-sf-ctf-stability-direct-images: that imported statement uses admissible condensed module-object coefficients and standing separated schemes; it does not give the parent's specified completed ordinary module-sheaf pullback, fixed uniform intervals or completed-unit isomorphism. No identification of these different categories is assumed.
lem-pur-all-stage-ctf-pullback-unit vs lem-sfb-dc-upper-star-preserves: that statement is bounded constructibility for condensed module objects; it omits the ordinary completed coefficient categories, uniform Tor bounds and unit maps.
lem-pur-all-stage-ctf-pullback-unit vs lem-pur-derived-pullback-tensor-iso: the existing statement gives tensor comparisons but no finite-Tor preservation theorem; that comparison is still cited directly by the item's final assembly.
lem-pur-all-stage-ctf-pullback-unit vs def-pur-section-invariant: the new task has no smooth morphism, exceptional inverse image, section, inverse pair or Picard conclusion. It supplies the domains and unit needed before the parent's inverse composites can be formed.

## Review by Q115

I reviewed the actual item, both new node files, the cited statements and the sources above against delivery-errors B-E, including both copies of those sections. This repair responds to the sole returned point by adding two genuine next-level tasks instead of merely reducing the word count. The previous proof is preserved verbatim below. The statements retain all its conclusions in independently usable forms. The parent statement is exactly unchanged, not replaced by a finite-coefficient approximation.

Current step 1 uses only lem-pur-varying-dimension-dualizing-inverse. Its statement explicitly supplies omega_g and P in D^b_ctf and the two named inverse isomorphisms at each coefficient stage, allowing varying dimension and the empty source. The parent has every input hypothesis: g is smooth, separated finite type and both schemes are finite type over k. There is no demand for a section in that task, so none is used to justify the partition. For its future proof, the original geometric admissibility, clopen exceptional comparison, pure-dimensional theorem and inverse assembly are all retained below. In particular the integral restrictions must be comparisons on actual coefficient systems; independent levelwise isomorphisms would not meet the new statement.

Current step 2 uses def-weil-derived-pullback-tensor-hom for the actual construction of C and Q. Its finite formula is copied verbatim into citations.json; it really defines the derived inverse image, rather than merely naming its universal property. The closed-immersion properness node states properness together with separatedness and finite type explicitly; that discharges exactly the morphism assumptions in lem-pur-all-stage-ctf-pullback-unit. I verified that the new node introduces its X,Y,f,K and coefficient data, allows the same finite-type schemes without assuming separatedness over k, and explicitly supplies both ctf membership and u_s. At finite coefficients it preserves the same [a,b], so at the integral stage the interval remains independent of j. At field levels bounded constructibility is supplied on representatives; I do not infer that an arbitrary rational object's chosen integral representative already lies in integral D^b_ctf. The unit is the completed sheaf, not the constant discrete integral ring, and its maps use the specified inverse-limit construction. The calculations in old steps 4-6 are preserved without replacing them by an unspecified transport.

Current step 3 uses exactly the tensor comparison in lem-pur-derived-pullback-tensor-iso, not a definition of pullback. I checked its displayed direction: mu goes from pullback of tensor to tensor of pullbacks, so the assembly starts with mu^{-1}, then applies Ls* to e, then u_s. The second composite reverses the factors and uses e'. Both are isomorphisms by composition of supplied isomorphisms, an elementary inference; the non-elementary tensor comparison is cited. At finite coefficients it is valid in the ambient derived category, so the proof does not assume arbitrary bounded inputs have a bounded tensor. The output is isomorphic to the unit, which is the desired object in the full ctf category. The higher-coefficient comparison is the actual coherent construction stated by that node. Nothing in these composites chooses an orientation or defines C from a mere existence assertion.

For B1-B3, both new files are statement-only and introduce their own objects and coefficient stages, including the meaning of the unit, the integral uniform interval and the field-stage categories. Their definitions have explicit existing statement dependencies. The finite-clopen equivalence mentioned in the first task is the existing lemma, not a third new node. Sources name the exact blueprint sentence and extracted proof steps. Stacks tags checked above are cited accurately in this report for the parts they prove, rather than used to supply unspecified meaning in new statements. TeX has single mathematical backslashes and real paragraph breaks. All search records are actual calls; the exact log remains in the sandbox. Their blueprint ancestor and same_as searches are recorded.

For C1-C4, every non-elementary fact used in the parent's assembly is in the statement of a cited node. citations.json contains substantive exact quotations, including full new-node statements and the full tensor comparison. The parent's proof_deps is exactly the union of step uses. The future proof material of the two unsplit tasks cites its existing mathematical inputs in the verbatim argument below; those tasks deliberately have no proof dependency list until their own workers split them. Existing dependencies remain reachable through the new tasks' definitions and the retained assembly as appropriate; no existing node was edited or duplicated. Off-unit generic tools still used by the parent are declared in split_report.tool_uses with their purpose.

For D1-D4, the first task is a geometric and exceptional-functor inverse argument before any section is introduced, the second is a pullback-domain and coefficient-unit argument that knows nothing about dualizing objects, and the item itself composes the tensor maps. Neither task restates the item or bears its whole content. The two tasks neither depend on each other nor depend on the item. No derived comparison has been weakened to equality of individual cohomology groups. All three assembly steps are below 2000 characters, their total below 3000; no long step hides another argument.

For E, I checked g=id in dimension zero (partition has only V_0), V empty (empty product category), and V equal to the disjoint union of a point and an affine line over a point (two relative dimensions, so a single global d cannot be assumed). The common Tor bounds are maxima/minima of finitely many intervals, including intervals already uniform in j, never extrema over an uncontrolled infinite set of levels. I checked the second task for f=id, the zero input complex and empty schemes. Its unit formula remains the completed ring even for integral coefficients, and it does not claim f^{-1} of the completed ring is already the completed ring. It uses completed derived pullback. I also checked that a closed section is separated finite type although B itself need not be separated over k. These are the hypotheses actually needed by the assembly.

The extraction preserves the current unit's route and the lecture-notes diagonal/deformation purity inputs beneath the existing pure-dimensional theorem. It uses no prohibited SGA source. No compiler, Lake or build tool was run; all writes are in this item's sandbox. The required server dry run and push are the final validation and delivery steps.

## Original arguments retained for the new workers

These are the complete returned proof texts, copied without shortening. The first three belong to lem-pur-varying-dimension-dualizing-inverse; the next three belong to lem-pur-all-stage-ctf-pullback-unit. The seventh is the explicit parent assembly still written in current step 3. They are report material, not proof fields in the statement-only new nodes.

### Returned step 1

By [sbc-lem-smooth-relative-dimension-locally-constant] the relative-dimension loci $V_d$ of $g$ are open and closed. They cover the quasi-compact finite-type $k$-scheme $V$, so only finitely many are nonempty. By [lem-pc-open-immersion-smooth-composition], each $g_d:V_d\to B$ is smooth, and it has pure relative dimension $d$ by the definition of $V_d$. It is separated and of finite type: its diagonal is the restriction of the closed diagonal of $g$, and a clopen subset of each quasi-compact inverse image of an affine open of $B$ is quasi-compact. Local finite-type conditions restrict to open subschemes. Thus the pure-dimensional theorem can be applied to every $g_d$, even though the dimension of $g$ need not be constant.

Cited nodes: sbc-lem-smooth-relative-dimension-locally-constant, def-weil-finite-type-morphism, def-weil-proper-morphism, def-sbc-smooth-morphisms, lem-pc-open-immersion-smooth-composition.

### Returned step 2

Apply [lem-pur-finite-clopen-derived-decomposition] to the finite cover $(V_d)_d$. It identifies the constructible finite-Tor category, its tensor and its unit with the product of the corresponding categories on the pieces. Apply [lem-pur-finite-clopen-exceptional-restriction] with $L=\Lambda_B$ to identify the component of $\omega_g$ with $\omega_{g_d}$ at every coefficient stage. Its system-level clause supplies the integral comparison; there is no passage from unrelated levelwise isomorphisms to a coherent tower. These statements also cover empty $V$.

Cited nodes: lem-pur-finite-clopen-derived-decomposition, lem-pur-finite-clopen-exceptional-restriction.

### Returned step 3

Apply the invertibility clause of [thm-pur-cohomological-smoothness] to each $g_d$ of step 1. Its schemes and coefficients are in the same purity conventions, and each $g_d$ is smooth separated with the single relative dimension $d$ required by that theorem. Choose an inverse $P_d$ of $\omega_{g_d}$ in the stated finite-Tor category. The finite product construction of step 2 gives a genuine object $P$ with these components, and the componentwise inverse isomorphisms give $\omega_g\otimes^L_\Lambda P\simeq\Lambda_V\simeq P\otimes^L_\Lambda\omega_g$. Thus $\omega_g$ and its inverse belong to $D^b_{ctf}(V,\Lambda)$. No implication from geometric smoothness to cohomological smoothness is taken from the definition of cohomological smoothness; the required mathematical input is the theorem just cited.

Cited nodes: thm-pur-cohomological-smoothness, lem-pur-finite-clopen-derived-decomposition.

### Returned step 4

Define $C(g,s)=Ls^*\omega_g$ by the actual derived pullback [def-weil-derived-pullback-tensor-hom], and put $Q=Ls^*P$. The data of $C(g,s)$ are therefore fixed by a construction. The closed immersion $s$ is proper, hence separated and of finite type, by [lem-weil-pbc-closed-immersion-proper]. At finite coefficients apply [lem-sf-pullback-tor-amplitude] to each $F\in\{\omega_g,P\}$: the source and target schemes are finite type over $k$ and $F$ is bounded constructible with a finite Tor interval by step 3. It follows that both $Ls^*F$ belong to $D^b_{ctf}(B,A)$, with their original Tor bounds.

Cited nodes: def-weil-derived-pullback-tensor-hom, lem-weil-pbc-closed-immersion-proper, lem-sf-pullback-tor-amplitude.

### Returned step 5

At integral coefficients [lem-pur-integral-operations-preserve-constructible], clause 1, gives $Ls^*F\in D^b_c(B,\mathcal O_E)$ and identifies its $j$-th reduction with $Ls_j^*F_j$, where $F_j=F\otimes^L_{\mathcal O_E}A_{E,j}$. By [def-weil-finite-tor-amplitude], the $F_j$ have one Tor interval $[a_F,b_F]$ independent of $j$. Apply [lem-sf-pullback-tor-amplitude] at every $j$: it preserves exactly that interval, so all reductions of $Ls^*F$ satisfy the required common bound. The same definition therefore puts $Ls^*F$ in $D^b_{ctf}(B,\mathcal O_E)$. At the rational stage pullback is integral pullback on representatives; at the algebraically closed stage it is represented at a finite coefficient field [def-weil-derived-pullback-tensor-hom]. These operations preserve bounded constructibility, and at both field stages $D^b_{ctf}=D^b_c$ by [def-weil-finite-tor-amplitude]. Apply this to both choices of $F$.

Cited nodes: lem-pur-integral-operations-preserve-constructible, def-weil-finite-tor-amplitude, lem-sf-pullback-tor-amplitude, def-weil-derived-pullback-tensor-hom.

### Returned step 6

The pullback of the unit is the unit. At finite level [def-weil-derived-pullback-tensor-hom] computes exact inverse image of the constant sheaf, giving $Ls^*\Lambda_V\simeq\Lambda_B$. At integral level that construction and [lem-weil-constant-coefficient-objects-constructible], clause 2, compute this pullback as $R\varprojlim_j\operatorname{Res}_j(A_{E,j})_B\simeq\widehat{\mathcal O}_{E,B}$. Indeed clause 2 identifies all finite reductions of the completed unit with the finite constant units, and its derived completeness identifies the completed unit with this derived limit. At field levels apply rationalization to this integral isomorphism and then represent it at a common finite stage, as specified in [def-weil-derived-pullback-tensor-hom].

Cited nodes: def-weil-derived-pullback-tensor-hom, lem-weil-constant-coefficient-objects-constructible.

### Returned step 7

Apply $Ls^*$ to the two inverse isomorphisms in step 3. The tensor comparison of [lem-pur-derived-pullback-tensor-iso], applied to $(\omega_g,P)$ and $(P,\omega_g)$, and step 6 give
$$
 C(g,s)\otimes^L_\Lambda Q\simeq Ls^*(\omega_g\otimes^L_\Lambda P)\simeq\Lambda_B,
 \qquad Q\otimes^L_\Lambda C(g,s)\simeq\Lambda_B.
$$
The cited comparison includes the compatible finite-reduction construction of the integral map and its rationalized and common-stage images. At finite level it is stated in the ambient derived category, so its use does not presume tensor closure for arbitrary bounded constructible inputs. Steps 4 and 5 place the factors in $D^b_{ctf}(B,\Lambda)$; the displayed isomorphisms exhibit the claimed inverse there. Hence the actual pullback $C(g,s)$ is an object of its Picard groupoid, with no orientation chosen.

Cited nodes: lem-pur-derived-pullback-tensor-iso.

## Unfinished work

No part of this one-level repair is omitted. Both new tasks intentionally remain unsplit for separate workers. This delivery does not claim their future Lean proofs are finished. Server validation and delivery results are recorded after the checks complete.

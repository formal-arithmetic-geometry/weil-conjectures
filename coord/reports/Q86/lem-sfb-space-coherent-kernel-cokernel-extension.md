## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-kernel-cokernel-extension.json (item, split), citations.json, and report.md. No new nodes and no Mathlib leaves.

Attachments: none. The exact blueprint-tag search and the concept search in lean/WeilConjectures show scheme coherent-closure results, not a declaration proving this algebraic-space item. The statement and its statement dependencies are unchanged.

WANTED: none.

Return repaired: the delivered version used lem-sfb-space-coherent-abelian. Current main has landed that node with a proof using this item, so retaining the old argument closes a two-node cycle. The required initial dry run reproduced exactly that failure. I compared the sandbox with the current item and re-read the entire current statement and proof of lem-sfb-space-coherent-abelian, including its reviewed record. I removed every citation of that downstream node. The replacement follows the proof of Stacks 07UC: exact etale localization, the scheme closure theorem, and transfer back to every affine chart. For the extension clause it first obtains quasi-coherence of the unknown middle term from the existing space extension theorem. This is a substantive proof repair, not an unchanged re-push.

The current item has its original statement, source, creation metadata and blueprint ancestry. The proof now has four steps, of lengths 1439, 905, 1199 and 475 characters. No step exceeds 2000 characters. Every selected dependency has no dependency path to the item in current main. The delivery tool performs the actual rebase and authoritative server checks.

All previous Mathlib searches and their recorded results are retained. I read searches.jsonl; the scheme/module ambient abelianness, finite-presentation predicates and topological coherence hits do not state this theorem. Supplementary repair searches (also retained in the log and item) locate generic module pullback/adjunction infrastructure, not exact small-etale algebraic-space pullback. The supplementary Loogle query used an unknown identifier and is explicitly recorded as rejected, with no absence inference. No new node is proposed and no new Mathlib match is claimed.

Nothing remains mathematically unfinished for this one-level split. No Lean file, shared repository file or launcher file was written; no git command or compiler was run by the worker.

## New nodes

None. Existing generic and scheme nodes supply all inputs; the same-unit nodes lem-sfb-scheme-etale-module-exact-finiteness-comparison and lem-sfb-space-qcoh-extension-closed were especially useful. The space closure theorem lem-sfb-space-coherent-abelian is downstream and is not used.

## Not duplicates

No new nodes. The item and lem-sfb-space-coherent-abelian overlap as statements, but current main deliberately proves the latter using this item's explicit affine formulation. This repair supplies that prerequisite without duplicating it or changing the other worker's node. Existing same-tag searches and blueprint searches are retained from the earlier delivery. The inherited blueprint.from.node is null; the existing detailed from.place and via ancestry are preserved. A supplementary whole-blueprint search for etale exact pullback algebraic space module found no blueprint node under that phrasing.

## Review by Q86

I read spaces-cohomology.tex 07UB (lemma-coherent-Noetherian) and 07UC (lemma-coherent-abelian-Noetherian), particularly the exact restriction and scheme reduction in the proof. I also read spaces-properties.tex 03LV/03LW for etale pullback as exact restriction and 03M1(4) for extension closure, descent.tex 03DX/06VE(5) for the scheme comparison and exactness, coherent.tex 01XZ/01Y0 and modules.tex 01BY for scheme coherence and closure, properties.tex 01PB for affine finite generation, and the cited scheme-associated-module statements 01HV/01I9/01IA. These are the item sources; there are no new-node sources. The latest blueprint ctf-stability direct-image preservation context was checked, and the inherited support route is preserved.

Step 1: def-trf-algebraic-space explicitly identifies etale pullback with restriction to localized sites. The current statement of lem-pur-site-restriction-module-adjunction-exact gives exactness for arbitrary ring sheaves and arbitrary site objects, so it applies to O_Z and any affine chart; it is not a constant-coefficient-only result. The scheme equivalence states full faithfulness and the precise tensor-sections formula. The existing exact-finiteness-comparison node states exactness into the ambient small-etale module category, which the equivalence alone would not supply. The tilde-sections and tilde-pullback nodes give B tensor_R N, not just equality at identity charts. The site-local-presentation definition gives quasi-coherence on Z from these affine-cover descriptions. The affine finite-type statement and locally Noetherian coherence criterion turn finite N into coherent tilde N and conversely. The affine tilde/Gamma counit supplies the missing isomorphism for an arbitrary coherent H. The source chart R is Noetherian; hence V is locally Noetherian as required for 01XZ. No hypothesis on the base scheme S is added.

Step 2: the full-faithfulness statement lifts the actual restricted map. The scheme closure node explicitly gives ambient kernels and cokernels of coherent sheaves; the scheme coherence criterion makes these quasi-coherent, allowing the exact comparison node to be applied. Exactness of both the comparison and chart restriction identifies their kernels and cokernels with the actual ambient etale kernels and cokernels. Thus each affine etale chart has the required finite-module description. This is an argument through scheme closure, not a citation of an equivalent algebraic-space closure assertion.

Step 3: lem-sfb-space-qcoh-extension-closed explicitly assumes only quasi-coherent endpoints in an ambient exact sequence, so its statement really gives quasi-coherence of E without assuming it first. The equivalence then lifts E and both maps. I included the scheme quasi-coherent kernel and cokernel/image nodes because their statements ensure the lifted homology objects are quasi-coherent. Exactness of A_V sends those homology objects to zero; full faithfulness reflects zero by reflecting the vanishing identity. This justifies reflection of exactness without silently assuming the inverse restriction is exact on arbitrary module sheaves. The scheme coherent-closure node's extension clause then applies to H_F and H_G and proves H_E coherent; step 1 gives the specified affine formula. Every input here was read in its current statement, and citations.json quotes those statements verbatim.

Step 4: zero is represented by N=0, which is generated by the empty set; composition of chart isomorphisms proves isomorphism invariance with exactly the same finite module. It needs no descent lemma and is elementary.

Against delivery-errors B through E: no new unsplit node has a hidden proof, no new duplicate or item-clause node was created, and no unrun search is recorded. Every non-elementary input is an explicit cited node; generic exactness, affine comparison and coherent closure are not taken from definition nodes or from their proofs. I checked all 20 citation quotes against the current statement text. I checked all chosen dependency closures for paths back to this item, rather than assuming a previously unsplit sibling was safe. The long steps were inspected individually; none exceeds 2000 characters or hides a new independent lemma. The off-unit tools are declared in split_report.tool_uses as generic inputs required by the source's scheme reduction; same-unit comparison and extension results are reused directly.

Small cases: the empty space has vacuous chart conditions; the zero sheaf has its explicit zero-module model; identity maps yield zero kernel and cokernel; zero maps reproduce the endpoints. Split extensions on Spec(k) and Spec(k[epsilon]/epsilon^2) give the expected finite direct-sum modules. The non-split extension argument first establishes quasi-coherence and does not assume sectionwise surjectivity of an arbitrary sheaf epimorphism, which would be false. No statement dispute, changed hypothesis, or source error was found.

## Previous delivery report (superseded by this repair)

The following retained report records the returned head. Its claim that the sibling closure node has no dependency on this item was true of the then-read unsplit version and is false on current main. The repair above supersedes that proof and audit; its historical searches and citations were retained as input material.

> ## Worker report
> 
> Files written: dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-kernel-cokernel-extension.json (item, split), citations.json, and this report. No new nodes and no Mathlib leaves.
> 
> Attachments: none. Searches for the exact blueprint tag and for algebraic-space/coherent terminology in lean/WeilConjectures found no declaration giving this item. The scheme results do not give an attachment for algebraic spaces.
> 
> WANTED: none.
> 
> The statement is unchanged. The inherited empty proof is replaced by three steps: compare the explicit affine finite-module convention with the existing chart-coherence convention, reuse lem-sfb-space-coherent-abelian, and compose chart isomorphisms to prove isomorphism invariance. The pre-existing node already gives the substantial closure assertion, with an extra finite-sum clause. Reusing an existing node is preferable to creating another same-tag node. Its proof remains its own stage-1 item; this delivery does not claim to prove its unsplit dependencies or attach Lean.
> 
> The sandbox previously contained only searches.jsonl and dispatch markers. I retained and read all recorded search results and reused them. They concern FGModuleCat.instAbelian, Scheme.Modules.instAbelian, SheafOfModules.IsFinitePresentation and quasi-coherent presentations, or Topology.IsCoherentWith. These do not state closure for the coherent subcategory on a locally Noetherian algebraic space. The second semantic phrasing already recorded searches finite-presentation module sheaves on Noetherian etale sites. A further logged grep checks the sheaf presentation files. No search was invented and no unavailable service is treated as a negative result.
> 
> Nothing remains unfinished for this one-level split. No repository, launcher or Lean file was written, and no compiler or build tool was run.
> 
> ## New nodes
> 
> None. In particular, the existing same-unit node lem-sfb-space-coherent-abelian is reused, not cloned. No new Mathlib leaf is asserted.
> 
> ## Not duplicates
> 
> The item is essentially the existing lem-sfb-space-coherent-abelian with its chart definition expanded and with isomorphism invariance made explicit; the existing lemma also includes finite sums. I have not modified either node's maintainer fields or merged them. The maintainer may merge these two ids later. Whole-DAG searches by 07UC/07UB, coherent kernels/cokernels and extensions found this node, scheme-only lem-weil-pbc-coherent-modules-kernel-cokernel-sum, and the chart groupoid equivalence. Blueprint searches by coherent, 07UB, 07UC, coherent.*kernel and coherent.*extension found no imported blueprint statement of this closure lemma. The exact source ancestry command returned blueprint.from.node = None, which is the existing ancestry; it is retained rather than invented. The exact inherited from.place already records the supporting direct-image chain.
> 
> ## Review by Q86
> 
> I read spaces-cohomology.tex Tags 07UB (lemma-coherent-Noetherian) and 07UC (lemma-coherent-abelian-Noetherian), including the proof reducing to an etale scheme chart. 07UB equates coherence, quasi-coherence of finite type, and coherent scheme pullbacks. 07UC explicitly takes kernels and cokernels in module sheaves and includes extensions. The item's finite-module formula expresses that same convention. I also read coherent.tex Tags 01XZ (lemma-coherent-Noetherian) and 01Y0 (lemma-coherent-abelian-Noetherian), properties.tex Tag 01PB (lemma-finite-type-module), descent.tex Tag 03DX (proposition-equivalence-quasi-coherent), and spaces-properties.tex Tag 03LV and Equation 03LW for the ambient chart restrictions. The current latest blueprint direct-images proof (3) supplies the inherited preservation context; no source route was replaced. There are no new-node sources to audit.
> 
> For step 1 I opened each cited statement. def-trf-space-quasi-coherent-module defines precisely site-local presentations, so quasi-coherence on affine chart covers implies quasi-coherence on Z. lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies the associated sheaf with a Zariski quasi-coherent module and states that the inverse is restriction to opens, with identity on their sections. This is exactly the comparison needed here, not a cohomology-only comparison. lem-weil-pbc-quasi-coherent-finite-type-affine states finite type iff affine sections are finitely generated, and its covering clause propagates finite type from affine opens. pqf-lem-coherent-ft-locnoeth equates coherent with quasi-coherent finite type. Each chart is locally Noetherian by the hypothesis on Z, so the latter criterion applies. Reading lem-sfb-space-coherent-abelian confirms that its convention is quasi-coherence together with coherent scheme-chart pullbacks, exactly what the comparison proves. No assertion about arbitrary non-quasi-coherent sheaves is taken from the scheme equivalence.
> 
> For step 2 I read the actual statement of lem-sfb-space-coherent-abelian: it supplies the zero object, kernels and cokernels in module sheaves, and all extensions, under the same scheme-base and locally Noetherian algebraic-space hypotheses. It assumes neither properness, quasi-compactness, separation nor finite dimension. The step uses its statement alone, not its missing proof. This is reuse of an already existing broader node, so none of the content was moved into a new lemma.
> 
> Step 3 is elementary in the literal affine formula of the item. An isomorphism on a chart composed with the chosen description yields that same description for the other sheaf; the identical finitely generated module N works. The inverse isomorphism proves both directions. No descent theorem or closure theorem is hidden here. All non-elementary steps have explicit node citations and their verbatim full-statement quotes in citations.json. Each step is shorter than 2000 characters, so no step exceeds the long-step threshold.
> 
> I checked B through E: no new nodes need standalone statements or searches; the existing statement and its definition dependencies are retained; quoted tags agree with the local labels; no plain-tag citation substitutes for a theorem; the closure node is already in the DAG and has no dependency on the item. I checked the zero sheaf, identity and zero morphisms, split extensions and the empty algebraic space. The chart condition is isomorphism-invariant in all of these cases. No Noetherian condition on the base S is introduced, and no Noetherian condition on an arbitrary ambient ring is used. There was no statement dispute or counterexample and no correction to the statement.
> 
> The generic off-unit tools are the Zariski/etale quasi-coherent equivalence, the affine finite-type criterion and the locally Noetherian scheme coherence criterion. They compare conventions only; they do not replace a unit's direct-image route. They are declared in split_report.tool_uses for the maintainer to approve. The site-local quasi-coherence citation is a definition. The substantial closure lemma itself belongs to this same unit.
> 
> Corrections made during self-review: step 1 now explicitly cites the closure node whose convention it compares, and it spells out why quasi-coherence holds before applying the equivalence. I avoided the tempting but invalid shortcut of using only the groupoid equivalence, whose statement would not by itself prove coherence of an arbitrary extension in the ambient module category. There is no second worker in this direct-delivery assignment; this section is my signed self-review for the maintainer's independent reading.
> 
> Dry-run repair: the first full preflight rejected the phrase “as in the item” in step 2 as non-self-contained. I replaced it with the explicit ambient category of module sheaves on the small etale ringed site. The mathematics and citations are unchanged.

# Q67 stage-1 repair: thm-pur-rational-and-qbar-purity

## Files written

- `dag/nodes/sec-smooth-purity/thm-pur-rational-and-qbar-purity.json`: existing statement node, unchanged statement and Lean attachment; four-step assembly, 2267 proof-text characters (returned version: 6019).
- `dag/nodes/sec-smooth-purity/lem-pur-rational-lattice-adic-domain.json`: new statement, unsplit; no Mathlib match. Extracts returned Steps 1a and 1b.
- `dag/nodes/sec-smooth-purity/lem-pur-rational-scalar-comparison-identification.json`: new statement, unsplit; no Mathlib match. Extracts the construction identifications and finite-extension equations of returned Steps 1c, 1d and 2.
- `dag/nodes/sec-smooth-purity/lem-pur-common-stage-smooth-operation-identification.json`: new statement, unsplit; no Mathlib match. Extracts the common-stage identification and representative/inverse argument of returned Steps 3a and 3b.
- `report.md` and `citations.json`: review signature, full argument preservation and verbatim statement quotations. Local search-plan, raw search outputs and searches.jsonl preserve the research; returned-node.json is an exact read-clone snapshot used for comparison.

All three new nodes have self-contained statements, empty proof and proof_deps, null proof_origin, source places, the item's chapter and unit, blueprint.from at this item with empty via, and same_as=[] after whole-DAG/blueprint searches. They are tasks for other workers, not claimed proofs.

## Attachments

None. I read `lean/WeilConjectures/EtaleCohomology/Purity/Smooth/Rational.lean`: the declaration at line 77 explicitly packages an assumed compatible finite family and arbitrary realizations. Its own docstring says it does not state this item. It does not supply the specified source/target functors or the Qbar clause. The attached canonical module `lean/Sheaf/Paper/RationalSmoothPurityCanonical.lean` contains sorry in supporting constructions and in rationalIso_scalar (line 844); thus its rationalIso/commonIso definitions are not evidence that the item is finished. Existing Lean metadata is retained, with no Lean editing or compilation.

## WANTED

None. The current blueprint statement/proof, unit, existing interface statements and their source records are available locally. The extracted identifications are marked as agent work, rather than attributed to a nonexistent Stacks theorem.

## What was wrong and what changed

This is the batch5 re-split requested on 2026-10-22. The retained sandbox was empty apart from dispatcher marker files; the first required dry run exited with “no node files”. The current read clone contains exactly the seven steps and 6019 proof-text characters described in the return. I copied that version, preserving its statement, searches, import flags, blueprint_update, review records and Lean record. There was no prior local report or search log to discard. No git command was run in the shared clone.

The earlier repair merely cut long paragraphs into seven shorter steps. This repair creates three independently stated argument tasks. Their argument allocations are approximately 1064 characters (lattice domain), 1946 plus the source/target identifications from 1c/1d (finite coefficient comparisons), and 1527 characters (common-stage identification/descent). None states unconditional rational or Qbar smooth purity: the first has no purity morphism at all, the second takes the compatible integral transformation as input and identifies comparison constructions, and the third identifies descent with specified operations and treats an arbitrary supplied compatible transformation. Existence of the actual adic family and assembly into the purity isomorphisms stay in the parent. The three jobs thus address separate arguments instead of moving the whole theorem into one replacement.

The statement is unchanged, including all coefficient categories and lattice hypotheses. I read blueprint_update and the main-20261015 proof; the route remains lattice -> adic family -> scalar localization -> finite extension -> common-stage descent. I did not cite the downstream transitivity/summands theorem, which depends on the item. No target, chapter or unit statement is changed. This item is not the unit's key node, so no unit realization file is written.

## Searches and Not-Mathlib verdicts

Every new node has leanfinder, loogle, grep and leansearch records made by the required msearch.py command, including a second semantic phrasing. Raw hits are retained in search-domain-*.txt, search-comparison-*.txt and search-common-*.txt. The exact queries and outcomes are copied from searches.jsonl. The common-stage LeanSearch request returned a rate-limit error and is recorded as unavailable, not no-match.

For the domain node, the first Finder and LeanSearch results concern finite/integral morphisms and rings; the second Finder results characterize cohomological bounds in an abstract derived category. They do not give a uniform Tor interval for all DVR reductions or identify the two integral constructible presentations. Loogle and grep found no match.

For the scalar node, Finder gave generic localized counit formulas, module-sheaf adjunction counits, and ordinary sheaf pullback associativity/free-module formulas. Loogle gave conjugateEquiv_counit and conjugateEquiv_counit_symm. Those express the generic mate identity, but neither identify the specified strict-tower, completed-tensor and rational constructible operations nor prove their coefficient comparison agreement. LeanSearch gave ring/module localization and integrality. Grep found no completed smooth purity comparison. These cannot specialize in one line to the node's comparison assertion.

For the common-stage node, Finder gave geometric Spec/Proj pullback identities, ordinary module-sheaf pullback comparisons and adjunction conjugation, not a filtered category of coefficient stages or its specified upper-shriek action. Loogle and grep found no match. Generic descent itself is already reused through prop-weil-pbc-descent-functors, rather than being introduced as a new generic lemma.

Before creating the nodes I searched dag/nodes by lattice/Tor, purity/scalar, common-stage/exceptional and rational comparison keywords, and ran blueprint_refs.py ancestor plus searches for lattice, scalar, descent, common-stage, uniform Tor and scalar comparison. I read the statements of the nearby nodes listed below, and searched the project Lean source by the item tag and the same notions. No existing node gives these complete construction-identification interfaces.

## Not duplicates

lem-pur-rational-lattice-adic-domain vs lem-coef-integral-residue-tor: the latter starts in the detailed derived-complete category; the new node starts with every integral representative in the separate rational-category presentation and discharges the geometric and presentation hypotheses before reaching the uniform Tor conclusion.

lem-pur-rational-lattice-adic-domain vs lem-weil-pbc-integral-stratified-perfect-characterization: the latter identifies integral presentations on an already noetherian finite-dimensional base; it does not give the finite-Tor interval of all reductions from the residue cohomological interval or discharge the finite-type-field geometric domain.

lem-pur-rational-lattice-adic-domain vs lem-weil-pbc-finite-type-over-noetherian: the latter gives noetherianity only, without finite dimension, invertibility, integral-category comparison or finite Tor amplitude.

lem-pur-rational-lattice-adic-domain vs lem-kun-dimension-finite-type: the latter only gives finite dimension, not the integral coefficient-domain identification or uniform Tor conclusion.

lem-pur-rational-scalar-comparison-identification vs lem-pur-adic-purity-scalar-naturality: the latter supplies the integral family and integral comparisons; the new conditional statement identifies their localizations with the specified rational operations and exceptional coefficient mate, retaining the strict-tower/ordinary-tensor comparison and both rational squares.

lem-pur-rational-scalar-comparison-identification vs prop-weil-pbc-rational-transport: generic localization of a supplied linear transformation does not identify the smooth source comparisons, completed scalar functor or the defining exceptional mate.

lem-pur-rational-scalar-comparison-identification vs lem-pur-semilinear-scalar-localization: this is the generic equation-preservation tool for supplied semilinear functors and transformations; it does not identify the concrete strict integral scalar extension with ordinary completed tensor, or the resulting rational exceptional comparison with its specified adjunction mate. The new task must use it, not repeat its proof.

lem-pur-rational-scalar-comparison-identification vs lem-weil-finite-free-completed-scalar-comparison: the latter states chi for scalar extension but has no smooth functors, rationalization, exceptional mate or purity comparison equations.

lem-pur-rational-scalar-comparison-identification vs sk-lem-sp-field-extension: that node concerns the separately constructed smooth-purity right adjoint from det-sp-integral-adjunction-bijection. The new node starts with the actual coefficient-system exceptional functor and a supplied compatible integral family; it identifies the concrete comparison maps, not merely an isomorphic right adjoint.

lem-pur-rational-scalar-comparison-identification vs det-sp-field-extension-towers: that node uses the separately constructed H=f! smooth right adjoint and ell-power towers. The new node identifies the raw rationalization of the completed ordinary-tensor/system construction and its specified mate and inverse square for the original exceptional functor.

lem-pur-common-stage-smooth-operation-identification vs prop-weil-pbc-descent-functors: generic descent accepts arbitrary comparison data; the new statement proves that the particular source and exceptional comparisons give the already specified common-stage operations, including their morphism actions. The generic descent assertion alone does not identify those data.

lem-pur-common-stage-smooth-operation-identification vs def-weil-derived-pullback-tensor-hom: the latter defines the common-stage pullback and tensor actions using their own theta comparisons; the new identification relates the composite pullback/twist/shift comparison a to that action and simultaneously treats upper shriek.

lem-pur-common-stage-smooth-operation-identification vs def-weil-exceptional-inverse-image: the latter defines upper shriek using the coefficient-system adjoint comparisons, not an assertion that descent with an independently supplied integral purity helper's b agrees with this definition. The new task includes that identification, at the level of functors and maps.

lem-pur-common-stage-smooth-operation-identification vs sk-thm-sp-qbar: that node states a smooth pullback adjunction; it does not identify the descent with the fixed exceptional functor on all common-stage representatives.

## Review by Q67

I read AGENTS.md, GOAL.md, the worker brief, stages/1-dag.md, the three-level and unit-route rules of SETUP.md, the item's chapter and unit records, and delivery-errors B–E. My source for the item and each extracted node is the current main-20261015 rational-and-Qbar proof, Steps 1–2, read together with the explicit seven-step returned argument below. The old master source and blueprint_update say the same coefficient-passage goal. The source does not justify invoking the downstream transitivity node here: the integral compatible-family statement is the acyclic replacement already present in the accepted argument.

For new parent Step 1 I checked the full statements of the lattice-domain node, thm-pur-adic-reconstruction and lem-pur-adic-purity-scalar-naturality. The first gives exactly the previously missing finite-Tor domain on both schemes. The reconstruction theorem assumes separated finite-type k-schemes, smooth separated pure relative dimension d>=0 and a uniform finite-Tor lattice; all are now available. It gives pointwise reconstructed maps without uniqueness. The helper explicitly gives a simultaneous exact linear natural family with these reductions and coefficient equations. I take that family, not an arbitrary reconstructed lift. A torsion lattice is allowed: no flat lattice hypothesis has been added.

For Step 2 I checked prop-weil-pbc-rational-transport's first paragraph: it extends supplied exact linear functors and every transformation on all localized morphisms. The scalar-comparison node identifies the localized source and target with exactly the rational pullback/twist/shift and exceptional operations, retaining their shift comparisons. The inverse is the image of the integral inverse, so its two identities follow by functoriality. The raw localization has the same objects as the integral category; a rational isomorphism between two presentations is a morphism of that category, so the extended naturality square, rather than a nonexistent equality of lattices, gives presentation independence. I read the rational clauses of the operation and twist definitions to verify the object and map formulas used by this extraction.

For Step 3 I checked that the scalar node uses ordinary tensor over the completed ring sheaves, with chi identifying it with the strict inverse-limit scalar extension on derived-complete inputs. The finite-free comparison lemma explicitly has this derived-completeness hypothesis and concludes chi is a natural isomorphism, including ramified extensions. I read the integral helper's typed a/b equations and its definition of b as the compact-support counit transpose. I also read the coefficient-system-adjoint statement and the upper-shriek definition's coefficient-passage paragraphs: equality with that defining mate is a real identification task, now stated explicitly in the new node, not an arbitrary replacement of the common-stage map. Generic semilinear scalar localization preserves equations and whiskering; it does not establish this construction comparison by itself. The displayed inverse square has correct type G_F(TK) -> T(H_EK), and follows by multiplying the forward square by the four specified inverses. Identity, triple-extension associators and shift comparisons are kept, rather than suppressing them before descent. These are the precise hypotheses in the statement of prop-weil-pbc-descent-functors.

For Step 4 I checked the common-stage node's statement, not a proof hidden in a definition. It identifies both descended functors on objects and common-stage morphisms, and treats an arbitrary compatible transformation and its inverse. In the formula u:T_{M/E}K -> T_{M/F}L, a_{M/E} is applied first and a_{M/F}^{-1} last, with the analogous b formula, so the displayed actions have the required source and target. The exceptional mate identification is inherited from the preceding comparison task. The generic descent theorem explicitly descends transformations AND their equations; hence the two identity composites remain identities of common-stage arrows. The new task's identification with the specified twist and exceptional operation supplies the final target interpretation; it does not claim unconditional purity as a replacement theorem.

I tested the statements at T empty, K0=0, a torsion lattice O_E/(varpi), d=0 (including the identity morphism), E=F, a ramified E subset F, a three-field tower, and a common-stage arrow represented over two different enlargements. The torsion example has first derived reduction in two adjacent degrees, so the node allows an interval rather than falsely demanding a degree-zero flat lattice. For the identity extension the tensor unitor is retained before writing identities. For d=0 the twist and shift are the unit and zero shift; the formulas reduce to ordinary scalar naturality. For ramified extensions chi, rather than identifying the quotient indices by definition, handles completion. Every comparison assertion is a derived-category/natural-functor identification, not just cohomology in each degree.

The B–E audit found no new missing-object shorthand: all primes, finite fields, schemes, categories, uniformizer reductions and transformations are introduced. Every bracketed notion has a statement dependency. No new node contains proof steps or an inline proof. The new results assert domain or construction comparisons, while the parent actually produces the purity isomorphisms. Existing nodes are reused for noetherianity, dimension, integral category comparison, residue Tor, integral naturality, scalar localization and generic descent; their arguments are not duplicated. citations.json contains a verbatim statement part for every parent-step citation. The old seven steps below remain complete material for the workers of the three new tasks, so this repair neither deletes an argument nor calls a shortened sketch a split. The four parent proof texts total 2267 characters, and no parent step exceeds 2000. No prohibited source route, repository write, compiler, Lake, or agent spawning was used.

## Argument destination map

| Returned step | Argument retained as a task or assembly |
|---|---|
| 1a, 528 characters | lattice-domain node: noetherian field base, finite-type noetherianity, finite dimension, ell invertibility, rational-category domain |
| 1b, 536 characters | lattice-domain node: equality of integral presentations, completeness, residue cohomological interval and uniform Tor interval, including torsion |
| 1c, 656 characters | parent Step 1 applies reconstruction and the simultaneous family; scalar-comparison node fixes the same integral functors and coefficient comparisons as its input |
| 1d, 826 characters | scalar-comparison node identifies localized functors; parent Step 2 applies transport, maps the inverse and checks lattice independence on all rational arrows |
| 2, 1946 characters | scalar-comparison node: ordinary vs strict scalar extension, chi, correct mate, rational square, inverse square, units/associators/shifts |
| 3a, 838 characters | common-stage node: comparison-based action on representatives, representative/enlargement independence and agreement with defined operations; parent Step 4 applies it |
| 3b, 689 characters | common-stage node: transformation representatives and inverse equations, identification with Qbar operations; parent Step 4 takes the two composites |

## Preserved returned argument (verbatim)

### Returned step 1

Step 1a (geometric domain). The field $k$ is noetherian, since its only ideals are $0$ and $k$. Apply [lem-weil-pbc-finite-type-over-noetherian] to the structure morphisms of $X$ and $Y$, and [lem-kun-dimension-finite-type] over $k$. Thus both schemes are noetherian and finite-dimensional. Since $\ell\ne p$, $\ell$ is invertible on them. They therefore satisfy the scheme hypotheses in [def-weil-pbc-rational-category]. Choose an integral lattice $K_0$ presenting the given rational object and write $Q_E$ for rationalization.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, def-weil-pbc-rational-category.

### Returned step 2

Step 1b (uniform Tor domain). By [lem-weil-pbc-integral-stratified-perfect-characterization], the integral category underlying the rationalization is exactly [def-weil-derived-complete-integral-detailed] on these schemes. In particular $K_0$ is derived complete and its first reduction is bounded; choose an interval $[r,s]$ containing its cohomology. By [lem-coef-integral-residue-tor], every reduction has Tor amplitude in that same interval. Consequently $K_0\in D^b_{ctf}(Y,\mathcal O_E)$, including when $K_0$ is a torsion lattice.

Cited nodes: lem-weil-pbc-integral-stratified-perfect-characterization, def-weil-derived-complete-integral-detailed, lem-coef-integral-residue-tor.

### Returned step 3

Step 1c (compatible integral choice). Set $H_E=Lf_E^*(-)(d)[2d]$ and $G_E=Rf_E^!$. The preceding domain checks and the stated smooth separated pure-dimensional hypotheses allow [thm-pur-adic-reconstruction] to be applied to every lattice. It supplies an integral isomorphism with the prescribed finite reductions, without uniqueness of coherent lifts. Choose the simultaneous family $\gamma_{E,K_0}:H_EK_0\to G_EK_0$ supplied by [lem-pur-adic-purity-scalar-naturality]. Its statement supplies the exact linear functors, integral linear naturality and coefficient compatibility, with exactly those reductions. All subsequent maps use this compatible choice.

Cited nodes: thm-pur-adic-reconstruction, lem-pur-adic-purity-scalar-naturality.

### Returned step 4

Step 1d (localization). Apply [prop-weil-pbc-rational-transport] to the exact integral linear functors $H_E,G_E$ and their chosen natural transformation. It extends the transformation to all localized morphisms, with component $Q_E(\gamma_{E,K_0})$. The rational pullback and tensor formulas of [def-weil-derived-pullback-tensor-hom] and the rational twist of [def-coefficient-twists-detailed] identify its source with $Lf_E^*(Q_EK_0)(d)[2d]$; [def-weil-exceptional-inverse-image] defines its target as $Rf_E^!(Q_EK_0)$. The inverse is $Q_E(\gamma_{E,K_0}^{-1})$: the two inverse identities follow by functoriality. Naturality, supplied for all rational morphisms by the cited transport theorem, applies in particular to rational isomorphisms between lattice presentations, so these components are independent of presentation.

Cited nodes: prop-weil-pbc-rational-transport, def-weil-derived-pullback-tensor-hom, def-coefficient-twists-detailed, def-weil-exceptional-inverse-image.

### Returned step 5

Step 2 (finite extensions and their equations). For $E\subset F$, let $T_{F/E}$ be [prop-weil-pbc-scalar-extension]. The helper's integral $C_{F/E,W}$ is ordinary tensor by the completed coefficient sheaf, as is the integral functor underlying this $T$. The natural isomorphism $\chi$ of [lem-weil-finite-free-completed-scalar-comparison] identifies it with the strict inverse-limit scalar extension of [def-weil-integral-scalar-extension]; its hypothesis holds because the lattices are derived complete. Thus there is no identification of these two constructions by definition alone. Work in the helper's ordinary-tensor presentation, whose associator is precisely the tensor associator specified in [prop-weil-pbc-scalar-extension]. For the simultaneously chosen integral family of Step 1, rationalize the natural comparison equation of [lem-pur-adic-purity-scalar-naturality]. Since $T_{F/E}=Q_FC_{F/E}$ on integral representatives, this gives, on every object,
$$b_{F/E,K}\,T_{F/E,X}(\gamma_{E,K})=\gamma_{F,T_{F/E,Y}K}\,a_{F/E,K}.$$
For the coefficient-passage exceptional functor defined in [def-weil-exceptional-inverse-image], use the rationalized integral $b$ as its scalar comparison. The helper identifies that integral map with the adjunction mate and proves its coherence, so no independent Verdier-duality comparison is needed. The twist comparison is the coefficient comparison of [def-coefficient-twists-detailed]. The identity and composition equations in the integral helper remain equations after applying rationalization; the helper also gives shift compatibility of both exact comparisons. Hence the displayed equation respects the unit, shifts and associators of [prop-weil-pbc-scalar-extension]. Solving it for inverses gives
$$T_{F/E,X}(\gamma_{E,K}^{-1})\,b_{F/E,K}^{-1}=a_{F/E,K}^{-1}\,\gamma_{F,T_{F/E,Y}K}^{-1}.$$
Thus both the purity family and its inverse satisfy the finite-stage compatibility required for descent.

Cited nodes: prop-weil-pbc-scalar-extension, lem-pur-adic-purity-scalar-naturality, def-weil-exceptional-inverse-image, def-coefficient-twists-detailed, lem-weil-finite-free-completed-scalar-comparison, def-weil-integral-scalar-extension.

### Returned step 6

Step 3a (common-stage descent). In [def-weil-pbc-qbar-category], objects are pairs $(E,K)$ and morphisms are common-stage classes $[M,u]$. Apply [prop-weil-pbc-descent-functors] to the rational exact families $H_E,G_E$, using the comparisons $a,b$ of Step 2. That step verifies precisely the unit, associator and shift hypotheses for both families, and the compatibility square for $\gamma$. The theorem explicitly descends compatible natural transformations and their equations, not just functors. It therefore descends this family to a natural transformation $\overline\gamma:H\Rightarrow G$, with component represented by $\gamma_{E,K}$. Its representative formula gives the functor actions $a_F^{-1}H_M(u)a_E$ and $b_F^{-1}G_M(u)b_E$; independence of enlargement and of the class representative is part of the cited descent assertion.

Cited nodes: def-weil-pbc-qbar-category, prop-weil-pbc-descent-functors.

### Returned step 7

Step 3b (inverse and conclusion). The inverse family satisfies the coefficient square established in Step 2, so [prop-weil-pbc-descent-functors] descends it too, along with the equations $\gamma_{E,K}^{-1}\gamma_{E,K}=1$ and $\gamma_{E,K}\gamma_{E,K}^{-1}=1$. Hence $\overline\gamma$ is an isomorphism. The common-stage pullback, tensor and twist definitions in [def-weil-derived-pullback-tensor-hom] and [def-coefficient-twists-detailed], and the coefficient-passage exceptional functor of [def-weil-exceptional-inverse-image], identify $H(K)=Lf^*K(d)[2d]$ and $G(K)=Rf^!K$. These are the claimed $\Qlb$ purity maps, transported from the rational maps and independent of the finite stage.

Cited nodes: prop-weil-pbc-descent-functors, def-weil-derived-pullback-tensor-hom, def-coefficient-twists-detailed, def-weil-exceptional-inverse-image.

## Unfinished work and validation

The three new statements are intentionally unsplit, as the return requires. No part of their proofs is claimed complete. The repaired parent is ready for the required server dry run, with each cited statement quoted verbatim. Validation outcomes are appended after the tool exits.

Server dry run: `deliver.py Q67 thm-pur-rational-and-qbar-purity --no-push` exited 0 with `OK (not pushed)` at 674cfc90832. The server preflight passed, including the required DAG and split checks. The read-clone item still matches returned-node.json exactly. There are three new unsplit statements and zero Mathlib leaves.

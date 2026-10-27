# Stage-1 worker report

Q19, 2026-10-22. Item: lem-sfb-standard-proj-twist-tensor. Direct delivery; the review below is my own check, with independent maintainer review to follow.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-standard-proj-twist-tensor.json: statement unchanged, seven proof steps, existing generic prerequisites reused; not a Mathlib leaf.
- citations.json: 33 entries, one verbatim statement quotation for each proof-step/node pair.
- report.md: this report. searches.jsonl is the search command's actual log.

No new nodes and no new Mathlib leaves. An initially drafted localization node was removed before delivery: multiplication by a homogeneous unit and its explicit tensor inverse are elementary calculations within the item, not separate queue items. None of that proposed node's statements or proofs is delivered.

## Attachments

None for the complete item. I searched lean/WeilConjectures by the exact blueprint tag and by tensor/twist/graded-module terminology, and read ProjectiveSpectrum/Twist/TensorObj.lean:184 and TensorIso.lean:75 onward. AlgebraicGeometry.Proj.nonempty_tensorObj_twist_iso and Proj.twistTensorIso cover tensor products of the structure twists on a degree-one cover. They do not assert the comparison for an arbitrary graded module M, or its full naturality. ProjectiveSpace/Resolution.lean's arbitrary sheaf is tensored with two twists; it is not the associated sheaf of M(n). No set of these declarations states every clause of this item, so this is not an ATTACH. I did not write or compile Lean.

## Wanted sources

None. The proof sources are locally available.

## Findings and unfinished work

The imported statement agrees with Stacks 01MT, using the local calculation of 01MS and the actual canonical multiplication maps preceding them. No hypothesis or conclusion is changed. In particular, generation of S by finitely many degree-one elements, Noetherianity of S_0, and finite generation of M are not needed; the given degree-one open cover is enough. No statement dispute was found.

The original item had no proof and no proof dependencies. Its inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor prints None. The existing from.place names det-thm-sf-ctf-stability-direct-images (3) and the long alteration/Hilbert-polynomial/section-tail prerequisite chain. I retained that provenance rather than replacing it with an unrelated blueprint ancestor. The current main-20261015 six-functor unit and direct-image proof were read, as were the recorded chapter/unit. This item is a coherent-sheaf tool below that route; it is not the unit's key node, and no realization record or unit route is changed.

All one-level mathematical work is complete. The existing prerequisites may still have their own open proof work; I do not identify an upstream sorry declaration with a completed proof. The first required dry run passed at 907f076a9b9. I then made the global inverse gluing in steps 4--5 explicit; the final dry run and push use this revised proof and its 33 quotations.

## Sources and searches

## Not duplicates

No new/existing-node pair needs duplicate clearance because no new node is delivered. Whole-DAG searches included 01MT, 01MS, equation-multiply, shifted associated sheaves, localized twists, and multiplication. Whole-blueprint searches included standard projective twists, localized degree-one generators, tensor/degree-zero localization, twisting, graded modules, and lem-pc-twist-tensor. I read the matches rather than treating titles as statements.

The blueprint lem-pc-twist-tensor is about a polynomial ring and its glued projective-space twists, and has no arbitrary-module clause. The P^1 twist-product and twist-multiplication nodes also specialize the ring. The trace-formula common-degree invertibility and nonvanishing nodes assert twist-only facts, with a quasi-compact/fixed-degree open in the former. None states this complete item; none is put into same_as. The broad existing Proj-sheaf, topology, basis-morphism and functoriality nodes are reused instead of recreated.

All five creator searches are retained unchanged. Every additional mathlib_searches entry records the exact tool/query and the raw JSON summary from searches.jsonl. I used LeanFinder twice on localized-degree formulations and again on the full sheaf statement, plus LeanSearch, Loogle and grep. The malformed Loogle pattern containing the unknown identifier `graded` is recorded as unavailable, and was followed by valid Loogle queries. No service failure is treated as evidence of absence. The returned HomogeneousLocalization.Away.isLocalization_mul is a localization-of-chart-ring statement; Proj.lift_awayMapₐ_awayMapₐ_surjective is a surjectivity statement for two chart rings, not a graded-module twist isomorphism. I read their source in Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean and AlgebraicGeometry/ProjectiveSpectrum/Proper.lean. Generic localization/tensor declarations do not construct the item's sheaf comparison in one line. The source grep found no twist or arbitrary graded-module tilde construction in Mathlib's Proj directory. The item therefore remains a split, not a Mathlib leaf.

## Review by Q19

I read constructions.tex around equations equation-multiply and equation-multiply-more-generally and both statements and proofs of lemma-when-invertible (01MS) and lemma-apply-modules (01MT), checking the tags against stacks-project/tags/tags. The proof is the source's multiplication-by-f argument with the omitted inverse and sheaf-map checks written out. I also read the basis-equivalence statement in sheaves.tex (009O), module sheafification in sites-modules.tex (03CY), and the actual statements of every cited node. For the generic basis-extension tool I additionally read Mathlib/Topology/Sheaves/SheafCondition/Sites.lean:240--266, whose presheaf-source extension and isomorphism detection are precisely what the node states.

Step 1 uses the standard-open node's clause (0) for the basis and intersections. The graded-module-sheaf existence node really states the chart sections, restriction formula and quasi-coherence, including for the separately shifted modules. The twisting definition explicitly fixes M(n)_d=M_{n+d}; hence the target chart is (M_h)_n with this sign, not (M_h)_{-n}. No affine tensor-sections comparison is silently assumed.

Step 2 uses the actual sectionwise tensor definition, module sheafification's unique factorization, and the basis-morphism node with a presheaf source. I checked its hypotheses with the underlying abelian-group category: the target is a sheaf, and positive homogeneous standard opens form the basis. The restriction calculation with g^e=ch is written explicitly and is exactly the formula in clause (a) of the existing Proj-sheaf node, applied to each shifted module. Linearity of the extended map is checked after restriction, so the basis theorem is not being cited as an unmentioned theorem for varying coefficient rings. The resulting maps are the fraction-product maps of the statement, not arbitrary isomorphisms.

Step 3 uses the standard-open inclusion node's explicit conclusion that f is a unit of S_h when D_+(h) is contained in D_+(f). Multiplication by f^r and f^{-r} gives the two inverse maps for every integer r; the equations work in localizations with zero divisors as well. The same basis-extension node turns these compatible maps into sheaf trivializations. The invertible-module definition requires quasi-coherence as well as local rank one, and step 1 has already supplied quasi-coherence. This avoids using an invertibility definition as a theorem proving the local calculation.

Step 4 is the substantive arbitrary-M calculation. The inverse y maps to (f^{-n}y) tensor f^n lands in degree zero in its first factor. The basis node states extension to any sheaf target and uniqueness, exactly as used to define beta_f and prove alpha beta_f=1. On an overlap the degree-zero scalar c=(g/f)^n moves from the first tensor factor to the second by balancing, proving beta_f=beta_g without assuming a tensor-sections comparison. Negative n is allowed because both f and g are units there.

Step 5 glues these actual local inverses using the sheaf axiom. For the other composite, the balancing identity uses scalar tf^{-n} in (S_h)_0. It first proves equality on pure tensors of the global sectionwise tensor presheaf, then additivity, basis extension and the global module-sheafification universal property prove beta alpha=1 on the sheaf tensor. A genuine subordinate basis is built: the degree-one cover itself need not be a basis or a finite cover. This formulation avoids an implicit interchange of restriction and sheafification, and never claims all sheaf tensor sections are global pure tensors. The binary twist multiplication is M=S(a), n=b, with S(a)(b)=S(a+b), and its canonical map was already pinned in step 2. No new lemma restates either clause of the item.

Step 6 checks the actual unit and associativity maps on local pure tensors. O_X(0) and the structure sheaf have the same basis sections and restrictions by the Proj and twisting definitions. The only algebra is the identity/associativity and commutativity of localized scalar multiplication. Multilinearity and the two previously cited uniqueness properties give equality of the sheaf maps. Step 7 uses lem-sc-p1-proj-tilde-functorial's statement: despite its historical P^1 id, it is explicitly for every graded ring and degree-preserving map. Its fraction formula makes the naturality square phi(vu)=v phi(u), which is then extended by the same uniqueness argument. I did not take functoriality from the proof of a node that only states existence.

The four generic off-unit theorem uses are declared in split_report.tool_uses: Proj-sheaf existence, standard-open topology, morphisms on a basis and tilde functoriality. They implement this coherent-sheaf prerequisite; they do not replace a step of the six-functor route. Definitions and the existing module-sheafification leaf supply the other notions.

I checked delivery-errors B--E individually against the files. B1--B10: zero new nodes, no proof hidden in an unsplit node, exact existing statement/provenance retained, sources identified by tags/labels, only actual logged searches appended, no spurious Mathlib match or attachment. C1--C8: all non-elementary inputs are explicit node citations, each cited statement was opened, all 33 quotations are verbatim, and generic off-unit uses are declared; no dependency is derived from another node's proof. D1--D5: the seven steps carry the construction and inverse argument, and no clause is merely transferred to a new node. E1--E7: the localization, grading sign, basis, sheafification and coefficient-ring hypotheses are checked above; no Noetherian, finite-type, flatness, domain or finite-cover assumption is inserted. All seven steps are below 2000 characters; none conceals a separate standard comparison.

Small cases checked: M=0; M=S(a) with a negative (which gives the binary twist product with the correct sign); torsion modules such as M=S/(f), which vanish after localizing at f; a nonreduced degree-zero ring in S=A[t]; nilpotent f giving an empty chart; and X empty, including a ring concentrated in degree zero. The argument uses the cover only locally and also applies to an infinite degree-one cover. The cover hypothesis is essential: for S=k[t] with deg(t)=2, Proj(S) is a point but O(1) has zero chart module, so invertibility would fail without it. The stated hypothesis excludes precisely that failure.

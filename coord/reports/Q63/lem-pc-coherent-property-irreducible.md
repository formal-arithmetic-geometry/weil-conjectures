## Worker report

Files written: dag/nodes/sec-picard-framework/lem-pc-coherent-property-irreducible.json (item, statement unchanged, short assembly); dag/nodes/sec-picard-framework/lem-pc-coherent-supported-property-devissage.json (statement, unsplit, no Mathlib match); dag/nodes/sec-picard-framework/lem-pc-coherent-rank-one-property-ideals.json (statement, unsplit, no Mathlib match). Two new nodes, zero Mathlib leaves. citations.json supplies the full verbatim statement for every citation of every parent step. No Lean files were written or compiled.

Attachments: none. A concept and blueprint-tag search in lean/WeilConjectures found no declaration of the whole item. The declaration in lean/Sheaf/AlgebraicGeometry/CoherentPropertyIrreducible.lean ends in sorry. Existing RankOneGenericIdealInclusion, IntegralIdealsCommonGenericLattice and IntegralIdealCommonSubmodule are available geometric inputs for the future workers; they do not state either new property lemma. No existing node was edited to attach them.

WANTED: none. The source is present in literature/stacks-project/coherent.tex. Tags verified in tags/tags: 01YH = coherent-lemma-property-irreducible, 01YF = coherent-lemma-coherent-filter, 01YG = coherent-lemma-property-initial. I read the complete 01YH statement/proof, the nearby 01YG proof, and the current main-20261015 blueprint ancestor lem-pc-coherent-hi and the chapter/unit records. The blueprint update's coherence route is unchanged by this local repair.

What was wrong: the released repair order requires distributing the 4344-character proof, not rewriting it more tersely. This delivery introduces two comparable tasks with different hypotheses and conclusions. The supported-property task has no generic-rank witness or irreducibility assumption: it is the filtration argument for an arbitrary support subset. The ideal-transfer task has no hypothesis about proper integral subschemes and concludes only for ideal pushforwards on a fixed integral Z; it assumes the small-support result supplied by the other task. Neither is the whole item or one of its stated clauses. The old first step incorrectly tried to infer P(0) from the all-zero exact sequence; two-out-of-three gives no starting property there. The parent now obtains it from 0 -> G -> G -> 0 -> 0 and P(G). The statement itself is correct and unchanged; no STATEMENT-DISPUTED is needed.

Unfinished: the two new tasks intentionally have no proof steps, proof dependencies, or proof origin. Other workers can take them independently. No work required by this repair is omitted.

## Preservation of the returned argument

The complete old proof is retained locally in original-proof.md. Its argument is assigned as follows, without discarding a step:

1. Old step 1: finite filtration propagation belongs to supported-property devissage. The parent derives zero and isomorphism invariance from the supplied G and two-out-of-three. For a filtration, start with P(F_0)=P(0), use the short exact sequence with the next quotient, and iterate, including the length-zero case.
2. Old step 2: supported-property devissage is first applied with S=T minus {xi}. Its future proof uses lem-weil-pbc-coherent-filtration-integral-subschemes. Stalk exactness puts every subobject and successive quotient support inside Supp(F). A nonzero integral ideal has full generic stalk by lem-weil-pbc-integral-scheme-ideal-generic-stalk; closedness of its coherent support and density of its generic point show that its pushforward support is the integral closed-subscheme image. Thus all the filtration images lie in S and hypothesis (2) applies. This is a substantial support-controlled filtration argument, not just extension induction.
3. Old step 3: the parent constructs T_red using lem-weil-pbc-reduced-induced-closed-subscheme(2); it is integral because T is nonempty irreducible. The ideal-transfer task carries the rank-one comparison: apply the generic ideal-sum inclusion 01YE, compare its generic stalk with G_xi, exclude r=0 or I=0, identify a nonzero ideal's generic stalk with the function field, and force r=1. The existing lem-pc-r2-rank-one-generic-ideal-inclusion already isolates this geometric input. Its cokernel Q is coherent, supported in T and zero at xi; the small-support hypothesis gives P(Q), and two-out-of-three gives P(i_*I).
4. Old step 4: in the ideal-transfer task, for each nonzero subideal I' of I, the composite i_*I' -> i_*I -> G is injective and a generic-stalk isomorphism. Its coherent cokernel Q' is supported in T and misses xi. The small-support hypothesis and P(G), through two-out-of-three, give P(i_*I'). This preserves the original subideal comparison rather than bypassing it in prose.
5. Old step 5: for an arbitrary nonzero ideal J, I intersect J has full generic stalk and is nonzero, as both ideals have the generic field. It is quasi-coherent and coherent on the Noetherian integral Z. Apply step 4 to the intersection; the quotient J/(I intersect J) has zero generic stalk. Its pushforward is coherent and supported in T, so its property and extension closure give P(i_*J). Equivalently the source's two exact intersection sequences give the same two uses of two-out-of-three. The zero ideal is covered by P(0). Existing common-generic-lattice nodes supply the intersection geometry, not this property-transfer theorem.
6. Old step 6: the second application of supported-property devissage, now with S=T, carries the final filtration. Proper-support integral quotients use hypothesis (2). A full-support integral closed subscheme is reduced, hence isomorphic over X to T_red by lem-weil-pbc-reduced-induced-closed-subscheme(3); transport the ideal under that isomorphism, identify its pushforward, and apply ideal transfer. All subquotients have the property and the filtration induction concludes.

## Searches and duplicate audit

Before creating either node I searched all DAG statements (not only titles or this unit), rg by 01YH/01YG and support/property/filtration/intersection concepts, and tools/blueprint_refs.py search for coherent property, property, filtration, 01YG, 01YH, 01YF, support filtration, supported coherent, ideal property, rank one and generic lattice. None states either new lemma. tools/blueprint_refs.py ancestor returns lem-pc-coherent-hi. The from.via chain is recorded through this item and its created.item ancestry. Source proof paragraphs are precise in from.place. A tag absent from the current blueprint statement does not erase the existing devissage provenance.

Every Mathlib search in the nodes is copied from the actual msearch.py log. Both new nodes have LeanFinder, LeanSearch, Loogle and grep, with two distinct semantic phrasings. The item was also searched again. LeanFinder hits were ideal-data constructors, local Noetherian or function-field instances, and affine module support statements. LeanSearch hits were ideal support/zero loci and generic pushforward constructions. Loogle returned no stalk or devissage theorem; its coherent-name query found only isQuasicoherent_restrictFunctor. Grep found no coherent devissage/property declaration; the generic-point hits are FunctionField.lean:132,157 and Morphisms/Smooth.lean:354. I read the FunctionField declaration and the actual IdealSheaf/Basic.lean:308-335 support definitions: the ideal-data support is the zero locus (support of O/I), not the nonzero-stalk support of I that this proof uses. Module.support_of_exact at RingTheory/Support.lean:174 and support_quotient at :249 concern ordinary ring modules; they do not supply either supported sheaf property theorem. Hence none is a one-line Mathlib specialization. Interrupted search processes had completed into searches.jsonl; those results were reused, not invented or duplicated.

## Review by Q63

I read coherent.tex at lemma-property-irreducible against each of the item's three assumptions: Noetherian is global here, T is nonempty through irreducibility, P is tested only on coherent modules supported in T, and the witness has ambient maximal-ideal annihilation plus a compatible one-dimensional residue-field structure. The new supported-property lemma assumes P(0) explicitly, so it remains valid for an empty X or empty support subset; it uses extension closure rather than assuming two-out-of-three unnecessarily. Its arbitrary-subset formulation is essential for T minus {xi}, which is generally not closed. The ideal-transfer lemma explicitly introduces X,Z,i,eta,T,xi,G and every property hypothesis; it has no extra generic-rank or reducedness assumptions hidden in another node.

I opened each statement cited by the parent. Step 1 uses the item's own two-out-of-three and witness, with the identity exact sequence rather than a circular all-zero argument. Step 2's sole citation, supported-property devissage, explicitly permits any subset S and asserts the property for all coherent modules supported there; the integral images it requires are proper subsets of T, exactly the scope of (2). Step 3 cites the reduced-structure node's existence clause, the integral-scheme definition's reduced-plus-irreducible equivalence, and the new ideal-transfer statement: its small-support premise is precisely step 2, and its witness and two-out-of-three premises are precisely (1),(3). Step 4 cites supported-property devissage again and the reduced-structure node's uniqueness clause; the latter explicitly provides the isomorphism over X needed to transport the ideal. Transport along an isomorphism is just reindexing sections and the module structure, hence identifies pushforwards; no flatness or unproved closed-image factorization is used. Every cited statement is copied verbatim to citations.json, so no step takes a fact only from the cited proof.

For the two future tasks I checked the available geometric inputs against their statements: 01YF gives actual finite coherent filtrations with nonzero integral ideals; the generic-stalk ideal criterion says a nonzero ideal has the full generic field; 01YE gives the locally invertible ideal-sum inclusion; the existing r2 rank-one node gives a mono whose generic stalk is invertible; the common-lattice node gives the two mono generic-stalk isomorphisms but deliberately no cokernel conclusion. The new ideal-transfer task still owns coherence and small-support verification for these cokernels and both exact-sequence property deductions; that work has not been silently attributed to common-lattice existence.

Small cases checked: F=0 and filtration length zero; S empty and S nonclosed; T a single point (small-support modules are zero); G already an ideal pushforward (cokernel zero); J=0 and J=O_Z; equal nonzero ideals (intersection quotient zero); X nonreduced along T (Z is explicitly T_red, and the ambient stalk action factors through kappa(xi)). Rank one forbids the zero generic ideal and r=0. The new statements neither claim that every nonzero ideal on a reducible scheme has full support nor assume affine intersections. I checked B-E: statement-only children, self-contained hypotheses and definitions, single-escaped TeX, correct local Stacks labels, actual recorded searches, exact citation scope, no cycles, no prohibited SGA route, no new node that merely restates the parent. The only elementary parent step is the identity-sequence argument. All assembly steps are below 2000 characters; together they are below 3000.

The return's required distribution is satisfied by two statement-only nodes of comparable size. Old steps 1/2/6 are assigned to supported filtration, old steps 3/4/5 to rank-one ideal transfer; the report above retains their full arguments and names the reusable inputs. The item's statement is unchanged. No repository, launcher, compiler or build files were modified.

## Not duplicates

lem-pc-coherent-supported-property-devissage vs lem-pc-v3-integral-ideal-comparison-filtrations: this supplies geometric comparison filtrations for cokernels and has no arbitrary property or property propagation assertion.

lem-pc-coherent-supported-property-devissage vs lem-pc-coherent-property-irreducible: the parent combines proper-integral-support hypotheses and a single witness to conclude for every coherent sheaf in T; the new lemma isolates only one of the two independent mechanisms with changed input/output.

lem-pc-coherent-supported-property-devissage vs lem-pc-a2-integral-ideal-common-submodule: this constructs a common submodule with small-support cokernels; it does not assert any property transfer or general supported-filtration criterion.

lem-pc-coherent-supported-property-devissage vs lem-pc-r2-integral-ideals-common-generic-lattice: this constructs two monomorphisms invertible generically; it makes no property or cokernel-support assertion.

lem-pc-coherent-supported-property-devissage vs new-rank-one-generic-ideal-inclusion-aux: this identifies two generic stalk modules only, without a global ideal map, filtration, or property conclusion.

lem-pc-coherent-supported-property-devissage vs lem-pc-r2-coherent-pushforward-ideal: this asserts coherence of i_*I only; no property or filtration conclusion is present.

lem-pc-coherent-supported-property-devissage vs lem-pc-r2-rank-one-generic-ideal-inclusion: this gives one nonzero ideal mono invertible at the generic stalk; it has neither the supported filtration criterion nor transfer to all ideal pushforwards.

lem-pc-coherent-supported-property-devissage vs lem-pc-r2-common-generic-lattice-maps: this gives generic common-lattice maps only, with no arbitrary property or final propagation.

lem-pc-coherent-supported-property-devissage vs lem-pc-e2-integral-ideal-proper-cohomology: this is finite cohomology for proper morphisms over a Noetherian affine base, not an arbitrary property lemma.

lem-pc-coherent-supported-property-devissage vs new-generic-ideal-stalk-embedding-extension: this extends an injective generic map to an ideal embedding, without the two-out-of-three or support-controlled property conclusions.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-v3-integral-ideal-comparison-filtrations: this supplies geometric comparison filtrations for cokernels and has no arbitrary property or property propagation assertion.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-coherent-property-irreducible: the parent combines proper-integral-support hypotheses and a single witness to conclude for every coherent sheaf in T; the new lemma isolates only one of the two independent mechanisms with changed input/output.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-a2-integral-ideal-common-submodule: this constructs a common submodule with small-support cokernels; it does not assert any property transfer or general supported-filtration criterion.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-r2-integral-ideals-common-generic-lattice: this constructs two monomorphisms invertible generically; it makes no property or cokernel-support assertion.

lem-pc-coherent-rank-one-property-ideals vs new-rank-one-generic-ideal-inclusion-aux: this identifies two generic stalk modules only, without a global ideal map, filtration, or property conclusion.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-r2-coherent-pushforward-ideal: this asserts coherence of i_*I only; no property or filtration conclusion is present.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-r2-rank-one-generic-ideal-inclusion: this gives one nonzero ideal mono invertible at the generic stalk; it has neither the supported filtration criterion nor transfer to all ideal pushforwards.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-r2-common-generic-lattice-maps: this gives generic common-lattice maps only, with no arbitrary property or final propagation.

lem-pc-coherent-rank-one-property-ideals vs lem-pc-e2-integral-ideal-proper-cohomology: this is finite cohomology for proper morphisms over a Noetherian affine base, not an arbitrary property lemma.

lem-pc-coherent-rank-one-property-ideals vs new-generic-ideal-stalk-embedding-extension: this extends an injective generic map to an ideal embedding, without the two-out-of-three or support-controlled property conclusions.

lem-pc-coherent-supported-property-devissage vs lem-pc-coherent-rank-one-property-ideals: supported devissage takes integral-ideal properties as inputs and concludes for sheaves on any support subset; ideal transfer instead takes a rank-one witness plus small-support properties and concludes only for ideals on a fixed integral closed subscheme. They are independent tasks.

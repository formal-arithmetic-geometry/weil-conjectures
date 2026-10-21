# Q121 — lem-pur-common-line-positive-scalar-powers

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-common-line-positive-scalar-powers.json`: item, statement, now split into seven steps. The statement and its four statement dependencies are unchanged. No new DAG nodes and no new Mathlib leaves.
- `citations.json`: fifteen entries, one per step/node citation, quoting the cited statement verbatim.
- `searches.jsonl`: command-generated searches for this item. The item's inherited Q42 search records are preserved, and the six actual Q121 searches are appended to `mathlib_searches`.
- `report.md`: this report. `write_split.py` is the sandbox-only preparation script.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, common-line/scalar-power terminology, tensor powers, and scalar-extension/associativity terminology. `SheafOfModules.positiveTensorPower` in `Algebra/Category/ModuleCat/Sheaf/TensorProduct.lean:213` supplies the recursion, not the asserted comparison theorem. That file's change-of-rings construction and the sheaf monoidal implementation do not state all clauses of this item. The representation tensor-power declarations concern representations over rings, and the geometric tensor-power files concern scheme module restrictions. None is an attachment for the present arbitrary ring-sheaf statement.

## WANTED

None. The necessary source is present.

## Corrections and source scope

No statement dispute or weakening. The item previously had no proof. I supplied the common-presentation maps and inverses, the first comparison and its inverse, the degree-zero unit, the actual induction using binary scalar extension, and the rank-one and generator calculations on the same covering.

I read the current `main-20261015` proof of `prop-weil-twist-preserves`: its opening scalar-extension/tensor-power sentence and final integral-coefficient sentence motivate this extracted item. I also read its recorded unit `sk-prop-sf-existence` and chapter `sec-smooth-purity`. This is a below-unit algebraic lemma, not a change of the exceptional-adjoint route or of the chapter. The supporting source is Stacks `sites-modules.tex`, Section 03EK, label `section-tensor-product`: the sheafified tensor definition, displayed associativity and change-of-ring formulas, and the displayed Hom/Bilin bijection. I read Tag 03EL, label `lemma-tensor-product-pullback`, including the proof. The item’s source points to 03EL, but the explicit mixed-ring inverse formulas and inductions are my expansion using 03EK; `proof_origin.by` is therefore `agent`. No SGA source is used.

## Mathlib searches and candidates read

The six Q121 searches were run through the required `msearch.py` command: LeanFinder with the initial sheafified-scalar-extension phrasing and a second phrasing about associativity and strong monoidal scalar extension; Loogle `SheafOfModules`; LeanSearch about change of rings and iterated tensor powers; and two source greps in the sheaf module and algebraic tensor directories. All services answered successfully. The command log gives the exact query strings and results; none is represented as unavailable or fabricated.

I read `Mathlib/LinearAlgebra/TensorProduct/Tower.lean:402` (`AlgebraTensorModule.assoc`), the cancellation equivalence and its pure-tensor formulas, and `:441` (`distribBaseChange`) with formulas at 462–470. These are algebraic modules, not the sheaf tensor comparison required here. I also read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53`: its pullback is an abstract left adjoint, not the sheafified pure-tensor theorem with powers and same-cover bases. The Loogle hits give the category and rank-one unit, and the other semantic hits give presheaf tensors, sheafification scalar axioms, or specialized condensed structures. None is an exact match or one-line specialization of all clauses of this item.

## Not duplicates

No new nodes. I reused the existing `lem-pc-sites-sheaf-tensor-bilinear-universal`, `def-weil-presheaf-modules-sheafification`, `lem-sp-scalar-extension-binary-coherence`, and `lem-sfb-localized-site-tensor-restriction` instead of creating tensor reassociation, scalar-distribution, or slice-restriction nodes. The whole-DAG and blueprint searches for tensor products, scalar extension, tensor powers and common-line terminology found no blueprint node stating this whole item. In particular the binary-coherence node explicitly excludes tensor-power comparisons: the power induction belongs in this item rather than being assumed from that node. The existing cancellation node does not need to be cited: its special-case inverse calculation is written directly here from the tensor universal property.

## Review by Q121

I checked B–E of `coord/delivery-errors.md` against the item, source and cited statements. I opened all five distinct proof-dependency files and read their `statement` fields, rather than using their implementation or proof. I also read the four original statement-dependency statements. There are no new nodes to hide an item clause, no statement-only nodes containing sketches, and no new source tags requiring duplicate-pair adjudication. Each step is shorter than 2000 characters.

Step 1 uses the actual Hom/Bilin bijection from `lem-pc-sites-sheaf-tensor-bilinear-universal`, the sheafified construction from `def-pur-sheaf-tensor-product`, and the module-sheafification factorization and uniqueness stated by `def-weil-presheaf-modules-sheafification`. These give existence and equality detection for the subsequent formulas. This avoids assuming that the sections of a sheaf tensor are the sectionwise tensor product, or that a section is globally pure.

Step 2 uses that same bijection and sheafification uniqueness to construct multiplication and the module action. I checked the B-balance in the A/C and T/C presentations, and ring/module axioms on pure inputs. A, B and C_i are commutative ring sheaves as required; the induced R_i action on L_i is specified explicitly.

Step 3 again uses those two statements, with the actual A- and B-balanced relations written out. I checked that the proposed inverse is R_i-linear, not merely B-linear, and that its composite sends `t tensor (a tensor c)` back to itself by moving a into t. It needs no rank-one assumption and no flatness.

Step 4 uses the same universal statements for the coefficient square and the exponent-one comparison. Both paths in the first square give `a t tensor phi(c)`. For the second comparison, the inverse composite is exactly the R_0-balanced relation moving r to iota(r) on the R_1 factor. The coefficient maps need not be injective.

Step 5 uses the binary natural isomorphism explicitly stated by `lem-sp-scalar-extension-binary-coherence`, including its pure-generator formula and naturality in both module factors. It applies to the ring-sheaf map R_0 to R_1 on this site with its chosen module universe. Converting between left and right scalar notation is the commutative balanced-tensor flip, and the inverse is written explicitly. The degree-one base is step 4; degree zero is handled separately; the induction is over n at least one and uses precisely the recursive association in `def-pur-sheaf-tensor-product`. I did not take powers from the binary node's data definitions.

Step 6 uses the exact tensor restriction isomorphism, including preservation of pure tensors and absence of flatness hypotheses, in `lem-sfb-localized-site-tensor-restriction`. Its hypotheses hold on the localized site C/U. The universal-property node applies there as well. I wrote the coefficient inverse q and multiplication-of-coefficients inverses to prove freeness on each original covering member; no refined cover or globally chosen basis is substituted.

Step 7 uses the formulas from the binary and restriction statements and the previous inductive claim. I computed the successor image explicitly, including both outer scalars and the degree-zero convention. It is elementary relative to those cited formulas. Restriction compatibility follows because the cited slice comparison preserves pure tensors and the input maps are sheaf morphisms; it is not asserted from an unmentioned stalk argument.

I tested the statement and inverses for n=0, n=1 and n=2, identity coefficient maps, T=0, a non-free T (the isomorphism assertions still hold), the non-flat coefficient map Z to Z/2, and zero ring sheaves. The rank-one claim is conditional on the supplied local trivializations, which remain meaningful for zero coefficient rings. For an arbitrary change of local basis e to u e, both sides of the displayed degree-n formula acquire the same factor iota(u)^n, so the generator description does not define a basis-dependent map. All equalities are sheaf-tensor equalities; none requires enough points, exact tensoring, or cohomology.

The generic off-unit proof tools are declared in `split_report.tool_uses`: Hom/Bilin universality, module sheafification, ordinary binary scalar extension, and slice tensor restriction. They serve the prescribed scalar-extension argument and replace no unit step. The proof-dependency list is the union of the seven `uses` lists, with a verbatim citation entry for every occurrence.

## Unfinished work

None for this one-level stage-1 split. The existing dependency nodes retain their own stages; no Lean was written and no compiler or build command was run.

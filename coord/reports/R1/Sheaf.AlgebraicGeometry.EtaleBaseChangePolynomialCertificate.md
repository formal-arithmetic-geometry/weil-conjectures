## What changed

Proved the item's theorem by choosing a Mathlib finite presentation, transporting its base change to the tensor map, applying the existing conormal criterion, and reducing bijectivity to finite polynomial inverse identities. Added a proved presentation transport module and an intermediate conormal calculation module. Existing signatures are unchanged.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_etale_baseChange_polynomialCertificate` and `Algebra.tensorMap_polynomialPresentation`. The sole new sorry is `Algebra.conormal_bijective_iff_polynomialCertificate`, node `lem-weil-pbc-conormal-polynomial-inverse`. The imported existing conormal criterion still contains its own sorry.

## No longer needed

Removed direct imports of Mathlib.RingTheory.TensorProduct.MvPolynomial and Mathlib.RingTheory.TensorProduct.Quotient: Mathlib's presentation API supplies their construction. `lem-weil-pbc-polynomial-scalar-extension` and `lem-weil-pbc-tensor-quotient-base-change` are no longer dependencies of this proof. `lem-weil-pbc-tensor-cancel-base-change` is no longer a direct dependency of the item, but remains a dependency of the proved transport lemma, via its Mathlib match `Algebra.TensorProduct.cancelBaseChange`. Thus all three removed entries of the original direct `proof_deps` are accounted for; only the first two are pruned from this route. No unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies do not state the finite inverse-certificate equivalence. Its proof is the finite basis/generating relation calculation in the source, now isolated as a strictly smaller algebraic statement without any base change or etaleness conclusion. LeanSearch was unavailable; LeanFinder and grep found ingredients rather than this equivalence. The source file is not present locally; the stated source places and argument are retained from the existing node.

## New nodes

`lem-weil-pbc-tensor-map-polynomial-presentation`: proved presentation transport, using Mathlib Presentation.baseChange and an explicit tensor algebra equivalence. Tested by compilation, without flatness or nonzero ring hypotheses.

`lem-weil-pbc-conormal-polynomial-inverse`: the remaining inverse differential calculation. Its docstring gives both implications and checks empty variable/relation families and the zero ring. It is strictly a part of the argument: it assumes the presentation and differential, and says nothing about etaleness or tensor maps. Blueprint searches for polynomial certificate and inverse conormal returned no matches.


## Second reading by R1

1. Compared the existing module with the repository by diff: its only changes are
   two proof-only imports and the theorem proof. The existing theorem signature
   and docstring are byte-for-byte unchanged; there are no changed definitions,
   targets, or other existing modules, and no change record is needed. Verdict: pass.
2. Compiled all three delivered modules in import order using lcompile.py, without
   errors or warnings. Explicit scratch-copy `#print axioms` checks show only
   propext, Classical.choice and Quot.sound for tensorMap_polynomialPresentation;
   the item and conormal_bijective_iff_polynomialCertificate additionally use
   sorryAx. The sole delivered sorry is the reported named conormal theorem;
   the imported existing conormal criterion is also still open. No forbidden
   declarations or hollow definitions occur. Verdict: pass, conditional reduction.
3. Read the split conormal theorem, certificate definition, docstring proof and
   matching node. The inverse identities have the correct derivative indices,
   ideal and ideal-square membership. For n = 0 they assert J = J², precisely
   vanishing of J/J²; for m = 0 they assert S^n = 0, precisely bijectivity of
   0 → S^n. A zero quotient gives J = J² = the whole polynomial ring, so both
   conditions hold. For f = X the coefficient c = 1 gives the expected inverse;
   for f = X² over a field, evaluation at zero rules out the first identity,
   agreeing with the zero differential on a nonzero conormal module. These are
   mathematical edge-case checks, not additional Lean proofs. The split result
   is a strict algebraic part of the original argument, with no tensor map or
   etaleness conclusion. Independent LeanFinder, Loogle, Mathlib grep and
   repository searches found cotangent quotient/surjectivity and submersive
   presentation ingredients, but no existing general equivalence. A full
   formal proof requires substantial quotient/scalar transport work and was
   retained as the sourced, documented split theorem. Verdict: pass.
4. Read from the item downward through the presentation transport and conormal
   criterion. The transport uses Mathlib Presentation.baseChange/ofAlgEquiv and
   tensor cancellation directly; no shorter replacement for the general inverse
   certificate was found. All public imports of the new modules provide types,
   operations or constants in their signatures; all item proof imports are plain
   imports. Compared old/new proof_deps and made the pruning report explicit.
   Read sk-thm-p1.json realized: this item and its replaced algebraic dependencies
   are below the realized unit steps, which remain unchanged. Verdict: pass.
5. Checked the three nodes against their Lean signatures and proofs: the item's
   dependencies are exactly transport, conormal criterion and inverse certificate;
   transport records its actual Mathlib tensor-cancellation dependency; the open
   conormal node records its complete inverse argument. New nodes have the source,
   provenance, searches, blueprint, chapter/unit and Lean records required by the
   brief. Verdict: pass.

Second reading changed only this report: explicit node identifiers and direct
versus transitive pruning accounting, and the five review verdicts above. The
Lean proofs and statements required no repair.

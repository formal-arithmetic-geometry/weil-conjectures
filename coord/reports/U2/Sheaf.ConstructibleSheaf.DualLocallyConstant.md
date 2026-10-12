## What changed

Proved the body of `IsFiniteLocallyConstantSheaf.ihom_unit_locallyConstant` without changing
its signature or existing docstring. The proof uses the original trivializing cover, extracts a
finite constant model on each member, transports the internal Hom through étale pullback and
through the model isomorphism, and applies the constant finite module dual calculation.

Added `Sheaf.ConstructibleSheaf.FiniteConstantModel` with a complete Lean proof of
`exists_finite_constant_model`. Its nonempty case identifies a model with a geometric stalk;
its empty case uses the zero module. No arbitrary data are chosen from unproved existence.

Added proof-only imports of `WeilConjectures.ConstructibleSheaf.Pullback`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`, and the three new modules.
Updated the original node's proof, proof dependencies and proof origin to match the Lean proof.
The two missing comparison results have separate modules with public named statements,
complete mathematical proofs in their docstrings, and matching DAG nodes.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom_unit_locallyConstant`
(node `lem-weil-pbc-flc-dual-locally-constant`). There are no holes left in the item's module.

Fully proved the added declaration `AlgebraicGeometry.Scheme.exists_finite_constant_model`
(node `lem-weil-pbc-finite-constant-model`).

Added exactly two holes:
`AlgebraicGeometry.Scheme.nonempty_etale_upperStar_ihom_iso`
(node `lem-weil-pbc-etale-pullback-internal-hom`) and
`AlgebraicGeometry.Scheme.nonempty_constant_finite_dual_iso`
(node `lem-weil-pbc-constant-finite-dual`). This is a decomposition of the original argument,
not a sorry-free proof of its transitive closure: one original hole closed, two holes added.
Neither new comparison assumes local constancy of the original F or concludes local constancy
of its dual. The first isolates localization compatibility for arbitrary sheaves, the second
the constant-module finite-presentation calculation. The target proof combines them by actual
cover construction, finite-model extraction, and three distinct isomorphism transports.

## No longer needed

No original imports removed. No original proof-dependency nodes removed: the node originally
had an empty proof_deps list. The coefficient-dual stalk theorem is not used or imported;
`Sheaf.ConstructibleSheaf.DualStalk` and `lem-weil-pbc-flc-dual-stalk` remain separate work
needed by the parent's finiteness proof. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node has a non-elementary argument with `uses: []`, so it supplies no formal
lemmas for its two main comparison steps. Searches found no direct comparison in the
fixed-coefficient `Sheaf J (ModuleCat Λ)` encoding. The source library contains
`SheafOfModules.overHomObjIso`, but this belongs to the different ringed-site module encoding
and has no immediate bridge to this module's internal Hom.

LeanFinder returned condensed locally constant functors, not étale module-sheaf duals.
Loogle did not resolve `Sheaf.IsConstant`; the source declaration was read directly.
LeanSearch returned Internal Server Error. The local source and Mathlib grep searches found
constant-sheaf stalk isomorphisms, empty-scheme vanishing, finite-generation transport,
constant-sheaf finite-limit preservation, and the distinct ringed-site internal-Hom APIs.
A blueprint search for constant finite duals found no duplicate; the internal-Hom results
in other units concern derived or finite-Tor operations, rather than this ordinary comparison.

Edge cases checked: the finite-model proof treats empty X explicitly and imposes no connectedness
or noetherian hypothesis. The constant-dual argument requires noetherianity to turn finite
generation into finite presentation; it works for zero modules and the zero coefficient ring.
The localization statement is restricted to étale morphisms; arbitrary pullback need not
commute with internal Hom. Each new statement retains exactly the hypotheses its argument uses.

All four modules compile together in import order, without warnings. Validation is through the
specified lcompile.py and deliver3.py tools only.

## New nodes

`lem-weil-pbc-finite-constant-model`: a finite constant sheaf admits a finite module model,
including over the empty scheme. The declaration is fully proved.

`lem-weil-pbc-etale-pullback-internal-hom`: localization compatibility for arbitrary module
sheaves; this is the first remaining comparison. The proof specifies the section description
of internal Hom and the iterated-localization equivalence.

`lem-weil-pbc-constant-finite-dual`: finite-presentation dual computation for a constant module,
using exact constant sheafification, finite free duals and the kernel of the transpose matrix.
This is the second remaining comparison. No statement or definition change records are needed.


## Second reading by U2

1. **Unchanged interfaces: PASS.** Compared each of the four delivered modules with
   the read-only repository. `DualLocallyConstant.lean` differs only by five plain,
   proof-only imports and the body of
   `IsFiniteLocallyConstantSheaf.ihom_unit_locallyConstant`. Its existing signature,
   variables, public imports and docstring are byte-for-byte unchanged. The other
   three modules are new; no existing definition, target or statement is changed,
   and no change record is needed.

2. **Lean proof and axioms: PASS as a decomposition.** All four modules compiled
   together through `lcompile.py --all`, in import order, with no warnings or errors.
   There are exactly two direct `sorry`s, the two public comparison theorems listed
   under `Proved and sorry left`; there are no new definitions or forbidden features.
   A scratch module explicitly importing all four modules printed the axioms of all
   four declarations. `exists_finite_constant_model` uses only `propext`,
   `Classical.choice`, `Quot.sound`. The original theorem and both open comparisons
   additionally use `sorryAx`, as expected; no other axiom appeared. The scratch file
   was removed. The finite-model witness is extracted from proved constancy and a
   stalk isomorphism, not from an unproved existence statement. The open isomorphism
   statements determine their objects up to the very isomorphism used downstream;
   they provide proof transport, not arbitrary object definitions.

3. **Split statements, sources and searches: PASS.** Read the coefficient-dual
   docstring of `WeilConjectures.ConstructibleSheaf.Monoidal.ihom_unit` and all three
   new theorem docstrings and nodes. For `nonempty_etale_upperStar_ihom_iso`, the
   etale hypothesis makes pullback restriction to a slice, and iterated slices
   identify both internal-Hom section modules. This applies to arbitrary F,G,
   including zero sheaves, the identity map and an empty source, without a
   noetherian hypothesis. For `nonempty_constant_finite_dual_iso`, noetherianity
   makes the finite model finitely presented; dualizing its finite free presentation
   gives the transpose kernel. Exact constant sheafification preserves that kernel
   and identifies the finite free terms and matrix. This covers nonprojective
   modules (for example Z/n over Z, whose dual is zero), M = 0, a zero ring, empty X,
   and disconnected X. Neither comparison assumes local constancy of F or asserts
   local constancy of its dual; each is a strict component of the cover argument.
   The finite-model proof separately treats empty X by the actual zero module,
   and nonempty X by a point with separable-closure residue field. All docstrings
   supply the full mathematical arguments and matching blueprint node IDs.

   Repeated searches using different words with LeanFinder and Loogle, and searched
   Mathlib, both repository Lean roots and the proper-base-change DAG with `rg`.
   LeanFinder returned condensed and ringed-module APIs; Loogle returned the generic
   tensor-Hom adjunction and unit isomorphisms. Read
   `SheafOfModules.overHomObjIso`; it concerns modules over a sheaf of rings, and no
   existing equivalence plus monoidal-closed comparison bridges it to the category
   here. No exact duplicate of either open comparison was found. An existing
   `moduleFinite_of_isFiniteSheaf_constantSheaf` in `KernelCokernel.lean` supplies
   the nonempty constant-model finiteness subargument, but not the new existential
   theorem including empty schemes. Its direct stalk proof uses the same proved
   stalk API. Retained the short direct proof to avoid importing KernelCokernel,
   Biproduct, GenericConstancy and their additional dependency closure. The two
   comparison proofs require substantial missing categorical constructions, so
   neither can be closed by a few-minute application of an existing declaration.

4. **Top-down reduction, imports and pruning: PASS.** Followed the original cover
   datum into each pullback. `IsFiniteSheaf.upperStar` supplies finite stalks;
   `exists_finite_constant_model` supplies M and its finiteness. The proof composes
   the restriction comparison, pulled-back unit isomorphism, contravariant
   internal-Hom transport along the model isomorphism, and constant-dual comparison.
   Their directions match, and constancy is transported back to the localized
   site. Every added import supplies a theorem or monoidal instance used here;
   all added imports in the existing module are plain imports. The original node
   had no proof dependencies to prune and no original imports became unused.
   Read `dag/units/sk-thm-p1.json`: none of its realized statement or step nodes is
   bypassed or edited. This reduction remains below those unit steps. The report
   correctly counts one original hole closed, two holes added, hence net -1 holes
   closed, a decomposition rather than a completed transitive proof.

5. **DAG alignment: PASS.** Read each delivered JSON alongside its theorem.
   The original node's three steps and dependency union match the finite-model,
   restriction and dual transports. Its citation of
   `lemma-constructible-pullback-locally-constant` is justified by that node's
   recorded additional declaration `isConstant_over_iff_upperStar`, used twice;
   `lemma-constructible-pullback-finite` records the actual finiteness theorem used.
   Each new node has the correct chapter/unit, self-contained statement, source,
   proof and origin, three search kinds, creation and blueprint ancestry, and the
   verbatim Lean theorem signature. No new node restates the original target.

**Second-reader changes:** No Lean repair was needed. Added the independent search
results to the two open comparison nodes and this review to the report. Retained the
proved finite-model construction and the two honestly reported comparison holes.

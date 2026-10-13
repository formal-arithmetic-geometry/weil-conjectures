## What changed

Completed and checked the earlier sandbox attempt. The existing signature and docstring of
`CategoryTheory.perfectRingHom_isKFlat` are unchanged. Its proof now uses the explicit dual
`perfectRingDual P`, proves its upper bound directly from the product cone defining the shared
Hom complex, applies the existing site theorem
`CochainComplex.isKFlat_of_boundedAbove_flat`, and transports acyclicity using the Mathlib
chain associator and totalization of the Hom--tensor isomorphism.

The private helpers `homObj_zero_source`, `homObj_zero_target`, and
`perfectRingDual_boundedAbove` have complete Lean proofs. The last helper uses only the lower
bound on P: for n > -a, every factor Hom(P^p,A[0]^(p+n)) has zero source if p < a and zero
target otherwise. Product extensionality proves that the identity is zero.

Two new modules contain the remaining finite-projective arguments:
`Sheaf.Algebra.Homology.PerfectRingDualTermFlat` constructs the actual dual using Hom into
the ring sheaf in degree zero and states flatness of its terms;
`Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso` states the chain isomorphism with tensor
by that explicit dual. No data is chosen from a new existence theorem in a definition.
The isomorphism existence is eliminated only in the theorem proof.

The parent node's proof, proof_deps and proof_origin now follow this Lean argument. The unit
and its route are untouched. All three delivered modules compile through lcompile.py.

## Proved and sorry left

Closed the original hole in `CategoryTheory.perfectRingHom_isKFlat`
(node `lem-pc-perfect-ring-hom-kflat`) by a compiling reduction.
No sorry remains in the item's module.

Added two holes, both whole proofs of public named theorems in separate modules:

- `CategoryTheory.perfectRingDual_term_isFlat`
  (node `lem-pc-perfect-ring-dual-term-flat`). This has neither a boundedness hypothesis nor
  a second complex; it asserts only termwise flatness of the explicit dual.
- `CategoryTheory.perfectRingHom_tensorDual_iso`
  (node `lem-pc-perfect-ring-hom-tensor-dual-iso`). This has no K-flatness hypothesis and
  asserts only the chain isomorphism for arbitrary Q.

This is a decomposition, not a complete foundational proof: one upper hole closed, two lower
holes added (net -1). The combination is fully proved in Lean: D makes F tensor D acyclic,
Q makes (F tensor D) tensor Q acyclic, associativity and the new isomorphism then give
F tensor Hom(P,Q) acyclic. Existing imported theorems may themselves rest on sorry.

## No longer needed

The planned node `lem-pc-module-bounded-flat-kflat` and its module
`Sheaf.Algebra.Homology.BoundedFlatKFlat` are no longer a direct proof dependency of this
item. The proof applies the existing ringed-site theorem
`lem-pc-bounded-above-flat-kflat-site` instead, avoiding a separate transport of acyclicity
and K-flatness between sheaves and module complexes. This is a generic tool specialization,
not a bypass of a unit statement or step. There is no claim that BoundedFlatKFlat becomes
unreachable globally: other proofs and inherited public imports may still need it.

The old proof edge to `def-pc-perfect-rhom-base-change-map` is also absent from the new
`proof_deps`; it remains a statement dependency and its public import remains necessary for
`RingSiteModules` and the one-object ring sheaf. No original public import was removed. Removed redundant tentative imports from the earlier
sandbox: `Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors` from the dual module and
the direct proof import of `Sheaf.Algebra.Homology.PerfectRingDualTermFlat` from the item
(the Hom--tensor module publicly imports it because its signature uses the explicit dual).
The retained `Mathlib.Algebra.Homology.Monoidal` import is necessary: removing it produced
an unknown-identifier error for `HomologicalComplex.associator`.

All original statement dependencies remain needed. New direct proof dependencies are the two
new nodes, the site bounded-above flat theorem and the tensor-closedness node. There are no
additional nodes or modules claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had compiling Lean files but no matching new node files or report.
Those missing delivery artifacts are now supplied. No statement was found false, changed,
or weakened. No existing module outside the item is adapted.

The precise chain-level dual argument is an expansion of Stacks 0A6A (1), rather than a
verbatim quotation of that lemma. The current Stacks proof passes through evaluation lemma
0ATK (1). Read both official tag pages and the 064K page; the new nodes record the chain-level
expansion as agent-written. The algebraic subfact that a finite-projective module has
projective dual already exists as `Module.dual_projective` in Mathlib/LinearAlgebra/Dual/Lemmas
(lines 145--147), and `Module.Flat.of_projective` supplies module flatness. The remaining
hole includes the identification of the shared sheaf Hom term and transport of exactness;
it is therefore not an exact Mathlib match.

Searches in the source library, Sheaf modules, DAG and whole imported blueprint found no
existing statement of either new interface. Logged Mathlib searches: LeanSearch unavailable
(HTTP internal error), LeanFinder found module dual/projective/flat facts but no chain/sheaf
interface, and grep found no matching Hom--dual chain isomorphism. The new node records use
those actual logged queries. The inherited blueprint ancestor is `lem-sc-finite-duality`;
its stored module-valued created.item chain makes blueprint_refs.py ancestor print None,
so the new nodes extend the parent's explicit blueprint.from record instead.

Edge cases checked mathematically: the zero ring and zero module give zero duals; the
flatness lemma allows unbounded P; an empty bound interval forces P and its dual to vanish;
a single term in any degree gives the expected reversed degree and Koszul sign; Q may be
unbounded because only finitely many P terms contribute in any degree. For the chain
isomorphism, the evaluation sign is (-1)^(rs): the d_Q term has sign (-1)^(rs), and the d_P
term has sign (-1)^(rs+r+s+1), exactly the shared Hom differential in degree r+s.

## New nodes

`lem-pc-perfect-ring-dual-term-flat` is in
`dag/nodes/sec-picard-framework/lem-pc-perfect-ring-dual-term-flat.json`, with module
`Sheaf.Algebra.Homology.PerfectRingDualTermFlat`. It records the explicit construction and
termwise flatness argument: project to the sole possibly nonzero Hom factor, evaluate on
the one-object site, dualize a finite-free splitting, and transport tensor exactness.
The flatness property alone has a sorry; the dual is a real Hom construction.

`lem-pc-perfect-ring-hom-tensor-dual-iso` is in
`dag/nodes/sec-picard-framework/lem-pc-perfect-ring-hom-tensor-dual-iso.json`, with module
`Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso`. It records finite-free evaluation and
restriction along a finite-projective splitting, finite diagonal reindexing, and the explicit
sign calculation that makes the degreewise evaluation maps a chain isomorphism.

No interface changes to existing declarations; no change record is needed.

## Second reading by W4

1. **Interface comparison: pass.** Read the repository and sandbox modules with `diff -u`.
   The entire existing `perfectRingHom_isKFlat` signature and its docstring are byte-for-byte
   unchanged: arbitrary commutative A, complexes P,Q, the two-sided zero bound hb, projective
   hp, finite hf, and K-flat hQ all remain. Its conclusion is the same shared Hom K-flatness.
   The four added imports are proof-only. The two other delivered modules are new; there
   are no existing definitions or statements changed and no forced adaptations.
2. **Lean and trust: pass as a decomposition.** Recompiled all three modules in import order
   using lcompile.py, with no errors or warnings. In a scratch copy printed axioms of the
   three private helpers, perfectRingDual, both new theorems, and the item. The helpers and
   actual dual use only propext, Classical.choice, Quot.sound; the two open theorems and item
   additionally use sorryAx, as declared above. There are precisely two syntactic sorry
   proofs, both public named theorems listed above, and no forbidden trust declarations.
   perfectRingDual is the actual shared Hom construction, not a witness of a holed existence
   theorem. Read homComplex_exists: its library proof constructs the product complex and
   verifies its differential and bifunctor laws, so this construction introduces no hole.
3. **Split statements: pass.** Read both new Lean statements and their complete docstring
   proofs against the new JSON nodes. Flatness concerns only individual terms, even for
   unbounded P; the chain isomorphism concerns arbitrary Q without hQ. Neither restates
   K-flatness of Hom. Checked the zero ring, zero complex, an empty interval a>b, single-term
   P in arbitrary degree, and unbounded Q. For the signed evaluation, the d_Q coefficient is
   (-1)^(rs), and the d_P coefficient is (-1)^(rs+r+s+1), matching the Hom differential.
   Read Stacks 0A6A (1), 0ATK (1), and 064K on their official tag pages: the first two give
   derived evaluation/base change, so the chain-level arguments here are correctly marked
   agent-written expansions, not quoted stronger chain-level source statements.
   Repeated search with the different concepts coevaluation, dualBasis, and tensorHom,
   and a LeanFinder query for internal Hom commuting with tensor by the linear dual.
   Searched Sheaf and upstream sources as well. Found the proved
   SheafOfModules.isIso_moduleDualEvaluation_of_retract and upstream CochainComplex.rightDual
   and exactPairingRightDual. These are useful ingredients but not either new statement:
   they require sheaf retraction/dualizability witnesses, and do not identify the shared
   product Hom with total tensor. Neither remaining hole closes by a short application;
   the term-product identifications and one-object-site transport still have to be proved.
4. **Route and pruning: pass.** Read the unit sk-thm-picard-duality and its realized field
   (currently empty statement list and one empty step list); this delivery does not alter
   those records or bypass any realized step. Read the bounded-above site K-flat theorem
   and tensor-closedness interface. The proof first bounds D by -a using product
   extensionality, obtains K-flat D, applies hQ to F tensor D, then transports exactness
   through the associator and tensor of the Hom isomorphism. The site theorem is the same
   generic bounded-flat tool directly in the ambient category. The unused old module-level
   bounded-flat edge is listed under No longer needed, along with the removed old definition
   proof edge. No module is claimed globally pruned. Retained public imports provide types
   and constructions in the new public signatures; all added imports of the item are plain.
5. **DAG agreement: pass.** Read all three delivered node records. Parent proof steps and
   proof_deps match the actual calls and product-bound helper; proof_origin describes the
   explicit-dual reduction. Both new nodes record sources, complete arguments, searches,
   blueprint ancestry, chapter/unit, creation records, and matching Lean declarations.
   The parent's other fields are unchanged. Each new lemma is strictly part of the argument.

Second reading changed the report only: completed the old proof-edge pruning inventory and
recorded this independent review and axiom probe. No Lean proof or signature needed repair.
One upper hole closed and two lower holes added remains a decomposition (net -1), not a
claim of a sorry-free foundational proof or positive ledger progress.

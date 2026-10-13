## What changed

Proved `DerivedCategory.exists_stablyFree_lift_mod_ideal` in
`Sheaf.RingTheory.StablyFreeComplexLift` without changing its statement or public imports.
The proof checks the finite stably free class conditions, applies the existing
`AlgebraicGeometry.complex_lift_class_projective`, evaluates the resulting complex
isomorphism, and proves the free-term clause for that same complex.

Added four proof imports to the item and three new modules, each with one proved public theorem:

- `Sheaf.RingTheory.FiniteModuleSurjectiveModIdeal`: identifies extension of scalars
  with quotient by I and applies Mathlib Nakayama to detect surjectivity.
- `Sheaf.RingTheory.StablyFreeModuleLift`: explicitly constructs the lifted module
  as the kernel of a lifted projection between finite free modules. Nakayama and
  projectivity supply a splitting; tensor exactness identifies its reduction.
- `Sheaf.RingTheory.FiniteProjectiveFreeModIdeal`: lifts a finite reduced basis,
  applies Nakayama, splits the resulting surjection, and applies the finite-module
  surjective-endomorphism theorem to prove injectivity.

All four modules compile in import order through `lcompile.py --all`, with no warnings.
The source construction and the general lifting theorem remain on the unit's original route;
`dag/units/sk-prop-av-cube.json` has no realized node bypassed by this proof.
No definition, target signature, existing theorem signature or other held module was changed.

## Proved and sorry left

Closed the one original hole:
`DerivedCategory.exists_stablyFree_lift_mod_ideal`
(node `lem-sc-pseudo-coherent-lift-stably-free-complex`).

Also proved, without adding any holes:

- `ModuleCat.surjective_of_extendScalars_mod_ideal`
  (node `lem-sc-finite-module-surjective-mod-ideal`).
- `ModuleCat.exists_finite_stablyFree_lift`
  (node `lem-sc-finite-stably-free-module-lift`).
- `ModuleCat.free_of_free_extendScalars_mod_ideal`
  (node `lem-sc-finite-projective-free-mod-ideal`).

No `sorry` remains in any delivered Lean module. Holes closed: 1; holes added: 0;
statements split off with `sorry`: 0. This is a proof from the existing general lifting
statement, not a decomposition into new holes. The imported, unchanged theorem
`AlgebraicGeometry.complex_lift_class_projective` still has its existing `sorry` and
remains a downstream item. Accordingly the main theorem still inherits that dependency;
the three new public theorems depend only on proved Mathlib declarations and one another.

## No longer needed

No original import or proof dependency was removed. The original general complex-lifting
node `lem-sc-complex-lift-class-projective` remains essential. No library module or DAG
node is claimed pruned. The second reader removed these redundant proof imports from
the newly added helpers (each removal checked by compilation):

- `FiniteProjectiveFreeModIdeal`: `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Mathlib.LinearAlgebra.TensorProduct.Basis`, `Mathlib.RingTheory.Finiteness.Finsupp`.
- `StablyFreeModuleLift`: `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Mathlib.LinearAlgebra.TensorProduct.Basis`, `Mathlib.LinearAlgebra.FreeModule.Finite.Basic`, `Mathlib.RingTheory.Finiteness.Finsupp`.

## Where the brief, the DAG or earlier work was wrong

The original node's proof says finite stably free modules are closed under direct summands.
That assertion is false: a nonfree rank-one projective module over a Dedekind domain
with nontrivial class group is a summand of a finite free module, but it cannot be
stably free (its determinant would then be trivial). The class condition in the actual
Lean general lifting theorem is the correct two-out-of-three condition, with the
first term fixed. The new proof establishes that condition by rearranging free stabilizations.
The statement of the item itself needs no correction.

The source tags in the earlier proof text were off by one: Tag 0BC3 is the definition;
the split-exact two-out-of-three result is Tag 0BC4, and module lifting is Tag 0BC5.
The new node proofs cite the correct tags. The published Stacks numbering has moved,
so tags, rather than section/lemma numbers, are used to identify the sources.

WANTED: `literature/stacks-project/more-algebra.tex`, Tags 0BC4, 0BC5, 0BC6 and 0BCB,
for the parent and new module-lifting/freeness nodes; the local file is absent on this machine.
WANTED: `literature/stacks-project/algebra.tex`, Tag 00DV, for the surjectivity bridge.
The mathematical arguments were checked against the authoritative online Stacks pages:
[0BCB](https://stacks.math.columbia.edu/tag/0BCB),
[0BC4](https://stacks.math.columbia.edu/tag/0BC4),
[0BC5](https://stacks.math.columbia.edu/tag/0BC5), and
[0BC6](https://stacks.math.columbia.edu/tag/0BC6).
The formal proofs are marked agent-written in `proof_origin`.

Edge cases: no nontrivial-ring assumption is introduced; Mathlib's finite chosen-basis
index handles the zero ring. Empty stabilization/basis indices are permitted. For I=0,
the construction reduces to the ordinary projection/kernel argument. If I=top, the
unit hypothesis forces the ring to be zero. Freeness is proved for each actual output
term, with no independent per-degree choice of a replacement term.

LeanSearch was attempted for all three new nodes but returned Internal Server Error;
these searches are recorded as unavailable, without claiming absence from that service.
Loogle/LeanFinder and pinned Mathlib/source-library searches supplied the proved building blocks.

## New nodes

`lem-sc-finite-module-surjective-mod-ideal` attaches the proved surjectivity bridge to
`Sheaf.RingTheory.FiniteModuleSurjectiveModIdeal`. It uses the existing Mathlib Nakayama
node; no new assumption or hole is added.

`lem-sc-finite-stably-free-module-lift` attaches the proved kernel construction to
`Sheaf.RingTheory.StablyFreeModuleLift`. Its dependencies are the proved surjectivity
bridge and the existing Mathlib free-module projectivity node. It is a statement about
one module, with no complexes or derived-category hypotheses.

`lem-sc-finite-projective-free-mod-ideal` attaches the proved freeness-detection theorem
to `Sheaf.RingTheory.FiniteProjectiveFreeModIdeal`. It uses the surjectivity bridge and
existing Mathlib projectivity and surjective-endomorphism nodes. It is a statement about
one finite projective module, not a renamed form of the main complex-lifting theorem.

The parent node's proof, proof dependencies and proof origin were updated to match the
compiled specialization. No change record is necessary: existing interfaces were preserved.


## Second reading by N3

1. **Interfaces: PASS.** Compared every delivered module with the repository. The only
   existing module is StablyFreeComplexLift: its existing theorem signature is byte for
   byte unchanged, as are its docstring and public imports. Its added imports are private
   to proofs. The three helper modules are new; no existing definition or other module
   is adapted, and no change record is required.
2. **Proofs and axioms: PASS, relative to the existing open dependency.** Compiled all
   four modules in import order with lcompile.py, without errors or warnings. Scanned
   the sources: no sorry, axiom, unsafe, opaque, implemented_by or extern. Scratch-copy
   #print axioms checks show only propext, Classical.choice and Quot.sound for each of
   the three helper theorems. The main theorem also has sorryAx from the unchanged
   complex_lift_class_projective; it is a closed local hole, not an axiom-free target.
   The lifted module is the explicitly constructed ker(f), with an explicit splitting
   and reduced kernel equivalence. No definition chooses data from an unproved existence
   theorem. Existential elimination of the existing complex-lifting theorem takes place
   only inside the proof of the existential conclusion.
3. **New statements: PASS.** All three are fully proved, strictly smaller module-level
   results; there are no split-off holes. Checked their natural-language proofs against
   the actual Lean constructions and Stacks Tags 0BC5, 0BC6 and 0BCB. Checked zero rings,
   I=0, I=top (the unit condition forces the zero ring), empty basis indices, and zero
   modules. Independent LeanFinder searches for quotient freeness and stable kernel
   lifting, Loogle for surjectivity/Jacobson, and rg of both library roots and upstream
   source found no exact replacement. Module.free_quotSMulTop_iff_free applies only to
   a principal ideal with an additional regularity hypothesis; the local-ring freeness
   results require a local ring, so neither replaces the general helper.
4. **Route and pruning: PASS after import cleanup.** The proof checks the projective
   class hypotheses, uses the existing general lifting theorem, and evaluates its one
   complex isomorphism to prove freeness of the actual output terms simultaneously.
   All old proof_deps are used; No longer needed is complete. Read the unit's realized
   record (empty statement list and one empty step list): no realized route is bypassed,
   and the original general-lifting route remains. Removed seven redundant Mathlib
   proof imports from the new modules; each remaining Mathlib proof import was tested
   for removal and was necessary in the resulting file. Existing public imports stay.
5. **Nodes: PASS.** Compared the existing node with the repository: only proof,
   proof_deps and proof_origin change. Each proof_deps list equals the union of its
   steps' uses. Checked the three new nodes' declarations and verbatim Lean statements,
   source/docstring proofs, chapter/unit, status, creation, blueprint, search and Lean
   attachment fields. No helper merely renames the main statement. The parent node's
   revised class condition matches the private stabilization lemmas; its final step
   matches the evaluated complex isomorphism and proved freeness helper.

Changed only redundant proof imports in the two new lifting/freeness modules and this
report (including correcting the count of imports added to the item). No mathematical
proof, existing statement, public import, definition or DAG route was changed by the
second reading. Holes closed: exists_stablyFree_lift_mod_ideal (1); holes added: none
(0); split-off holes: none (0).

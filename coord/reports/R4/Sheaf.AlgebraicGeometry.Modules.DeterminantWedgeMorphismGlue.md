## What changed

The signature of `AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_glue_family`
is unchanged. Its proof now descends a concatenated wedge map through an exterior tensor
quotient, using Mathlib `Abelian.epiDesc` and `Abelian.comp_epiDesc`. Evaluating the factorization
on tensors of lifted wedges proves precisely the original formula. The two new proof imports
are private imports, so importers see the same existing interface.

Added `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorQuotient`, with a fully proved
`exteriorTensor_quotient_exists`. It constructs the exterior presheaf map using
`exteriorPower.map`, verifies restrictions on pure wedges, sheafifies, and tensors with the
identity. Naturality of the sheafification unit gives its formula. Its epimorphism proof uses
the already proved `exteriorTensor_lift_hom_ext`, rather than repeating local generation and
simultaneous local lifting.

Added `Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel`, containing the remaining
prequotient construction and kernel-annihilation theorem. Its source is the sheaf of lifts,
not the quotient sheaf: its formula does not mention quotient lifts, and its essential
conclusion is that the kernel inclusion is killed. It is a strictly lower part of the
argument, not the original global quotient-morphism existence statement under another name.
The docstring and node contain the construction, the local exterior-quotient relation
argument, and the rank/alternation argument still to be formalized.

The scoped unused-variable linter setting on the original theorem preserves the binder names
and signature: the family has an intentionally unused `U` binder, and this route does not need
the family or its formula. All four existing public imports remain needed by that signature.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_glue_family`
(node `new-wedge-glue-family`). This is a decomposition, not a completed axiom-free proof.

Also proved the new
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_quotient_exists`
(node `new-exterior-tensor-quotient`) without `sorry`.

Exactly one new hole remains, as the whole proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.determinant_liftWedge_kernel_exists`
(node `new-determinant-lift-wedge-kernel`). No holes remain in the item's own module.
Thus one original hole is closed and one lower hole is added; the net hole reduction is zero.
No data definition contains a hole. Both morphisms in the decomposition are determined by
their complete pure-wedge formulas: uniqueness follows from the existing tensor/wedge
extensionality theorem with the identity epimorphism. No arbitrary witness of an
underdetermined existence statement is used in a definition.

Compiled the complete delivered sandbox in import order through `lcompile.py`. The quotient
proof takes about 25 seconds. The compiler checks the descent formula and all existing
signatures. The new kernel theorem was checked in the cases `r₃ = 0` (identity exterior
quotient, zero kernel), `r₁ = 0` (zero first term, isomorphic quotient), empty opens, and zero
coefficient rings. It needs no local freeness of the middle or quotient terms.

## No longer needed

None. No existing imports were removed, and the original node had no recorded proof
prerequisites to prune. The proof does not import `DeterminantWedgeMorphismLocalAt`,
`DeterminantWedgeMorphismLocal`, `DeterminantWedgeMorphism`, or the determinant isomorphism
modules; importing those ancestors would create a cycle. The supplied family is unused, but
its parameter is retained verbatim. The unit's recorded realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node's only step said to perform the corresponding construction/gluing argument,
with no named dependencies. The supplied `φU` are global morphisms, each constrained only on
pure wedges over its indexing open. The statement does not supply overlap compatibility for
arbitrary sections. One cannot justify naturality of the diagonal components by saying only
that pure wedges generate locally: on a smaller open, the larger-open morphism has no given
formula for arbitrary new sections. The delivered descent route avoids that inference and
proves the unchanged existence conclusion independently of the supplied family.

The referenced blueprint file is not present in this machine's read-only literature tree.
The source proof was read from the existing wedge theorem's full docstring and the recorded
DAG proof steps for `lem-sc-determinant-wedge-morphism`; the decomposition records the same
source and explicitly identifies its agent-written categorical descent route. LeanSearch
returned HTTP 500; LeanFinder, Loogle, source search, and blueprint-node search supplied the
other searches.

An exploratory attempt to formalize exterior sheaf multiplication separately reached the
60-second compiler limit in the presheaf tensor naturality elaboration. That incomplete
scratch module was removed, and is not part of this delivery. The verified quotient proof
and descent reduction are retained.

## New nodes

`new-exterior-tensor-quotient`: a generic epimorphism on tensor products of exterior sheaves,
with its exact section formula. Module `ExteriorTensorQuotient`, completely proved. It uses
`def-sc-sheaf-exterior-power` and `lem-sc-exterior-tensor-lift-hom-ext`.

`new-determinant-lift-wedge-kernel`: construction of the wedge on the sheaf of lifts and
annihilation of the exterior quotient kernel. Module `DeterminantLiftWedgeKernel`, one
remaining named theorem with `sorry`. Its proof plan records exterior multiplication,
local quotient relations, and vanishing of wedges above the rank.

Updated the existing `new-wedge-glue-family` node's proof, proof dependencies, and proof origin
to match the quotient-descent Lean proof. No existing statement or definition was changed;
no change record or forced adaptation is required.

## Second reading by R4

1. **Interface: pass.** Compared all delivered files against the read-only repository.
   `determinant_wedgeMorphism_glue_family` is the only existing declaration changed;
   its signature is byte-for-byte identical, including the unused family and its
   hypothesis. The two added imports are proof-only. The other modules are new;
   there are no changed definitions, forced adaptations, or statement changes.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all three
   modules through `lcompile.py` in import order, without errors or warnings.
   Scratch copies with `#print axioms` show only `propext`, `Classical.choice`, and
   `Quot.sound` for `exteriorTensor_quotient_exists`. The kernel theorem and original
   glue theorem additionally use `sorryAx`, as reported. There is exactly one textual
   hole, the entire named theorem `determinant_liftWedge_kernel_exists`; no forbidden
   declarations or hollow definitions occur. The descent map is a local proof term,
   not a public data definition choosing an undetermined witness.
3. **Split statements: pass.** The quotient statement is proved. The kernel statement
   constructs the map on tensors of *lifts* and kills the kernel; categorical descent
   remains a separate, verified reduction, so this is not an application of a renamed
   original existence statement. Its natural-language proof covers exterior quotient
   relations, right exactness of tensoring, and the rank/alternation vanishing. No
   freeness of the quotient or middle term is used. Independently checked degree zero
   (the exterior quotient is an isomorphism), rank zero (the first term is zero and
   the quotient map is an isomorphism), empty opens, zero rings, and the nonsplit
   module sequence `Z --2--> Z --> Z/2` with ranks `r₁ = r₃ = 1`: the target second
   exterior power of `Z` is zero, so the wedge kills the kernel. These are mathematical
   edge-case checks, not claims that the remaining theorem has a Lean proof.
   New LeanFinder query “exterior power quotient kernel generated by wedge containing
   a kernel element” found exterior-power presentation APIs; Loogle `exteriorPower.map`
   found sectionwise mapping, surjectivity, and degree-zero naturality. Independent
   `rg` searches found exterior multiplication and ordinary tensor right exactness,
   but no existing sheaf kernel theorem closing the hole. Existing determinant
   existence/local-data modules import this item, so using them here would be circular.
   Closing the kernel theorem requires substantial sheaf multiplication and quotient
   formalization, beyond a short second-reading repair.
4. **Route and pruning: pass.** The actual proof constructs the exterior tensor quotient,
   uses its section formula and epimorphy, obtains the kernel-annihilating wedge, and
   evaluates `Abelian.comp_epiDesc` on pure wedges. The family assumptions are retained
   even though this stronger construction does not use them. The original node has
   no old `proof_deps`, so `No longer needed: None` is complete. All current public
   imports supply names or instances in signatures; new proof imports are private.
   Read `dag/units/sk-thm-picard-rr.json`: its `realized` fields are empty and unchanged;
   the determinant wedge needed for the Riemann–Roch additivity step is retained.
5. **DAG: pass after correction.** Both new nodes have their required source, creation,
   blueprint, Lean, and search records. Their normalized Lean statements match their
   files, and `proof_deps` equals the union of step uses. The existing node changes
   only `proof`, `proof_deps`, and `proof_origin`. Its steps match the Lean descent.
   The free exterior-power basis node is a Mathlib leaf providing the rank vanishing.
   Changed the kernel node's construction step from `elementary: true` to `false`:
   constructing and sheafifying exterior multiplication is substantive work left
   inside this hole, not an elementary calculation.

Second-reading changes: corrected the original theorem's stale gluing docstring to
explain the actual quotient-descent proof, corrected the quotient theorem's docstring
to describe its actual cancellation/extensionality proof of epimorphy, corrected the
kernel node's elementary flag, and recorded this independent review. No proof term,
statement, definition, hole count, or import changed in the second reading.

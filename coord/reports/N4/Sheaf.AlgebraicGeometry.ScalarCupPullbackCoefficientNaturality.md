## What changed

Replaced the sorry of
`AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_coefficient_naturality`
with a complete Lean proof. The proof first establishes coefficient-map composition
by unfolding `scalarCohomologyMap` and using the two functors' `map_comp` laws and
`ModuleCat.hom_comp`. It then applies pullback-only cup naturality and coefficient-only
cup naturality, in that order. The original signature and docstring are unchanged.

Added proof-only imports of `Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality`
and `Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality`. Each new module has one
public theorem, its source, a resolution-level proof in words, and a matching node.
Updated the item's proof, proof_deps and proof_origin to match this composition.
No definitions, existing signatures, public imports, or unit records changed.

All three delivered modules compile together through lcompile.py with no warnings.
The new statements were checked against the definitions and on degree-zero section
formulas: coefficient naturality is phi(s tensor r) = phi(s) tensor psi(r), with
phi tensor psi on the left; pullback naturality is the normalized tensor of the two
pullback-unit sections. For zero coefficients, zero maps, zero classes, or an empty
scheme these formulas have zero on both sides. Identity coefficient maps give the
identity equality; identity pullback uses its normalized unit and tensor comparison.
The actual classes and operations occur in the hypotheses and conclusions: neither
helper asserts equality of unrelated values under an arbitrary injective function.

## Proved and sorry left

Holes closed: 1 of 1 in the item,
`AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_coefficient_naturality`
(node `lem-sc-scalar-cup-pullback-coefficient-naturality`).
There is no remaining sorry in the item's module.

Holes added: 2, both whole proofs of named public theorems in separate modules:

- `AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_naturality`
  (node `lem-sc-scalar-cup-pullback-naturality`). This has no arbitrary coefficient
  maps and only compares pullback with cup using the normalized tensor comparison.
- `AlgebraicGeometry.Scheme.Modules.scalarCup_coefficient_naturality`
  (node `lem-sc-scalar-cup-coefficient-naturality`). This stays on a single scheme
  and has no scheme morphism, pullback, or tensor-pullback comparison.

This is a decomposition, not a sorry-free proof or net hole reduction: 1 closed,
2 added. The derived-functor composition step combining the two claims is proved
without sorry. Existing holes in imported operations are unchanged.

## No longer needed

No original import or module is pruned. The original public import of
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` is necessary for the
statement and the proved map-composition step. The tensor-pullback node
`lem-weil-pbc-module-pullback-tensor` is now used by the pullback-only helper; it
remains in the transitive proof closure and is not pruned. Its removal from the
item's direct proof_deps merely records where the normalization is used.

No Cech cover, Cech comparison inverse, quasicoherent cup product module, generic
injectivity helper, or unrelated Ext transport import is introduced. In particular
`Sheaf.Paper.CechCupPullbackCompat` is not usable here: its available moduleCup
naturality statements impose quasi-coherence and a different cup interface, whereas
the item covers arbitrary modules with the recorded scalar Ext-defined operations.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's arbitrary-injective-map helper was false and provided no
progress. It remains excluded from the delivery; its old scratch file is only
historical material outside lean/. This attempt uses neither that helper nor a
renamed version of the whole target.

The original node's two proof dependencies give the operations and normalized
module tensor comparison but do not state the needed cup compatibility. The two
new nodes isolate the pullback part and the coefficient part of its resolution
argument. They can be proved independently and neither contains the combined
statement or merely repackages its hypotheses.

Searches: LeanSearch returned Internal Server Error. LeanFinder searches for the
combined and coefficient-only properties returned group-cohomology and nonabelian
H1 hits, not the scalar scheme-module claim. Loogle found generic Ext composition
transport. Mathlib grep returned no matching cup naturality. Local library and DAG
searches found the quasicoherent Cech-interface lemmas described above; blueprint
search for cup product naturality found no duplicate unrestricted scalar node.

Read the current explicit-coefficients change record and used its actual definitions
of scalarUnitMorphism and scalarTensorCoefficient, not the older arbitrary choices.
The local Stacks TeX is unavailable, so the cited official pages for Tags 01F7,
01FD, 07MB and 0FKV were read online. The source arguments describe the resolution
and tensor pairings; the identification with this project's normalized scalar
operations is documented explicitly in the new theorem docstrings.
The theorem-of-the-cube unit's realized route and all its records are untouched.

## New nodes

`lem-sc-scalar-cup-pullback-naturality` at
`dag/nodes/sec-abelian-varieties/lem-sc-scalar-cup-pullback-naturality.json`, module
`Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality`, isolates the inverse-image
Yoneda pairing and the normalized module tensor coefficient square. Its proof in
words identifies the square on pure tensor sections under the pullback adjunction.

`lem-sc-scalar-cup-coefficient-naturality` at
`dag/nodes/sec-abelian-varieties/lem-sc-scalar-cup-coefficient-naturality.json`, module
`Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality`, isolates the fixed-scheme
coefficient comparison and tensor naturality. Its proof in words specifies the
resolution comparison maps, evaluation at 1, and the coefficient tensor square.

Both inherit the item's chapter, unit, and blueprint ancestor, record the searches,
and contain the verbatim Lean signatures. No change record is needed: existing
interfaces and definitions are unchanged. The second reading is recorded below.


## Second reading by N4

1. **Interfaces: pass.** Read the diff of the item against the repository.
   Only two plain proof imports and the original theorem's proof changed;
   its signature and docstring are byte for byte unchanged. The other two modules
   are new. No definition, target, public import, or change record is modified.
2. **Proof and axioms: pass as a decomposition.** Compiled all three modules in
   import order through lcompile.py with no warnings or errors. Scratch copies
   with #print axioms for each theorem show exactly propext, Classical.choice,
   Quot.sound and sorryAx. The item has no direct sorry; the only two new holes
   are the named public theorems listed above. No forbidden declaration or data
   construction occurs. The local map_comp proof follows both functors' map_comp
   laws, and its rewrite followed by the two helper applications has the required
   coefficient composite and degree.
3. **Split statements: pass.** Read the actual definitions, including the explicit
   tensor coefficient and the normalized tensor-pullback comparison. The cocycle
   characterization of moduleExtEquiv determines its comparison; the pullback
   coefficient is determined by its adjunction formula. The helper docstrings
   describe the comparison maps and the tensor coefficient square, rather than
   relying on arbitrary choices. Coefficient naturality on one scheme omits all
   pullback data; pullback naturality omits both arbitrary coefficient maps.
   They are true independent parts of the argument. In degree zero, coefficient
   naturality is the equality of images of a pure tensor, and pullback naturality
   is exactly the normalized unit-section formula of module_pullback_tensor.
   Identity and zero maps, zero coefficients and empty schemes introduce no
   exception. Read the cited official Stacks pages 01FD, 07MB and 0FKV.
   Repeated searches using the different phrases "Yoneda tensor pairing
   naturality under postcomposition of extension coefficients" (LeanFinder) and
   CategoryTheory.Abelian.Ext, "comp" (Loogle), and grep for moduleExtEquiv,
   scalarExtCup and scalarCup_ found no matching unrestricted theorem. General
   Ext composition lemmas do not supply the scalar derived-functor comparison
   or either coefficient square. Neither helper can be closed in a few minutes
   by the available lemmas without further decomposition.
4. **Route and pruning: pass.** The proof uses the elementary map-composition
   argument before the two specialized naturality claims. Each helper's sole
   public import supplies its signature; the item's new imports are proof-only
   and both are used. Checked all old proof_deps: the operations node remains
   direct, and the tensor-pullback node remains through the pullback helper.
   No module is pruned. Read sk-prop-av-cube.json and its realized fields;
   no unit statement, step, or realization is changed or bypassed.
5. **Nodes: pass.** The existing node differs only in proof, proof_deps and
   proof_origin. Its three proof steps match map composition, pullback naturality
   and coefficient naturality. Each new node records its own exact Lean
   signature, source, word proof, dependencies, searches, split status, creator,
   chapter, unit and blueprint ancestry. Their proof_deps are the union of the
   steps' uses. No new hole is missing a node or docstring proof.

Second reading changed only this report, adding the independent checks and removing
its obsolete note that a second reading was still pending. Lean and node records
were retained. The result remains a decomposition: one original hole closed,
two strictly simpler holes added, net minus one; it is not a sorry-free proof.

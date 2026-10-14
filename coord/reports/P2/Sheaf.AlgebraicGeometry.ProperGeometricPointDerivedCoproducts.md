## What changed

The target theorem now installs the derived coproduct instances and applies the existing
`preservesCoproducts_of_preservesCopowers` retract argument. The proper finite-coefficient
cohomology calculation is isolated as the copower theorem in
`Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCopowers`.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.Etale.proper_geometricPoint_pushforward_preservesCoproducts`.

Sorry left:

- `AlgebraicGeometry.Etale.proper_geometricPoint_preservesCopowers`, node
  `lem-etale-proper-geometric-point-derived-copowers`.

## No longer needed

The temporary projection-formula, localization, cohomological-bound, and fixed-cocone
modules were removed. The target does not import the circular geometric-point
projection-formula route.

## Where the brief, the DAG or earlier work was wrong

The original projection-formula route reaches this target through the finite geometric-point
projection module and creates an import cycle. The proof is therefore reduced at the copower
component, while the existing copower-to-coproduct retract theorem supplies the remaining
categorical step.

## Earlier second reading (a previous round; superseded)

The target proof and the new copower statement are open for the second P2 reading. The
reader should compile both modules, check that the target signature is unchanged, and verify
that the copower theorem is strictly the component required by the retract argument.

## Second reading by P2

1. **Signatures and accidental changes.** Compared the delivered target module with the
   repository version. The declaration
   `AlgebraicGeometry.Etale.proper_geometricPoint_pushforward_preservesCoproducts` has the
   identical signature; its proof and proof-only imports are the only changes. The copower
   declaration is new and is recorded by its new DAG node.
2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`, including the
   `--all` import-order check. The target theorem has no `sorry`; the sole remaining `sorry` is
   the named `proper_geometricPoint_preservesCopowers` split listed above, with its source,
   proof sketch, and node. No definitions, axioms, unsafe declarations, or forbidden commands
   were introduced.
3. **Statements and split.** The new copower statement is the single component required by
   `preservesCoproducts_of_preservesCopowers`; it is strictly narrower than the target because
   it concerns one constant family at one object. Its finite-ring, proper geometric-point
   hypotheses and universe levels match the target component exactly. Searches recorded in the
   node found no existing declaration of this statement.
4. **Pruning and route.** The target proof uses only the derived-coproduct existence theorem,
   the copowers-to-coproduct retract theorem, and the new copower component. The former
   projection-formula, localization, filtered-colimit, and K-injective-resolution imports are
   therefore removed from the target module and are documented under `No longer needed`.
5. **DAG and unit.** The target and copower node records match the Lean declarations and their
   proof dependencies. The unit route remains the categorical retract step followed by its
   copower component; no unit statement or realized step was bypassed.

The second reading found no mathematical or interface defect. The changes are the target proof,
its reduced proof-only imports, and the new split copower module/node; no existing target
statement was weakened or altered.

## New nodes

- `lem-etale-proper-geometric-point-derived-copowers`, implemented by
  `Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCopowers`.

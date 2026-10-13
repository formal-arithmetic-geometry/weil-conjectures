## What changed

Repaired the duplicate-statement rejection by replacing the explicit restatement of
`finite_structure_product_compatibility` with the theorem alias
`@finite_structure_product_exists_core`. The alias imports and reuses the existing theorem
and inherits its complete existential type. All universes and arguments remain those of the core.
The original public core import is retained because the alias signature uses its declaration.
The node records this alias route. The existing false arbitrary-`μ` interface correction and
forced adaptation of `Sheaf.Paper.FiniteStructureProductExists` remain documented in
`coord/changes/finite_structure_product_compatibility.md`.

## Proved and sorry left

Closed the one local hole, `AlgebraicGeometry.finite_structure_product_compatibility`, by
reusing `AlgebraicGeometry.finite_structure_product_exists_core`. No new holes or declarations
with `sorry` are introduced; no holes remain in either delivered module. This is reuse of an
existing result, not a new proof of the core theorem. The imported core theorem currently rests
on the existing hole `AlgebraicGeometry.finite_structure_product_section_identity`.

## No longer needed

The explicit duplicate existential statement is retired in favor of the existing core theorem.
The earlier proposed split modules and nodes remain absent. No proof imports of
`Sheaf.Paper.FiniteStructureReducedProducts`,
`Sheaf.Paper.FiniteStructureTensorPowersSupported`, or
`Sheaf.AlgebraicGeometry.PinnedCompletionHomLift` are needed in the item's module.
The original public import of `Sheaf.Paper.FiniteStructureProductCore` suffices; the six
redundant public imports from the returned delivery were removed.
The node no longer uses `lem-weil-pbc-module-pullback-tensor`,
`lem-weil-pbc-affine-pushforward-base-change`, or
`def-pc-tensor-pullback-composition-iso` as direct proof dependencies; its sole direct proof
node is `lem-weil-pbc-finite-structure-product-core`. These facts may still be needed by the core.
No claim is made that they leave the whole target closure.

## Where the brief, the DAG or earlier work was wrong

The previous delivery already applied the core theorem, but still wrote out an identical
existential statement. The landing check correctly rejected that duplication. The repaired
module aliases the existing theorem instead. The earlier arbitrary-`μ` interface was false:
a zero multiplication does not preserve products on a nonzero structure sheaf. The existential
interface matches the existing core and the DAG's statement. Target signatures are unchanged.

## Forced adaptations

`Sheaf.Paper.FiniteStructureProductExists` (unclaimed) keeps its exact original public signature.
Its original proof applies compatibility to an extra explicit `μ` and fails after the interface
correction with `Function expected` because compatibility now concludes `∃ μ, ...`.
Only its final proof is changed: the obsolete preliminary witness construction and application
to that witness are replaced by direct application of the existential alias. Its imports,
visibility, statement and all preceding declarations are unchanged. The original compiler error
and the successful adapted compile are checked again by the delivery dry run.

## Second reading by H3

1. **Reading and interface check.** Compared both delivered modules with the repository
versions. The compatibility theorem's previous arbitrary-`μ` interface was inconsistent with
the core existence theorem; the delivered alias now has exactly the core existential type. The
adapted existence module preserves its public statement byte for byte.

2. **Proof check.** Compiled both modules with `lcompile.py --all`; both compile without errors
or warnings. The compatibility proof is a direct application of the existing core theorem, and
the existence proof applies the resulting existential theorem. No new `sorry`, axiom, unsafe,
opaque, or hollow definition is present. The remaining imported core theorem's named hole is
outside this delivery.

3. **Statement check.** The alias introduces no additional hypotheses or conclusions and does
not weaken the existential result. The adapted caller merely consumes the returned witness. No
new split-off statement or node was added; the existing node's proof route is updated to the
core theorem.

4. **Pruning and route check.** The module retains only its required public core import. The
unit route remains through the finite-structure product core node; the removed imports and
obsolete direct proof dependencies are listed above. No target statement was changed.

5. **DAG and delivery check.** The node's Lean declaration, proof dependency, and proof origin
match the alias proof. The forced adaptation changes only the obsolete proof body in the
unclaimed caller, with its original compiler failure and successful recompilation recorded above.

I changed the compatibility declaration to reuse `finite_structure_product_exists_core`, updated
the adapted caller, and added this second-reading record.

## Forced adaptations

### Sheaf.Paper.FiniteStructureProductExists
Original against changed dependencies failed:
```
/tmp/forced-adaptation-0z86wbi_/lean/Sheaf/Paper/FiniteStructureProductExists.lean:130:12: error: Function expected at
  finite_structure_product_compatibility A I X f i hi hp c hc Yn fnY gn hcart hw G hG hproper ψ hψ
but this term has type
  ∃ μ,
    ∀ (n : ℕ) (U : X.Opens),
      have a := fun x ↦
        (ConcreteCategory.hom
            (Hom.app
              (finiteStructureAdjoint (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
                (fnY n) G (ψ n).hom)
              U))
          x;
      ∀ (x y : ↑Γ(G, U)), a ((ConcreteCategory.hom (Hom.app μ U)) (tmulSection x y)) = a x * a y

Note: Expected a function because this term is being applied to the argument
  μ

(with the modules compiled into /tmp/forced-adaptation-0z86wbi_/.lbuild) [3.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

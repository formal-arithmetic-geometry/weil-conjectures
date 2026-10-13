## What changed

Proved `exists_finite_adjoin_with_jacobson_power` from the integral-overring
Jacobson-power theorem and a new finite-adjoin auxiliary theorem. Added the
proof-only import `Sheaf.AlgebraicGeometry.AdjoinFiniteFractionSpec` and the new
module `Sheaf.AlgebraicGeometry.AdjoinFiniteFractionSpec`.

## Proved and sorry left

The target declaration `exists_finite_adjoin_with_jacobson_power` is proved.
The new declaration `exists_adjoin_finite_fraction_spec` remains a single named
`sorry`, recording the finite-adjoin, compatible integral-closure map, and
lying-over construction needed by the proof.

## No longer needed

No existing imports or proof-dependency nodes were removed. The target's
unused `hdim` binder remains part of its fixed interface.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the explicit construction of the compatible algebra
structure from the adjoin subalgebra into the integral closure. This is isolated
in the new auxiliary node; the target statement is unchanged.

## New nodes

`adjoin-finite-fraction-spec`: new module and node for the finite adjoin,
fraction-field, compatible injective map, and prime-spectrum surjectivity
subargument. No change record is needed.

## Second reading by K3

1. Compared both delivered modules with the repository versions. The target
   declaration and all existing interfaces are unchanged; only proof imports,
   the target proof, and the new auxiliary theorem/module were added.
2. Compiled the two modules together with `lcompile.py --all`; compilation
   succeeds. The only remaining `sorry` is the named theorem
   `exists_adjoin_finite_fraction_spec`, documented with node
   `adjoin-finite-fraction-spec`; there are no hollow definitions or forbidden
   declarations.
3. Checked the split theorem statement against the adjoin and lying-over
   construction in Varieties Lemma 09N2. It is a strictly lower auxiliary
   statement and exactly the data consumed by the target proof.
4. The target proof follows the unit route: it invokes the finite-adjoin
   construction and then `integral_overring_jacobson_power`; no unit step is
   bypassed. No existing import was removable.
5. The DAG nodes match the declarations, imports, and proof route. The unit's
   `realized` record is unchanged.

I changed only this report section; no Lean statement or definition was
changed during the second reading.

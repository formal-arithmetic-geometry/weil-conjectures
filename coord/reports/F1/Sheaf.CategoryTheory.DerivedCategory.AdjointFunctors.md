## What changed

Replaced the proof of `CategoryTheory.Adjunction.exists_derived_adjunction_of_essentially_constant` by a real witness assembly from two strictly smaller named construction theorems. Added modules for assembling everywhere-defined derived functors and for assembling the compatible derived adjunction.

## Proved and sorry left

The target theorem is proved by combining the two intermediate theorems. The intermediate declarations `CategoryTheory.exists_everywhere_defined_derived_functors` and `CategoryTheory.exists_derived_adjunction_compatibility` remain as named `sorry` statements.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted explicit Lean statements for the two assembly steps; they are now split into independently provable construction claims.

## New nodes

`new-everywhere-defined-derived-functors`; `new-derived-adjunction-compatibility`.

## Earlier second reading (a previous round; superseded)

The target proof and both intermediate signatures compile in the sandbox; the intermediate claims are strictly smaller construction steps and retain the Stacks proof dependencies.

## Second reading by F1

1. Compared the delivered target module against the repository version. The target declaration's
   signature is unchanged; only its proof and proof-only imports changed. The two added modules are
   new split statements, and their declarations match their Lean source.
2. Compiled all three modules with `lcompile.py --all`; compilation is clean. The only remaining
   `sorry`s are the two named construction theorems, with no `axiom`, `unsafe`, or hollow definition.
3. Reviewed the split statements and tested the original compatibility interface conceptually: it
   was false for arbitrary RF/LG and arbitrary comparison maps. I repaired it by requiring the
   essential-constancy hypotheses and the corresponding `IsRightDerivedFunctor`/
   `IsLeftDerivedFunctor` properties. These are strictly smaller than the target and are the
   hypotheses used by the Stacks assembly argument.
4. The target still follows the documented two-step Stacks route. No imports or proof dependencies
   became unused; the added public imports in the compatibility module are required by its public
   hypotheses.
5. Updated `new-derived-adjunction-compatibility` so its statement, dependencies, and proof route
   agree with the repaired Lean declaration. The unit route remains assembly followed by compatible
   adjunction.

The second reading changed the compatibility theorem's interface and its node metadata, updated the
call in the target proof, and expanded this report.

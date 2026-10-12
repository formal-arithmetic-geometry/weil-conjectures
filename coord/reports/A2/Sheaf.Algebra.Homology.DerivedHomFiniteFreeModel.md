## What changed

Added `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModelAux` with the strictly simpler
bounded-above finite-free comparison theorem, left as a named `sorry`. The target theorem
now applies that comparison and transports across the quasi-isomorphism `f` using
`DerivedCategory.Q` and contravariance of derived internal Hom. Removed the target's direct
proof-only imports of the bounded-resolution and acyclic-Hom modules; the auxiliary module
imports them.

## Proved and sorry left

`AlgebraicGeometry.derivedInternalHom_of_boundedAbove_finiteFree` is proved. The new
`AlgebraicGeometry.derivedInternalHom_of_boundedAbove_finiteFree_aux` remains `sorry` in
node `lem-sc-derived-hom-finite-free-model-aux`.

## No longer needed

The target module no longer directly imports `Sheaf.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic`
or `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`; they are dependencies of the
auxiliary module.

## Where the brief, the DAG or earlier work was wrong

The original target proof plan omitted the substantial categorical construction needed to
assemble the injective-resolution comparison. I split precisely that comparison into one
strictly simpler intermediate theorem and gave the remaining transport proof completely.

## New nodes

`lem-sc-derived-hom-finite-free-model-aux`, stated in
`Sheaf.Algebra.Homology.DerivedHomFiniteFreeModelAux`.

## Earlier second reading (a previous round; superseded)

The target transport proof preserves the exact target signature and uses the auxiliary
statement only for the E,G comparison; the new statement is strictly simpler because it
omits K and f. The unit route remains represented by the auxiliary theorem's three proof
steps.

## Second reading by A2

1. **Signatures and visibility.** Compared the delivered target module with the repository
   version: the target declaration is byte-for-byte unchanged, and the auxiliary declaration
   is new. The target proof-only imports were moved behind the auxiliary module; no unrelated
   declarations or target statements changed. Verdict: pass.

2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; both compile cleanly.
   The target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. Its only remaining imported open assumption is the named auxiliary
   theorem, whose `sorry` is recorded below and in its node. Verdict: pass.

3. **Split statement.** Checked the auxiliary theorem against the imported declarations and
   searched Mathlib and the repository. It is true as the injective-resolution/acyclic-Hom
   comparison, is strictly simpler than the target because it omits `K` and `f`, and is not a
   duplicate of an existing declaration. Its docstring gives the source and proof route, and
   node `lem-sc-derived-hom-finite-free-model-aux` matches its Lean signature. Verdict: pass.

4. **Pruning and route.** The target now uses the shortest available transport proof after the
   auxiliary comparison. The removed bounded-resolution and acyclic-Hom imports remain needed
   by the auxiliary module, and the unit's injective-resolution, acyclic-Hom, and comparison
   steps remain represented in that node. Verdict: pass.

5. **DAG agreement.** Verified the target and auxiliary node `proof`, `proof_deps`,
   `proof_origin`, `lean` records, unit, and chapter agree with the delivered declarations.
   The auxiliary node is the only added node and is marked `split`; no statement or definition
   was changed. Verdict: pass.

Changed only this report section after the prior reading: recorded the five checks and their
verdicts. No Lean source or DAG content required repair.

## What changed

Proved `AddCommGroup.exists_compatible_lift_of_bijective_nsmul` in
`Sheaf.GroupTheory.CompatibleAbelianGroupLifting`, preserving its complete signature,
universes, hypotheses, visibility and original public imports. Added private proof imports
of `Mathlib.Algebra.EuclideanDomain.Int`, `Mathlib.Algebra.Module.Projective`,
`Mathlib.Algebra.Module.Torsion.Free`, `Mathlib.LinearAlgebra.FreeModule.PID` and
`Mathlib.RingTheory.Finiteness.Basic`. Each supplies a used instance or theorem.

The proof first descends `a` to `D = u.range`. It extends this map to the preimage `P`
of the torsion subgroup of `C = B / D` by choosing the unique lift whose multiple by
`N = Nat.card (torsion C)` has the prescribed value. Existence comes from correcting
an arbitrary lift in `i(J)`; injectivity of multiplication by `N` proves uniqueness and
therefore additivity. The group `Q = C / torsion C` is finitely generated and torsion-free,
so Mathlib makes it free over the integers. Two applications of projective lifting
supply a section of `B → Q` and a lift of its composite with `b₀`. Combining these with
the corrected lift on `P` proves both required equalities.

Updated the proof docstring and the `proof`, `proof_deps`, and `proof_origin` of both
nodes attached to this declaration: `lem-per-compatible-abelian-group-lifting` and
`lem-sfb-compatible-abelian-group-lifting`. No other module or statement changed,
so no change record or consumer adaptation is required. The algebra input remains
below the units' log-chart arguments and changes neither unit's statement nor route.

Validation: the complete module compiles without errors or warnings in 4.3 seconds
through `lcompile.py`; all lines have at most 100 characters. The delivery tool also
runs its declaration axiom probe. There is no `sorry` in the file. The argument covers
zero groups, trivial kernel, trivial torsion subgroup (`N = 1`), empty free quotient,
`u = 0`, and `u` an isomorphism; it never assumes a nontrivial group or positive rank.
All witnesses come from proved existence assertions or the given surjectivity hypotheses.

Searches actually run through `msearch.py` for this item included:

- LeanFinder: “Extend compatible homomorphisms of finitely generated abelian groups
  across a surjection if finite kernel and torsion cokernel orders act invertibly on
  the kernel”. No whole-theorem match; `AddMonoidHom.liftOfSurjective` is used for descent.
- Loogle: `"Module.Free", "IsTorsionFree"` found `Module.free_iff_isTorsionFree`;
  Loogle for `Module.projective_lifting_property` found exactly the lifting API used.
- Grep: `free_of_finite_type_torsion_free|projective_lifting_property|card_nsmul_eq_zero`
  confirmed the component lemmas; source inspection checked their signatures.

The finite torsion-free freeness step reuses the existing Mathlib leaf
`lem-trf-fg-torsionfree-group-free`. This is a generic algebra tool and introduces
no trace-formula argument. Searches of `lean/Sheaf`, `lean/WeilConjectures` and
`dag/nodes` found no distinct existing declaration of the compatible lifting theorem.

## Proved and sorry left

Closed the single hole in
`AddCommGroup.exists_compatible_lift_of_bijective_nsmul`, shared by nodes
`lem-per-compatible-abelian-group-lifting` and
`lem-sfb-compatible-abelian-group-lifting`.

Holes closed: 1. Holes added: 0. Sorries remaining in the item: 0.
No split-off statements, new public declarations or new nodes.

## No longer needed

No original Lean import was removed and no module was withdrawn.
The full cyclic structure theorem dependency
`lem-sbc-finitely-generated-abelian-group-structure` and its planned cyclic-factor
cardinality/presentation calculation are unnecessary for this proof: the single
integer `Nat.card (torsion C)` corrects lifts on all of `P` at once. We use the weaker
finite torsion-free freeness leaf for the remaining quotient. This is dependency
pruning for this item only; the structure-theorem leaf can still serve other nodes.

Removed the per node's proof edge and obsolete `tool_uses` entry to
`lem-sfb-compatible-abelian-group-lifting`. Both nodes are attached to this very same
Lean declaration, now proved directly. Neither node nor its module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original per-node proof and theorem docstring say to apply the sfb lifting node,
but both nodes' Lean attachments name the same declaration. In Lean that application
would be circular. The sfb node has a valid independent six-step group-theoretic proof;
the present proof keeps its kernel descent and error-correction mechanism, replacing
individual cyclic presentations with torsion saturation and free projectivity.
Both node copies now describe this actual proof, with their statements and attachments
unchanged. The original source correctly labels the general theorem as agent-formulated;
this report does not attribute it verbatim to ILO or Kato.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

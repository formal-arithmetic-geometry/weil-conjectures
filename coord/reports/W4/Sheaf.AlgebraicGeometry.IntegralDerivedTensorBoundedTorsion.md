## What changed

Restored the quarantined item module from its recorded archive. Its public theorem statement,
public imports, and Lean attachment are unchanged. Replaced the Kunneth/truncation-colimit
proof plan with a direct proof using hereditary flatness of integer sheaves and a torsion
complex representative. All additional helpers are private and proved in the item module; helper instances are
explicitly local. The preflight-requested record of proof-local elaboration commands is
coord/changes/w4-integral-tensor-proof-local-instances.md. No consumer adaptation is needed.

For the bound, geometric stalks show that subobjects of flat integer sheaves are flat.
Upper good truncations then show every complex of flat integer sheaves is K-flat. Lower
truncation of a flat resolution at a-1 remains flat, because exactness makes the boundary
opcycles a subobject of the next flat term. Tensor this model with a strict lower model of B.
For torsion, use the existing bounded-below torsion-complex representative under the exact
equivalence between integer-module sheaves and abelian sheaves. Tensor it with a K-flat
resolution of B. Geometric stalks show that tensor products, coproducts, subobjects and
quotients preserve torsion. No common annihilator is introduced.

The complete module compiled through lcompile.py in 13.6 seconds with no warnings or errors.
Public imports and the theorem signature were compared verbatim with the quarantine source;
there are no new public declarations, definition holes, or raised heartbeat limits. Local
instance priorities align the lifted-integer ring with the derived-category coefficient
instance and avoid expensive definitionally equal instance comparisons.

The DAG proof, proof dependencies, proof origin, and obsolete tool-use entries are updated.
The unit has no realized proof steps requiring the abandoned lower-level Kunneth route.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.integral_derivedTensor_boundedBelow_torsion
(lem-kun-integral-derived-tensor-bounded-torsion), the original one hole.
Added: none. Left in this module: none. Split off: none.

This proof uses the existing declaration
CategoryTheory.Sheaf.exists_torsion_complex_representative
(lem-trf-torsion-sheaf-complex-representative), which already contains sorry. It adds no
hole to that declaration and does not claim to prove it. Other source-library dependencies
are used as published. Counts here refer to the item body, not a claim that its entire
transitive axiom closure is now sorry-free.

## No longer needed

Removed direct proof imports:

- Sheaf.Algebra.Homology.FilteredColimitDerivedTensor
- Sheaf.Algebra.Homology.IntegralBoundedKunnethExact
- Sheaf.AlgebraicGeometry.AbelianSheavesGModules
- Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
- Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
- Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
- WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
- WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

The proof no longer needs lem-exc-abelian-sheaves-gmodules, lem-kun-stalk-as-pullback,
lem-kun-inverse-image-monoidal, lem-kun-integral-bounded-kunneth-exact,
lem-pc-filtered-colimit-derived-tensor, lem-kun-tensor-sym, lem-weil-pbc-tor-symmetry,
def-weil-pbc-tor-modules, or lemma-weil-pbc-geometric-stalk-conservative. There is no
passage from a bounded Kunneth sequence to the unbounded result and no separate Tor
calculation or derived stalk comparison. The good-truncation and torsion-stalk criteria
remain needed via the proved source interfaces. Remove the obsolete top-level tool-use
entries for the Galois equivalence, filtered derived tensor colimits, and Tor symmetry;
retain the torsion-sheaf characterization entry. No source-library declaration is deleted,
and no claim is made that another parent does not need one of these modules.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, not withdrawn; this delivery restores its recorded attachment.
The old proof plan is mathematically valid but considerably longer than the available
hereditary-flat and torsion-representative route. The lower-bound loss of one is essential:
for Z/2 in degree zero in both factors, Tor_1 occurs in degree -1. The proof preserves this
loss, allows zero objects, arbitrary bounds, and torsion with no bounded exponent.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

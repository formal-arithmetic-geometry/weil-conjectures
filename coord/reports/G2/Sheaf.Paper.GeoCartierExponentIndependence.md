## What changed

Proved `SheafOfModules.GeoCartierExponent.geoCartier_exponent_independence` in
`lean/Sheaf/Paper/GeoCartierExponentIndependence.lean`, preserving its complete signature
and all existing public definitions and public imports. All additional helpers are private
and proved in this module. Updated the existing node's proof, proof dependencies, proof origin
and obsolete tool-use entries to match the implementation. No other library module changes.

The proof environment commands are recorded in
`coord/changes/geo-cartier-exponent-proof-environment.md`, as required by the conservative
preflight classification of `open` and local `attribute` commands. They change no public
declaration. The complete module compiled with zero warnings in 29.8 seconds before delivery.

Flatness makes `ordinarySingle` invertible by the independent-universe bounded-flat criterion.
The quotient and torsion isomorphisms are the preimages of the actual derived comparison under
fully faithful single and shifted-single functors. The normalized units prove the quotient
formula. For torsion, the kernel lift multiplying by m/n gives a morphism of Kummer sequences.
The exact Hom sequence identifies this lift with the ordinary transpose: maps from the
m-divisible middle object to the m-torsion target vanish. This establishes both section formulas
and both displayed derived identities without any split-off theorem.

The new private proof imports are `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`,
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
`WeilConjectures.CategoryTheory.Abelian.Flat.Basic`, and
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.
The existing private Mathlib fully-faithful single import remains.

## Proved and sorry left

Closed 1 hole: `SheafOfModules.GeoCartierExponent.geoCartier_exponent_independence`
(node `lem-geo-cartier-exponent-independence`).

Added 0 holes. There are 0 `sorry` occurrences in the delivered module, and no new modules
or public declarations. Existing normalized-identification and scalar-adjunction declarations
are used as the stated dependencies of this stage; their proofs are outside this delivery.

## No longer needed

Removed these private imports from the item:

- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`:
  replaced by the existing independent-universe bounded-flat theorem.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  no new resolution of the integral objects is needed after using the recorded identifications.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  their required interfaces are supplied by the imports actually used.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  use the normalized ordinary and derived adjunctions recorded in DivisibleExtensionDerivedReduction.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  use the single-triangle interface and its exact Hom sequence directly.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  already supplied by the public DivisibleExtensionDerivedReduction import.

Removed direct proof-dependency edges to `lem-pc-bounded-above-flat-kflat-site`,
`lem-pc-kflat-resolution`, `lem-sf-derived-homology-long-exact`, and
`lem-pur-sheaf-ring-derived-coefficient-adjunction`; removed their obsolete `tool_uses`
entries as well. The last remains an unchanged statement dependency. Its general interface
is not reproved here. The old bounded-flat edge is replaced by
`lem-weil-pbc-independent-bounded-flat-kflat`.

The old proof's local tensor inverses and local surjectivity/kernel calculations (steps 7–8)
are unnecessary: invertibility follows directly from the derived comparison and flatness.
The tensor-product definition remains used for the pure-tensor formulas. The public successive
quotient normalization import remains, including its actual scalar-first pure tensors.
No module is withdrawn; none of the listed dependencies is claimed unnecessary for its other
consumers, and no adopted source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The old bounded-flat proof dependency has incompatible universe/flatness interfaces for this
statement. The existing independent-universe theorem fits without changing any assumptions.
The normalized one-exponent identifications already provide the quotient-unit equation, so
reconstructing it by another resolution and homology sequence is unnecessary.

The implementation constructs the residue-linear torsion map as the ordinary transpose first,
then identifies its integer restriction using boundary injectivity. The injection is proved
from the exact Hom sequence and the stated divisibility/torsion hypotheses; the Kummer
boundary is not cancelled without justification. This avoids any additional lemma asserting
fullness of scalar restriction along a constant quotient ring map.

Temporary decomposition modules from early development are excluded from the delivery.
The final packet has one Lean module, the existing node and the proof-environment change record.
The Cartier unit route,
target statements, and all public interfaces are unchanged.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

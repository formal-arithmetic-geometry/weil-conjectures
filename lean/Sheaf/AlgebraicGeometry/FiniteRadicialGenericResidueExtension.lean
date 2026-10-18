/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.FieldTheory.PurelyInseparableDegreePIntermediate
import Sheaf.AlgebraicGeometry.FiniteRadicialAffineShrinking
import Sheaf.AlgebraicGeometry.PurelyInseparableRootCover

/-! # Finite radicial realization of a generic residue-field extension

Source: Stacks Project, More on Morphisms, Tag 0GK7, purely inseparable tower paragraph.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A finite purely inseparable extension of the residue field at a generic point
can be realized by a reduced affine finite radicial cover after shrinking the base.
Source: Stacks Project, More on Morphisms, Tag 0GK7, the paragraph beginning
"If the characteristic of k is zero".
(blueprint: lem-weil-pbc-finite-radicial-generic-residue-extension)

Proof: Write the reduced affine base as Spec A, with η corresponding to a minimal
prime p. The local ring A_p is its residue field k. For characteristic zero the
extension is trivial. Otherwise invert an element outside p annihilating the integer
characteristic, so the base has characteristic p. Induct on the degree of K/k, using
a tower with successive degree-p purely inseparable extensions. At each stage invert
an element outside the current generic prime to write the p-th power of the next
generator in the base ring. Adjoin it as a root of t^p-a. This monic quotient is finite
free. Its spectrum map is surjective by existence of roots in field extensions and
universally injective by uniqueness of roots in characteristic p. Localizing at the
unique generic point gives the specified next field, since its defining polynomial
is the minimal polynomial. The finite radicial surjection assertion for this quotient
is `finite_radicial_root_cover`. The unique prime above the old minimal prime is minimal:
a prime below it maps to a prime below the old minimal prime, hence to that same prime,
and uniqueness of the prime above it forces equality. Reduce the ring, which preserves
this generic local field and gives another finite radicial surjection.
A shrinking on an intermediate cover
can be made on the original base by removing the finite image of its closed complement;
an affine refinement preserves affineness, as formalized by
`exists_affine_shrinking_under_finite_radicial`. Base changing along the refined open
preserves the distinguished generic residue field since an open immersion induces an
isomorphism on residue fields. Compose the resulting finite radicial
covers. Their generic residue-field identifications compose to e, and their naturality
gives the displayed equality on the original residue field. The zero-length tower
uses the identity cover. All rings are explicitly constructed by quotient, reduction,
and localization; no definition selects a witness of this existence theorem. -/
theorem exists_finite_radicial_generic_residue_extension
    {S : Scheme.{u}} [IsAffine S] [IsReduced S]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (K : Type u) [Field K] [Algebra (S.residueField η) K]
    [Module.Finite (S.residueField η) K] [IsPurelyInseparable (S.residueField η) K] :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsAffine U.toScheme ∧ IsAffine V ∧ IsReduced V ∧
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (ηV : V) (hq : (g ≫ U.ι) ηV = η),
        (∃ Z ∈ irreducibleComponents V, IsGenericPoint ηV Z) ∧
        ∃ e : V.residueField ηV ≃+* K,
          e.toRingHom.comp
            (((S.residueFieldCongr hq).inv ≫ (g ≫ U.ι).residueFieldMap ηV).hom) =
              algebraMap (S.residueField η) K := by
  sorry

end AlgebraicGeometry

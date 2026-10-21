module

public import Sheaf.Paper.CompactSupportCoefficientChange
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.StratumScalarExtension

/-! # The coefficient comparison in intrinsic constant-ring coordinates

Source: Stacks Tags 07A6, 0GL5 and 0GL6; blueprint coefficient comparison
(blueprint: def-coef-compact-support-tensor-comparison).

The published tensor presentations use module-valued sheaves. This interface evaluates
that same universal-arrow definition on the normalized intrinsic scalar adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The published universal-arrow coefficient comparison in intrinsic coordinates.
The tensor presentations are the units of the existing normalized derived adjunctions;
the inverse Hom bijection is exactly the defining operation of
`compactSupportCoefficientComparison`. No comparison is chosen independently.
Source: Stacks Tags 07A6, 0GL5 and 0GL6
(blueprint: def-coef-compact-support-tensor-comparison). -/
def intrinsicCompactSupportCoefficientComparison
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) φ)).obj
        ((sfIntrinsicCompactSupport c A).obj K) ⟶
      (sfIntrinsicCompactSupport c B).obj
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ)).obj K) :=
  ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).symm
    ((sfIntrinsicCompactSupport c A).map
        ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ)).unit.app K) ≫
      (sfCompactSupportRestriction c φ).hom.app
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ)).obj K))

end AlgebraicGeometry.ProEtale

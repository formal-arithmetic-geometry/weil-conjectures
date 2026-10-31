/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientTensorCtf
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.TensorMateBaseChange

/-!
# Composition of cohomologically smooth morphisms

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-qlbar-two-colimit/lem-pur-co-smooth-composition.md
(blueprint: lem-pur-co-smooth-composition).

The finite-coefficient predicate and relative dualizing objects are those of the
recorded definition of cohomological smoothness, in canonical pro-etale comparison
coordinates. The isomorphism is in the derived category of pro-etale module sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Cohomological smoothness is stable under composition, and the dualizing object
of the composite is the tensor product of the first dualizing object with the
pullback of the second.

Source: latest blueprint, sec-six-functors-basics/sk-prop-qlbar-two-colimit,
lem-pur-co-smooth-composition (blueprint: lem-pur-co-smooth-composition).

Proof plan:
1. Separatedness and finite type are stable under composition. Apply
   lem-pur-constructible-tensor-composition to the two tensor clauses of
   def-pur-co-smoothness. It gives an isomorphism from
   W = omega_f tensor Lf*omega_g to omega_(gf), identifying the composite tensor
   mate with theta_(gf) after tensoring with that isomorphism. All factors of the
   composite tensor mate are invertible, so theta_(gf) is invertible. Inverting
   the isomorphism W to omega_(gf) gives the displayed dualizing identification.
2. Choose the two-sided Dctf inverses M_f and M_g in the invertibility clauses.
   Exceptional inverse image preserves Dctf, so both dualizing objects are Dctf.
   By lem-sf-pullback-tor-amplitude and lem-sf-tensor-ctf, W and
   B = Lf*M_g tensor M_f are Dctf. The monoidal pullback comparison of
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback, associativity, and the two
   inverse identities give W tensor B and B tensor W isomorphic to the unit.
   Pullback preserves the coefficient unit by def-weil-derived-pullback-tensor-hom.
   Transport along W isomorphic to omega_(gf) proves the first clause.
3. For an arbitrary base change of the composite, form the two constituent
   Cartesian squares. Their vertical maps remain separated finite type by
   lem-pod-separated-finite-type-base-change. The base-change clauses for f and g
   give invertible unit mates. Monoidal pullback makes the pulled-back omega_g
   invertible. Apply lem-pur-tensor-mate-invertible-input before and after base
   change, then lem-pur-tensor-mate-base-change: its two tensor mates and its
   tensor of the unit base-change mate are invertible, so the base-change mate
   for f at omega_g is invertible. The equality of
   lem-pur-exceptional-base-change-pasting expresses the composite unit mate as
   this map followed by the image of g's unit mate and the two compositors.
   Every factor is invertible, proving the third clause. Together with the
   first two steps this proves all three cohomological-smoothness conditions. -/
theorem cohomologicallySmooth_comp
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (hf : IsCohomologicallySmoothFiniteCompared P f)
    (hg : IsCohomologicallySmoothFiniteCompared P g) :
    IsCohomologicallySmoothFiniteCompared P (f ≫ g) ∧
      Nonempty (@finiteComparedDualizing P X Z (f ≫ g)
        (P.finiteComparedCompactification (f ≫ g)
          (Z ↘ Spec (.of P.field.k))).hasCompactification ≅
        ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
          (@finiteComparedDualizing P X Y f
            (P.finiteComparedCompactification f
              (Y ↘ Spec (.of P.field.k))).hasCompactification)).obj
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
            (@finiteComparedDualizing P Y Z g
              (P.finiteComparedCompactification g
                (Z ↘ Spec (.of P.field.k))).hasCompactification))) := by
  sorry

end AlgebraicGeometry.ProEtale

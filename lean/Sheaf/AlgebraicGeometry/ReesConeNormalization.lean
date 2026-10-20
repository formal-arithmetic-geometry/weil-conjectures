/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.PurityNormalCone
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec

/-! # The normalized extended-Rees and relative-Spec cone comparison

Source: Stacks 0630, 0632; current blueprint `sk-thm-dnc`, Local construction
(blueprint: def-pur-rees-cone-normalization).

The comparison is fixed on homogeneous representatives. The existing section-deformation
and gamma-normalization modules retain ownership of their geometry, bundle adjoints and
etale comparison coordinates; this module introduces only the missing normalized Rees
comparison and its uniquely characterizing specification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The conormal algebra identified with functions on its relative spectrum.
Source: Stacks 01LX and 0630
(blueprint: def-pur-rees-cone-normalization). -/
def coneAlgebraIso {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    (PurityNormalBundle.algebraObject s).obj ≅
      Under.mk (⟨(PurityNormalBundle.projection s).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (PurityNormalBundle.projection s).base).obj
            (PurityNormalBundle.normalCone s).sheaf) :=
  ((ObjectProperty.ι (fun B : S.CommAlgebraSheaf ↦ B.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence S).counitIso.app
      (PurityNormalBundle.algebraObject s))).symm ≪≫
    eqToIso ((affine_morphism_relative_spec S).2.choose_spec.choose
      (PurityNormalBundle.over s))

/-- The affine-chart inclusion in the actual Rees zero fibre.
Source: extended-Rees gluing, sk-thm-dnc
(blueprint: def-pur-rees-cone-normalization). -/
def reesConeChart {V S : Scheme.{u}} (s : S ⟶ V) (U : V.AffineZariskiSite) :
    Spec (s.ker.normalConePresheaf.obj (Opposite.op U)) ⟶ s.ker.normalCone :=
  colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
    s.ker.coequifibered_toNormalConePresheaf).functor U

/-- The canonical associated-graded identification fixes constants and sends a degree-one
ideal class of a to a/t modulo t on EVERY affine chart. These classes generate the graded
algebra, so this condition rules out rescaling and all other bundle automorphisms.
Source: Stacks 0630, 0632; sk-thm-dnc, Local construction
(blueprint: def-pur-rees-cone-normalization). -/
def ReesConeNormalized {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s]
    (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s) : Prop :=
  q.hom ≫ PurityNormalBundle.projection s = Scheme.Hom.purityNormalProjection s ∧
  s.normalConeZeroSection ≫ q.hom = PurityNormalBundle.zeroSection s ∧
  ∀ (U : V.AffineZariskiSite)
    (b : (ConormalGradedAlgebra.power s 1).val.obj (Opposite.op U.1))
    (hb : (ConormalGradedAlgebra.powerInclusion s 1).val.app (Opposite.op U.1) b ∈
      s.ker.siteIdeal U)
    (hU : ⊤ ≤ (reesConeChart s U ≫ q.hom) ⁻¹ᵁ
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1))),
    ((reesConeChart s U ≫ q.hom).appLE
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ⊤ hU)
        (((coneAlgebraIso s).hom.right.hom.app (Opposite.op (s ⁻¹ᵁ U.1)))
          (ConormalGradedAlgebra.homogeneousClass s
            (ConormalGradedAlgebra.presentation s).algebra
            (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 b)) =
      (Scheme.ΓSpecIso (s.ker.normalConePresheaf.obj (Opposite.op U))).inv
        (Ideal.Quotient.mk (s.ker.tIdeal (Opposite.op U))
          ⟨LaurentPolynomial.C (R := Γ(V, U.1))
              ((ConormalGradedAlgebra.powerInclusion s 1).val.app (Opposite.op U.1) b) *
            LaurentPolynomial.T (-1),
            Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (I := s.ker.siteIdeal U) hb⟩)

end AlgebraicGeometry.Etale.FiniteSmoothPurity

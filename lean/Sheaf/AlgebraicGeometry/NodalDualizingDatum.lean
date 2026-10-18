/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.SheafExt
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The adjunction line of a nodal relative curve

Source: Temkin, Stable modification of relative curves, §1.2(a),(b), and the local
complete-intersection adjunction construction (blueprint: def-trf-nodal-dualizing-datum).

The fundamental class is normalized by the Jacobian determinant. This condition fixes
transition maps: local generators are identified by their images of differentials, rather
than by an arbitrary choice of isomorphisms between locally free modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- An affine regular presentation of a relative curve, with `c + 1` coordinates and `c`
equations. The coefficient map is the actual map on sections of the structure morphism.
Source: Temkin §1.2(a), local complete intersections
(blueprint: def-trf-nodal-dualizing-datum). -/
structure NodalCanonicalPresentation {Y T : Scheme.{u}} (p : Y ⟶ T) where
  U : Y.affineOpens
  V : T.affineOpens
  over : U.1 ≤ p ⁻¹ᵁ V.1
  c : ℕ
  quotient : MvPolynomial (Fin (c + 1)) Γ(T, V.1) →+* Γ(Y, U.1)
  coefficients : quotient.comp MvPolynomial.C = (p.appLE V.1 U.1 over).hom
  surjective : Function.Surjective quotient
  equations : Fin c → MvPolynomial (Fin (c + 1)) Γ(T, V.1)
  regular : RingTheory.Sequence.IsRegular
    (MvPolynomial (Fin (c + 1)) Γ(T, V.1)) (List.ofFn equations)
  kernel : RingHom.ker quotient = Ideal.span (Set.range equations)

/-- The ambient affine space of a regular presentation, over the affine base chart.
Source: Temkin §1.2(a) (blueprint: def-trf-nodal-dualizing-datum). -/
def NodalCanonicalPresentation.ambient {Y T : Scheme.{u}} {p : Y ⟶ T}
    (A : NodalCanonicalPresentation p) : Scheme.{u} :=
  Spec (.of (MvPolynomial (Fin (A.c + 1)) Γ(T, A.V.1)))

/-- The chart's actual regular closed immersion into its ambient affine space.
Source: Temkin §1.2(a) (blueprint: def-trf-nodal-dualizing-datum). -/
def NodalCanonicalPresentation.immersion {Y T : Scheme.{u}} {p : Y ⟶ T}
    (A : NodalCanonicalPresentation p) : A.U.1.toScheme ⟶ A.ambient :=
  A.U.1.toSpecΓ ≫ Spec.map (CommRingCat.ofHom A.quotient)

/-- The fundamental-class Jacobian: append `a` after the ordered regular equations and
map the determinant of their partial derivatives to the quotient.
Source: local complete-intersection adjunction in Temkin §1.2(a)
(blueprint: def-trf-nodal-dualizing-datum). -/
def NodalCanonicalPresentation.jacobian {Y T : Scheme.{u}} {p : Y ⟶ T}
    (A : NodalCanonicalPresentation p)
    (a : MvPolynomial (Fin (A.c + 1)) Γ(T, A.V.1)) : Γ(Y, A.U.1) :=
  A.quotient (Matrix.det (fun i j : Fin (A.c + 1) ↦
    MvPolynomial.pderiv j (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (A.c + 1)) Γ(T, A.V.1))
      A.equations a i)))

/-- The actual sheaf Ext in codimension `c`. The top differential module of affine
`(c+1)`-space is identified with its structure module by the ordered coordinate volume
form. The standard derived category fixes a model without a size assumption.
Source: Temkin §1.2(a), regular-immersion adjunction
(blueprint: def-trf-nodal-dualizing-datum). -/
def NodalCanonicalPresentation.ext {Y T : Scheme.{u}} {p : Y ⟶ T}
    (A : NodalCanonicalPresentation p) : A.ambient.Modules :=
  @moduleSheafExt A.ambient (HasDerivedCategory.standard _) (A.c : ℤ)
    ((Scheme.Modules.pushforward A.immersion).obj
      (SheafOfModules.unit A.U.1.toScheme.ringCatSheaf))
    (SheafOfModules.unit A.ambient.ringCatSheaf)

/-- A dualizing line with its fundamental class. In every affine regular presentation,
the local generator is fixed by the Jacobian formula for the fundamental class, and its
pushforward is the actual sheaf Ext. This fixes the adjunction line and its gluing even
on a nonseparated curve; no affine-intersection hypothesis is imposed.
Source: Temkin §1.2(a),(b), local complete-intersection adjunction
(blueprint: def-trf-nodal-dualizing-datum). -/
structure NodalDualizingDatum {Y T : Scheme.{u}} (p : Y ⟶ T) (omega : Y.Modules) where
  invertible : omega.IsInvertible
  fundamental : p.relativeDifferentials ⟶ omega
  charts_cover : ∀ y : Y, ∃ A : NodalCanonicalPresentation p, y ∈ A.U.1
  normalized : ∀ A : NodalCanonicalPresentation p,
    ∃ e : Γ(omega, A.U.1) ≃ₗ[Γ(Y, A.U.1)] Γ(Y, A.U.1),
      ∀ a : MvPolynomial (Fin (A.c + 1)) Γ(T, A.V.1),
        e (fundamental.app A.U.1
          (p.relativeDifferentialsDerivation.d (X := op A.U.1) (A.quotient a))) =
            A.jacobian a
  local_ext : ∀ A : NodalCanonicalPresentation p,
    Nonempty ((Scheme.Modules.pushforward A.immersion).obj
      ((Scheme.Modules.tensorPullback A.U.1.ι).obj omega) ≅ A.ext)

end AlgebraicGeometry

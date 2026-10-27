module
public import Sheaf.SecSmoothPurity.TransportFiniteEncoding
public import Sheaf.SecSmoothPurity.TransportRoot
public import Sheaf.AlgebraicGeometry.CartierReductionData
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-finite-line-coordinates). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The section-action encoding retains the literal underlying abelian sheaf.
Source: finite encoding (blueprint: def-pur-transport-finite-line-coordinates). -/
def finiteEncodingForget (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (X : Scheme.{u}) :=
  finiteDiscreteCoefficientEquivalenceForgetIso A (finitePointIso A)
    (finiteModuleEncoding (ULift.{u + 1} A)) (finiteModuleEncoding_forget _) X

/-- The specified annihilator is preserved by the coefficient universe lift.
Source: coefficient-size convention
(blueprint: def-pur-transport-finite-line-coordinates).
Proof: apply the down ring isomorphism, which preserves natural casts and zero,
and use the given annihilator. Its injectivity reflects the resulting equality. -/
theorem finiteLiftAnnihilator (A : CommRingCat.{0}) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) :
    ((ell ^ (n + 1) : ℕ) : ULift.{u + 1} A) = 0 := by
  have _hEll : ell.Prime := Fact.out
  apply ULift.ringEquiv.injective
  simpa only [map_natCast, map_pow, map_zero, Nat.cast_pow] using hA

/-- The root-normalized finite line comparison. The equation is tested on the
actual projection at the annihilating level, using the free and scalar units.
Thus the comparison is not an independently chosen trivialization of the line.
Source: finite Tate definition and Stacks 03PK
(blueprint: def-pur-transport-finite-line-coordinates). -/
structure FiniteLineCoordinates (A : CommRingCat.{0}) (fin : Finite A)
    (n : ℕ) (hA : (ell ^ (n + 1) : A) = 0) (X : Scheme.{u})
    (hX : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(X, ⊤))) where
  line : (Coefficient.finite A fin n hA).firstLine ell X ≅
    (letI : TopologicalSpace A := ⊥
     letI : DiscreteTopology A := discreteTopology_bot A
     (finiteEncoding A X).functor.obj
       (geoCartierLine (ULift.{u + 1} A) (ell ^ (n + 1))
         (finiteLiftAnnihilator ell A n hA) X))
  unit :
    (letI : TopologicalSpace A := ⊥
     letI : DiscreteTopology A := discreteTopology_bot A
     (finiteEncoding A X).inverse.obj (𝟙_ _)) ≅
      geoCartierConstant (ULift.{u + 1} A) X
  unit_normalized :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    ∀ (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} A),
      HEq (unit.inv.hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))).app U a))
        ((finiteDiscreteSchemeRingIso A X (finitePointIso A)).hom.hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a))
  normalized :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    let φ := coefficientMap ((Coefficient.finite A fin n hA).integralMap ell) X
    let M := geoCartierLine (ULift.{u + 1} A) (ell ^ (n + 1))
      (finiteLiftAnnihilator ell A n hA) X
    let raw := (rootComparison X (ell ^ (n + 1))).hom ≫
      cartierProRootMap (ULift.{u + 1} A) (ell ^ (n + 1))
        (finiteLiftAnnihilator ell A n hA) X (pow_pos (Fact.out : ell.Prime).pos _) hX ≫
      (finiteEncodingForget A X).inv.app M
    (Mod.extendUnit φ (tateModule X ell)).hom ≫ line.hom.hom =
      (limit.π (tateModuleSystem X ell) (op (n + 1))).hom ≫
        (Mod.freeDesc (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X)
          (M := (Mod.comap φ).obj ((finiteEncoding A X).functor.obj M)) raw).hom

end AlgebraicGeometry.ProEtale.PurityTransport

module
public import Sheaf.SecSmoothPurity.TransportAffineTrace

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-affine-counit-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The finite counit of the same family is integration on the actual affine line.
Every comparison in the equation is fixed on sections, roots, or by adjunction.
Together with scalar compatibility, this fixes integral, rational and common-stage
normalizations as well. There is no independent trace parameter.
Source: smooth-purity affine normalization
(blueprint: def-pur-transport-affine-counit-normalization). -/
def AffineNormalized (D : WeilConjectures.FiniteFieldDatum.{u})
    (b : AdjunctionFamily ell D) : Prop :=
  ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0)
    (Y : Over (Spec (.of D.k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom],
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    let c := Coefficient.finite A fin n hA
    let s := affineDatum D Y
    let B := ULift.{u + 1} A
    ∃ (hY : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(Y.left, ⊤)))
      (hX : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(s.X.left, ⊤))),
    ∃ (pY : FiniteLineCoordinates ell A fin n hA Y.left hY)
      (pX : FiniteLineCoordinates ell A fin n hA s.X.left hX)
      (hu : property ell c Y.left (unit ell c Y.left)),
    let M := (Etale.ordinaryFiniteLine B (ell ^ (n + 1))
      (finiteLiftAnnihilator ell A n hA) s.X.left) ⟦(2 : ℤ)⟧
    ∃ hM : DerivedCategory.TStructure.t.plus M,
      (finiteEncodingDerived A Y.left).inverse.map
          ((b c s).trace ⟨_, hu⟩) ≫
        (finiteDerivedUnit ell A n hA Y.left hY pY).hom =
      (finiteEncodingSupport A s.compactification).hom.app
          ((c.smoothSource ell s.map 1).obj (unit ell c Y.left)) ≫
        (ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} B) s.compactification).map
            ((finiteEncodingDerived A s.X.left).inverse.map
              (sourceUnit ell c s.map 1).hom ≫
              (finiteDerivedLine ell A n hA s.X.left hX pX).hom) ≫
        (ProEtale.compactSupportSiteComparison B s.compactification).hom.app ⟨M, hM⟩ ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y.left).mapDerivedCategory.map
          (ordinaryAffineIntegration B (ell ^ (n + 1))
            (pow_pos (Fact.out : ell.Prime).pos _) (finiteLiftAnnihilator ell A n hA)
            Y.left hY)

end AlgebraicGeometry.ProEtale.PurityTransport

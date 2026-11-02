/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison

/-!
# Restriction of the abelian derived exchange to bounded-below complexes
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem inverse_mate_app
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (β : TwoSquare R₁ H G R₂) (K : C₁) :
    ((mateEquiv adj₁ adj₂).symm β).natTrans.app K =
      L₂.map (G.map (adj₁.unit.app K) ≫ β.natTrans.app (L₁.obj K)) ≫
        adj₂.counit.app (H.obj (L₁.obj K)) := by
  simp [mateEquiv]

/-- The normalized scalar/pullback comparison is the inverse scalar-adjunction mate of
`scalarRestrictionPullbackIso`; its components are the unit--restriction--counit composite.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Existence/uniqueness/naturality and Charts
(blueprint: lem-pur-etale-scalar-pullback-restriction-mate).

Proof, following the node's two steps.
1. Both sides are natural maps `S_Z Lf_A^* ⟶ Lf_B^* S_W`, so compare them at `Q P` for a
   K-flat complex `P` with flat terms (lem-pc-kflat-resolution). Write `F = - ⊗_A B`
   termwise, `r_P : S (Q P) ≅ Q (F P)` (lem-pur-derived-change-of-rings) and
   `g_{R,X} : Lf_R^* (Q X) ⟶ Q (f_R^* X)` (lem-weil-pbc-ringed-topoi-derived-pullback); as
   `f_R^*` is exact, `g_{R,X}` is the comparison with `D(f_R^*)`. `f_A^* P` is K-flat with
   flat terms (lem-weil-pbc-ringed-topoi-derived-tensor-pullback), and so is `F P` over `B`.
   (a) Under `r_P` the unit at `Q P` is `Q (ι_P)`, `ι_P x = x ⊗ 1`
   (lem-pur-sheaf-ring-derived-coefficient-adjunction (1)).
   (b) By naturality and the definition of `scalarRestrictionPullbackIso` (termwise
   identity `f_A^* Res = Res f_B^*`, conjugated by the comparisons), restriction after the
   unit is `Res (g_{B,F P})⁻¹ ≫ Q (g_P) ≫ g_{A,P}` up to `r_P`, with `g_P = f_A^* ι_P`
   followed by that identity.
   (c) By naturality of the counit and clause (2) of the scalar adjunction, the inverse-mate
   composite at `Q P` is the inverse normalization with middle map `Q (g̃_P) ≫ r`, where
   `g̃_P : F f_A^* P ⟶ f_B^* F P` sends `x ⊗ b` to `b g_P(x)`.
   (d) `g̃_P = a_P⁻¹` by the iterated-mates lemma (lem-trf-iterated-square-mates): the
   conjugate of `a⁻¹` is the direct-image identity (def-pur-etale-scalar-pullback-iso), the
   inverse-image/restriction identity is the identity on `f⁻¹ G` with abelian unit and
   counit (prop-weil-pbc-inverse-image-modules-exact (2),(3)), and mates are a bijection.
   (e) Inverting the K-flat normalization of `scalarPullbackIso` gives the same composite
   at `Q P`; naturality and resolution independence give equality at every object.
2. The inverse direction of `mateEquiv` (def-weil-pbc-adjunction-mate) applied to
   `scalarRestrictionPullbackIso` has component at `K` the displayed
   unit--restriction--counit composite; step 1 identifies it with `scalarPullbackIso.inv`.
No flatness, finiteness, boundedness, constructibility, or condition on `f` is used. -/
theorem scalarPullbackIso_inv_mate_restriction
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (scalarPullbackIso φ f).inv =
        ((mateEquiv
          (Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
          (Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))).symm
          (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)).natTrans ∧
      ∀ (K : DerivedCategoryModule A W),
        (scalarPullbackIso φ f).inv.app K =
          (scalarExtension φ Z).map
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
                ((Adjunction.ofIsRightAdjoint
                  (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).unit.app K)) ≫
            (scalarExtension φ Z).map
              ((scalarRestrictionPullbackIso φ f).hom.app
                ((scalarExtension φ W).obj K)) ≫
            (Adjunction.ofIsRightAdjoint
              (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).counit.app
              ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
                ((scalarExtension φ W).obj K)) := by
  have hm : (scalarPullbackIso φ f).inv =
      ((mateEquiv
        (Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
        (Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))).symm
        (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)).natTrans := by
    rw [← scalarPullback_eq φ f]
    rfl
  refine ⟨hm, ?_⟩
  intro K
  rw [hm]
  exact inverse_mate_app _ _ _ K

private noncomputable def exactComp {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W)
    (d : U ⟶ W := a ≫ b) (hd : d = a ≫ b := by cat_disch) :
    D(upperStar AddCommGrpCat.{u + 1} d) ≅
      D(upperStar AddCommGrpCat.{u + 1} b) ⋙ D(upperStar AddCommGrpCat.{u + 1} a) :=
  Functor.mapDerivedCategoryNatIso (upperStarComp AddCommGrpCat.{u + 1} a b d hd) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private noncomputable def exactSquare {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f) :
    D(upperStar AddCommGrpCat.{u + 1} f) ⋙ D(upperStar AddCommGrpCat.{u + 1} h) ≅
      D(upperStar AddCommGrpCat.{u + 1} g) ⋙ D(upperStar AddCommGrpCat.{u + 1} e) :=
  (exactComp h f (e ≫ g) sq.w).symm ≪≫ exactComp e g

end AlgebraicGeometry.Etale

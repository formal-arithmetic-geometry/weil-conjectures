/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenComparison
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import all WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearCompositorCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-! # Underived clopen pasting in the ambient coefficient categories

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D; the blueprint's
underived identity-restriction argument on pro-etale modules and semilinear systems
(blueprint: lem-sf-ambient-underived-clopen-pasting).

The assertion predicates record the two pasting equalities, both individual factor
restrictions, and both identity-square cases. The system horizontal factors retain
their category instances in a concrete data package. All maps are the already constructed
ordinary intrinsic clopen arrows; no derived evaluation enters these assertions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Exact cached proof arguments avoid expanding the chosen adjoints during conversion.
set_option linter.auxLemma false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open WeilConjectures WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.AmbientClopen.UnderivedPasting

namespace Ordinary
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The identity open-extension compositor fixed by the ordinary open adjunction.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def openIdentity (X : Scheme.{u}) : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 X)) ≅ 𝟭
  (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  Adjunction.leftAdjointIdIso
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
    (upperStarId (ModuleCat.{u + 1} Λ) X)

/-- Vertical pasting and identity restriction of each of its two factors.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def Vertical (F : FiniteFieldDatum.{u}) : Prop :=
  ∀ (U₀ U₁ U₂ V₀ V₁ V₂ : Scheme.{u})
    [U₀.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U₀ ↘ Spec (.of F.k))]
    [QuasiCompact (U₀ ↘ Spec (.of F.k))]
    [U₁.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U₁ ↘ Spec (.of F.k))]
    [QuasiCompact (U₁ ↘ Spec (.of F.k))]
    [U₂.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U₂ ↘ Spec (.of F.k))]
    [QuasiCompact (U₂ ↘ Spec (.of F.k))]
    [V₀.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V₀ ↘ Spec (.of F.k))]
    [QuasiCompact (V₀ ↘ Spec (.of F.k))]
    [V₁.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V₁ ↘ Spec (.of F.k))]
    [QuasiCompact (V₁ ↘ Spec (.of F.k))]
    [V₂.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V₂ ↘ Spec (.of F.k))]
    [QuasiCompact (V₂ ↘ Spec (.of F.k))]
    (j₀ : U₀ ⟶ V₀) (j₁ : U₁ ⟶ V₁) (j₂ : U₂ ⟶ V₂)
    (r₁ : U₀ ⟶ U₁) (r₂ : U₁ ⟶ U₂) (p₁ : V₀ ⟶ V₁) (p₂ : V₁ ⟶ V₂)
    [j₀.IsOver (Spec (.of F.k))]
    [j₁.IsOver (Spec (.of F.k))]
    [j₂.IsOver (Spec (.of F.k))]
    [r₁.IsOver (Spec (.of F.k))]
    [r₂.IsOver (Spec (.of F.k))]
    [p₁.IsOver (Spec (.of F.k))]
    [p₂.IsOver (Spec (.of F.k))]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [QuasiCompact j₀] [QuasiCompact j₁] [QuasiCompact j₂]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : j₀ ≫ p₁ = r₁ ≫ j₁) (h₂ : j₁ ≫ p₂ = r₂ ≫ j₂)
    (h : j₀ ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j₂),
    (Functor.whiskerRight (AmbientClopen.alpha Λ j₁ r₂ p₂ j₂ h₂) (upperStar (ModuleCat.{u + 1} Λ)
      p₁) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) r₂) (AmbientClopen.alpha Λ j₀ r₁ p₁ j₁
        h₁) =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂) (upperStarComp
        (ModuleCat.{u + 1} Λ) p₁ p₂).inv ≫
      (AmbientClopen.alpha Λ j₀ (r₁ ≫ r₂) (p₁ ≫ p₂) j₂ h) ≫
      Functor.whiskerRight (upperStarComp (ModuleCat.{u + 1} Λ) r₁ r₂).hom (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) j₀) ≫
      (Functor.associator _ _ _).hom) ∧
    (∀ M : Sheaf (Scheme.ProEt.topology U₂) (ModuleCat.{u + 1} Λ),
      (upperStar (ModuleCat.{u + 1} Λ) r₁).map ((upperStar (ModuleCat.{u + 1} Λ) r₂).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₂).unit.app M)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) r₁).map ((upperStarCompIso (ModuleCat.{u + 1} Λ)
          h₂.symm).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).obj M)) ≫
        (upperStarCompIso (ModuleCat.{u + 1} Λ) h₁.symm).hom.app ((upperStar (ModuleCat.{u + 1} Λ)
          p₂).obj ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).obj M)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) j₀).map ((upperStar (ModuleCat.{u + 1} Λ) p₁).map
          ((AmbientClopen.alpha Λ j₁ r₂ p₂ j₂ h₂).app M)) =
      (upperStar (ModuleCat.{u + 1} Λ) r₁).map ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j₁).unit.app ((upperStar (ModuleCat.{u + 1} Λ) r₂).obj M)) ≫
        (upperStarCompIso (ModuleCat.{u + 1} Λ) h₁.symm).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) j₁).obj ((upperStar (ModuleCat.{u + 1} Λ) r₂).obj M))) ∧
    (∀ M : Sheaf (Scheme.ProEt.topology U₂) (ModuleCat.{u + 1} Λ),
      (upperStar (ModuleCat.{u + 1} Λ) r₁).map ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j₁).unit.app ((upperStar (ModuleCat.{u + 1} Λ) r₂).obj M)) ≫
        (upperStarCompIso (ModuleCat.{u + 1} Λ) h₁.symm).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) j₁).obj ((upperStar (ModuleCat.{u + 1} Λ) r₂).obj M)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) j₀).map ((AmbientClopen.alpha Λ j₀ r₁ p₁ j₁ h₁).app
          ((upperStar (ModuleCat.{u + 1} Λ) r₂).obj M)) =
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₀).unit.app ((upperStar
        (ModuleCat.{u + 1} Λ) r₁).obj ((upperStar (ModuleCat.{u + 1} Λ) r₂).obj M)))

/-- Horizontal pasting and identity restriction of each factor along the composite open.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def Horizontal (F : FiniteFieldDatum.{u}) : Prop :=
  ∀ (U V T W Z Y : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    [T.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of F.k))]
    [QuasiCompact (T ↘ Spec (.of F.k))]
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))]
    [QuasiCompact (W ↘ Spec (.of F.k))]
    [Z.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of F.k))]
    [QuasiCompact (Z ↘ Spec (.of F.k))]
    [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))]
    [QuasiCompact (Y ↘ Spec (.of F.k))]
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    [k₁.IsOver (Spec (.of F.k))]
    [k₂.IsOver (Spec (.of F.k))]
    [i₁.IsOver (Spec (.of F.k))]
    [i₂.IsOver (Spec (.of F.k))]
    [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))]
    [q.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact k₁] [QuasiCompact k₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (h : (k₁ ≫ k₂) ≫ q = r ≫ (i₁ ≫ i₂)),
    ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁) (AmbientClopen.alpha Λ
        k₂ p q i₂ h₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (AmbientClopen.alpha Λ k₁ r p i₁ h₁) (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k₂) =
      Functor.whiskerRight (AmbientClopen.openComp Λ i₁ i₂).hom (upperStar (ModuleCat.{u + 1} Λ) q)
        ≫
      (AmbientClopen.alpha Λ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h) ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) r) (AmbientClopen.openComp Λ k₁ k₂).inv ≫
      (Functor.associator _ _ _).inv) ∧
    (∀ M : Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ),
      (upperStar (ModuleCat.{u + 1} Λ) r).map ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) i₁).unit.app M) ≫
        (upperStarCompIso (ModuleCat.{u + 1} Λ) h₁.symm).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) i₁).obj M) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k₁).map ((upperStar (ModuleCat.{u + 1} Λ) p).map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i₂).unit.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).obj M))) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k₁).map ((upperStarCompIso (ModuleCat.{u + 1} Λ)
          h₂.symm).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₂).obj ((openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) i₁).obj M))) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k₁).map ((upperStar (ModuleCat.{u + 1} Λ) k₂).map
          ((AmbientClopen.alpha Λ k₂ p q i₂ h₂).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).obj M))) =
      (upperStar (ModuleCat.{u + 1} Λ) r).map ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) i₁).unit.app M) ≫
        (upperStarCompIso (ModuleCat.{u + 1} Λ) h₁.symm).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) i₁).obj M) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k₁).map ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) k₂).unit.app ((upperStar (ModuleCat.{u + 1} Λ) p).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).obj M)))) ∧
    (∀ M : Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ),
      (upperStar (ModuleCat.{u + 1} Λ) r).map ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) i₁).unit.app M) ≫
        (upperStarCompIso (ModuleCat.{u + 1} Λ) h₁.symm).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) i₁).obj M) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k₁).map ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) k₂).unit.app ((upperStar (ModuleCat.{u + 1} Λ) p).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).obj M))) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k₁).map ((upperStar (ModuleCat.{u + 1} Λ) k₂).map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k₂).map
          ((AmbientClopen.alpha Λ k₁ r p i₁ h₁).app M))) =
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k₁).unit.app ((upperStar
        (ModuleCat.{u + 1} Λ) r).obj M) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k₁).map ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) k₂).unit.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
          k₁).obj ((upperStar (ModuleCat.{u + 1} Λ) r).obj M))))

/-- Identity verticals and identity horizontals give identity under the canonical units.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def Identities (F : FiniteFieldDatum.{u}) : Prop :=
  (∀ (U V : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    (k : U ⟶ V) [k.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [QuasiCompact k] (h : k ≫ 𝟙 V = 𝟙 U ≫ k),
    (AmbientClopen.alpha Λ k (𝟙 U) (𝟙 V) k h) =
      Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) (upperStarId
        (ModuleCat.{u + 1} Λ) V).hom ≫
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (upperStarId (ModuleCat.{u + 1} Λ) U).inv (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k)) ∧
  (∀ (U V : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    (p : U ⟶ V) [p.IsOver (Spec (.of F.k))] [IsProper p]
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 V)),
    (AmbientClopen.alpha Λ (𝟙 U) p p (𝟙 V) h) =
      Functor.whiskerRight (openIdentity Λ V).hom (upperStar (ModuleCat.{u + 1} Λ) p) ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) p) (openIdentity Λ U).inv)

end Ordinary

namespace Systems
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The system inverse-image identity compositor, conjugate to the section identity.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def pullIdentity (X : Scheme.{u}) : (VaryingRing.pull C τ (𝟙 X)) ≅ 𝟭 (VaryingRing.Modules C τ X) :=
  Adjunction.leftAdjointIdIso (VaryingRing.moduleAdj C τ (𝟙 X))
    (VaryingRing.modulePId C τ X)

/-- The identity open-extension compositor fixed by the ordinary open adjunction.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def openIdentity (X : Scheme.{u}) : (VaryingRing.extension C τ (𝟙 X)) ≅ 𝟭 (VaryingRing.Modules C τ
  X) :=
  Adjunction.leftAdjointIdIso
    (VaryingRing.moduleJAdj C τ (𝟙 X))
    (pullIdentity C τ X)

section FactorData

universe v w

set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] VaryingRing.moduleJAdj VaryingRing.moduleSquareG

-- This bundle records independent universes for its objects and its morphisms.
set_option linter.checkUnivs false in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Two horizontal squares, retaining the category instances used by their operations.
Source: Stacks Project, Tag 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
structure HorizontalFactorData where
  A : Type w
  B : Type w
  C : Type w
  D : Type w
  E : Type w
  H : Type w
  [catA : Category.{v} A]
  [catB : Category.{v} B]
  [catC : Category.{v} C]
  [catD : Category.{v} D]
  [catE : Category.{v} E]
  [catH : Category.{v} H]
  I : A ⥤ B
  PI : B ⥤ A
  J : B ⥤ E
  PJ : E ⥤ B
  K : C ⥤ D
  PK : D ⥤ C
  L : D ⥤ H
  PL : H ⥤ D
  R : A ⥤ C
  P : B ⥤ D
  Q : E ⥤ H
  etaI : 𝟭 A ⟶ I ⋙ PI
  etaJ : 𝟭 B ⟶ J ⋙ PJ
  etaK : 𝟭 C ⟶ K ⋙ PK
  etaL : 𝟭 D ⟶ L ⋙ PL
  s₁ : PI ⋙ R ⟶ P ⋙ PK
  s₂ : PJ ⋙ P ⟶ Q ⋙ PL
  a₁ : I ⋙ P ⟶ R ⋙ K
  a₂ : J ⋙ Q ⟶ P ⋙ L

/-- The two factor restriction equations of horizontal pasting.
Source: Stacks Project, Tag 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def HorizontalFactorData.factors (d : HorizontalFactorData.{v, w}) : Prop :=
  letI := d.catA
  letI := d.catB
  letI := d.catC
  letI := d.catD
  letI := d.catE
  letI := d.catH
  (∀ M, d.R.map (d.etaI.app M) ≫ d.s₁.app (d.I.obj M) ≫
    d.PK.map (d.P.map (d.etaJ.app (d.I.obj M))) ≫
    d.PK.map (d.s₂.app (d.J.obj (d.I.obj M))) ≫
    d.PK.map (d.PL.map (d.a₂.app (d.I.obj M))) =
    d.R.map (d.etaI.app M) ≫ d.s₁.app (d.I.obj M) ≫
      d.PK.map (d.etaL.app (d.P.obj (d.I.obj M)))) ∧
  (∀ M, d.R.map (d.etaI.app M) ≫ d.s₁.app (d.I.obj M) ≫
    d.PK.map (d.etaL.app (d.P.obj (d.I.obj M))) ≫
    d.PK.map (d.PL.map (d.L.map (d.a₁.app M))) =
    d.etaK.app (d.R.obj M) ≫ d.PK.map (d.etaL.app (d.K.obj (d.R.obj M))))

/-- The actual functors and units in two horizontal system squares.
The smallness argument records a presentation witness, never a choice of module data.
Source: Stacks Project, Tag 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def horizontalFactorData
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V T W Z Y : Scheme.{u}}
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact k₁] [QuasiCompact k₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (small : ∀ X : Scheme.{u}, EssentiallySmall.{u + 1} (ℕ × X.ProEt)) :
    HorizontalFactorData.{u + 1, u + 2} := by
  let cat (X : Scheme.{u}) : Category (VaryingRing.Modules C τ X) :=
    show Category (SheafOfModules.{u + 1}
      (@SemilinearSections.ring _ _ (small X)
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (@SemilinearSections.systemRing _ _ (VaryingRing.siteSmall X)
          (Scheme.ProEt.topology X)
          (VaryingRing.coefficients C X) (VaryingRing.coefficientTransition C τ X)))) from
      inferInstance
  exact {
    A := VaryingRing.Modules C τ W
    B := VaryingRing.Modules C τ Z
    C := VaryingRing.Modules C τ U
    D := VaryingRing.Modules C τ V
    E := VaryingRing.Modules C τ Y
    H := VaryingRing.Modules C τ T
    catA := cat W
    catB := cat Z
    catC := cat U
    catD := cat V
    catE := cat Y
    catH := cat T
    I := VaryingRing.extension C τ i₁
    PI := VaryingRing.pull C τ i₁
    J := VaryingRing.extension C τ i₂
    PJ := VaryingRing.pull C τ i₂
    K := VaryingRing.extension C τ k₁
    PK := VaryingRing.pull C τ k₁
    L := VaryingRing.extension C τ k₂
    PL := VaryingRing.pull C τ k₂
    R := VaryingRing.pull C τ r
    P := VaryingRing.pull C τ p
    Q := VaryingRing.pull C τ q
    etaI := @Adjunction.unit _ (cat W) _ (cat Z)
      (VaryingRing.extension C τ i₁) (VaryingRing.pull C τ i₁)
      (VaryingRing.moduleJAdj C τ i₁)
    etaJ := @Adjunction.unit _ (cat Z) _ (cat Y)
      (VaryingRing.extension C τ i₂) (VaryingRing.pull C τ i₂)
      (VaryingRing.moduleJAdj C τ i₂)
    etaK := @Adjunction.unit _ (cat U) _ (cat V)
      (VaryingRing.extension C τ k₁) (VaryingRing.pull C τ k₁)
      (VaryingRing.moduleJAdj C τ k₁)
    etaL := @Adjunction.unit _ (cat V) _ (cat T)
      (VaryingRing.extension C τ k₂) (VaryingRing.pull C τ k₂)
      (VaryingRing.moduleJAdj C τ k₂)
    s₁ := @Iso.hom _ (@Functor.category _ (cat Z) _ (cat U))
      (@Functor.comp _ (cat Z) _ (cat W) _ (cat U)
        (VaryingRing.pull C τ i₁) (VaryingRing.pull C τ r))
      (@Functor.comp _ (cat Z) _ (cat V) _ (cat U)
        (VaryingRing.pull C τ p) (VaryingRing.pull C τ k₁))
      (VaryingRing.moduleSquareG C τ k₁ r p i₁ h₁)
    s₂ := @Iso.hom _ (@Functor.category _ (cat Y) _ (cat V))
      (@Functor.comp _ (cat Y) _ (cat Z) _ (cat V)
        (VaryingRing.pull C τ i₂) (VaryingRing.pull C τ p))
      (@Functor.comp _ (cat Y) _ (cat T) _ (cat V)
        (VaryingRing.pull C τ q) (VaryingRing.pull C τ k₂))
      (VaryingRing.moduleSquareG C τ k₂ p q i₂ h₂)
    a₁ := VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁
    a₂ := VaryingRing.moduleAlpha C τ k₂ p q i₂ h₂ }

end FactorData

/-- Vertical pasting and identity restriction of each of its two factors.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def Vertical (F : FiniteFieldDatum.{u}) : Prop :=
  ∀ (U₀ U₁ U₂ V₀ V₁ V₂ : Scheme.{u})
    [U₀.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U₀ ↘ Spec (.of F.k))]
    [QuasiCompact (U₀ ↘ Spec (.of F.k))]
    [U₁.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U₁ ↘ Spec (.of F.k))]
    [QuasiCompact (U₁ ↘ Spec (.of F.k))]
    [U₂.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U₂ ↘ Spec (.of F.k))]
    [QuasiCompact (U₂ ↘ Spec (.of F.k))]
    [V₀.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V₀ ↘ Spec (.of F.k))]
    [QuasiCompact (V₀ ↘ Spec (.of F.k))]
    [V₁.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V₁ ↘ Spec (.of F.k))]
    [QuasiCompact (V₁ ↘ Spec (.of F.k))]
    [V₂.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V₂ ↘ Spec (.of F.k))]
    [QuasiCompact (V₂ ↘ Spec (.of F.k))]
    (j₀ : U₀ ⟶ V₀) (j₁ : U₁ ⟶ V₁) (j₂ : U₂ ⟶ V₂)
    (r₁ : U₀ ⟶ U₁) (r₂ : U₁ ⟶ U₂) (p₁ : V₀ ⟶ V₁) (p₂ : V₁ ⟶ V₂)
    [j₀.IsOver (Spec (.of F.k))]
    [j₁.IsOver (Spec (.of F.k))]
    [j₂.IsOver (Spec (.of F.k))]
    [r₁.IsOver (Spec (.of F.k))]
    [r₂.IsOver (Spec (.of F.k))]
    [p₁.IsOver (Spec (.of F.k))]
    [p₂.IsOver (Spec (.of F.k))]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [QuasiCompact j₀] [QuasiCompact j₁] [QuasiCompact j₂]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : j₀ ≫ p₁ = r₁ ≫ j₁) (h₂ : j₁ ≫ p₂ = r₂ ≫ j₂)
    (h : j₀ ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j₂),
    (Functor.whiskerRight (VaryingRing.moduleAlpha C τ j₁ r₂ p₂ j₂ h₂) (VaryingRing.pull C τ p₁) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.pull C τ r₂) (VaryingRing.moduleAlpha C τ j₀ r₁ p₁ j₁ h₁) =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.extension C τ j₂) (VaryingRing.moduleGComp C τ p₁ p₂).inv ≫
      (VaryingRing.moduleAlpha C τ j₀ (r₁ ≫ r₂) (p₁ ≫ p₂) j₂ h) ≫
      Functor.whiskerRight (VaryingRing.moduleGComp C τ r₁ r₂).hom (VaryingRing.extension C τ j₀) ≫
      (Functor.associator _ _ _).hom) ∧
    (∀ M : VaryingRing.Modules C τ U₂,
      (VaryingRing.pull C τ r₁).map ((VaryingRing.pull C τ r₂).map ((VaryingRing.moduleJAdj C τ
        j₂).unit.app M)) ≫
        (VaryingRing.pull C τ r₁).map ((VaryingRing.moduleSquareG C τ j₁ r₂ p₂ j₂ h₂).hom.app
          ((VaryingRing.extension C τ j₂).obj M)) ≫
        (VaryingRing.moduleSquareG C τ j₀ r₁ p₁ j₁ h₁).hom.app ((VaryingRing.pull C τ p₂).obj
          ((VaryingRing.extension C τ j₂).obj M)) ≫
        (VaryingRing.pull C τ j₀).map ((VaryingRing.pull C τ p₁).map ((VaryingRing.moduleAlpha C τ
          j₁ r₂ p₂ j₂ h₂).app M)) =
      (VaryingRing.pull C τ r₁).map ((VaryingRing.moduleJAdj C τ j₁).unit.app ((VaryingRing.pull C τ
        r₂).obj M)) ≫
        (VaryingRing.moduleSquareG C τ j₀ r₁ p₁ j₁ h₁).hom.app ((VaryingRing.extension C τ j₁).obj
          ((VaryingRing.pull C τ r₂).obj M))) ∧
    (∀ M : VaryingRing.Modules C τ U₂,
      (VaryingRing.pull C τ r₁).map ((VaryingRing.moduleJAdj C τ j₁).unit.app ((VaryingRing.pull C τ
        r₂).obj M)) ≫
        (VaryingRing.moduleSquareG C τ j₀ r₁ p₁ j₁ h₁).hom.app ((VaryingRing.extension C τ j₁).obj
          ((VaryingRing.pull C τ r₂).obj M)) ≫
        (VaryingRing.pull C τ j₀).map ((VaryingRing.moduleAlpha C τ j₀ r₁ p₁ j₁ h₁).app
          ((VaryingRing.pull C τ r₂).obj M)) =
      (VaryingRing.moduleJAdj C τ j₀).unit.app ((VaryingRing.pull C τ r₁).obj ((VaryingRing.pull C τ
        r₂).obj M)))

/-- Horizontal pasting and identity restriction of each factor along the composite open.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def Horizontal (F : FiniteFieldDatum.{u}) : Prop :=
  ∀ (U V T W Z Y : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    [T.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of F.k))]
    [QuasiCompact (T ↘ Spec (.of F.k))]
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))]
    [QuasiCompact (W ↘ Spec (.of F.k))]
    [Z.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of F.k))]
    [QuasiCompact (Z ↘ Spec (.of F.k))]
    [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))]
    [QuasiCompact (Y ↘ Spec (.of F.k))]
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    [k₁.IsOver (Spec (.of F.k))]
    [k₂.IsOver (Spec (.of F.k))]
    [i₁.IsOver (Spec (.of F.k))]
    [i₂.IsOver (Spec (.of F.k))]
    [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))]
    [q.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact k₁] [QuasiCompact k₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (h : (k₁ ≫ k₂) ≫ q = r ≫ (i₁ ≫ i₂)),
    ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.extension C τ i₁) (VaryingRing.moduleAlpha C τ k₂ p q i₂ h₂)
        ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁) (VaryingRing.extension C τ k₂)
        =
      Functor.whiskerRight (VaryingRing.moduleJComp C τ i₁ i₂).hom (VaryingRing.pull C τ q) ≫
      (VaryingRing.moduleAlpha C τ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h) ≫
      Functor.whiskerLeft (VaryingRing.pull C τ r) (VaryingRing.moduleJComp C τ k₁ k₂).inv ≫
      (Functor.associator _ _ _).inv) ∧
    (horizontalFactorData C τ k₁ k₂ i₁ i₂ r p q h₁ h₂
      @pullIdentity._proof_1).factors

/-- Identity verticals and identity horizontals give identity under the canonical units.
Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def Identities (F : FiniteFieldDatum.{u}) : Prop :=
  (∀ (U V : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    (k : U ⟶ V) [k.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [QuasiCompact k] (h : k ≫ 𝟙 V = 𝟙 U ≫ k),
    (VaryingRing.moduleAlpha C τ k (𝟙 U) (𝟙 V) k h) =
      Functor.whiskerLeft (VaryingRing.extension C τ k) (pullIdentity C τ V).hom ≫
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (pullIdentity C τ U).inv (VaryingRing.extension C τ k)) ∧
  (∀ (U V : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    (p : U ⟶ V) [p.IsOver (Spec (.of F.k))] [IsProper p]
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 V)),
    (VaryingRing.moduleAlpha C τ (𝟙 U) p p (𝟙 V) h) =
      Functor.whiskerRight (openIdentity C τ V).hom (VaryingRing.pull C τ p) ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft (VaryingRing.pull C τ p) (openIdentity C τ U).inv)

end Systems

section PastingProof

universe v w

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 128

attribute [local irreducible] AlgebraicGeometry.ProEtale.VaryingRing.moduleGId
  AlgebraicGeometry.ProEtale.AmbientClopen.alpha
  AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha
  AlgebraicGeometry.ProEtale.upperStarCompIso
  AlgebraicGeometry.ProEtale.VaryingRing.moduleSquareG
  AlgebraicGeometry.ProEtale.upperStar
  AlgebraicGeometry.ProEtale.upperStarComp
  AlgebraicGeometry.ProEtale.upperStarId
  AlgebraicGeometry.ProEtale.openImmersionLowerShriek
  AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction
  AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj
  AlgebraicGeometry.ProEtale.VaryingRing.moduleJAdj
  AlgebraicGeometry.ProEtale.VaryingRing.moduleGComp
  AlgebraicGeometry.ProEtale.VaryingRing.moduleJComp
  AlgebraicGeometry.ProEtale.VaryingRing.modulePId

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem unit_iso_transport {C : Type*} [Category C] (F : C ⥤ C)
    (η : 𝟭 C ⟶ F) {X Y : C} (e : X ≅ Y) :
    e.hom ≫ η.app Y ≫ F.map e.inv = η.app X := by
  have h := η.naturality e.inv
  dsimp only [Functor.id_map] at h
  rw [← h, ← Category.assoc, e.hom_inv_id, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem unconjugate {C : Type*} [Category C]
    {X Y Z W : C} (e : X ≅ Y) (f : Z ≅ W) (a : Y ⟶ Z) (b : X ⟶ W)
    (h : e.hom ≫ a ≫ f.hom = b) : a = e.inv ≫ b ≫ f.inv := by
  rw [← h]
  simp only [Category.assoc, f.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem vertical_factor
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ B) (S : C ⥤ A) (T : C ⥤ D) (K : D ⥤ B)
    (q : S ⋙ R ⟶ T ⋙ K) {X Y : C} (a : X ⟶ Y)
    {Z : A} (v : Z ⟶ S.obj X) (w : Z ⟶ S.obj Y)
    (ha : v ≫ S.map a = w) :
    R.map v ≫ q.app X ≫ K.map (T.map a) = R.map w ≫ q.app Y := by
  have hn := q.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← R.map_comp_assoc, ha]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem horizontal_factor
    {B C D : Type*} [Category B] [Category C] [Category D]
    (K : C ⥤ B) (L : C ⥤ D) (P : D ⥤ C) (η : 𝟭 C ⟶ L ⋙ P)
    {X : B} {Y Z : C} (v : X ⟶ K.obj Y) (a : Y ⟶ Z) :
    v ≫ K.map (η.app Y) ≫ K.map (P.map (L.map a)) =
      (v ≫ K.map a) ≫ K.map (η.app Z) := by
  exact (congrArg (fun f ↦ v ≫ f) ((K.map_comp _ _).symm.trans
    ((congrArg K.map (η.naturality a).symm).trans (K.map_comp _ _)))).trans
      (Category.assoc v (K.map a) (K.map (η.app Z))).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem composite_open_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (e : R'' ≅ R' ⋙ R) (M : A) :
    c.unit.app M ≫ e.hom.app (L''.obj M) =
      (a.comp b).unit.app M ≫
        (R' ⋙ R).map ((Adjunction.leftAdjointCompIso a b c e.symm).hom.app M) := by
  have h : (a.comp b).homEquiv M _
      ((Adjunction.leftAdjointCompIso a b c e.symm).hom.app M) ≫
      e.inv.app (L''.obj M) = c.unit.app M := by
    rw [Adjunction.homEquiv_unit, Category.assoc, e.inv.naturality, ← Category.assoc]
    have hu := unit_conjugateEquiv (a.comp b) c
      (Adjunction.leftAdjointCompIso a b c e.symm).inv M
    rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
    dsimp only [Iso.symm_hom] at hu
    rw [hu, Category.assoc, ← R''.map_comp, Iso.inv_hom_id_app, R''.map_id]
    exact Category.comp_id _
  have h' := congrArg (fun f ↦ f ≫ e.hom.app (L''.obj M)) h
  simpa only [Adjunction.homEquiv_unit, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using h'.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem horizontal_normalized
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    {I : A ⥤ B} {PI : B ⥤ A} {J : B ⥤ E} {PJ : E ⥤ B}
    {K : C ⥤ D} {PK : D ⥤ C} {L : D ⥤ H} {PL : H ⥤ D}
    (ai : I ⊣ PI) (aj : J ⊣ PJ) (ak : K ⊣ PK) (al : L ⊣ PL)
    (R : A ⥤ C) (P : B ⥤ D) (Q : E ⥤ H)
    (s₁ : PI ⋙ R ⟶ P ⋙ PK) (s₂ : PJ ⋙ P ⟶ Q ⋙ PL)
    (a₁ : I ⋙ P ⟶ R ⋙ K) (a₂ : J ⋙ Q ⟶ P ⋙ L)
    (h₁ : ∀ M, R.map (ai.unit.app M) ≫ s₁.app (I.obj M) ≫ PK.map (a₁.app M) =
      ak.unit.app (R.obj M))
    (h₂ : ∀ M, P.map (aj.unit.app M) ≫ s₂.app (J.obj M) ≫ PL.map (a₂.app M) =
      al.unit.app (P.obj M)) (M : A) :
    R.map ((ai.comp aj).unit.app M) ≫
      s₁.app (PJ.obj (J.obj (I.obj M))) ≫
      PK.map (s₂.app (J.obj (I.obj M))) ≫
      PK.map (PL.map (a₂.app (I.obj M) ≫ L.map (a₁.app M))) =
        (ak.comp al).unit.app (R.obj M) := by
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  simp only [Functor.map_comp, Category.assoc]
  have hn := s₁.naturality (aj.unit.app (I.obj M))
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← PK.map_comp_assoc, h₂]
  rw [horizontal_factor PK L PL al.unit]
  simpa only [Category.assoc, Functor.comp_obj] using
    congrArg (fun f ↦ f ≫ _) (h₁ M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transport_normalized
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I I' : A ⥤ B} {PI PI' : B ⥤ A} {K K' : C ⥤ D} {PK PK' : D ⥤ C}
    (ai : I ⊣ PI) (ai' : I' ⊣ PI') (ak : K ⊣ PK) (ak' : K' ⊣ PK')
    (R : A ⥤ C) (Q : B ⥤ D)
    (ei : I ≅ I') (ci : PI' ≅ PI) (ek : K ≅ K') (ck : PK' ≅ PK)
    (s : PI ⋙ R ⟶ Q ⋙ PK) (s' : PI' ⋙ R ⟶ Q ⋙ PK')
    (a : I ⋙ Q ⟶ R ⋙ K)
    (hi : ∀ M, ai'.unit.app M ≫ ci.hom.app (I'.obj M) =
      ai.unit.app M ≫ PI.map (ei.hom.app M))
    (hk : ∀ M, ak'.unit.app M ≫ ck.hom.app (K'.obj M) =
      ak.unit.app M ≫ PK.map (ek.hom.app M))
    (hs : ∀ N, s'.app N ≫ ck.hom.app (Q.obj N) =
      R.map (ci.hom.app N) ≫ s.app N)
    (ha : ∀ M, R.map (ai.unit.app M) ≫ s.app (I.obj M) ≫ PK.map (a.app M) =
      ak.unit.app (R.obj M)) (M : A) :
    R.map (ai'.unit.app M) ≫ s'.app (I'.obj M) ≫
      PK'.map (Q.map (ei.inv.app M) ≫ a.app M ≫ ek.hom.app (R.obj M)) =
        ak'.unit.app (R.obj M) := by
  rw [← cancel_mono (ck.hom.app (K'.obj (R.obj M)))]
  have hn := ck.hom.naturality
    (Q.map (ei.inv.app M) ≫ a.app M ≫ ek.hom.app (R.obj M))
  simp only [Category.assoc]
  rw [hn, reassoc_of% (hs (I'.obj M)), ← R.map_comp_assoc, hi]
  simp only [R.map_comp, PK.map_comp, Category.assoc]
  have hn' := s.naturality (ei.inv.app M)
  dsimp only [Functor.comp_map] at hn'
  rw [← reassoc_of% hn']
  have hc : (ai.unit.app M ≫ PI.map (ei.hom.app M)) ≫ PI.map (ei.inv.app M) =
      ai.unit.app M := by
    rw [Category.assoc, ← PI.map_comp, Iso.hom_inv_id_app, PI.map_id]
    exact Category.comp_id _
  have hc' : R.map (ai.unit.app M) ≫ R.map (PI.map (ei.hom.app M)) ≫
      R.map (PI.map (ei.inv.app M)) = R.map (ai.unit.app M) := by
    simpa only [R.map_comp, Category.assoc] using congrArg R.map hc
  rw [reassoc_of% hc', reassoc_of% (ha M), hk]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_vertical_normalized
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {I : C ⥤ C} {H : D ⥤ D} (eI : I ≅ 𝟭 C) (eH : H ≅ 𝟭 D)
    (M : C) :
    I.map (a.unit.app M) ≫ eI.hom.app (R.obj (L.obj M)) ≫
      R.map (eH.inv.app (L.obj M)) ≫
      R.map (eH.hom.app (L.obj M) ≫ L.map (eI.inv.app M)) =
        a.unit.app (I.obj M) := by
  simp only [R.map_comp]
  rw [← R.map_comp_assoc, Iso.inv_hom_id_app]
  erw [R.map_id, Category.id_comp]
  have hn := eI.hom.naturality (a.unit.app M)
  dsimp only [Functor.id_map] at hn
  rw [reassoc_of% hn]
  have hu := a.unit.naturality (eI.inv.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  erw [← hu, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_unit
    {C : Type*} [Category C] {L R : C ⥤ C} (a : L ⊣ R)
    (e : R ≅ 𝟭 C) (M : C) :
    a.unit.app M ≫ R.map ((Adjunction.leftAdjointIdIso a e).hom.app M) =
      e.inv.app M := by
  have h := unit_conjugateEquiv Adjunction.id a
    (Adjunction.leftAdjointIdIso a e).hom M
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp]
    using h.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_horizontal_normalized
    {C D : Type*} [Category C] [Category D]
    {L₀ R₀ : C ⥤ C} {L₁ R₁ : D ⥤ D}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (F : C ⥤ D)
    (e₀ : R₀ ≅ 𝟭 C) (e₁ : R₁ ≅ 𝟭 D) (M : C) :
    F.map (a₀.unit.app M) ≫ F.map (e₀.hom.app (L₀.obj M)) ≫
      e₁.inv.app (F.obj (L₀.obj M)) ≫
      R₁.map (F.map ((Adjunction.leftAdjointIdIso a₀ e₀).hom.app M) ≫
        (Adjunction.leftAdjointIdIso a₁ e₁).inv.app (F.obj M)) =
      a₁.unit.app (F.obj M) := by
  let j₀ := Adjunction.leftAdjointIdIso a₀ e₀
  let j₁ := Adjunction.leftAdjointIdIso a₁ e₁
  change F.map (a₀.unit.app M) ≫ F.map (e₀.hom.app (L₀.obj M)) ≫
    e₁.inv.app (F.obj (L₀.obj M)) ≫
    R₁.map (F.map (j₀.hom.app M) ≫ j₁.inv.app (F.obj M)) = _
  rw [← cancel_mono (R₁.map (j₁.hom.app (F.obj M)))]
  simp only [Category.assoc, ← R₁.map_comp, Iso.inv_hom_id_app]
  rw [identity_unit]
  simp only [Functor.id_obj, Category.comp_id]
  have hn := e₁.inv.naturality (F.map (j₀.hom.app M))
  dsimp only [Functor.id_map] at hn
  rw [← hn]
  simp only [← F.map_comp_assoc]
  have hu := identity_unit a₀ e₀ M
  have hn₀ := e₀.hom.naturality (j₀.hom.app M)
  dsimp only [Functor.id_map] at hn₀
  rw [← hn₀, ← Category.assoc, hu]
  dsimp only [Functor.id_obj]
  rw [Iso.inv_hom_id_app]
  erw [F.map_id, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_identity_square
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V : Scheme.{u}} (k : U ⟶ V)
    (h : 𝟙 U ≫ k = k ≫ 𝟙 V)
    (M : Sheaf (Scheme.ProEt.topology V) A) :
    (upperStarCompIso A h).hom.app M =
      (upperStarId A U).hom.app
          ((upperStar A k).obj M) ≫
        (upperStar A k).map
          ((upperStarId A V).inv.app M) := by
  have ht : (upperStarCongr A (Category.id_comp k)).symm ≪≫
      upperStarCongr A h ≪≫
      upperStarCongr A (Category.comp_id k) = Iso.refl _ := by
    apply Iso.ext
    simp only [upperStarCongr, Iso.trans_hom, Iso.symm_hom,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Iso.refl_hom, Category.comp_id]
  have hs : upperStarCompIso A h =
      Functor.isoWhiskerLeft (upperStar _ k) (upperStarId _ U) ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (upperStarId _ V).symm (upperStar _ k) := by
    unfold upperStarCompIso
    rw [upperStarComp_id_left, upperStarComp_id_right]
    simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_symm_eq]
    have htt := congrArg (fun e ↦ e ≪≫
      (Functor.leftUnitor (upperStar A k)).symm ≪≫
        Functor.isoWhiskerRight (upperStarId A V).symm
          (upperStar A k)) ht
    simp only [Iso.trans_assoc, Iso.refl_trans] at htt
    rw [htt]
    simp only [← Functor.isoWhiskerLeft_symm, Iso.symm_symm_eq]
  rw [hs]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Iso.symm_hom, Category.id_comp]
  erw [Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_square_symm
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V W X : Scheme.{u}} {a : U ⟶ V} {b : V ⟶ X}
    {c : U ⟶ W} {d : W ⟶ X} (h : a ≫ b = c ≫ d) (heq : c ≫ d = a ≫ b) :
    upperStarCompIso A heq =
      (upperStarCompIso A h).symm := by
  rw [upperStarCompIso_eq_upperStarFactor _ heq heq rfl,
    upperStarCompIso_eq_upperStarFactor _ h rfl heq,
    Iso.trans_symm, Iso.symm_symm_eq]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_horizontal_identity_square
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V : Scheme.{u}} (p : U ⟶ V)
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 V))
    (heq : p ≫ (𝟙 V) = (𝟙 U) ≫ p)
    (M : Sheaf (Scheme.ProEt.topology V) A) :
    (upperStarCompIso A heq).hom.app M =
      (upperStar A p).map ((upperStarId A V).hom.app M) ≫
        (upperStarId A U).inv.app ((upperStar A p).obj M) := by
  have hs := ordinary_identity_square A p h M
  have he := congrArg Iso.inv (Iso.ext
    (α := (upperStarCompIso A h).app M)
    (β := (upperStarId A U).app ((upperStar A p).obj M) ≪≫
      (upperStar A p).mapIso ((upperStarId A V).symm.app M)) hs)
  rw [ordinary_square_symm A h heq]
  simpa only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_inv] using he

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_horizontal_square
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V T W Z Y : Scheme.{u}}
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (h : (k₁ ≫ k₂) ≫ q = r ≫ (i₁ ≫ i₂))
    (e₁ : r ≫ i₁ = k₁ ≫ p) (e₂ : p ≫ i₂ = k₂ ≫ q)
    (e : r ≫ (i₁ ≫ i₂) = (k₁ ≫ k₂) ≫ q)
    (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCompIso A e).hom.app N ≫
      (upperStarComp _ k₁ k₂).hom.app ((upperStar _ q).obj N) =
    (upperStar _ r).map ((upperStarComp _ i₁ i₂).hom.app N) ≫
      (upperStarCompIso A e₁).hom.app
        ((upperStar _ i₂).obj N) ≫
      (upperStar _ k₁).map
        ((upperStarCompIso A e₂).hom.app N)  := by
  have hh := upperStarCompIso_hom_app_paste A h₂ h₁ h N
  have he := congrArg Iso.inv (Iso.ext
    (α := (upperStarComp A k₁ k₂).app ((upperStar A q).obj N) ≪≫
      (upperStar A k₁).mapIso ((upperStarCompIso A h₂).app N) ≪≫
      (upperStarCompIso A h₁).app ((upperStar A i₂).obj N))
    (β := (upperStarCompIso A h).app N ≪≫
      (upperStar A r).mapIso ((upperStarComp A i₁ i₂).app N)) hh)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at he
  change ((upperStarCompIso A h₁).inv.app ((upperStar A i₂).obj N) ≫
    (upperStar A k₁).map ((upperStarCompIso A h₂).inv.app N)) ≫
    (upperStarComp A k₁ k₂).inv.app ((upperStar A q).obj N) =
    (upperStar A r).map ((upperStarComp A i₁ i₂).inv.app N) ≫
    (upperStarCompIso A h).inv.app N at he
  rw [← Iso.symm_hom (upperStarCompIso A h₁),
    ← Iso.symm_hom (upperStarCompIso A h₂),
    ← Iso.symm_hom (upperStarCompIso A h)] at he
  rw [← ordinary_square_symm A h e,
    ← ordinary_square_symm A h₁ e₁,
    ← ordinary_square_symm A h₂ e₂] at he
  have ht := congrArg (fun f ↦
    (upperStar A r).map ((upperStarComp A i₁ i₂).hom.app N) ≫ f ≫
      (upperStarComp A k₁ k₂).hom.app ((upperStar A q).obj N)) he
  simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] using ht.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_identity_square
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V : Scheme.{u}} (k : U ⟶ V)
    (h : k ≫ 𝟙 V = 𝟙 U ≫ k) (M : VaryingRing.Modules C τ V) :
    (VaryingRing.moduleSquareG C τ k (𝟙 U) (𝟙 V) k h).hom.app M =
      (Systems.pullIdentity C τ U).hom.app ((VaryingRing.pull C τ k).obj M) ≫
        (VaryingRing.pull C τ k).map ((Systems.pullIdentity C τ V).inv.app M) := by
  have hid : ∀ X : Scheme.{u}, Systems.pullIdentity C τ X =
      VaryingRing.moduleGId C τ X := by
    intro X
    unfold Systems.pullIdentity VaryingRing.moduleGId
    rfl
  simp only [hid]
  have hl := congr_app (VaryingRing.ordinary_g_left C τ k) M
  have hr := congr_app (VaryingRing.ordinary_g_right C τ k) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hl hr
  have hr' : (VaryingRing.moduleGComp C τ k (𝟙 V)).hom.app M ≫
      (VaryingRing.pull C τ k).map ((VaryingRing.moduleGId C τ V).hom.app M) =
        (eqToIso (congrArg (VaryingRing.pull C τ) (Category.comp_id k))).hom.app M := by
    rw [← hr, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have ht : (eqToIso (congrArg (VaryingRing.pull C τ) h.symm)).hom ≫
      (eqToIso (congrArg (VaryingRing.pull C τ) (Category.comp_id k))).hom =
        (eqToIso (congrArg (VaryingRing.pull C τ) (Category.id_comp k))).hom := by
    simp only [eqToIso.hom, eqToHom_trans]
  have htM := congr_app ht M
  dsimp only [NatTrans.comp_app] at htM
  rw [VaryingRing.moduleSquareG_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← cancel_mono ((VaryingRing.pull C τ k).map
    ((VaryingRing.moduleGId C τ V).hom.app M))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  change (VaryingRing.moduleGComp C τ (𝟙 U) k).inv.app M ≫
      (eqToIso (congrArg (VaryingRing.pull C τ) h.symm)).hom.app M ≫
      (VaryingRing.moduleGComp C τ k (𝟙 V)).hom.app M ≫
      (VaryingRing.pull C τ k).map ((VaryingRing.moduleGId C τ V).hom.app M) = _
  rw [hr', htM, hl]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_horizontal_identity_square
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V : Scheme.{u}} (p : U ⟶ V)
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 V)) (M : VaryingRing.Modules C τ V) :
    (VaryingRing.moduleSquareG C τ (𝟙 U) p p (𝟙 V) h).hom.app M =
      (VaryingRing.pull C τ p).map ((Systems.pullIdentity C τ V).hom.app M) ≫
        (Systems.pullIdentity C τ U).inv.app ((VaryingRing.pull C τ p).obj M) := by
  have hs := system_identity_square C τ p h.symm M
  have he : VaryingRing.moduleSquareG C τ (𝟙 U) p p (𝟙 V) h =
      (VaryingRing.moduleSquareG C τ p (𝟙 U) (𝟙 V) p h.symm).symm := by
    rw [VaryingRing.moduleSquareG_eq, VaryingRing.moduleSquareG_eq]
    simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
    rfl
  rw [he]
  have hh := congrArg Iso.inv (Iso.ext
    (α := (VaryingRing.moduleSquareG C τ p (𝟙 U) (𝟙 V) p h.symm).app M)
    (β := (Systems.pullIdentity C τ U).app ((VaryingRing.pull C τ p).obj M) ≪≫
      (VaryingRing.pull C τ p).mapIso ((Systems.pullIdentity C τ V).symm.app M)) hs)
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_hom,
    Iso.symm_inv] using hh

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem vertical_normalized
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {J₀ : A ⥤ B} {K₀ : B ⥤ A} {J₁ : C ⥤ D} {K₁ : D ⥤ C}
    {J₂ : E ⥤ F} {K₂ : F ⥤ E}
    (ad₀ : J₀ ⊣ K₀) (ad₁ : J₁ ⊣ K₁) (ad₂ : J₂ ⊣ K₂)
    (R₁ : C ⥤ A) (R₂ : E ⥤ C) (R : E ⥤ A)
    (P₁ : D ⥤ B) (P₂ : F ⥤ D) (P : F ⥤ B)
    (cr : R ≅ R₂ ⋙ R₁) (cp : P ≅ P₂ ⋙ P₁)
    (s₁ : K₁ ⋙ R₁ ⟶ P₁ ⋙ K₀) (s₂ : K₂ ⋙ R₂ ⟶ P₂ ⋙ K₁)
    (s : K₂ ⋙ R ⟶ P ⋙ K₀)
    (a₁ : J₁ ⋙ P₁ ⟶ R₁ ⋙ J₀) (a₂ : J₂ ⋙ P₂ ⟶ R₂ ⋙ J₁)
    (h₁ : ∀ M, R₁.map (ad₁.unit.app M) ≫ s₁.app (J₁.obj M) ≫
      K₀.map (a₁.app M) = ad₀.unit.app (R₁.obj M))
    (h₂ : ∀ M, R₂.map (ad₂.unit.app M) ≫ s₂.app (J₂.obj M) ≫
      K₁.map (a₂.app M) = ad₁.unit.app (R₂.obj M))
    (hpaste : ∀ N, cr.hom.app (K₂.obj N) ≫ R₁.map (s₂.app N) ≫
      s₁.app (P₂.obj N) = s.app N ≫ K₀.map (cp.hom.app N)) (M : E) :
    R.map (ad₂.unit.app M) ≫ s.app (J₂.obj M) ≫
      K₀.map (cp.hom.app (J₂.obj M) ≫ P₁.map (a₂.app M) ≫
        a₁.app (R₂.obj M) ≫ J₀.map (cr.inv.app M)) = ad₀.unit.app (R.obj M) := by
  simp only [Functor.map_comp]
  rw [← reassoc_of% (hpaste (J₂.obj M))]
  rw [reassoc_of% (cr.hom.naturality (ad₂.unit.app M))]
  have hv := vertical_factor R₁ K₁ P₁ K₀ s₁ (a₂.app M)
    (R₂.map (ad₂.unit.app M) ≫ s₂.app (J₂.obj M)) _
    (by simpa only [Category.assoc] using h₂ M)
  simp only [Functor.map_comp, Category.assoc] at hv
  rw [reassoc_of% hv, reassoc_of% (h₁ (R₂.obj M))]
  exact unit_iso_transport _ ad₀.unit (cr.app M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem vertical_full
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {J₀ : A ⥤ B} {K₀ : B ⥤ A} {J₁ : C ⥤ D} {K₁ : D ⥤ C}
    {J₂ : E ⥤ F} {K₂ : F ⥤ E}
    (ad₀ : J₀ ⊣ K₀) (ad₁ : J₁ ⊣ K₁) (ad₂ : J₂ ⊣ K₂)
    (R₁ : C ⥤ A) (R₂ : E ⥤ C) (R : E ⥤ A)
    (P₁ : D ⥤ B) (P₂ : F ⥤ D) (P : F ⥤ B)
    (cr : R ≅ R₂ ⋙ R₁) (cp : P ≅ P₂ ⋙ P₁)
    (s₁ : K₁ ⋙ R₁ ⟶ P₁ ⋙ K₀) (s₂ : K₂ ⋙ R₂ ⟶ P₂ ⋙ K₁)
    (s : K₂ ⋙ R ⟶ P ⋙ K₀)
    (a₁ : J₁ ⋙ P₁ ⟶ R₁ ⋙ J₀) (a₂ : J₂ ⋙ P₂ ⟶ R₂ ⋙ J₁)
    (a : J₂ ⋙ P ⟶ R ⋙ J₀)
    (ha₁ : ∀ M, R₁.map (ad₁.unit.app M) ≫ s₁.app (J₁.obj M) ≫
      K₀.map (a₁.app M) = ad₀.unit.app (R₁.obj M))
    (ha₂ : ∀ M, R₂.map (ad₂.unit.app M) ≫ s₂.app (J₂.obj M) ≫
      K₁.map (a₂.app M) = ad₁.unit.app (R₂.obj M))
    (unique : ∀ a' : J₂ ⋙ P ⟶ R ⋙ J₀,
      (∀ M, R.map (ad₂.unit.app M) ≫ s.app (J₂.obj M) ≫ K₀.map (a'.app M) =
        ad₀.unit.app (R.obj M)) → a' = a)
    (hpaste : ∀ N, cr.hom.app (K₂.obj N) ≫ R₁.map (s₂.app N) ≫
      s₁.app (P₂.obj N) = s.app N ≫ K₀.map (cp.hom.app N)) :
    (Functor.whiskerRight a₂ P₁ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft R₂ a₁ = (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft J₂ cp.inv ≫ a ≫ Functor.whiskerRight cr.hom J₀ ≫
      (Functor.associator _ _ _).hom) ∧
    (∀ M, R₁.map (R₂.map (ad₂.unit.app M)) ≫
      R₁.map (s₂.app (J₂.obj M)) ≫ s₁.app (P₂.obj (J₂.obj M)) ≫
      K₀.map (P₁.map (a₂.app M)) =
      R₁.map (ad₁.unit.app (R₂.obj M)) ≫ s₁.app (J₁.obj (R₂.obj M))) ∧
    (∀ M, R₁.map (ad₁.unit.app (R₂.obj M)) ≫ s₁.app (J₁.obj (R₂.obj M)) ≫
      K₀.map (a₁.app (R₂.obj M)) = ad₀.unit.app (R₁.obj (R₂.obj M))) := by
  refine ⟨?_, ?_, ?_⟩
  · let paste : J₂ ⋙
        P ⟶
        R ⋙
        J₀ :=
      Functor.whiskerLeft _ (cp).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (a₂) _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (a₁) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (cr).inv _
    have hA : (∀ M, R.map (ad₂.unit.app M) ≫ s.app (J₂.obj M) ≫ K₀.map (paste.app M) =
          ad₀.unit.app (R.obj M)) := by
      intro M
      simpa only [paste, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.comp_obj, Functor.id_obj,
        Category.id_comp, Category.comp_id] using vertical_normalized
        (ad₀)
        (ad₁)
        (ad₂)
        (R₁) (R₂)
        (R)
        (P₁) (P₂)
        (P)
        (cr)
        (cp)
        s₁
        s₂
        s
        (a₁)
        (a₂) ha₁ ha₂
        hpaste M
    have eA := unique paste hA
    apply NatTrans.ext
    funext M
    have he := congr_app eA M
    dsimp only [paste, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app] at he ⊢
    simp only [Category.id_comp, Category.comp_id] at he ⊢
    simpa only [Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc] using
      unconjugate ((cp).app
        ((J₂).obj M))
        ((J₀).mapIso
          ((cr).symm.app M))
        ((P₁).map ((a₂).app M) ≫
          (a₁).app
            ((R₂).obj M)) _
        (by simpa only [Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
          Iso.symm_hom, Category.assoc] using he)
  · intro M
    simpa only [Functor.map_comp, Functor.comp_map, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using vertical_factor _ _ _ _
      s₁
      ((a₂).app M)
      ((R₂).map
          ((ad₂).unit.app M) ≫
        s₂.app
          ((J₂).obj M)) _
      (by simpa only [Category.assoc] using ha₂ M)
  · intro M
    exact ha₁ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem horizontal_full
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    {I : A ⥤ B} {PI : B ⥤ A} {J : B ⥤ E} {PJ : E ⥤ B}
    {K : C ⥤ D} {PK : D ⥤ C} {L : D ⥤ H} {PL : H ⥤ D}
    {I₁₂ : A ⥤ E} {PI₁₂ : E ⥤ A} {K₁₂ : C ⥤ H} {PK₁₂ : H ⥤ C}
    (ai : I ⊣ PI) (aj : J ⊣ PJ) (ak : K ⊣ PK) (al : L ⊣ PL)
    (ai₁₂ : I₁₂ ⊣ PI₁₂) (ak₁₂ : K₁₂ ⊣ PK₁₂)
    (R : A ⥤ C) (P : B ⥤ D) (Q : E ⥤ H)
    (ei : I ⋙ J ≅ I₁₂) (ek : K ⋙ L ≅ K₁₂)
    (ci : PI₁₂ ≅ PJ ⋙ PI) (ck : PK₁₂ ≅ PL ⋙ PK)
    (s₁ : PI ⋙ R ⟶ P ⋙ PK) (s₂ : PJ ⋙ P ⟶ Q ⋙ PL)
    (s : PI₁₂ ⋙ R ⟶ Q ⋙ PK₁₂)
    (a₁ : I ⋙ P ⟶ R ⋙ K) (a₂ : J ⋙ Q ⟶ P ⋙ L)
    (a : I₁₂ ⋙ Q ⟶ R ⋙ K₁₂)
    (ha₁ : ∀ M, R.map (ai.unit.app M) ≫ s₁.app (I.obj M) ≫ PK.map (a₁.app M) =
      ak.unit.app (R.obj M))
    (ha₂ : ∀ M, P.map (aj.unit.app M) ≫ s₂.app (J.obj M) ≫ PL.map (a₂.app M) =
      al.unit.app (P.obj M))
    (unique : ∀ a' : I₁₂ ⋙ Q ⟶ R ⋙ K₁₂,
      (∀ M, R.map (ai₁₂.unit.app M) ≫ s.app (I₁₂.obj M) ≫ PK₁₂.map (a'.app M) =
        ak₁₂.unit.app (R.obj M)) → a' = a)
    (hi : ∀ M, ai₁₂.unit.app M ≫ ci.hom.app (I₁₂.obj M) =
      (ai.comp aj).unit.app M ≫ (PJ ⋙ PI).map (ei.hom.app M))
    (hk : ∀ M, ak₁₂.unit.app M ≫ ck.hom.app (K₁₂.obj M) =
      (ak.comp al).unit.app M ≫ (PL ⋙ PK).map (ek.hom.app M))
    (hpaste : ∀ N, s.app N ≫ ck.hom.app (Q.obj N) =
      R.map (ci.hom.app N) ≫ s₁.app (PJ.obj N) ≫ PK.map (s₂.app N)) :
    ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft I a₂ ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight a₁ L =
      Functor.whiskerRight ei.hom Q ≫ a ≫ Functor.whiskerLeft R ek.inv ≫
      (Functor.associator _ _ _).inv) ∧
    (∀ M, R.map (ai.unit.app M) ≫ s₁.app (I.obj M) ≫
      PK.map (P.map (aj.unit.app (I.obj M))) ≫ PK.map (s₂.app (J.obj (I.obj M))) ≫
      PK.map (PL.map (a₂.app (I.obj M))) =
      R.map (ai.unit.app M) ≫ s₁.app (I.obj M) ≫ PK.map (al.unit.app (P.obj (I.obj M)))) ∧
    (∀ M, R.map (ai.unit.app M) ≫ s₁.app (I.obj M) ≫ PK.map (al.unit.app (P.obj (I.obj M))) ≫
      PK.map (PL.map (L.map (a₁.app M))) =
      ak.unit.app (R.obj M) ≫ PK.map (al.unit.app (K.obj (R.obj M)))) := by
  refine ⟨?_, ?_, ?_⟩
  · let word : (I ⋙ J) ⋙
        Q ⟶
        R ⋙ (K ⋙
          L) :=
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (a₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (a₁) _ ≫ (Functor.associator _ _ _).hom
    let S : (PJ ⋙
        PI) ⋙ R ⟶
        Q ⋙ (PL ⋙ PK) :=
      (Functor.associator (PJ) (PI) (R)).hom ≫
        Functor.whiskerLeft (PJ)
          s₁ ≫
        (Functor.associator (PJ) (P) (PK)).inv ≫
        Functor.whiskerRight
          s₂
          (PK) ≫
        (Functor.associator (Q) (PL) (PK)).hom
    let paste : I₁₂ ⋙
        Q ⟶
        R ⋙ K₁₂ :=
      Functor.whiskerRight (ei).inv _ ≫ word ≫
        Functor.whiskerLeft _ (ek).hom
    have hb : ∀ M,
        (R).map
            (((ai).comp
              (aj)).unit.app M) ≫
          S.app ((I ⋙
            J).obj M) ≫
          (PL ⋙ PK).map (word.app M) =
            (((ak).comp
              (al)).unit.app
              ((R).obj M)) := by
      intro M
      simpa only [word, S, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.map_comp, CategoryTheory.Functor.map_id,
        Functor.comp_obj, Functor.id_obj,
        Category.id_comp, Category.comp_id, Functor.comp_map, Category.assoc] using
        horizontal_normalized
          (ai)
          (aj)
          (ak)
          (al)
          (R) (P) (Q)
          s₁ s₂
          (a₁)
          (a₂) ha₁ ha₂ M
    have hA : (∀ M, R.map (ai₁₂.unit.app M) ≫ s.app (I₁₂.obj M) ≫ PK₁₂.map (paste.app M) =
          ak₁₂.unit.app (R.obj M)) := by
      intro M
      exact transport_normalized
        ((ai).comp
          (aj))
        (ai₁₂)
        ((ak).comp
          (al))
        (ak₁₂)
        (R) (Q)
        (ei) (ci)
        (ek) (ck)
        S s word
        hi hk
        (by
          intro N
          simpa only [S, NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.whiskerRight_app, Functor.associator_hom_app,
            Functor.associator_inv_app, Category.id_comp, Category.comp_id] using
            hpaste N) hb M
    have eA := unique paste hA
    apply NatTrans.ext
    funext M
    have he := congr_app eA M
    dsimp only [paste, word, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app] at he ⊢
    simp only [Category.id_comp, Category.comp_id] at he ⊢
    rw [← cancel_epi ((Q).map
      ((ei).inv.app M)), ← cancel_mono
      ((ek).hom.app ((R).obj M))]
    simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp] using he
  · intro M
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦
        ((R).map
          ((ai).unit.app M) ≫
            s₁.app
              ((I).obj M)) ≫
            (PK).map f)
        (ha₂ ((I).obj M))
  · intro M
    rw [horizontal_factor _ _ _
      (al).unit]
    simpa only [Category.assoc, Functor.comp_obj] using
      congrArg (fun f ↦ f ≫ _) (ha₁ M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_vertical_full
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (ad : L ⊣ R)
    {I : C ⥤ C} {H : D ⥤ D} (eI : I ≅ 𝟭 C) (eH : H ≅ 𝟭 D)
    (s : R ⋙ I ⟶ H ⋙ R) (a : L ⋙ H ⟶ I ⋙ L)
    (hs : ∀ N, s.app N = eI.hom.app (R.obj N) ≫ R.map (eH.inv.app N))
    (unique : ∀ b : L ⋙ H ⟶ I ⋙ L,
      (∀ M, I.map (ad.unit.app M) ≫ s.app (L.obj M) ≫ R.map (b.app M) =
        ad.unit.app (I.obj M)) → b = a) :
    a = Functor.whiskerLeft L eH.hom ≫ (Functor.rightUnitor _).hom ≫
      (Functor.leftUnitor _).inv ≫ Functor.whiskerRight eI.inv L := by
  symm
  apply unique
  intro M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app]
  rw [hs]
  simp only [Category.id_comp]
  simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc,
    Category.id_comp, Category.comp_id] using identity_vertical_normalized ad eI eH M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_horizontal_full
    {C D : Type*} [Category C] [Category D]
    {L₀ R₀ : C ⥤ C} {L₁ R₁ : D ⥤ D}
    (ad₀ : L₀ ⊣ R₀) (ad₁ : L₁ ⊣ R₁) (P : C ⥤ D)
    (e₀ : R₀ ≅ 𝟭 C) (e₁ : R₁ ≅ 𝟭 D)
    (s : R₀ ⋙ P ⟶ P ⋙ R₁) (a : L₀ ⋙ P ⟶ P ⋙ L₁)
    (hs : ∀ N, s.app N = P.map (e₀.hom.app N) ≫ e₁.inv.app (P.obj N))
    (unique : ∀ b : L₀ ⋙ P ⟶ P ⋙ L₁,
      (∀ M, P.map (ad₀.unit.app M) ≫ s.app (L₀.obj M) ≫ R₁.map (b.app M) =
        ad₁.unit.app (P.obj M)) → b = a) :
    a = Functor.whiskerRight (Adjunction.leftAdjointIdIso ad₀ e₀).hom P ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft P (Adjunction.leftAdjointIdIso ad₁ e₁).inv := by
  symm
  apply unique
  intro M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app]
  rw [hs]
  simp only [Category.id_comp]
  simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc,
    Category.id_comp, Category.comp_id] using identity_horizontal_normalized ad₀ ad₁ P e₀ e₁ M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem vertical_word
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (J₀ : A ⥤ B) (J₁ : C ⥤ D) (J₂ : E ⥤ F)
    (R₁ : C ⥤ A) (R₂ : E ⥤ C) (R : E ⥤ A)
    (P₁ : D ⥤ B) (P₂ : F ⥤ D) (P : F ⥤ B)
    (cr : R ≅ R₂ ⋙ R₁) (cp : P ≅ P₂ ⋙ P₁)
    (a₁ : J₁ ⋙ P₁ ⟶ R₁ ⋙ J₀) (a₂ : J₂ ⋙ P₂ ⟶ R₂ ⋙ J₁)
    (a : J₂ ⋙ P ⟶ R ⋙ J₀)
    (h : ∀ M, cp.hom.app (J₂.obj M) ≫ P₁.map (a₂.app M) ≫
      a₁.app (R₂.obj M) = a.app M ≫ J₀.map (cr.hom.app M)) :
    Functor.whiskerRight a₂ P₁ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft R₂ a₁ =
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J₂ cp.inv ≫ a ≫
      Functor.whiskerRight cr.hom J₀ ≫ (Functor.associator _ _ _).hom := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id]
  rw [← cancel_epi (cp.hom.app (J₂.obj M))]
  simp only [Iso.hom_inv_id_app_assoc]
  exact h M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem horizontal_word
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (I₁ : A ⥤ B) (I₂ : B ⥤ C) (I : A ⥤ C)
    (K₁ : D ⥤ E) (K₂ : E ⥤ F) (K : D ⥤ F)
    (R : A ⥤ D) (P : B ⥤ E) (Q : C ⥤ F)
    (ci : I₁ ⋙ I₂ ≅ I) (ck : K₁ ⋙ K₂ ≅ K)
    (a₁ : I₁ ⋙ P ⟶ R ⋙ K₁) (a₂ : I₂ ⋙ Q ⟶ P ⋙ K₂)
    (a : I ⋙ Q ⟶ R ⋙ K)
    (h : ∀ M, Q.map (ci.hom.app M) ≫ a.app M =
      a₂.app (I₁.obj M) ≫ K₂.map (a₁.app M) ≫ ck.hom.app (R.obj M)) :
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft I₁ a₂ ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight a₁ K₂ =
    Functor.whiskerRight ci.hom Q ≫ a ≫ Functor.whiskerLeft R ck.inv ≫
      (Functor.associator _ _ _).inv := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id]
  rw [← cancel_mono (ck.hom.app (R.obj M))]
  simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using (h M).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem horizontal_factors
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    {I : A ⥤ B} {PI : B ⥤ A} {J : B ⥤ E} {PJ : E ⥤ B}
    {K : C ⥤ D} {PK : D ⥤ C} {L : D ⥤ H} {PL : H ⥤ D}
    (ai : 𝟭 A ⟶ I ⋙ PI) (aj : 𝟭 B ⟶ J ⋙ PJ)
    (ak : 𝟭 C ⟶ K ⋙ PK) (al : 𝟭 D ⟶ L ⋙ PL)
    (R : A ⥤ C) (P : B ⥤ D) (Q : E ⥤ H)
    (s₁ : PI ⋙ R ⟶ P ⋙ PK) (s₂ : PJ ⋙ P ⟶ Q ⋙ PL)
    (a₁ : I ⋙ P ⟶ R ⋙ K) (a₂ : J ⋙ Q ⟶ P ⋙ L)
    (ha₁ : ∀ M, R.map (ai.app M) ≫ s₁.app (I.obj M) ≫ PK.map (a₁.app M) =
      ak.app (R.obj M))
    (ha₂ : ∀ M, P.map (aj.app M) ≫ s₂.app (J.obj M) ≫ PL.map (a₂.app M) =
      al.app (P.obj M)) :
    (∀ M, R.map (ai.app M) ≫ s₁.app (I.obj M) ≫
      PK.map (P.map (aj.app (I.obj M))) ≫ PK.map (s₂.app (J.obj (I.obj M))) ≫
      PK.map (PL.map (a₂.app (I.obj M))) =
      R.map (ai.app M) ≫ s₁.app (I.obj M) ≫ PK.map (al.app (P.obj (I.obj M)))) ∧
    (∀ M, R.map (ai.app M) ≫ s₁.app (I.obj M) ≫ PK.map (al.app (P.obj (I.obj M))) ≫
      PK.map (PL.map (L.map (a₁.app M))) =
      ak.app (R.obj M) ≫ PK.map (al.app (K.obj (R.obj M)))) := by
  constructor
  · intro M
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ (R.map (ai.app M) ≫ s₁.app (I.obj M)) ≫ PK.map f)
        (ha₂ (I.obj M))
  · intro M
    have hu : PK.map (al.app (P.obj (I.obj M))) ≫
        PK.map (PL.map (L.map (a₁.app M))) =
      PK.map (a₁.app M) ≫ PK.map (al.app (K.obj (R.obj M))) :=
      (PK.map_comp _ _).symm.trans
        ((congrArg PK.map (al.naturality (a₁.app M)).symm).trans (PK.map_comp _ _))
    calc
      _ = (R.map (ai.app M) ≫ s₁.app (I.obj M) ≫ PK.map (a₁.app M)) ≫
          PK.map (al.app (K.obj (R.obj M))) := by
        simpa only [Category.assoc] using
          congrArg (fun f ↦ (R.map (ai.app M) ≫ s₁.app (I.obj M)) ≫ f) hu
      _ = _ := congrArg (fun f ↦ f ≫ PK.map (al.app (K.obj (R.obj M)))) (ha₁ M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_normalized_iff
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (h : k ≫ p = r ≫ i)
    (a : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (heq : r ≫ i = k ≫ p) :
    AmbientClopen.Normalized Λ k r p i h a ↔
      ∀ M, (upperStar (ModuleCat.{u + 1} Λ) r).map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app M) ≫
        (upperStarCompIso (ModuleCat.{u + 1} Λ) heq).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k).map (a.app M) =
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k).unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) r).obj M) := by
  have e : AmbientClopen.Normalized._proof_1 k r p i h = heq := Subsingleton.elim _ _
  cases e
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_vertical (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Normalized Λ k r p i h (AmbientClopen.alpha Λ k r p i h) ∧
        (∀ a, AmbientClopen.Normalized Λ k r p i h a →
          a = AmbientClopen.alpha Λ k r p i h)) :
    Ordinary.Vertical Λ F := by
  intro U₀ U₁ U₂ V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j₀ j₁ j₂ r₁ r₂ p₁ p₂ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ h₁ h₂ h
  exact vertical_full
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₀)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₁)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₂)
    (upperStar (ModuleCat.{u + 1} Λ) r₁) (upperStar (ModuleCat.{u + 1} Λ) r₂)
    (upperStar (ModuleCat.{u + 1} Λ) (r₁ ≫ r₂))
    (upperStar (ModuleCat.{u + 1} Λ) p₁) (upperStar (ModuleCat.{u + 1} Λ) p₂)
    (upperStar (ModuleCat.{u + 1} Λ) (p₁ ≫ p₂))
    (upperStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)
    (upperStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)
    (upperStarCompIso (ModuleCat.{u + 1} Λ)
      (Ordinary.Vertical._proof_1 U₀ U₁ V₀ V₁ j₀ j₁ r₁ p₁ h₁)).hom
    (upperStarCompIso (ModuleCat.{u + 1} Λ)
      (Ordinary.Vertical._proof_1 U₁ U₂ V₁ V₂ j₁ j₂ r₂ p₂ h₂)).hom
    (upperStarCompIso (ModuleCat.{u + 1} Λ) h.symm).hom
    (AmbientClopen.alpha Λ j₀ r₁ p₁ j₁ h₁)
    (AmbientClopen.alpha Λ j₁ r₂ p₂ j₂ h₂)
    (AmbientClopen.alpha Λ j₀ (r₁ ≫ r₂) (p₁ ≫ p₂) j₂ h)
    ((ordinary_normalized_iff Λ j₀ r₁ p₁ j₁ h₁ _
      (Ordinary.Vertical._proof_1 U₀ U₁ V₀ V₁ j₀ j₁ r₁ p₁ h₁)).mp
      (localize j₀ r₁ p₁ j₁ h₁).1)
    ((ordinary_normalized_iff Λ j₁ r₂ p₂ j₂ h₂ _
      (Ordinary.Vertical._proof_1 U₁ U₂ V₁ V₂ j₁ j₂ r₂ p₂ h₂)).mp
      (localize j₁ r₂ p₂ j₂ h₂).1)
    (fun a ha ↦ (localize j₀ (r₁ ≫ r₂) (p₁ ≫ p₂) j₂ h).2 a
      ((ordinary_normalized_iff Λ j₀ (r₁ ≫ r₂) (p₁ ≫ p₂) j₂ h a h.symm).mpr ha))
    (upperStarCompIso_hom_app_paste (ModuleCat.{u + 1} Λ)
      (Ordinary.Vertical._proof_1 U₁ U₂ V₁ V₂ j₁ j₂ r₂ p₂ h₂)
      (Ordinary.Vertical._proof_1 U₀ U₁ V₀ V₁ j₀ j₁ r₁ p₁ h₁) h.symm)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_horizontal (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Normalized Λ k r p i h (AmbientClopen.alpha Λ k r p i h) ∧
        (∀ a, AmbientClopen.Normalized Λ k r p i h a →
          a = AmbientClopen.alpha Λ k r p i h)) :
    Ordinary.Horizontal Λ F := by
  intro U V T W Z Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k₁ k₂ i₁ i₂ r p q _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ h₁ h₂ h
  exact horizontal_full
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i₁)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i₂)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k₁)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k₂)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (i₁ ≫ i₂))
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (k₁ ≫ k₂))
    (upperStar (ModuleCat.{u + 1} Λ) r) (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) q)
    (AmbientClopen.openComp Λ i₁ i₂) (AmbientClopen.openComp Λ k₁ k₂)
    (upperStarComp (ModuleCat.{u + 1} Λ) i₁ i₂)
    (upperStarComp (ModuleCat.{u + 1} Λ) k₁ k₂)
    (upperStarCompIso (ModuleCat.{u + 1} Λ) (Ordinary.Horizontal._proof_1 U V W Z k₁ i₁ r p h₁)).hom
    (upperStarCompIso (ModuleCat.{u + 1} Λ) (Ordinary.Horizontal._proof_1 V T Z Y k₂ i₂ p q h₂)).hom
    (upperStarCompIso (ModuleCat.{u + 1} Λ) h.symm).hom
    (AmbientClopen.alpha Λ k₁ r p i₁ h₁) (AmbientClopen.alpha Λ k₂ p q i₂ h₂)
    (AmbientClopen.alpha Λ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h)
    ((ordinary_normalized_iff Λ k₁ r p i₁ h₁ _
      (Ordinary.Horizontal._proof_1 U V W Z k₁ i₁ r p h₁)).mp
      (localize k₁ r p i₁ h₁).1)
    ((ordinary_normalized_iff Λ k₂ p q i₂ h₂ _
      (Ordinary.Horizontal._proof_1 V T Z Y k₂ i₂ p q h₂)).mp
      (localize k₂ p q i₂ h₂).1)
    (fun a ha ↦ (localize (k₁ ≫ k₂) r q (i₁ ≫ i₂) h).2 a
      ((ordinary_normalized_iff Λ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h a h.symm).mpr ha))
    (composite_open_unit
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i₁)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i₂)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (i₁ ≫ i₂))
      (upperStarComp (ModuleCat.{u + 1} Λ) i₁ i₂))
    (composite_open_unit
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k₁)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k₂)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (k₁ ≫ k₂))
      (upperStarComp (ModuleCat.{u + 1} Λ) k₁ k₂))
    (ordinary_horizontal_square (ModuleCat.{u + 1} Λ) k₁ k₂ i₁ i₂ r p q h₁ h₂ h
      (Ordinary.Horizontal._proof_1 U V W Z k₁ i₁ r p h₁)
      (Ordinary.Horizontal._proof_1 V T Z Y k₂ i₂ p q h₂) h.symm)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_identities (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Normalized Λ k r p i h (AmbientClopen.alpha Λ k r p i h) ∧
        (∀ a, AmbientClopen.Normalized Λ k r p i h a →
          a = AmbientClopen.alpha Λ k r p i h)) :
    Ordinary.Identities Λ F := by
  constructor
  · intro U V _ _ _ _ _ _ k _ _ _ h
    exact identity_vertical_full
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k)
      (upperStarId (ModuleCat.{u + 1} Λ) U) (upperStarId (ModuleCat.{u + 1} Λ) V)
      (upperStarCompIso (ModuleCat.{u + 1} Λ)
        (AmbientClopen.Normalized._proof_1 k (𝟙 U) (𝟙 V) k h)).hom
      (AmbientClopen.alpha Λ k (𝟙 U) (𝟙 V) k h)
      (ordinary_identity_square (ModuleCat.{u + 1} Λ) k
        (AmbientClopen.Normalized._proof_1 k (𝟙 U) (𝟙 V) k h))
      (localize k (𝟙 U) (𝟙 V) k h).2
  · intro U V _ _ _ _ _ _ p _ _ h
    exact identity_horizontal_full
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 V))
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 U))
      (upperStar (ModuleCat.{u + 1} Λ) p)
      (upperStarId (ModuleCat.{u + 1} Λ) V) (upperStarId (ModuleCat.{u + 1} Λ) U)
      (upperStarCompIso (ModuleCat.{u + 1} Λ)
        (AmbientClopen.Normalized._proof_1 (𝟙 U) p p (𝟙 V) h)).hom
      (AmbientClopen.alpha Λ (𝟙 U) p p (𝟙 V) h)
      (ordinary_horizontal_identity_square (ModuleCat.{u + 1} Λ) p h
        (AmbientClopen.Normalized._proof_1 (𝟙 U) p p (𝟙 V) h))
      (localize (𝟙 U) p p (𝟙 V) h).2

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_vertical_word
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U₀ U₁ U₂ V₀ V₁ V₂ : Scheme.{u}}
    (j₀ : U₀ ⟶ V₀) (j₁ : U₁ ⟶ V₁) (j₂ : U₂ ⟶ V₂)
    (r₁ : U₀ ⟶ U₁) (r₂ : U₁ ⟶ U₂) (p₁ : V₀ ⟶ V₁) (p₂ : V₁ ⟶ V₂)
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [QuasiCompact j₀] [QuasiCompact j₁] [QuasiCompact j₂]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : j₀ ≫ p₁ = r₁ ≫ j₁) (h₂ : j₁ ≫ p₂ = r₂ ≫ j₂)
    (h : j₀ ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j₂) :
    Functor.whiskerRight (VaryingRing.moduleAlpha C τ j₁ r₂ p₂ j₂ h₂) (VaryingRing.pull C τ p₁) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.pull C τ r₂) (VaryingRing.moduleAlpha C τ j₀ r₁ p₁ j₁ h₁) =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.extension C τ j₂) (VaryingRing.moduleGComp C τ p₁ p₂).inv ≫
      (VaryingRing.moduleAlpha C τ j₀ (r₁ ≫ r₂) (p₁ ≫ p₂) j₂ h) ≫
      Functor.whiskerRight (VaryingRing.moduleGComp C τ r₁ r₂).hom (VaryingRing.extension C τ j₀) ≫
      (Functor.associator _ _ _).hom := by
  exact vertical_word
    (VaryingRing.extension C τ j₀) (VaryingRing.extension C τ j₁)
    (VaryingRing.extension C τ j₂)
    (VaryingRing.pull C τ r₁) (VaryingRing.pull C τ r₂)
    (VaryingRing.pull C τ (r₁ ≫ r₂))
    (VaryingRing.pull C τ p₁) (VaryingRing.pull C τ p₂)
    (VaryingRing.pull C τ (p₁ ≫ p₂))
    (VaryingRing.moduleGComp C τ r₁ r₂) (VaryingRing.moduleGComp C τ p₁ p₂)
    (VaryingRing.moduleAlpha C τ j₀ r₁ p₁ j₁ h₁)
    (VaryingRing.moduleAlpha C τ j₁ r₂ p₂ j₂ h₂)
    (VaryingRing.moduleAlpha C τ j₀ (r₁ ≫ r₂) (p₁ ≫ p₂) j₂ h)
    (VaryingRing.moduleAlpha_vertical C τ j₀ j₁ j₂ r₁ r₂ p₁ p₂ h₁ h₂ h)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_vertical
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Systems.Normalized C τ k r p i h
        (VaryingRing.moduleAlpha C τ k r p i h) ∧
        (∀ a, AmbientClopen.Systems.Normalized C τ k r p i h a →
          a = VaryingRing.moduleAlpha C τ k r p i h)) :
    Systems.Vertical C τ F := by
  intro U₀ U₁ U₂ V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j₀ j₁ j₂ r₁ r₂ p₁ p₂ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ h₁ h₂ h
  have a₁ := (localize j₀ r₁ p₁ j₁ h₁).1
  have a₂ := (localize j₁ r₂ p₂ j₂ h₂).1
  refine ⟨?_, ?_, ?_⟩
  · exact system_vertical_word C τ j₀ j₁ j₂ r₁ r₂ p₁ p₂ h₁ h₂ h
  · intro M
    simpa only [Functor.map_comp, Functor.comp_map, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using vertical_factor _ _ _ _
      (VaryingRing.moduleSquareG C τ
        j₀ r₁ p₁ j₁ h₁).hom
      ((VaryingRing.moduleAlpha C τ
        j₁ r₂ p₂ j₂ h₂).app M)
      ((VaryingRing.pull C τ r₂).map ((VaryingRing.moduleJAdj C τ j₂).unit.app M) ≫
        (VaryingRing.moduleSquareG C τ j₁ r₂ p₂ j₂ h₂).hom.app
          ((VaryingRing.extension C τ j₂).obj M)) _
      (by simpa only [Category.assoc] using a₂ M)
  · intro M
    exact a₁ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_horizontal_word
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V T W Z Y : Scheme.{u}}
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact k₁] [QuasiCompact k₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (h : (k₁ ≫ k₂) ≫ q = r ≫ (i₁ ≫ i₂)) :
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.extension C τ i₁) (VaryingRing.moduleAlpha C τ k₂ p q i₂ h₂)
        ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁) (VaryingRing.extension C τ k₂)
        =
      Functor.whiskerRight (VaryingRing.moduleJComp C τ i₁ i₂).hom (VaryingRing.pull C τ q) ≫
      (VaryingRing.moduleAlpha C τ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h) ≫
      Functor.whiskerLeft (VaryingRing.pull C τ r) (VaryingRing.moduleJComp C τ k₁ k₂).inv ≫
      (Functor.associator _ _ _).inv := by
  exact horizontal_word
    (VaryingRing.extension C τ i₁) (VaryingRing.extension C τ i₂)
    (VaryingRing.extension C τ (i₁ ≫ i₂))
    (VaryingRing.extension C τ k₁) (VaryingRing.extension C τ k₂)
    (VaryingRing.extension C τ (k₁ ≫ k₂))
    (VaryingRing.pull C τ r) (VaryingRing.pull C τ p) (VaryingRing.pull C τ q)
    (VaryingRing.moduleJComp C τ i₁ i₂) (VaryingRing.moduleJComp C τ k₁ k₂)
    (VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁)
    (VaryingRing.moduleAlpha C τ k₂ p q i₂ h₂)
    (VaryingRing.moduleAlpha C τ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h)
    (VaryingRing.moduleAlpha_horizontal C τ k₁ k₂ i₁ i₂ r p q h₁ h₂ h)

private def Systems.HorizontalFactorData.norm₁ (d : Systems.HorizontalFactorData.{v, w}) : Prop :=
  letI := d.catA
  letI := d.catB
  letI := d.catC
  letI := d.catD
  letI := d.catE
  letI := d.catH
  ∀ M, d.R.map (d.etaI.app M) ≫ d.s₁.app (d.I.obj M) ≫ d.PK.map (d.a₁.app M) =
    d.etaK.app (d.R.obj M)

private def Systems.HorizontalFactorData.norm₂ (d : Systems.HorizontalFactorData.{v, w}) : Prop :=
  letI := d.catA
  letI := d.catB
  letI := d.catC
  letI := d.catD
  letI := d.catE
  letI := d.catH
  ∀ M, d.P.map (d.etaJ.app M) ≫ d.s₂.app (d.J.obj M) ≫ d.PL.map (d.a₂.app M) =
    d.etaL.app (d.P.obj M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem Systems.HorizontalFactorData.paste (d : Systems.HorizontalFactorData.{v, w})
    (h₁ : d.norm₁) (h₂ : d.norm₂) : d.factors := by
  exact @horizontal_factors d.A d.B d.C d.D d.E d.H
    d.catA d.catB d.catC d.catD d.catE d.catH
    d.I d.PI d.J d.PJ d.K d.PK d.L d.PL
    d.etaI d.etaJ d.etaK d.etaL d.R d.P d.Q d.s₁ d.s₂ d.a₁ d.a₂ h₁ h₂

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_horizontal
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Systems.Normalized C τ k r p i h
        (VaryingRing.moduleAlpha C τ k r p i h) ∧
        (∀ a, AmbientClopen.Systems.Normalized C τ k r p i h a →
          a = VaryingRing.moduleAlpha C τ k r p i h)) :
    Systems.Horizontal C τ F := by
  intro U V T W Z Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k₁ k₂ i₁ i₂ r p q _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ h₁ h₂ h
  refine ⟨system_horizontal_word C τ k₁ k₂ i₁ i₂ r p q h₁ h₂ h, ?_⟩
  let data := Systems.horizontalFactorData C τ k₁ k₂ i₁ i₂ r p q h₁ h₂
  have hnorm₁ : (data @AmbientClopen.Systems.Normalized._proof_1).norm₁ :=
    (localize k₁ r p i₁ h₁).1
  have hnorm₂ : (data @AmbientClopen.Systems.Normalized._proof_1).norm₂ :=
    (localize k₂ p q i₂ h₂).1
  have hfac := (data @AmbientClopen.Systems.Normalized._proof_1).paste hnorm₁ hnorm₂
  have heq : data @AmbientClopen.Systems.Normalized._proof_1 =
      data @Systems.pullIdentity._proof_1 := congrArg data (Subsingleton.elim _ _)
  exact Eq.mp (congrArg Systems.HorizontalFactorData.factors heq) hfac

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_identities
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Systems.Normalized C τ k r p i h
        (VaryingRing.moduleAlpha C τ k r p i h) ∧
        (∀ a, AmbientClopen.Systems.Normalized C τ k r p i h a →
          a = VaryingRing.moduleAlpha C τ k r p i h)) :
    Systems.Identities C τ F := by
  constructor
  · intro U V _ _ _ _ _ _ k _ _ _ h
    exact identity_vertical_full
      (VaryingRing.moduleJAdj C τ k)
      (Systems.pullIdentity C τ U) (Systems.pullIdentity C τ V)
      (VaryingRing.moduleSquareG C τ k (𝟙 U) (𝟙 V) k h).hom
      (VaryingRing.moduleAlpha C τ k (𝟙 U) (𝟙 V) k h)
      (system_identity_square C τ k h)
      (localize k (𝟙 U) (𝟙 V) k h).2
  · intro U V _ _ _ _ _ _ p _ _ h
    exact identity_horizontal_full
      (VaryingRing.moduleJAdj C τ (𝟙 V)) (VaryingRing.moduleJAdj C τ (𝟙 U))
      (VaryingRing.pull C τ p)
      (Systems.pullIdentity C τ V) (Systems.pullIdentity C τ U)
      (VaryingRing.moduleSquareG C τ (𝟙 U) p p (𝟙 V) h).hom
      (VaryingRing.moduleAlpha C τ (𝟙 U) p p (𝟙 V) h)
      (system_horizontal_identity_square C τ p h)
      (localize (𝟙 U) p p (𝟙 V) h).2

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_pasting (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Normalized Λ k r p i h (AmbientClopen.alpha Λ k r p i h) ∧
        (∀ a, AmbientClopen.Normalized Λ k r p i h a →
          a = AmbientClopen.alpha Λ k r p i h)) :
    Ordinary.Vertical Λ F ∧ Ordinary.Horizontal Λ F ∧ Ordinary.Identities Λ F := by
  exact ⟨ordinary_vertical Λ F localize, ordinary_horizontal Λ F localize,
    ordinary_identities Λ F localize⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_pasting
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (F : FiniteFieldDatum.{u})
    (localize : ∀ {U V W Z : Scheme.{u}}
      [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
      [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
      [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
      [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      AmbientClopen.Systems.Normalized C τ k r p i h
        (VaryingRing.moduleAlpha C τ k r p i h) ∧
        (∀ a, AmbientClopen.Systems.Normalized C τ k r p i h a →
          a = VaryingRing.moduleAlpha C τ k r p i h)) :
    Systems.Vertical C τ F ∧ Systems.Horizontal C τ F ∧ Systems.Identities C τ F := by
  exact ⟨system_vertical C τ F localize, system_horizontal C τ F localize,
    system_identities C τ F localize⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The intrinsic clopen arrows paste before deriving, for each positive coefficient
level and for the simultaneous semilinear system category.
Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D; agent underived formulation
(blueprint: lem-sf-ambient-underived-clopen-pasting).

Proof: Use the normalization and uniqueness clauses of the existing clopen localization
assertion. For ordinary vertical and horizontal rectangles, normalize the pasted arrow
using naturality, pullback coherence, and the unit equation of the composite open
adjunction. Uniqueness identifies it with the outer arrow; cancel the compositors.
The individual factor equations are the same normalization and naturality calculations.
For systems, use the published ordinary-system pasting equations and prove the factor
equations from the same single-square normalization. For identity squares, the unit
equations for the specified identity adjoint isomorphisms normalize the displayed word;
uniqueness identifies it with the intrinsic arrow. All calculations are categorical and
therefore include the empty open and the zero module without additional assumptions. -/
theorem ambientUnderivedClopenPasting
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (∀ n : ℕ, Ordinary.Vertical (scalarRings l E n) F ∧
      Ordinary.Horizontal (scalarRings l E n) F ∧
      Ordinary.Identities (scalarRings l E n) F) ∧
    (Systems.Vertical (scalarRings l E) (scalarTransitions l E) F ∧
      Systems.Horizontal (scalarRings l E) (scalarTransitions l E) F ∧
      Systems.Identities (scalarRings l E) (scalarTransitions l E) F) := by
  constructor
  · intro n
    apply ordinary_pasting (scalarRings l E n) F
    intro U V W Z _ _ _ _ _ _ _ _ _ _ _ _ k r p i _ _ _ _ _ _ _ _ _ _ h
    have hloc := (ambientExactClopenComparisonLocalizes F l _hl E k r p i h).1 n
    exact ⟨hloc.1, hloc.2.1⟩
  · apply system_pasting (scalarRings l E) (scalarTransitions l E) F
    intro U V W Z _ _ _ _ _ _ _ _ _ _ _ _ k r p i _ _ _ _ _ _ _ _ _ _ h
    have hloc := (ambientExactClopenComparisonLocalizes F l _hl E k r p i h).2.1
    exact ⟨hloc.1, hloc.2.1⟩

end PastingProof

end AlgebraicGeometry.ProEtale.AmbientClopen.UnderivedPasting

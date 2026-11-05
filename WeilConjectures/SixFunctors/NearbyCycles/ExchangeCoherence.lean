/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-!

# Coherence of the pullback exchanges of nearby cycles

The pullback exchanges `α_φ : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of morphisms of models
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange`) are
compatible with commutative squares of morphisms of models (blueprint
`sk-lem-tf-nearby-mate-coherences` (2), `α_{gf} = α_f(g^*) f_s^* α_g`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']

/-- The counit identity of the exchange morphism `exchangeRight af af' θ : Rf ⋙ G ⟶ G' ⋙ Rf'`. -/
lemma exchangeRight_app_comp_counit {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    (K : A) :
    Lf'.map ((exchangeRight af af' θ).app K) ≫ af'.counit.app (G'.obj K) =
      θ.hom.app (Rf.obj K) ≫ G'.map (af.counit.app K) := by
  simp [exchangeRight_app]

/-- `exchangeRight_app_comp_counit` for a transformation `bc` equal to the exchange morphism. -/
lemma exchangeRight_app_comp_counit' {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    (bc : Rf ⋙ G ⟶ G' ⋙ Rf') (h : bc = exchangeRight af af' θ) (K : A) :
    Lf'.map (bc.app K) ≫ af'.counit.app (G'.obj K) =
      θ.hom.app (Rf.obj K) ≫ G'.map (af.counit.app K) := by
  subst h
  exact exchangeRight_app_comp_counit af af' θ K

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Abstract computations -/

section Abstract

variable {DX1 DX DZ1 DZ TM1 TM TP1 TP GM1 GM GP1 GP : Type*} [Category DX1] [Category DX]
  [Category DZ1] [Category DZ] [Category TM1] [Category TM] [Category TP1] [Category TP]
  [Category GM1] [Category GM] [Category GP1] [Category GP]
  {g : DX1 ⥤ DX} {f : DX ⥤ DZ} {e : DX1 ⥤ DZ1} {k : DZ1 ⥤ DZ}
  {tψ : TM1 ⥤ TM} {tφ : TM ⥤ TP} {tφ' : TM1 ⥤ TP1} {tψ' : TP1 ⥤ TP}
  {gψ : GM1 ⥤ GM} {gφ : GM ⥤ GP} {gφ' : GM1 ⥤ GP1} {gψ' : GP1 ⥤ GP}
  {εM1 : DX1 ⥤ GM1} {εM : DX ⥤ GM} {εP1 : DZ1 ⥤ GP1} {εP : DZ ⥤ GP}
  {jM1 : TM1 ⥤ GM1} {jM : TM ⥤ GM} {jP1 : TP1 ⥤ GP1} {jP : TP ⥤ GP}
  {RM1 : GM1 ⥤ TM1} {RM : GM ⥤ TM} {RP1 : GP1 ⥤ TP1} {RP : GP ⥤ TP}

section Monoidal

variable {TN TM GN GM : Type*} [Category TN] [Category TM] [Category GN] [Category GM]
  [MonoidalCategory TN] [MonoidalCategory TM] [MonoidalCategory GN] [MonoidalCategory GM]
  {t : TN ⥤ TM} {gen : GN ⥤ GM} {jN : TN ⥤ GN} {jM : TM ⥤ GM} {RN : GN ⥤ TN} {RM : GM ⥤ TM}
  [t.OplaxMonoidal] [gen.OplaxMonoidal] [jN.OplaxMonoidal] [jM.OplaxMonoidal]

end Monoidal

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Exchange maps -/

namespace NearbyCyclesModel.Hom

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

variable {Z Z' X₁ X₁' Z₁ Z₁' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P₁ : NearbyCyclesModel Z₁ Z₁'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'}
  {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'} {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'} {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'}

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing

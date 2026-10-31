/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFiniteScalarUnderlying

/-! # Equivariance of the normalized scalar comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

/-- The underlying scalar comparison commutes with the two representation actions.
Source: Stacks 0DV5 (3), blueprint `cor-galois-lisse-representations`, paragraph
"Base change of coefficients". (blueprint: new-w8-galois-scalar-action).

Proof: the scalar-adjunction unit followed by sheafification and α⁻¹ defines a map
of the underlying finite locally constant sheaves of sets. Its stalk commutes with γ(g) by
naturality of this fibre automorphism. The germ formulas for scalarStalk and the two
κ maps in heval identify its stalk with the conjugate of the unit-tensor map through
τ. Therefore the inverse underlying comparison intertwines on pure tensors. These
generate scalar extension by its adjunction; hence it intertwines everywhere. Conjugate
this equality by the invertible comparison to obtain the asserted orientation. -/
theorem galois_finite_scalar_action
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (d : GaloisLisseFiniteData y G)
    (heval : galoisFiniteEvaluationAction y G d)
    (scalarStalk : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S),
      let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R) ⋙
        ModuleCat.ringExtendScalars.{u + 1, u + 1} f ≅
      (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f :
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)) ⋙
        (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} S))
    (scalarStalkGerm : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S),
      let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (a : S)
        (s : F.obj.obj (op U)),
      ((scalarStalk R S f).hom.app F)
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a
          ((pointSmallEtale y).toPresheafFiber U x F.obj s)) =
        (pointSmallEtale y).toPresheafFiber U x
          ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).obj
          ((toSheafify Y.smallEtaleTopology
            (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U)
            (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a s)))
    (B : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S], (R →+* S) →
      (LisseModuleSheafCategory Y R ⥤ LisseModuleSheafCategory Y S))
    (α : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S),
      B R S f ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
        Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f)
    : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S) (F : LisseModuleSheafCategory Y R) (g : G)
      (z : ((d.e S).functor.obj ((B R S f).obj F)).obj.V),
      ((galoisFiniteScalarUnderlying d R S f (B R S f) (α R S f)
        (scalarStalk R S f)).hom.app F)
        (((d.e S).functor.obj ((B R S f).obj F)).obj.ρ g z) =
      (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).map
        (ModuleCat.ofHom (((d.e R).functor.obj F).obj.ρ g))
        (((galoisFiniteScalarUnderlying d R S f (B R S f) (α R S f)
          (scalarStalk R S f)).hom.app F) z) := by
  classical
  intro R S _ _ _ _ f F g z
  let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let p := pointSmallEtale y
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let H := (B R S f).obj F
  let X := ((d.e R).functor.obj F).obj
  let Z := ((d.e S).functor.obj H).obj
  let θ := (galoisFiniteScalarUnderlying d R S f (B R S f) (α R S f)
    (scalarStalk R S f)).app F
  let a := (α R S f).inv.app F
  let j := toSheafify Y.smallEtaleTopology (F.obj.obj ⋙ E)
  obtain ⟨hF, κF, κFgerm, hFρ⟩ := heval R F
  obtain ⟨hH, κH, κHgerm, hHρ⟩ := heval S H
  let δ : F.obj.obj ⟶ H.obj.obj ⋙ ModuleCat.restrictScalars f :=
    Functor.whiskerLeft F.obj.obj adj.unit ≫
      Functor.whiskerRight j (ModuleCat.restrictScalars f) ≫
      Functor.whiskerRight a.hom (ModuleCat.restrictScalars f)
  let ψ : galoisUnderlyingFLC R F.obj hF ⟶ galoisUnderlyingFLC S H.obj hH :=
    ObjectProperty.homMk
      { hom := Functor.whiskerRight δ (CategoryTheory.forget (ModuleCat.{u + 1} R)) }
  have hunitmap {M N : ModuleCat.{u + 1} R} (φ : M ⟶ N) (m : M) :
      E.map φ (adj.unit.app M m) = adj.unit.app N (φ m) := by
    exact (congrArg (fun k ↦ k m) (adj.unit.naturality φ)).symm
  have hτH (w : (p.sheafFiber (A := ModuleCat.{u + 1} S)).obj H.obj) :
      (d.τ S).hom.app H ((d.τ S).inv.app H w) = w :=
    ConcreteCategory.congr_hom ((d.τ S).inv_hom_id_app H) w
  have hi (m : X.V) :
      (d.τ S).hom.app H (θ.inv (adj.unit.app (ModuleCat.of R X.V) m)) =
      p.sheafFiber.map a ((scalarStalk R S f).hom.app F.obj
        (adj.unit.app _ ((d.τ R).hom.app F m))) := by
    change (d.τ S).hom.app H ((d.τ S).inv.app H
      (p.sheafFiber.map a ((scalarStalk R S f).hom.app F.obj
        (E.map ((d.τ R).hom.app F) (adj.unit.app _ m))))) = _
    rw [hunitmap, hτH]
    rfl
  have hq (m : X.V) :
      κH ((d.τ S).hom.app H (θ.inv (adj.unit.app (ModuleCat.of R X.V) m))) =
      (ObjectProperty.ι _ ⋙ p.sheafFiber).map ψ (κF ((d.τ R).hom.app F m)) := by
    rw [hi]
    obtain ⟨U, x, s, hs⟩ := p.toPresheafFiber_jointly_surjective
      (P := F.obj.obj) ((d.τ R).hom.app F m)
    rw [← hs, κFgerm]
    have hσ := scalarStalkGerm R S f F.obj U x 1 s
    simp only [ModuleCat.ringExtensionTmul, one_smul] at hσ
    rw [hσ]
    have hn := p.toPresheafFiber_naturality_apply a.hom U x (j.app (op U)
      (adj.unit.app _ s))
    change p.sheafFiber.map a
        (p.toPresheafFiber U x
          ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F.obj).obj
          (j.app (op U) (adj.unit.app _ s))) =
      p.toPresheafFiber U x H.obj.obj (a.hom.app (op U)
        (j.app (op U) (adj.unit.app _ s))) at hn
    rw [hn, κHgerm]
    exact (p.toPresheafFiber_naturality_apply ψ.hom.hom U x s).symm
  have hqρ (m : X.V) :
      θ.inv (adj.unit.app (ModuleCat.of R X.V) (X.ρ g m)) =
      Z.ρ g (θ.inv (adj.unit.app (ModuleCat.of R X.V) m)) := by
    apply ((d.τ S).app H).toLinearEquiv.injective
    change (d.τ S).hom.app H
        (θ.inv (adj.unit.app (ModuleCat.of R X.V) (X.ρ g m))) =
      (d.τ S).hom.app H (Z.ρ g (θ.inv (adj.unit.app (ModuleCat.of R X.V) m)))
    apply κH.injective
    erw [hq, hFρ, hHρ, hq]
    exact congrArg (fun k ↦ k (κF ((d.τ R).hom.app F m)))
      ((d.γ g).hom.naturality ψ).symm
  let rX : ModuleCat.of R X.V ⟶ ModuleCat.of R X.V := ModuleCat.ofHom (X.ρ g)
  let rZ : ModuleCat.of S Z.V ⟶ ModuleCat.of S Z.V := ModuleCat.ofHom (Z.ρ g)
  have hinv : E.map rX ≫ θ.inv = θ.inv ≫ rZ := by
    apply (adj.homEquiv _ _).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    simp only [Adjunction.homEquiv_unit]
    change θ.inv (E.map rX (adj.unit.app _ m)) =
      Z.ρ g (θ.inv (adj.unit.app _ m))
    rw [hunitmap]
    exact hqρ m
  have hcon := congrArg (fun k ↦ θ.hom ≫ k ≫ θ.hom) hinv
  have hh : θ.hom ≫ E.map rX = rZ ≫ θ.hom := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using hcon
  exact (ConcreteCategory.congr_hom hh z).symm

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteScalarUnderlying
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteScalarGerm

/-! # Composition of the normalized scalar comparisons -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 2000000 in
-- Iterated scalar adjunctions and fibre comparisons require many definitional reductions.
/-- A scalar representation comparison with the specified underlying normalization
satisfies the three-coefficient composite identity. Source: Stacks 0DV5 (3), blueprint
`cor-galois-lisse-representations`, base change of coefficients.
(blueprint: new-w8-galois-scalar-beta-composite).

Proof: conjugate both sides by the fibre normalizations τ and the scalar-stalk maps.
Every stalk element is represented by a section germ, and the adjunction unit generates
scalar extension as an S-module. Consequently it suffices to check the two linear maps
on iterated pure tensors b tensor (a tensor germ(s)). Naturality of τ transports c to
its stalk map. The germ formula for scalarStalk and the section identity hc turn the
left side into (b g(a)) tensor germ(s). Naturality of the scalar adjunction unit and
unit_leftAdjointUniq_hom_app give this same value for ringExtensionComp on the right.
Cancel the invertible comparisons. The normalization hypothesis is essential: an
arbitrary family β may be rescaled and need not satisfy this identity. -/
theorem galois_finite_scalar_beta_composite
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (d : GaloisLisseFiniteData y G)
    (scalarStalk : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S),
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R) ⋙
        ModuleCat.ringExtendScalars.{u + 1, u + 1} f ≅
      (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f :
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)) ⋙
        (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} S))
    (scalarStalkGerm : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S),
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
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
    (c : ∀ (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f :
      R →+* S)
    (g : S →+* T), B R S f ⋙ B S T g ≅ B R T (g.comp f))
    (hc : ∀
    (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f : R →+* S)
    (g : S →+* T), ∀ (F :
    LisseModuleSheafCategory Y R) (U : Y.Etale) (a : S) (b : T) (z : F.obj.obj.obj (op U)), ((α R T
    (g.comp f)).hom.app F).hom.app (op U) (((c R S T f g).hom.app F).hom.hom.app (op U) (((α S T
      g).inv.app ((B
    R S f).obj F)).hom.app (op U) (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1}
    T)).app (((B R S f).obj F).obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} g)).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ b (((α R S f).inv.app F).hom.app (op U)
    (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} S)).app (F.obj.obj ⋙
    ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U) (ModuleCat.ringExtensionTmul.{u + 1, u
    + 1} f _ a z))))))) = ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} T)).app
    (F.obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f))).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) _ (b * g a) z))
    (β : ∀ (R S : Type (u + 1))
    [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S), B R S f ⋙ (d.e S).functor ⋙
    ObjectProperty.ι _ ≅ (d.e R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).mapAction G ⋙ (Rep.repIsoAction S G).inverse)
    (hβ : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S) (F : LisseModuleSheafCategory Y R),
      (forget₂ (Rep.{u + 1} S G) (ModuleCat S)).map ((β R S f).hom.app F) =
        (galoisFiniteScalarUnderlying d R S f
    (B R S f) (α R S f)
          (scalarStalk R S f)).hom.app F) : ∀
    (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f : R →+* S)
    (g : S →+* T), (∀ (F : LisseModuleSheafCategory Y R)
    (z : ((d.e T).functor.obj ((B S T g).obj ((B R S f).obj F))).obj.V), ((β R T (g.comp f)).hom.app
    F).hom (((d.e T).functor.map ((c R S T f g).hom.app F)).hom.hom z) =
      (ModuleCat.ringExtensionComp.{u + 1, u
    + 1} f g).hom.app (ModuleCat.of R ((d.e R).functor.obj F).obj.V)
    ((ModuleCat.ringExtendScalars.{u + 1, u + 1} g).map ((forget₂ (Rep.{u + 1} S G) (ModuleCat.{u +
    1} S)).map ((β R S f).hom.app F)) (((β S T g).hom.app ((B R S f).obj F)).hom z))) := by
  classical
  have hσ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
      (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj (op U)) :=
    scalarStalkGerm R S f F U x 1 s
  simp only [ModuleCat.ringExtensionTmul, one_smul] at hσ
  have hχ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S) :=
    galois_finite_scalar_inverse_germ d f
    (B R S f) (α R S f)
      (scalarStalk R S f) (hσ R S f)
  intro R S T _ _ _ _ _ _ f g F z
  let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} T) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let p := pointSmallEtale y
  let E₂ := ModuleCat.ringExtendScalars.{u + 1, u + 1} g
  let adj₁ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let adj₂ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g
  let adj₃ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (g.comp f)
  let A := (B R S f).obj F
  let H := (B S T g).obj A
  let K := (B R T (g.comp f)).obj F
  let M := ModuleCat.of R ((d.e R).functor.obj F).obj.V
  let θ₁ : ModuleCat.of S ((d.e S).functor.obj A).obj.V ≅
      (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M :=
    (galoisFiniteScalarUnderlying d R S f (B R S f) (α R S f)
      (scalarStalk R S f)).app F
  let θ₂ : ModuleCat.of T ((d.e T).functor.obj H).obj.V ≅
      E₂.obj (ModuleCat.of S ((d.e S).functor.obj A).obj.V) :=
    (galoisFiniteScalarUnderlying d S T g (B S T g) (α S T g)
      (scalarStalk S T g)).app A
  let θ₃ : ModuleCat.of T ((d.e T).functor.obj K).obj.V ≅
      (ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f)).obj M :=
    (galoisFiniteScalarUnderlying d R T (g.comp f) (B R T (g.comp f))
      (α R T (g.comp f)) (scalarStalk R T (g.comp f))).app F
  let a := ModuleCat.ringExtensionComp.{u + 1, u + 1} f g
  let q := ((d.e T).functor ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} T G) (ModuleCat T)).map ((c R S T f g).hom.app F)
  have hmap {L N : ModuleCat.{u + 1} S} (φ : L ⟶ N) (m : L) :
      E₂.map φ (adj₂.unit.app L m) = adj₂.unit.app N (φ m) :=
    (congrArg (fun k ↦ k m) (adj₂.unit.naturality φ)).symm
  have ha (m : M) : a.hom.app M
      (adj₂.unit.app _ (adj₁.unit.app M m)) = adj₃.unit.app M m := by
    exact congrArg (fun k ↦ k m)
      ((adj₁.comp adj₂).unit_leftAdjointUniq_hom_app
        (adj₃.ofNatIsoRight (ModuleCat.restrictScalarsComp f g)) M)
  have hτ (v : ((d.e T).functor.obj H).obj.V) :
      (d.τ T).hom.app K (q v) =
        p.sheafFiber.map ((c R S T f g).hom.app F).hom ((d.τ T).hom.app H v) :=
    congrArg (fun k ↦ k v) ((d.τ T).hom.naturality ((c R S T f g).hom.app F))
  have hτcancel (L : LisseModuleSheafCategory Y T)
      (v : (p.sheafFiber (A := ModuleCat.{u + 1} T)).obj L.obj) :
      (d.τ T).hom.app L ((d.τ T).inv.app L v) = v :=
    ConcreteCategory.congr_hom ((d.τ T).inv_hom_id_app L) v
  have hgerm {L N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} T)}
      (φ : L ⟶ N) (U : Y.Etale) (x : p.fiber.obj U) (s : L.obj.obj (op U)) :
      p.sheafFiber.map φ (p.toPresheafFiber U x L.obj s) =
        p.toPresheafFiber U x N.obj (φ.hom.app (op U) s) :=
    p.toPresheafFiber_naturality_apply φ.hom U x s
  have hcompare : E₂.map θ₁.inv ≫ θ₂.inv ≫ q = a.hom.app M ≫ θ₃.inv := by
    apply (adj₂.homEquiv _ _).injective
    apply (adj₁.homEquiv _ _).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    simp only [Adjunction.homEquiv_unit, ModuleCat.comp_apply]
    change q (θ₂.inv (E₂.map θ₁.inv (adj₂.unit.app _ (adj₁.unit.app M m)))) =
      θ₃.inv (a.hom.app M (adj₂.unit.app _ (adj₁.unit.app M m)))
    rw [hmap, ha]
    obtain ⟨U, x, s, hs⟩ := p.toPresheafFiber_jointly_surjective
      (P := F.obj.obj) ((d.τ R).hom.app F m)
    have hm : m = (d.τ R).inv.app F (p.toPresheafFiber U x F.obj.obj s) := by
      rw [hs]
      exact (ConcreteCategory.congr_hom ((d.τ R).hom_inv_id_app F) m).symm
    rw [hm]
    erw [hχ R S f, hχ S T g, hχ R T (g.comp f)]
    apply ((d.τ T).app K).toLinearEquiv.injective
    simp only [Iso.toLinearEquiv_apply]
    apply (p.sheafFiber.mapIso ((α R T (g.comp f)).app F)).toLinearEquiv.injective
    simp only [Iso.toLinearEquiv_apply]
    erw [hτ, hτcancel, hτcancel, hgerm, hgerm, hgerm]
    have hsec := hc R S T f g F U 1 1 s
    simp only [ModuleCat.ringExtensionTmul, one_smul, map_one, mul_one] at hsec
    have hinv := congrArg (fun k ↦ k.hom.app (op U)
      ((toSheafify Y.smallEtaleTopology
        (F.obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f))).app
        (op U) (adj₃.unit.app _ s))) ((α R T (g.comp f)).inv_hom_id_app F)
    change ((α R T (g.comp f)).hom.app F).hom.app (op U)
      (((α R T (g.comp f)).inv.app F).hom.app (op U)
        ((toSheafify Y.smallEtaleTopology
          (F.obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f))).app
          (op U) (adj₃.unit.app _ s))) = _ at hinv
    exact congrArg (fun w ↦ p.toPresheafFiber U x
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
        (g.comp f)).obj F.obj).obj w) (hsec.trans hinv.symm)
  let Ψ := E₂.map θ₁.inv ≫ θ₂.inv
  have hh : q ≫ θ₃.hom = θ₂.hom ≫ E₂.map θ₁.hom ≫ a.hom.app M := by
    apply (cancel_epi Ψ).1
    calc
      Ψ ≫ (q ≫ θ₃.hom) = a.hom.app M := by
        change (E₂.map θ₁.inv ≫ θ₂.inv ≫ q) ≫ θ₃.hom = _
        rw [hcompare]
        simp
      _ = Ψ ≫ (θ₂.hom ≫ E₂.map θ₁.hom ≫ a.hom.app M) := by
        dsimp only [Ψ]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← E₂.map_comp_assoc, Iso.inv_hom_id, E₂.map_id, Category.id_comp]
  have hb₁ : (forget₂ (Rep.{u + 1} S G) (ModuleCat S)).map
      ((β R S f).hom.app F) = θ₁.hom := hβ R S f F
  have hb₂ : (forget₂ (Rep.{u + 1} T G) (ModuleCat T)).map
      ((β S T g).hom.app A) = θ₂.hom := hβ S T g A
  have hb₃ : (forget₂ (Rep.{u + 1} T G) (ModuleCat T)).map
      ((β R T (g.comp f)).hom.app F) = θ₃.hom := hβ R T (g.comp f) F
  have hv := ConcreteCategory.congr_hom hh z
  change θ₃.hom (q z) = a.hom.app M (E₂.map θ₁.hom (θ₂.hom z)) at hv
  erw [← hb₃, ← hb₂, ← hb₁] at hv
  exact hv

end AlgebraicGeometry.Scheme

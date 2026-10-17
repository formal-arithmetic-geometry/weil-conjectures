/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseUniversalCover

/-!
# Compatibility of the monodromy of lisse sheaves with pullback

The monodromy of lisse `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.LisseMonodromy`) records the
compatibility of `cor-galois-lisse-representations` with pullback only along endomorphisms
(`AlgebraicGeometry.ProEtale.LisseMonodromy.mono_upperStar`). This file states the compatibility
with base change along an arbitrary morphism `f : X ⟶ Y` of connected regular Noetherian
schemes: a path `τ : F_y ≅ F_z` of `X` and the induced path `F_{y ≫ f} ≅ F_{z ≫ f}` of `Y` act
compatibly on `G_{y ≫ f} = (f^* G)_y` for a lisse sheaf `G` on `Y`.

## Implementation notes

The stalk of a lisse sheaf `G` at `y` is identified with `Γ(Ỹ_y, p_y^* G)` and paths act through
the transports of the universal covers. For a morphism `φ : X̃_x ⟶ Ỹ_{x ≫ f}` of universal covers
over `f`, the restriction `Γ(Ỹ_{x ≫ f}, p^* G) ⟶ Γ(X̃_x, p^* f^* G)` along `φ`
(`AlgebraicGeometry.Scheme.UniversalCovers.pullbackRes`) intertwines the restrictions to the base
points and the transports, which gives the compatibility
(`AlgebraicGeometry.Scheme.UniversalCovers.monoIso_pullback`).

## Main statements

- `AlgebraicGeometry.ProEtale.exists_lisseMonodromy_pullback`: the base change compatibility
  of `cor-galois-lisse-representations`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.UniversalCovers

open ProEtale FiniteEtale

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  (UX : Scheme.UniversalCovers X Ω) (UY : Scheme.UniversalCovers Y Ω) {f : X ⟶ Y}

/-- The comparison `Γ(Ỹ_{x ≫ f}, p_{x ≫ f}^* F) ⟶ Γ(X̃_x, p_x^* f^* F)` along a morphism
`φ : X̃_x ⟶ Ỹ_{x ≫ f}` of universal covers over `f : X ⟶ Y`. -/
noncomputable def pullbackRes {x : Spec (.of (AlgebraicClosure Ω)) ⟶ X}
    (φ : UX.cover x ⟶ UY.cover (x ≫ f)) (hφ : φ ≫ UY.proj (x ≫ f) = UX.proj x ≫ f)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).obj ((UY.proj (x ≫ f))^*[WeilCoefficients.{u} l].obj F) ⟶
      (Sheaf.Γ _ _).obj ((UX.proj x)^*[WeilCoefficients.{u} l].obj ((f)^*[_].obj F)) :=
  globalSectionsTransport _ hφ (𝟙 _)

/-- The restriction to the base point over `x ≫ f`, followed by
`Γ(Spec Ω̄, (x ≫ f)^* F) ≅ Γ(Spec Ω̄, x^* f^* F)`, is the comparison along a morphism
`X̃_x ⟶ Ỹ_{x ≫ f}` of universal covers preserving base points, followed by the restriction to the
base point over `x`. -/
lemma ptRes_app_comp_upperStarStalkIso_eq_pullbackRes {x : Spec (.of (AlgebraicClosure Ω)) ⟶ X}
    (φ : UX.cover x ⟶ UY.cover (x ≫ f)) (hφ : φ ≫ UY.proj (x ≫ f) = UX.proj x ≫ f)
    (hpt : UX.pt x ≫ φ = UY.pt (x ≫ f))
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (UY.ptRes l (x ≫ f)).app F ≫ (upperStarStalkIso l f x F).hom =
      UX.pullbackRes l UY φ hφ F ≫ (UX.ptRes l x).app ((f)^*[_].obj F) := by
  have h₀ : UY.pt (x ≫ f) ≫ UY.proj (x ≫ f) = x ≫ f := UY.pt_proj _
  rw [ptRes_app, ptRes_app, resOver_app_eq_transport, resOver_app_eq_transport, pullbackRes]
  refine Eq.trans ?_ (globalSectionsTransport_comp_eq _ _ _ h₀ hpt
    (Category.id_comp f) _ _ (𝟙 _) ?_).symm
  · rw [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, globalSectionsTransport,
      globalSectionsTransport, Category.assoc, ← Functor.map_comp]
    refine congrArg (_ ≫ ·) (congrArg (Sheaf.Γ _ _).map ?_)
    rw [upperStarCompIso_hom_app, upperStarCompIso_hom_app]
    simp only [CategoryTheory.Functor.map_id, Category.assoc]
    rw [reassoc_of% upperStarComp_id_right_hom_app,
      reassoc_of% (upperStarCongr_hom_app_comp_hom_app _ _ _ h₀ F)]
    exact (Category.comp_id _).symm
  · simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    exact upperStarComp_id_left_hom_app _ f F

/-- Comparisons along morphisms of universal covers over `f` which are compatible with the
transports intertwine the transports along a path and along the induced path of `f`. -/
lemma transportRes_hom_app_comp_pullbackRes {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ X}
    (τ : fiber y ≅ fiber z) (φy : UX.cover y ⟶ UY.cover (y ≫ f))
    (φz : UX.cover z ⟶ UY.cover (z ≫ f)) (hφy : φy ≫ UY.proj (y ≫ f) = UX.proj y ≫ f)
    (hφz : φz ≫ UY.proj (z ≫ f) = UX.proj z ≫ f)
    (htr : φy ≫ (UY.transport (pullbackPathIso f τ)).hom = (UX.transport τ).hom ≫ φz)
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (UY.transportRes l (pullbackPathIso f τ)).hom.app F ≫ UX.pullbackRes l UY φz hφz F =
      UX.pullbackRes l UY φy hφy F ≫ (UX.transportRes l τ).hom.app ((f)^*[_].obj F) := by
  have hτ : (UX.transport τ).inv ≫ φy = φz ≫ (UY.transport (pullbackPathIso f τ)).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, htr, Iso.inv_hom_id_assoc]
  have h'' : (φz ≫ (UY.transport (pullbackPathIso f τ)).inv) ≫ UY.proj (y ≫ f) =
      UX.proj z ≫ f := by
    rw [Category.assoc, UY.transport_inv_proj, hφz]
  rw [transportRes_hom_app, transportRes_hom_app, resOver_app_eq_transport,
    resOver_app_eq_transport, pullbackRes, pullbackRes]
  refine (globalSectionsTransport_comp_eq _ _ _ h'' rfl (Category.comp_id f) _ _ (𝟙 _) ?_).trans
    (globalSectionsTransport_comp_eq _ _ _ h'' hτ (Category.id_comp f) _ _ (𝟙 _) ?_).symm
  · simp only [Category.comp_id]
    exact upperStarComp_id_right_hom_app _ f F
  · simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    exact upperStarComp_id_left_hom_app _ f F

variable {l UX UY}

/-- **Compatibility of the transport with pullback along a morphism `f : X ⟶ Y`**, for
monodromies from universal covers related by morphisms `X̃_x ⟶ Ỹ_{x ≫ f}` over `f` which preserve
base points and are compatible with the transports. -/
lemma monoIso_pullback
    (hUX : ∀ (x : Spec (.of (AlgebraicClosure Ω)) ⟶ X) (G : LisseSheaf l X), ∃ n : ℕ,
      Nonempty ((UX.proj x)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (UX.cover x)))
    (hUY : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
      Nonempty ((UY.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (UY.cover y)))
    (φ : ∀ x : Spec (.of (AlgebraicClosure Ω)) ⟶ X, UX.cover x ⟶ UY.cover (x ≫ f))
    (hφ : ∀ x, φ x ≫ UY.proj (x ≫ f) = UX.proj x ≫ f)
    (hpt : ∀ x, UX.pt x ≫ φ x = UY.pt (x ≫ f))
    {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z)
    (htr : φ y ≫ (UY.transport (pullbackPathIso f τ)).hom = (UX.transport τ).hom ≫ φ z)
    (G : LisseSheaf l Y) :
    (monoIso hUY (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
      (upperStarStalkIso l f y G.obj.X).hom ≫ (monoIso hUX τ).hom.app (G.upperStar l f) := by
  have := isIso_ptRes_app hUY (y ≫ f) G
  rw [← cancel_epi ((UY.ptRes l (y ≫ f)).app G.obj.X),
    reassoc_of% ptRes_app_comp_monoIso_hom_app,
    ptRes_app_comp_upperStarStalkIso_eq_pullbackRes l UX UY (φ z) (hφ z) (hpt z),
    reassoc_of% ptRes_app_comp_upperStarStalkIso_eq_pullbackRes l UX UY (φ y) (hφ y) (hpt y),
    reassoc_of% transportRes_hom_app_comp_pullbackRes l UX UY τ (φ y) (φ z) (hφ y) (hφ z) htr]
  exact congrArg (UX.pullbackRes l UY (φ y) (hφ y) G.obj.X ≫ ·)
    (ptRes_app_comp_monoIso_hom_app hUX τ (G.upperStar l f)).symm

end AlgebraicGeometry.Scheme.UniversalCovers

namespace AlgebraicGeometry.ProEtale

open Scheme.FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (Ω : Type u) [Field Ω]
/-- **Lisse `ℚ̄_ℓ`-sheaves and continuous representations: compatibility with base change**
(blueprint: `cor-galois-lisse-representations`, the compatibility with base change, and
`def-wf-fundamental-representation`). On a connected regular Noetherian scheme `Y` there
is a monodromy of lisse sheaves which is an equivalence at every base point
(`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`) and which is compatible with pullback along
every morphism `f : X ⟶ Y` from a connected regular Noetherian scheme: for some
monodromy on `X`, again an equivalence at every base point, the transport along the path
`F_{y ≫ f} ≅ F_{z ≫ f}` induced by a path `τ : F_y ≅ F_z` of `X` acts on
`Γ(Spec Ω̄, (y ≫ f)^* G) = Γ(Spec Ω̄, y^* f^* G)` as the transport along `τ` acts on the stalks of
`f^* G`. This extends `AlgebraicGeometry.ProEtale.LisseMonodromy.mono_upperStar`, which records
the case of an endomorphism `f` of `Y`.

Both monodromies are those of the universal covers
(`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy`, for
`AlgebraicGeometry.Scheme.universalCovers`), and the
compatibility comes from the morphisms `X̃_x ⟶ Ỹ_{x ≫ f}` of universal covers over `f`
(`AlgebraicGeometry.Scheme.exists_universalCovers_map`), as in
`AlgebraicGeometry.Scheme.UniversalCovers.monoIso_pullback`. -/
theorem exists_lisseMonodromy_pullback [IsLocallyNoetherian Y] [IsRegular Y] [ConnectedSpace Y]
    [CompactSpace Y] :
    ∃ M : LisseMonodromy l Y Ω, (∀ t, M.IsEquivalenceAt t) ∧
      ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsRegular X] [ConnectedSpace X]
        [CompactSpace X] (f : X ⟶ Y),
        ∃ M' : LisseMonodromy l X Ω, (∀ t, M'.IsEquivalenceAt t) ∧
          ∀ {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z)
            (G : LisseSheaf l Y),
            (M.mono (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
              (upperStarStalkIso l f y G.obj.X).hom ≫ (M'.mono τ).hom.app (G.upperStar l f) := by
  have hUY (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :=
    IsAdicLisseSheaf.exists_iso_upperStar_universalCover (Scheme.universalCovers Y Ω) y G.property
  refine ⟨_, (Scheme.universalCovers Y Ω).lisseMonodromy_isEquivalenceAt hUY,
    fun X _ _ _ _ f ↦ ?_⟩
  have hUX (x : Spec (.of (AlgebraicClosure Ω)) ⟶ X) (G : LisseSheaf l X) :=
    IsAdicLisseSheaf.exists_iso_upperStar_universalCover (Scheme.universalCovers X Ω) x G.property
  obtain ⟨φ, hφ, hpt, htr⟩ := Scheme.exists_universalCovers_map (Ω := Ω) f
  exact ⟨_, (Scheme.universalCovers X Ω).lisseMonodromy_isEquivalenceAt hUX,
    fun τ G ↦ Scheme.UniversalCovers.monoIso_pullback hUX hUY φ hφ hpt τ (htr τ) G⟩

end AlgebraicGeometry.ProEtale

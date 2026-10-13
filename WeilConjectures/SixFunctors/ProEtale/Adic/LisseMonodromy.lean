/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.RepresentationTheory.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.SixFunctors.ProEtale.Adic.StalkEvaluation
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Restriction

/-!
# The monodromy of lisse `ℓ`-adic sheaves

Let `Y` be a connected scheme, `Ω` a separably closed field and `ℚ̄_ℓ = PadicAlgCl ℓ`. For a
geometric point `y : Spec Ω ⟶ Y` write `F_y` both for the fibre functor on finite étale
`Y`-schemes and for the stalk functor `G ↦ Γ(Spec Ω, y^* G)` on lisse `ℓ`-adic sheaves on
`Y_proét`. By `cor-galois-lisse-representations` (for `Λ = ℚ̄_ℓ`), the stalk functor at a
geometric point `t` identifies lisse `ℚ̄_ℓ`-sheaves with the continuous finite-dimensional
`ℚ̄_ℓ`-representations of `π₁(Y, t) = Aut F_t`, as an exact tensor equivalence compatible with
base change; and `def-wf-fundamental-representation` transports stalks along paths, i.e.
isomorphisms of fibre functors `F_y ≅ F_z`.

This file packages these facts as a *monodromy* of lisse sheaves
(`AlgebraicGeometry.ProEtale.LisseMonodromy`): for every path `τ : F_y ≅ F_z` a natural
isomorphism `mono τ` from the stalk functor at `y` to the stalk functor at `z`, such that

* `mono` is functorial in the path (`mono_refl`, `mono_trans`);
* reparametrising a geometric point by an automorphism `a` of `Spec Ω` is transported by the
  canonical identification `Γ(Spec Ω, (a ≫ y)^* G) ≅ Γ(Spec Ω, a^* y^* G) ≅ Γ(Spec Ω, y^* G)`
  (`mono_reparam`);
* it is compatible with pullback along an endomorphism `f` of `Y`: the path `F_{y ≫ f} ≅ F_{z ≫ f}`
  induced by `τ` acts on `Γ(Spec Ω, (y ≫ f)^* G) = Γ(Spec Ω, y^* f^* G)` as `τ` acts on the
  stalks of `f^* G` (`mono_upperStar`, the compatibility of `cor-galois-lisse-representations`
  with base change);
* global sections restrict to flat sections (`mono_globalSections`);
* it preserves the evaluation pairing `(G^∨)_y × G_y → ℚ̄_ℓ` (`mono_evaluationPairing`, the
  tensor compatibility of `cor-galois-lisse-representations` applied to `G^∨ ⊗ G → ℚ̄_ℓ`).

At a base point `t`, the automorphisms of `F_t` act on the stalk `G_t`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.rep`), and
`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt` records that this is a fully
faithful and essentially surjective functor to continuous finite-dimensional representations.

The existence of a monodromy which is an equivalence at every base point, for a connected
regular locally Noetherian `Y`, is `AlgebraicGeometry.ProEtale.exists_lisseMonodromy`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme.FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The category of lisse `ℓ`-adic sheaves on `Y_proét`. -/
abbrev LisseSheaf : Type (u + 2) :=
  (adicLisseSheaf l Y).FullSubcategory

variable {Y Ω}

/-- The stalk functor `G ↦ Γ(Spec Ω, y^* G)` at a geometric point `y`, on lisse sheaves. -/
noncomputable abbrev lisseStalk (y : Spec (.of Ω) ⟶ Y) : LisseSheaf l Y ⥤ WeilCoefficients.{u} l :=
  ObjectProperty.ι _ ⋙ AdicSheaf.forget Y ⋙ stalkFunctor l y

/-- The identification `Γ(Spec Ω, (a ≫ y)^* G) ≅ Γ(Spec Ω, a^* y^* G) ≅ Γ(Spec Ω, y^* G)` of the
stalks at a geometric point `y` and at its reparametrisation by an automorphism `a` of
`Spec Ω`. -/
noncomputable def reparamStalkIso (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y)
    (G : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (stalkFunctor l (a.hom ≫ y)).obj G ≅ (stalkFunctor l y).obj G :=
  (Sheaf.Γ _ _).mapIso ((upperStarComp _ a.hom y).app G) ≪≫
    (globalSectionsUpperStarIso _ a).app _

/-- The identification `Γ(Spec Ω, (y ≫ f)^* G) ≅ Γ(Spec Ω, y^* f^* G)` of the stalk of `G` at
`y ≫ f` with the stalk of `f^* G` at `y`. -/
noncomputable def upperStarStalkIso {X : Scheme.{u}} (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X)
    (G : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (stalkFunctor l (y ≫ f)).obj G ≅ (stalkFunctor l y).obj ((f)^*[_].obj G) :=
  (Sheaf.Γ _ _).mapIso ((upperStarComp _ y f).app G)

omit [IsSepClosed Ω] in
/-- The identification `Γ(Spec Ω, (y ≫ f)^* G) ≅ Γ(Spec Ω, y^* f^* G)` is natural in `G`. -/
lemma upperStarStalkIso_hom_naturality {X : Scheme.{u}} (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X)
    {G H : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)} (φ : G ⟶ H) :
    (stalkFunctor l (y ≫ f)).map φ ≫ (upperStarStalkIso l f y H).hom =
      (upperStarStalkIso l f y G).hom ≫ (stalkFunctor l y).map ((f)^*[_].map φ) := by
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map,
    ← Functor.map_comp, (upperStarComp _ y f).hom.naturality]

/-- The pullback of a lisse sheaf, as a lisse sheaf. -/
noncomputable abbrev LisseSheaf.upperStar {X : Scheme.{u}} (f : X ⟶ Y) (G : LisseSheaf l Y) :
    LisseSheaf l X :=
  ⟨(f)^*ᵃ[l].obj G.obj, G.property.upperStar f⟩

/-- The constant sheaf `ℚ̄_ℓ`, as a lisse sheaf. -/
noncomputable abbrev LisseSheaf.unit : LisseSheaf l Y :=
  ⟨AdicSheaf.unit l Y, isAdicLisseSheaf_adicConstantSheaf Y⟩

variable (Y Ω)

/-- **The monodromy of lisse sheaves** on `Y`: the transport of stalks of lisse `ℓ`-adic sheaves
along paths between geometric points with values in `Ω`, in the sense of
`def-wf-fundamental-representation` ("the usual transport of the stalk"), with the
compatibilities of `cor-galois-lisse-representations` (functoriality, base change, tensor
products), see the module docstring. -/
structure LisseMonodromy where
  /-- The transport `F_y ≅ F_z` of stalks of lisse sheaves along a path `τ : F_y ≅ F_z`. -/
  mono {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) : lisseStalk l y ≅ lisseStalk l z
  mono_refl (y : Spec (.of Ω) ⟶ Y) : mono (Iso.refl (fiber y)) = Iso.refl _
  mono_trans {y z w : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (τ' : fiber z ≅ fiber w) :
    mono (τ ≪≫ τ') = mono τ ≪≫ mono τ'
  /-- The reparametrisation path acts by the canonical identification of the stalks. -/
  mono_reparam (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y) (G : LisseSheaf l Y) :
    (mono (fiberReparamIso a y)).hom.app G = (reparamStalkIso l a y G.obj.X).hom
  /-- Compatibility with pullback along an endomorphism `f` of `Y`. -/
  mono_upperStar (f : Y ⟶ Y) {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z)
    (G : LisseSheaf l Y) :
    (mono (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
      (upperStarStalkIso l f y G.obj.X).hom ≫ (mono τ).hom.app (G.upperStar l f)
  /-- Global sections restrict to sections of the stalks which are invariant under transport. -/
  mono_globalSections {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y) :
    (globalSectionsToUpperStar _ y).app G.obj.X ≫ (mono τ).hom.app G =
      (globalSectionsToUpperStar _ z).app G.obj.X
  /-- Transport preserves the evaluation pairing `(G^∨)_y × G_y → ℚ̄_ℓ` of the dual. -/
  mono_evaluationPairing {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y)
    (hG : IsAdicLisseSheaf ((AdicSheaf.ihom G.obj).obj (AdicSheaf.unit l Y)))
    (d : (stalkFunctor l y).obj ((AdicSheaf.ihom G.obj).obj (AdicSheaf.unit l Y)).X)
    (v : (stalkFunctor l y).obj G.obj.X) :
    Mod.evaluationPairing (stalkFunctor l z) G.obj (AdicSheaf.unit l Y)
        (((mono τ).hom.app ⟨_, hG⟩).hom d) (((mono τ).hom.app G).hom v) =
      ((mono τ).hom.app (LisseSheaf.unit l)).hom
        (Mod.evaluationPairing (stalkFunctor l y) G.obj (AdicSheaf.unit l Y) d v)

namespace LisseMonodromy

variable {l Y Ω} (M : LisseMonodromy l Y Ω)

/-- The stalk `G_t` of a lisse sheaf at a geometric point, as a `ℚ̄_ℓ`-vector space. -/
noncomputable abbrev StalkSpace (t : Spec (.of Ω) ⟶ Y) (G : LisseSheaf l Y) :
    ModuleCat.{u + 1} (PadicAlgCl l) :=
  (WeilCoefficients.toModuleCat l).obj ((lisseStalk l t).obj G)

/-- The `ℚ̄_ℓ`-linear transport `G_y → G_z` along a path. -/
noncomputable def monoLinear {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z)
    (G : LisseSheaf l Y) : StalkSpace y G →ₗ[PadicAlgCl l] StalkSpace z G :=
  ((WeilCoefficients.toModuleCat l).map ((M.mono τ).hom.app G)).hom

lemma monoLinear_refl (y : Spec (.of Ω) ⟶ Y) (G : LisseSheaf l Y) (v : StalkSpace y G) :
    M.monoLinear (Iso.refl (fiber y)) G v = v := by
  simp [monoLinear, M.mono_refl]

lemma monoLinear_trans {y z w : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) (G : LisseSheaf l Y) (v : StalkSpace y G) :
    M.monoLinear (τ ≪≫ τ') G v = M.monoLinear τ' G (M.monoLinear τ G v) := by
  simp [monoLinear, M.mono_trans]
  rfl

/-- The monodromy representation of `π₁(Y, t) = Aut F_t` on the stalk `G_t` of a lisse sheaf:
an automorphism `g` of the fibre functor acts by transport along the path `g`. -/
noncomputable def rep (t : Spec (.of Ω) ⟶ Y) (G : LisseSheaf l Y) :
    Representation (PadicAlgCl l) (Aut (fiber t)) (StalkSpace t G) where
  toFun g := M.monoLinear g G
  map_one' := LinearMap.ext fun v ↦ M.monoLinear_refl t G v
  map_mul' g h := LinearMap.ext fun v ↦ by
    rw [Aut.Aut_mul_def, M.monoLinear_trans]
    rfl

lemma rep_apply (t : Spec (.of Ω) ⟶ Y) (G : LisseSheaf l Y) (g : Aut (fiber t))
    (v : StalkSpace t G) : M.rep t G g v = M.monoLinear g G v :=
  rfl

/-- The monodromy at the base point `t` is an equivalence onto continuous finite-dimensional
representations (`cor-galois-lisse-representations` for `Λ = ℚ̄_ℓ`): the representations
`AlgebraicGeometry.ProEtale.LisseMonodromy.rep` are continuous, the stalk functor at `t` is
faithful and full onto `π₁(Y, t)`-equivariant maps, and every continuous finite-dimensional
representation of `π₁(Y, t)` is the monodromy representation of a lisse sheaf. -/
structure IsEquivalenceAt (t : Spec (.of Ω) ⟶ Y) : Prop where
  continuous_rep (G : LisseSheaf l Y) (φ : Module.Dual (PadicAlgCl l) (StalkSpace t G))
    (v : StalkSpace t G) : Continuous fun g : Aut (fiber t) ↦ φ (M.rep t G g v)
  faithful {G H : LisseSheaf l Y} (f g : G ⟶ H)
    (h : (lisseStalk l t).map f = (lisseStalk l t).map g) : f = g
  full {G H : LisseSheaf l Y} (φ : StalkSpace t G →ₗ[PadicAlgCl l] StalkSpace t H)
    (hφ : ∀ g v, φ (M.rep t G g v) = M.rep t H g (φ v)) :
    ∃ f : G ⟶ H, ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom = φ
  essSurj (V : Type (u + 1)) [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) (Aut (fiber t)) V)
    (hρ : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ (G : LisseSheaf l Y) (e : StalkSpace t G ≃ₗ[PadicAlgCl l] V),
      ∀ g v, e (M.rep t G g v) = ρ g (e v)

/-- The stalk map of a morphism of lisse sheaves intertwines the monodromy representations. -/
lemma rep_naturality (t : Spec (.of Ω) ⟶ Y) {G H : LisseSheaf l Y} (f : G ⟶ H)
    (g : Aut (fiber t)) (v : StalkSpace t G) :
    ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom (M.rep t G g v) =
      M.rep t H g (((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom v) := by
  have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    ((M.mono g).hom.naturality f)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

variable {M} in
/-- A morphism of lisse sheaves whose stalk at a base point is bijective is an isomorphism, if
the monodromy at that base point is an equivalence. -/
lemma IsEquivalenceAt.isIso_of_bijective {t : Spec (.of Ω) ⟶ Y} (hM : M.IsEquivalenceAt t)
    {G H : LisseSheaf l Y} (f : G ⟶ H)
    (hf : Function.Bijective ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom) :
    IsIso f := by
  let e := LinearEquiv.ofBijective _ hf
  obtain ⟨f', hf'⟩ := hM.full e.symm.toLinearMap fun g v ↦ by
    apply e.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    change _ = ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom _
    rw [M.rep_naturality]
    exact congrArg _ (e.apply_symm_apply v).symm
  have hcomp : ∀ (a : G ⟶ H) (b : H ⟶ G) (x : StalkSpace t G),
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (a ≫ b))).hom x =
        ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map b)).hom
          (((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map a)).hom x) := fun a b x ↦ by
    rw [Functor.map_comp, Functor.map_comp]
    rfl
  refine ⟨f', hM.faithful _ _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)),
    hM.faithful _ _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))⟩
  · change ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (f ≫ f'))).hom x =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (𝟙 G))).hom x
    rw [hcomp, hf', CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact e.symm_apply_apply x
  · change ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (f' ≫ f))).hom x =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map (𝟙 H))).hom x
    rw [CategoryTheory.Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      hf', CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact e.apply_symm_apply x

end LisseMonodromy

/-- **Lisse `ℚ̄_ℓ`-sheaves and continuous representations** (blueprint:
`cor-galois-lisse-representations`, the case `Λ = ℚ̄_ℓ`). On a connected regular locally
Noetherian scheme `Y` (hence geometrically unibranch), the stalks of lisse `ℓ`-adic sheaves carry
a monodromy along paths of fibre functors, compatible with reparametrisation, pullback, global
sections and duals, which at every base point `t` identifies lisse sheaves with continuous
finite-dimensional `ℚ̄_ℓ`-representations of `π₁(Y, t)`.

The blueprint deduces the case `Λ = ℚ̄_ℓ` from finite coefficient rings `𝒪_E / 𝔪ⁿ` by passing to
adic limits, inverting `ϖ_E` and taking the colimit over the finite extensions `E ⊆ ℚ̄_ℓ`. In the
Bhatt–Scholze model of lisse sheaves used here (pro-étale locally free `ℚ̄_ℓ,Y`-modules) this
needs in addition the comparison with adic systems: lisse `𝒪_E`-lattices, whose reductions are
finite locally constant étale sheaves. -/
theorem exists_lisseMonodromy [IsLocallyNoetherian Y] [IsRegular Y] [ConnectedSpace Y] :
    ∃ M : LisseMonodromy l Y Ω, ∀ t, M.IsEquivalenceAt t := by
  sorry

end AlgebraicGeometry.ProEtale

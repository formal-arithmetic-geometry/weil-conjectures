/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.GenericPoint
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.MonoFactorization
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.MonoUnitComp
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.PointSplitting
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# A finite pushforward detecting the stalk at a point

Let `C` be a constructible sheaf of `Λ`-modules on a quasi-compact quasi-separated scheme `X`,
`Λ` noetherian, and `x ∈ X`. There is a finite morphism `h : V ⟶ X` and a finitely generated
`Λ`-module `M` with a map `C ⟶ h_* M` injective on the stalk at a geometric point over `x`
(`AlgebraicGeometry.Etale.exists_mono_sheafFiber_lowerStar`). This is Steps 1 to 5 of the proof
of Stacks 09Z6 in the blueprint (`lem-weil-pbc-constructible-finite-pushforward-noetherian`):

1. `C` is constant with value `M` over a finite (separable) extension `K` of `κ(x)`;
2. the normalization `ν : Y ⟶ X` of the closure of `x` in `K` is integral, `Y` is a normal
   integral scheme with function field `K`, and by Stacks 09Z5 the constant sheaf `M_Y` is the
   pushforward of `M_K`, so the identification `C|_K ≅ M_K` gives a map `C ⟶ ν_* M_Y`;
3. its stalk at a geometric point over `x` is injective;
4. `ν` is a cofiltered limit of finite morphisms, through one of which the map factors since `C`
   is finitely presented (`AlgebraicGeometry.Etale.exists_comp_constantSheafPullbackMap_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing Topology

namespace AlgebraicGeometry

open Scheme

/-- A residue map out of a stalk which is a field is an isomorphism. -/
lemma Scheme.isIso_residue_of_isField {X : Scheme.{u}} (x : X)
    (h : IsField (X.presheaf.stalk x)) : IsIso (X.residue x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, X.residue_surjective x⟩
  let := h.toField
  exact (X.residue x).hom.injective

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Stacks 09Z5 for a generic point with trivial residue field extension.** Let `Y` be an
integral scheme with integrally closed local rings and `g : Spec K ⟶ Y` a morphism onto the
generic point inducing an isomorphism of residue fields. Then the unit `M_Y ⟶ g_* g^* M_Y` is an
isomorphism. -/
theorem isIso_unit_constantSheaf_of_isIso_residueFieldMap {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ Y) (hg : g (closedPoint K) = genericPoint Y)
    [IsIso (g.residueFieldMap (closedPoint K))] (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have h₁ : IsIso (Y.residue (g (closedPoint K))) :=
    isIso_residue_of_isField _ (by rw [hg]; exact Field.toIsField Y.functionField)
  have h₂ : IsIso ((Spec (.of K)).residue (closedPoint K)) :=
    isIso_residue_of_isField _ (MulEquiv.isField (Field.toIsField K)
      (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv)
  have h₃ : IsIso (g.stalkMap (closedPoint K) ≫ (Spec (.of K)).residue (closedPoint K)) := by
    rw [← Scheme.residue_residueFieldMap]
    infer_instance
  have : IsIso (g.stalkMap (closedPoint K)) :=
    IsIso.of_isIso_comp_right _ ((Spec (.of K)).residue (closedPoint K))
  have : IsIso (Scheme.stalkClosedPointTo g) := by
    unfold Scheme.stalkClosedPointTo
    infer_instance
  have hgen : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Y.fromSpecStalk (g (closedPoint K)))).unit.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
    rw [hg]
    exact isIso_unit_constantSheaf_fromSpecStalk_genericPoint Y hY M
  have := isIso_unit_app_comp (ModuleCat.{u + 1} Λ) (Spec.map (Scheme.stalkClosedPointTo g))
    (Y.fromSpecStalk _) ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  rwa [Scheme.Spec_stalkClosedPointTo_fromSpecStalk] at this

/-- Injectivity on the stalk of a pullback at `t` gives injectivity on the stalk at `t ≫ k`. -/
lemma mono_sheafFiber_map_of_upperStar {S T : Scheme.{u}} (k : S ⟶ T) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ S) {G G' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (χ : G ⟶ G') (h : Mono (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
      ((k)^*[ModuleCat.{u + 1} Λ].map χ))) :
    Mono (((pointSmallEtale (t ≫ k)).sheafFiber (A := ModuleCat.{u + 1} Λ)).map χ) := by
  let e := upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) k t
  have he : ((pointSmallEtale (t ≫ k)).sheafFiber (A := ModuleCat.{u + 1} Λ)).map χ =
      e.inv.app G ≫ ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
        ((k)^*[ModuleCat.{u + 1} Λ].map χ) ≫ e.hom.app G' := by
    have hn := e.hom.naturality χ
    simp only [Functor.comp_map] at hn
    rw [hn, Iso.inv_hom_id_app_assoc]
  rw [he]
  have h₁ : Mono (e.inv.app G) := IsIso.mono_of_iso _
  have h₂ : Mono (e.hom.app G') := IsIso.mono_of_iso _
  exact @mono_comp _ _ _ _ _ _ h₁ _ (@mono_comp _ _ _ _ _ _ h _ h₂)

/-- **A finite pushforward detecting the stalk at a point** (Steps 1 to 5 of the proof of
Stacks 09Z6). Let `C` be a constructible sheaf of `Λ`-modules on a quasi-compact
quasi-separated scheme `X`, `Λ` noetherian, and `x ∈ X`. There are a finite morphism
`h : V ⟶ X`, a finitely generated `Λ`-module `M` and a map `C ⟶ h_* M` which is injective on
the stalk at the geometric point `X.algClosurePoint x` over `x`. -/
theorem exists_mono_sheafFiber_lowerStar [IsNoetherianRing Λ] {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (C : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf C] (x : X) :
    ∃ (V : Scheme.{u}) (h : V ⟶ X) (_ : IsFinite h) (M : ModuleCat.{u + 1} Λ)
      (_ : Module.Finite Λ M) (φ : C ⟶ (h)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
      Mono (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map φ) := by
  -- Step 1: `C` is constant over a finite extension `K` of `κ(x)`
  obtain ⟨W, w, v, rfl, hfin, -, hconst⟩ :=
    Scheme.exists_isConstant_upperStar_of_isConstructibleSheaf C x
  obtain ⟨M, ⟨eM⟩⟩ := hconst.mem_essImage
  have hMfin : Module.Finite Λ M := by
    have : Nonempty W := ⟨v⟩
    have := IsConstructibleSheaf.upperStar w C
    have := (IsConstructibleSheaf.of_iso eM.symm).isFiniteSheaf
    exact moduleFinite_of_isFiniteSheaf_constantSheaf (Y := W) M
  let K := W.residueField v
  let : Algebra (X.residueField (w.base v)) K := (w.residueFieldMap v).hom.toAlgebra
  have : Module.Finite (X.residueField (w.base v)) K := hfin
  -- Step 2: the normalization `ν : Y ⟶ X` of the closure of `x` in `K`
  obtain ⟨-, -, Y, ν, g, hν, hcomp, hY, hYs, η, hη, hgη, hres⟩ :=
    normalization_in_finite_residue_field_extension X (w.base v) K
  obtain rfl : η = genericPoint Y := hη.eq (genericPoint_spec Y)
  have hu := isIso_unit_constantSheaf_of_isIso_residueFieldMap (Λ := Λ) (fun y ↦ (hYs y).2) g
    hgη M
  have hgw : g ≫ ν = W.fromSpecResidueField v ≫ w := by
    rw [← hcomp, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rfl
  -- the identification `g^* ν^* C ≅ g^* M_Y` over the generic point
  let a := W.fromSpecResidueField v
  let e : (g)^*[ModuleCat.{u + 1} Λ].obj ((ν)^*[ModuleCat.{u + 1} Λ].obj C) ≅
      (g)^*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    ((upperStarComp (ModuleCat.{u + 1} Λ) g ν).app C).symm ≪≫
      eqToIso (congrArg (fun f ↦ (f)^*[ModuleCat.{u + 1} Λ].obj C) hgw) ≪≫
      (upperStarComp (ModuleCat.{u + 1} Λ) a w).app C ≪≫
      (a)^*[ModuleCat.{u + 1} Λ].mapIso eM.symm ≪≫
      (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) a).app M ≪≫
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M).symm
  -- Step 2: the map `C ⟶ ν_* M_Y`
  let adjg := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  let adjν := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν
  let ψb : (ν)^*[ModuleCat.{u + 1} Λ].obj C ⟶
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
    have : IsIso (adjg.unit.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := hu
    adjg.homEquiv _ _ e.hom ≫
      inv (adjg.unit.app ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
  have hψb : (g)^*[ModuleCat.{u + 1} Λ].map ψb = e.hom := by
    apply (adjg.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit]
    have := adjg.unit.naturality ψb
    simp only [Functor.id_map, Functor.comp_map] at this
    rw [← this]
    simp only [ψb, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ := adjν.homEquiv _ _ ψb
  -- Step 3: the stalk of `ψ` at the geometric point over `x` is injective
  have : Algebra.IsAlgebraic (X.residueField (w.base v)) K := Algebra.IsAlgebraic.of_finite _ _
  let ι : K →ₐ[X.residueField (w.base v)] AlgebraicClosure (X.residueField (w.base v)) :=
    IsAlgClosed.lift
  let t : Spec (.of (AlgebraicClosure (X.residueField (w.base v)))) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom ι.toRingHom)
  have ht : (t ≫ g) ≫ ν = X.algClosurePoint (w.base v) := by
    rw [Category.assoc, ← hcomp, ← Spec.map_comp_assoc]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (w.base v))
      (AlgebraicClosure (X.residueField (w.base v))))) ≫ X.fromSpecResidueField _
    congr 2
    ext r
    exact ι.commutes r
  have hψ : Mono (((pointSmallEtale (X.algClosurePoint (w.base v))).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map ψ) := by
    rw [← ht]
    apply mono_sheafFiber_map_of_upperStar ν (t ≫ g) ψ
    have hεψ : (ν)^*[ModuleCat.{u + 1} Λ].map ψ ≫ adjν.counit.app _ = ψb := by
      have := (adjν.homEquiv _ _).symm_apply_apply ψb
      rw [Adjunction.homEquiv_counit] at this
      exact this
    have h₂ : Mono (((pointSmallEtale (t ≫ g)).sheafFiber (A := ModuleCat.{u + 1} Λ)).map ψb) := by
      apply mono_sheafFiber_map_of_upperStar g t ψb
      rw [hψb]
      have : IsIso (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map e.hom) :=
        Functor.map_isIso _ _
      exact IsIso.mono_of_iso _
    rw [← hεψ, Functor.map_comp] at h₂
    exact @mono_of_mono _ _ _ _ _ _ _ h₂
  -- Step 4: `ψ` factors through a finite stage of `ν`
  have : IsIntegralHom ν := hν
  obtain ⟨A⟩ := ν.nonempty_finiteApproximation_of_isIntegralHom
  obtain ⟨i, θ, hθ⟩ := exists_comp_constantSheafPullbackMap_eq M A C ψ
  refine ⟨A.D.obj i, A.p i, inferInstance, M, hMfin, θ, ?_⟩
  have h₃ : Mono (((pointSmallEtale (X.algClosurePoint (w.base v))).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map θ ≫
      ((pointSmallEtale (X.algClosurePoint (w.base v))).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map
        (constantSheafPullbackMap M ν (A.p i) (A.π.app i) (A.π_p i))) := by
    rw [← Functor.map_comp, hθ]
    exact hψ
  exact @mono_of_mono _ _ _ _ _ _ _ h₃

/-- A morphism of étale sheaves of `Λ`-modules which is injective on the stalks at the geometric
points `X.algClosurePoint x` is a monomorphism. -/
lemma mono_of_mono_sheafFiber_algClosurePoint {X : Scheme.{u}}
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : G ⟶ G')
    (h : ∀ x : X, Mono (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map φ)) : Mono φ := by
  have hmono := (isConservativeFamilyOfPoints_ulift_pointSmallEtale X).jointlyReflectMonomorphisms
    (ModuleCat.{u + 1} Λ)
  refine @JointlyReflectMonomorphisms.mono _ _ _ _ _ _ hmono _ _ φ (fun Φ ↦ ?_)
  obtain ⟨-, ⟨x⟩⟩ := Φ
  let e : (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber :=
    (pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _
  have he : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).map φ =
      e.hom.app G ≫ ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map φ ≫ e.inv.app G' := by
    rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [he]
  have h₁ : Mono (e.hom.app G) := IsIso.mono_of_iso _
  have h₂ : Mono (e.inv.app G') := IsIso.mono_of_iso _
  exact @mono_comp _ _ _ _ _ _ h₁ _ (@mono_comp _ _ _ _ _ _ (h x) _ h₂)

/-- **Injectivity on a stalk spreads to a constructible neighbourhood.** Let `X` be Noetherian
and `φ : G ⟶ Q` a morphism out of a constructible sheaf which is injective on the stalk at the
geometric point over `x`. Then `φ` is injective on the stalks at the points of a constructible
subset containing `x`: the stalks of the kernel of `φ` vanish there
(`AlgebraicGeometry.Etale.exists_isConstructible_sheafFiber_map_eq_zero`). -/
lemma exists_isConstructible_mono_sheafFiber {X : Scheme.{u}} [IsNoetherian X]
    {G Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [IsConstructibleSheaf G]
    (φ : G ⟶ Q) (x : X)
    (hx : Mono (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map φ)) :
    ∃ E : Set X, IsConstructible E ∧ x ∈ E ∧ ∀ y ∈ E,
      Mono (((pointSmallEtale (X.algClosurePoint y)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map φ) := by
  have hadd (y : X) := (pointSmallEtale (X.algClosurePoint y)).sheafFiber_additive
    (A := ModuleCat.{u + 1} Λ)
  obtain ⟨E, hE, hxE, hE0⟩ := exists_isConstructible_sheafFiber_map_eq_zero (kernel.ι φ) x (by
    rw [← cancel_mono (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map φ), ← Functor.map_comp, kernel.condition, Functor.map_zero,
      zero_comp])
  refine ⟨E, hE, hxE, fun y hy ↦ ?_⟩
  set P := (pointSmallEtale (X.algClosurePoint y)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hι : kernel.ι (P.map φ) = 0 := by
    rw [← cancel_epi (kernelComparison φ P), kernelComparison_comp_ι, hE0 y hy, comp_zero]
  refine (Preadditive.mono_iff_cancel_zero _).2 fun Z g hg ↦ ?_
  have := kernel.lift_ι (P.map φ) g hg
  rw [hι, comp_zero] at this
  exact this.symm

end Etale

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverDescent
public import WeilConjectures.WeilSheaf.BoundaryStalkFrobenius
public import WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# Boundary stalks of direct images through the generic specialization

Let `j : U₀ ⟶ C₀` be a quasi-compact open immersion of `k₀`-schemes, `F` a Weil sheaf on `U₀`,
`h : Spec A ⟶ C̄` a pro-étale neighbourhood of a geometric point with a point `ε` of `Spec A`
over a point `η` of `Ū`. The *generic specialization*
`Γ(Spec A, h^* j_* F) ⟶ Γ(Spec Ω, (η ≫ j̄)^* j_* F) ⟶ Γ(Spec Ω, η^* F)`
(`AlgebraicGeometry.WeilSheaf.genericSpecialization`) is the restriction along `ε` followed by the
counit `j̄^* j̄_* F ⟶ F`. It intertwines the transports along lifts of the Frobenius
(`AlgebraicGeometry.WeilSheaf.genericSpecialization_frobenius`), and on germs it is the
restriction of sections of `F` from `Spec A ×_C̄ Ū` to `Spec Ω`
(`AlgebraicGeometry.WeilSheaf.genericSpecialization_germ_diagLift`).

This is the stalk side of blueprint `lem-wf-boundary-stalk-invariants`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The transport along the trivial square `𝟙 ≫ (t ≫ g) = t ≫ g` and `θ : g^* P ⟶ Q` is
`Γ(S, (t ≫ g)^* P) ≅ Γ(S, t^* g^* P) ⟶ Γ(S, t^* Q)`. -/
lemma globalSectionsTransport_refl_eq {S Y Z : Scheme.{u}} (t : S ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (ProEt.topology Z) A) {Q : Sheaf (ProEt.topology Y) A} (θ : (g)^*[A].obj P ⟶ Q) :
    globalSectionsTransport A (τ := (Iso.refl S).hom) (Category.id_comp (t ≫ g)) θ =
      (Sheaf.Γ _ A).map ((upperStarComp A t g).hom.app P ≫ (t)^*[A].map θ) := by
  have h := upperStarComp_id_left_hom_app A (t ≫ g) P
  have h' : (upperStarId A S).inv.app _ ≫ (upperStarComp A (𝟙 S) (t ≫ g)).inv.app P =
      (upperStarCongr A (Category.id_comp (t ≫ g))).inv.app P := by
    rw [← cancel_mono ((upperStarCongr A (Category.id_comp (t ≫ g))).hom.app P),
      Iso.inv_hom_id_app, ← h, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [globalSectionsTransport, Iso.refl_hom, globalSectionsToUpperStar_id_app, ← Functor.map_comp,
    upperStarCompIso]
  congr 1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% h', Iso.inv_hom_id_app_assoc]

/-- A lift `t` of `T` through `V ×_Y T` is the lift given by its first component. -/
lemma eq_overLift {Y T : Scheme.{u}} (V : Y.ProEt) {g : T ⟶ Y}
    (t : ProEt.mk (𝟙 T) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    t = overLift V (t.left ≫ pullback.fst V.hom g) (by
      have hw : t.left ≫ pullback.snd V.hom g = 𝟙 T := MorphismProperty.Over.w t
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp]) := by
  have hw : t.left ≫ pullback.snd V.hom g = 𝟙 T := MorphismProperty.Over.w t
  refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
  · simp [overLift]
  · simp [overLift, hw]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open ProEtale Scheme

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))

section Generic

variable {A : Type u} [CommRing A]
  (h : Spec (.of A) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  {Ω : Type u} [Field Ω] (η : Spec (.of Ω) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (ε : Spec (.of Ω) ⟶ Spec (.of A)) (hε : ε ≫ h = η ≫ j̄)

/-- **The generic specialization** `Γ(Spec A, h^* j_* F) ⟶ Γ(Spec Ω, η^* F)`: the restriction
along a point `ε : Spec Ω ⟶ Spec A` over `η ≫ j̄`, followed by the counit `j̄^* j̄_* F ⟶ F`. -/
noncomputable def genericSpecialization :
    (Sheaf.Γ _ _).obj ((h)^*[WeilCoefficients.{u} l].obj ((directImage j).obj F).obj.carrier.X) ⟶
      (Sheaf.Γ _ _).obj ((η)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X) :=
  (ProEtale.resOver _ ε hε).app _ ≫
    ProEtale.globalSectionsTransport _ (τ := (Iso.refl _).hom) (Category.id_comp (η ≫ j̄))
      (directImageCounit' j F)

/-- **The generic specialization intertwines the Frobenius lifts.** For a lift `α` of `Frᵐ` to
`Spec A` and `a` of `Frᵐ` to `Spec Ω` with `a ≫ ε = ε ≫ α`, the generic specialization
intertwines the transports along `α` and `a` and the iterated Weil structures. -/
theorem genericSpecialization_frobenius (m : ℕ) (hm : 1 ≤ m) (α : Spec (.of A) ⟶ Spec (.of A))
    (hα : α ≫ h = h ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω))
    (ha : a ≫ η = η ≫ ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)
    (haε : a ≫ ε = ε ≫ α) :
    ProEtale.globalSectionsTransport _ hα (((directImage j).obj F).frobeniusPowStr m) ≫
        genericSpecialization j F h η ε hε =
      genericSpecialization j F h η ε hε ≫
        ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr m) := by
  have haC : a ≫ (η ≫ j̄) =
      (η ≫ j̄) ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom := by
    rw [← Category.assoc, ha, Category.assoc, Category.assoc,
      ← Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow]
  rw [genericSpecialization, genericSpecialization, ← Category.assoc,
    ProEtale.globalSectionsTransport_comp_resOver hα haC ε hε haε, Category.assoc,
    globalSectionsTransport_frobeniusPowStr_comp_upperStar
      (directImageCounit_frobeniusStr_compatible j F) m hm ha haC, Category.assoc]

end Generic

set_option maxHeartbeats 4000000 in
-- the underlying sheaves of `j^* j_* F` and `j̄^* j̄_* F` agree only up to unfolding
/-- The counit of Weil sheaves is the counit of `j̄^* ⊣ j̄_*` on the underlying sheaves. -/
lemma directImageCounit'_eq :
    directImageCounit' j F =
      (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) (j̄)).counit.app
        F.obj.carrier.X := by
  rw [directImageCounit', directImageCounit, upperStarLowerStarAdjunction_counit_app_hom_hom_f]
  exact Category.id_comp _

section Neighbourhood

variable {A : Type u} [CommRing A]
  (h : Spec (.of A) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) [WeaklyEtale h]
  {K' Ω : Type u} [Field K'] [Field Ω] [Algebra K' Ω] [Algebra.IsSeparable K' Ω]
  (k : Spec (.of K') ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) [WeaklyEtale k]
  (e : Scheme.ProEt.mk k ≅
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (Scheme.ProEt.mk h))

variable (Ω) in
/-- The generic point `Spec Ω ⟶ Spec K' ≅ Spec A ×_C̄ Ū ⟶ Spec A` of the neighbourhood. -/
noncomputable abbrev nbhdGenericPoint : Spec (.of Ω) ⟶ Spec (.of A) :=
  specFieldMap K' Ω ≫ e.hom.left ≫ pullback.fst h (j̄)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] in
lemma nbhdGenericPoint_comp :
    nbhdGenericPoint j h k e Ω ≫ h = (specFieldMap K' Ω ≫ k) ≫ j̄ := by
  have hw : e.hom.left ≫ pullback.snd h (j̄) = k := MorphismProperty.Over.w e.hom
  rw [nbhdGenericPoint, Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc e.hom.left, hw, Category.assoc]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] in
/-- The lift of `Spec Ω` through the iterated base change, given by the generic point. -/
lemma overLift_nbhdGenericPoint_comp_pullbackComp :
    overLift (Scheme.ProEt.mk h) (nbhdGenericPoint j h k e Ω) (nbhdGenericPoint_comp j h k e) ≫
      (MorphismProperty.Over.pullbackComp (specFieldMap K' Ω ≫ k) (j̄)).hom.app
        (Scheme.ProEt.mk h) =
      overLift ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (Scheme.ProEt.mk h))
        (specFieldMap K' Ω ≫ e.hom.left)
        (by rw [Category.assoc]; exact congrArg (specFieldMap K' Ω ≫ ·) (MorphismProperty.Over.w e.hom)) := by
  refine MorphismProperty.Over.Hom.ext ?_
  erw [MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [overLift, nbhdGenericPoint]
    · simp [overLift, nbhdGenericPoint]
  · simp [overLift]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- **The generic specialization on germs.** The generic specialization of the germ along the
diagonal of a section `p` of `j_* F` over the neighbourhood is the germ along the diagonal of
the restriction of `p`, as a section of `F` over `Spec A ×_C̄ Ū = Spec K'`, to `Spec Ω`. -/
lemma genericSpecialization_germ_diagLift
    (p : ToType (((j̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X).obj.obj
      (op (Scheme.ProEt.mk h)))) :
    (genericSpecialization j F h (specFieldMap K' Ω ≫ k) (nbhdGenericPoint j h k e Ω)
        (nbhdGenericPoint_comp j h k e)).hom
      ((germ _ (Scheme.ProEt.mk h).hom ((j̄)_*[_].obj F.obj.carrier.X)
        (diagLift (Scheme.ProEt.mk h))).hom p) =
      (germ _ (fieldExtObj Ω k).hom F.obj.carrier.X (diagLift (fieldExtObj Ω k))).hom
        (F.obj.carrier.X.obj.map (fieldExtHom Ω k ≫ e.hom).op p) := by
  set Vu := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (Scheme.ProEt.mk h)
  have hℓ : (specFieldMap K' Ω ≫ e.hom.left) ≫ Vu.hom = specFieldMap K' Ω ≫ k := by
    rw [Category.assoc]
    exact congrArg (specFieldMap K' Ω ≫ ·) (MorphismProperty.Over.w e.hom)
  -- the left side, as a germ of `F` along `η`
  have e₁ := germ_overLift (WeilCoefficients.{u} l) ((j̄)_*[_].obj F.obj.carrier.X)
    (Scheme.ProEt.mk h) (nbhdGenericPoint j h k e Ω) (nbhdGenericPoint_comp j h k e)
  have e₂ := germ_comp_lowerStar (WeilCoefficients.{u} l) (specFieldMap K' Ω ≫ k) (j̄)
    F.obj.carrier.X _ _ (overLift_nbhdGenericPoint_comp_pullbackComp j h k e)
  have e₃ := germ_overLift (WeilCoefficients.{u} l) F.obj.carrier.X Vu
    (specFieldMap K' Ω ≫ e.hom.left) hℓ
  -- the right side
  have e₄ := map_comp_germ_diagLift (WeilCoefficients.{u} l) F.obj.carrier.X
    (fieldExtHom Ω k ≫ e.hom)
  rw [genericSpecialization, ProEtale.globalSectionsTransport_refl_eq, directImageCounit'_eq,
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply _ ((resOver _ _ _).app _), ← e₁,
    ← ConcreteCategory.comp_apply, e₂, e₃, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    e₄]
  rfl

section Specialization

variable [IsStrictlyHenselianLocalRing A] [Normal K' Ω] (x : X.finitePoints)
  (t : Scheme.ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤
    ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)).obj
      (Scheme.ProEt.mk h))

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- **The boundary stalk of `j_* F` as Galois invariants, Frobenius-equivariantly.** Let
`h : Spec A ⟶ C̄` be a weakly étale neighbourhood of the geometric point `x̄` of a closed point `x`
through the closed point of the strictly henselian `Spec A`, whose punctured part
`Spec A ×_C̄ Ū` is `k : Spec K' ⟶ Ū`, and `Ω / K'` a Galois extension. Given lifts `α` of the
Frobenius `Frᵐ`, `m = deg x`, to `Spec A` and `a` to `Spec Ω`, compatible with the lift of `x̄`
and with the generic point `Spec Ω ⟶ Spec A`, there is an injective linear map
`(j_* F)_x̄ ⟶ Γ(Spec Ω, η^* F)`, `η : Spec Ω ⟶ Spec K' ⟶ Ū`, with image the
`Gal(Ω / K')`-invariants, intertwining the Frobenius of the stalk with the transport along
`a ≫ η = η ≫ Frᵐ` and the Weil structure of `F`.
(blueprint: `lem-wf-boundary-stalk-invariants`) -/
theorem exists_stalk_directImage_linearMap_invariants (hF : F.IsLisse)
    (ht : (t.left ≫ pullback.fst h _) (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      IsLocalRing.closedPoint A)
    (α : Spec (.of A) ⟶ Spec (.of A))
    (hα : α ≫ h = h ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).hom)
    (hcα : (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).hom ≫
      (t.left ≫ pullback.fst h _) = (t.left ≫ pullback.fst h _) ≫ α)
    (η : Spec (.of Ω) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hη : specFieldMap K' Ω ≫ k = η) (a : Spec (.of Ω) ⟶ Spec (.of Ω))
    (ha : a ≫ η = η ≫
      ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).hom)
    (haε : a ≫ nbhdGenericPoint j h k e Ω = nbhdGenericPoint j h k e Ω ≫ α) :
    ∃ Sp : (((directImage j).obj F).stalk x).carrier →ₗ[PadicAlgCl l]
        (WeilCoefficients.toModuleCat l).obj
          ((Sheaf.Γ _ _).obj ((η)^*[_].obj F.obj.carrier.X)),
      Function.Injective Sp ∧
      (∀ u, u ∈ LinearMap.range Sp ↔ ∀ σ : Ω ≃ₐ[K'] Ω,
        ((WeilCoefficients.toModuleCat l).map ((resOver _ _
          (show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ η = η by
              rw [← hη, ← Category.assoc, specMap_algEquiv_comp_specFieldMap])).app
                F.obj.carrier.X)).hom u = u) ∧
      ∀ v, Sp ((((directImage j).obj F).stalk x).frobenius v) =
        ((WeilCoefficients.toModuleCat l).map
          (globalSectionsTransport _ ha (F.frobeniusPowStr _))).hom (Sp v) := by
  subst hη
  set x̄ := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  set P := ((directImage j).obj F).obj.carrier.X
  set c := t.left ≫ pullback.fst h x̄
  have hc : c ≫ h = x̄ := by
    have hw : t.left ≫ pullback.snd h x̄ = 𝟙 _ := MorphismProperty.Over.w t
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp]
  set g := germ (WeilCoefficients.{u} l) x̄ P t
  have hg : Function.Bijective g := bijective_germ_stalk_directImage j F x h t ht
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective g).2 hg
  set DA := germ (WeilCoefficients.{u} l) h P (diagLift (Scheme.ProEt.mk h))
  set rc := (resOver (WeilCoefficients.{u} l) c hc).app P
  have hgD : g = DA ≫ rc := by
    rw [eq_overLift _ t]
    exact germ_overLift _ P (Scheme.ProEt.mk h) c hc
  have : IsIso rc := by
    have : rc = inv DA ≫ g := by rw [hgD, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  have hinv : inv rc = inv g ≫ DA :=
    (IsIso.inv_eq_of_inv_hom_id (by rw [Category.assoc, ← hgD, IsIso.inv_hom_id])).symm
  set GS := genericSpecialization j F h (specFieldMap K' Ω ≫ k) (nbhdGenericPoint j h k e Ω)
    (nbhdGenericPoint_comp j h k e)
  set DΩ := germ (WeilCoefficients.{u} l) (fieldExtObj Ω k).hom F.obj.carrier.X
    (diagLift (fieldExtObj Ω k))
  have hDΩ : Function.Bijective DΩ := ConcreteCategory.bijective_of_isIso DΩ
  -- the specialization on sections over the neighbourhood
  set ρ : P.obj.obj (op (Scheme.ProEt.mk h)) ⟶ F.obj.carrier.X.obj.obj (op (fieldExtObj Ω k)) :=
    F.obj.carrier.X.obj.map (fieldExtHom Ω k ≫ e.hom).op
  have hρ' (p) : ρ p = F.obj.carrier.X.obj.map (fieldExtHom Ω k).op
      (F.obj.carrier.X.obj.map e.hom.op p) := by
    simp only [ρ, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hρi : Function.Injective ρ := by
    have he : Function.Injective (F.obj.carrier.X.obj.map e.hom.op) :=
      (ConcreteCategory.bijective_of_isIso (F.obj.carrier.X.obj.map e.hom.op)).1
    have := (hF.injective_map_fieldExtHom (Ω := Ω) k).comp he
    intro p q hpq
    apply this
    simpa only [Function.comp_apply, hρ'] using hpq
  have hSp (v) : ((WeilCoefficients.toModuleCat l).map (inv rc ≫ GS)).hom v =
      DΩ (ρ ((inv g) v)) := by
    change GS ((inv rc) v) = _
    rw [hinv, ConcreteCategory.comp_apply]
    exact genericSpecialization_germ_diagLift j F h k e _
  -- the Galois action on `Γ(Spec Ω, η^* F)` and on sections over `Spec Ω`
  have hσ (σ : Ω ≃ₐ[K'] Ω) (q) :
      ((WeilCoefficients.toModuleCat l).map ((resOver _ _
        (show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (specFieldMap K' Ω ≫ k) =
          specFieldMap K' Ω ≫ k by
            rw [← Category.assoc, specMap_algEquiv_comp_specFieldMap])).app
              F.obj.carrier.X)).hom (DΩ q) =
        DΩ (F.obj.carrier.X.obj.map (fieldExtAut k σ).op q) :=
    (ConcreteCategory.congr_hom
      (map_comp_germ_diagLift (WeilCoefficients.{u} l) F.obj.carrier.X (fieldExtAut k σ)) q).symm
  refine ⟨((WeilCoefficients.toModuleCat l).map (inv rc ≫ GS)).hom,
    fun v w hvw ↦ ?_, fun u ↦ ⟨?_, fun hu ↦ ?_⟩, fun v ↦ ?_⟩
  · rw [hSp, hSp] at hvw
    exact (ConcreteCategory.bijective_of_isIso (inv g)).1 (hρi (hDΩ.1 hvw))
  · rintro ⟨v, rfl⟩ σ
    rw [hSp, hσ, hρ', map_fieldExtAut_map_fieldExtHom]
  · obtain ⟨q, rfl⟩ := hDΩ.2 u
    have hq (σ : Ω ≃ₐ[K'] Ω) : F.obj.carrier.X.obj.map (fieldExtAut k σ).op q = q :=
      hDΩ.1 ((hσ σ q).symm.trans (hu σ))
    obtain ⟨s, hs⟩ := hF.exists_map_fieldExtHom_eq k q hq
    refine ⟨g (F.obj.carrier.X.obj.map e.inv.op s), ?_⟩
    rw [hSp, ← ConcreteCategory.comp_apply g (inv g), IsIso.hom_inv_id, ConcreteCategory.id_apply,
      hρ', ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e.hom_inv_id, op_id,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, hs]
  · have hpos : 1 ≤ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 :=
      Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ x.2)
    have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) x
    have hfr : (((directImage j).obj F).stalk x).frobenius v =
        ((WeilCoefficients.toModuleCat l).map (globalSectionsTransport _ hs.symm
          (((directImage j).obj F).frobeniusPowStr _))).hom v :=
      LinearMap.congr_fun (frobeniusEnd_stalkAt ((directImage j).obj F) x̄ _ hs) v
    have h₁ := globalSectionsTransport_comp_resOver hα hs.symm c hc hcα P
      (((directImage j).obj F).frobeniusPowStr _)
    have h₂ : globalSectionsTransport _ hs.symm (((directImage j).obj F).frobeniusPowStr _) ≫
        inv rc = inv rc ≫ globalSectionsTransport _ hα
          (((directImage j).obj F).frobeniusPowStr _) := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, ← h₁, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    have h₃ := genericSpecialization_frobenius j F h (specFieldMap K' Ω ≫ k)
      (nbhdGenericPoint j h k e Ω) (nbhdGenericPoint_comp j h k e) _ hpos α hα a ha haε
    have hm : globalSectionsTransport _ hs.symm (((directImage j).obj F).frobeniusPowStr _) ≫
        inv rc ≫ GS = (inv rc ≫ GS) ≫ globalSectionsTransport _ ha (F.frobeniusPowStr _) := by
      rw [reassoc_of% h₂, h₃, Category.assoc]
    rw [hfr, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, hm]

end Specialization

end Neighbourhood

end AlgebraicGeometry.WeilSheaf

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExtFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModuleBaseChange

/-!
# Cohomology and flat base change

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `H^q(X, ℱ) ⊗_A B ≅ H^q(Y, g'^* ℱ)`
(Stacks 02KH).

## Strategy

Everything happens on `X`. The morphism `g'` is affine, so `H^q(Y, g'^* ℱ) = H^q(X, ℱ'')` for the
quasi-coherent module `ℱ'' = g'_* g'^* ℱ`, on which `B` acts by sheaf endomorphisms. For every
open `W` of `X` there is a base change map `B ⊗_A H^q(W, ℱ) ⟶ H^q(W, ℱ'')`, `b ⊗ x ↦ b • η_* x`
for the unit `η : ℱ ⟶ ℱ''`, and we show that it is bijective
* on affine opens: in positive degrees both sides vanish, and in degree `0` this is the base
  change of sections `B ⊗_A Γ(W, ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`;
* on `U ∪ V` if it is so on `U`, `V` and `U ∩ V`, by the Mayer–Vietoris sequences and the five
  lemma, `B` being flat over `A` (`CategoryTheory.Abelian.Ext.WithAction`);
* hence on finite unions of affine opens contained in an affine open (intersections of affine
  opens in an affine scheme are affine), then on all quasi-compact opens of the quasi-separated
  scheme `X`, in particular on `X` itself.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct Opposite

namespace AlgebraicGeometry

/-- **Induction on quasi-compact opens of a quasi-separated scheme.** A property of the opens
of a quasi-separated scheme which holds for the affine opens, and holds for `U ⊔ V` whenever it
holds for `U`, `V` and `U ⊓ V`, holds for every quasi-compact open. -/
theorem Scheme.induction_isCompact_of_quasiSeparatedSpace {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (P : X.Opens → Prop) (h_aff : ∀ U, IsAffineOpen U → P U)
    (h_sup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V)) (S : X.Opens)
    (hS : IsCompact (S : Set X)) : P S := by
  classical
  -- intersections of affine opens contained in an affine open are affine
  have hinf : ∀ U, IsAffineOpen U → ∀ V₁ ≤ U, ∀ V₂ ≤ U, IsAffineOpen V₁ → IsAffineOpen V₂ →
      IsAffineOpen (V₁ ⊓ V₂) := fun U hU V₁ h₁ V₂ h₂ ↦ by
    refine isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal (𝟙 X)))
      U hU V₁ ?_ V₂ ?_ <;> simpa
  -- finite unions of affine opens contained in an affine open
  have hfin : ∀ U, IsAffineOpen U → ∀ (n : ℕ) (s : Finset X.Opens), s.card ≤ n →
      (∀ V ∈ s, IsAffineOpen V ∧ V ≤ U) → P (s.sup id) := by
    intro U hU n
    induction n with
    | zero =>
      intro s hs _
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs), Finset.sup_empty]
      exact h_aff _ (isAffineOpen_bot X)
    | succ n ih =>
      intro s hs hsU
      induction s using Finset.induction_on with
      | empty => exact h_aff _ (isAffineOpen_bot X)
      | insert V s hV _ =>
        rw [Finset.card_insert_of_notMem hV] at hs
        have hsU' : ∀ W ∈ s, IsAffineOpen W ∧ W ≤ U := fun W hW ↦
          hsU W (Finset.mem_insert_of_mem hW)
        have hVU := hsU V (Finset.mem_insert_self V s)
        rw [Finset.sup_insert]
        refine h_sup _ _ (h_aff _ hVU.1) (ih s (by omega) hsU') ?_
        have hs_img : V ⊓ s.sup id = (s.image (V ⊓ ·)).sup id := by
          rw [Finset.sup_inf_distrib_left, Finset.sup_image]; rfl
        rw [id_eq, hs_img]
        refine ih _ (Finset.card_image_le.trans (by omega)) fun W hW ↦ ?_
        obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hW
        exact ⟨hinf U hU V hVU.2 W' (hsU' W' hW').2 hVU.1 (hsU' W' hW').1,
          inf_le_left.trans hVU.2⟩
  -- quasi-compact opens contained in an affine open
  have hcpt : ∀ U, IsAffineOpen U → ∀ W ≤ U, IsCompact (W : Set X) → P W := by
    intro U hU W hWU hW
    obtain ⟨s, hs, hsW⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
    have hsW' : ∀ i ∈ s, (i : X.Opens) ≤ W := fun i hi ↦
      hsW ▸ le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) ↦ (i : X.Opens)) i hi
    have ht : (hs.toFinset.image Subtype.val).sup id = W := by
      apply le_antisymm
      · simp only [Finset.sup_le_iff, Finset.mem_image, Set.Finite.mem_toFinset, id_eq,
          forall_exists_index, and_imp]
        rintro _ i hi rfl
        exact hsW' i hi
      · rw [hsW]
        exact iSup₂_le fun i hi ↦
          Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (hs.mem_toFinset.mpr hi))
    rw [← ht]
    refine hfin U hU _ _ le_rfl fun V hV ↦ ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨i.2, (hsW' i (hs.mem_toFinset.mp hi)).trans hWU⟩
  refine compact_open_induction_on S hS (h_aff _ (isAffineOpen_bot X)) ?_
  intro S hS U hP
  refine h_sup _ _ hP (h_aff _ U.2) (hcpt U U.2 _ inf_le_right ?_)
  exact QuasiSeparatedSpace.inter_isCompact _ _ S.2 hS U.1.2 U.2.isCompact

end AlgebraicGeometry

namespace TopCat.Sheaf

open CategoryTheory.Abelian

variable {X : TopCat.{u}}

lemma homFreeSheafEquiv_eq (U : Opens X)
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : freeSheaf U ⟶ G) :
    homFreeSheafEquiv U G φ =
      φ.hom.app (op U) (homFreeSheafEquiv U (freeSheaf U) (𝟙 (freeSheaf U))) := by
  rw [← homFreeSheafEquiv_comp, Category.id_comp]

/-- The cohomology in degree `0` of an abelian sheaf `G` on an open `U` is `G(U)`:
`Ext⁰(ℤ_U, G) ≅ Hom(ℤ_U, G) ≅ G(U)`. -/
noncomputable def extFreeSheafZeroAddEquiv (U : Opens X)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Ext (freeSheaf U) G 0 ≃+ G.obj.obj (op U) where
  toEquiv := Ext.addEquiv₀.toEquiv.trans (homFreeSheafEquiv U G)
  map_add' x y := by
    change homFreeSheafEquiv U G (Ext.addEquiv₀ (x + y)) =
      homFreeSheafEquiv U G (Ext.addEquiv₀ x) + homFreeSheafEquiv U G (Ext.addEquiv₀ y)
    rw [map_add]
    rw [homFreeSheafEquiv_eq, homFreeSheafEquiv_eq U (Ext.addEquiv₀ x),
      homFreeSheafEquiv_eq U (Ext.addEquiv₀ y)]
    rfl

lemma extFreeSheafZeroAddEquiv_comp_mk₀ (U : Opens X)
    {G G' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (x : Ext (freeSheaf U) G 0)
    (φ : G ⟶ G') :
    extFreeSheafZeroAddEquiv U G' (x.comp (Ext.mk₀ φ) (add_zero 0)) =
      φ.hom.app (op U) (extFreeSheafZeroAddEquiv U G x) := by
  change homFreeSheafEquiv U G' (Ext.addEquiv₀ _) = _
  rw [Ext.addEquiv₀_comp_mk₀, homFreeSheafEquiv_comp]
  rfl

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian.Ext

variable {X : Scheme.{u}}

/-- Multiplication by global functions on the underlying abelian sheaf of a sheaf of modules, as
a ring homomorphism to its endomorphisms. -/
noncomputable def smulRingHom (M : X.Modules) :
    Γ(X, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) where
  toFun a := (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a)
  map_one' := by rw [smulHom_one, CategoryTheory.Functor.map_id]; rfl
  map_mul' a b := by rw [smulHom_mul, CategoryTheory.Functor.map_comp, End.mul_def]
  map_zero' := by rw [smulHom_zero, CategoryTheory.Functor.map_zero]
  map_add' a b := by rw [smulHom_add, CategoryTheory.Functor.map_add]

/-- Multiplication by global functions of `Y` on the underlying abelian sheaf of the pushforward
`g_* N` of a sheaf of modules along `g : Y ⟶ X`, as a ring homomorphism to its endomorphisms. -/
noncomputable def pushforwardSmulRingHom {Y : Scheme.{u}} (g : Y ⟶ X) (N : Y.Modules) :
    Γ(Y, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((pushforward g).obj N)) where
  toFun b := (SheafOfModules.toSheaf X.ringCatSheaf).map ((pushforward g).map (N.smulHom b))
  map_one' := by
    rw [smulHom_one, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]; rfl
  map_mul' a b := by
    rw [smulHom_mul, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, End.mul_def]
  map_zero' := by
    rw [smulHom_zero, CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]
  map_add' a b := by
    rw [smulHom_add, CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]

section BaseChange

variable {Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

variable (f) in
/-- The action of `A = Γ(S, ⊤)` on the underlying abelian sheaf of `ℱ`, through `f^♯`. -/
noncomputable abbrev baseAction : Γ(S, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) :=
  (smulRingHom ℱ).comp f.appTop.hom

variable (f' g') in
/-- The action of `B = Γ(T, ⊤)` on the underlying abelian sheaf of `g'_* g'^* ℱ`, through
`f'^♯`. -/
noncomputable abbrev pushforwardPullbackAction :
    Γ(T, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((pushforward g').obj ((pullback g').obj ℱ))) :=
  (pushforwardSmulRingHom g' ((pullback g').obj ℱ)).comp f'.appTop.hom

variable (g') in
/-- The unit `ℱ ⟶ g'_* g'^* ℱ`, on the underlying abelian sheaves. -/
noncomputable abbrev toSheafUnit :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj ((pushforward g').obj ((pullback g').obj ℱ)) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map ((pullbackPushforwardAdjunction g').unit.app ℱ)

include H in
omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] in
lemma appTop_appTop_of_isPullback (a : Γ(S, ⊤)) :
    g'.appTop (f.appTop a) = f'.appTop (g.appTop a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, H.w]

include H hg in
/-- The unit `ℱ ⟶ g'_* g'^* ℱ` intertwines the actions of `A` and `B`. -/
lemma baseAction_comp_toSheafUnit (a : Γ(S, ⊤)) :
    baseAction f ℱ a ≫ toSheafUnit g' ℱ =
      toSheafUnit g' ℱ ≫ pushforwardPullbackAction f' g' ℱ (algebraMap Γ(S, ⊤) Γ(T, ⊤) a) := by
  have key : ℱ.smulHom (f.appTop a) ≫ (pullbackPushforwardAdjunction g').unit.app ℱ =
      (pullbackPushforwardAdjunction g').unit.app ℱ ≫
        (pushforward g').map (((pullback g').obj ℱ).smulHom (f'.appTop (algebraMap _ _ a))) := by
    rw [smulHom_naturality, hg, ← appTop_appTop_of_isPullback H, pushforward_map_smulHom]
    rfl
  have h := congrArg (SheafOfModules.toSheaf X.ringCatSheaf).map key
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  exact h

/-- The base change map `B ⊗_A H^n(W, ℱ) ⟶ H^n(W, g'_* g'^* ℱ)`, `b ⊗ x ↦ b • η_* x`, for an open
`W` of `X` (with `H^n(W, -) = Ext^n(ℤ_W, -)`), or more generally with `ℤ_W` replaced by any
abelian sheaf `P`. -/
noncomputable abbrev cohomologyBaseChange (P : Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) :=
  WithAction.baseChange (baseAction f ℱ) (pushforwardPullbackAction f' g' ℱ) (toSheafUnit g' ℱ)
    (baseAction_comp_toSheafUnit H ℱ hg) P n

section Affine

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- `H⁰(W, ℱ) ≅ Γ(W, ℱ)` as `Γ(S, ⊤)`-modules. -/
noncomputable def sectionsLinearEquiv (W : X.Opens) :
    WithAction (baseAction f ℱ) (TopCat.Sheaf.freeSheaf W) 0 ≃ₗ[Γ(S, ⊤)]
      sectionsModule f ℱ W where
  __ := (WithAction.toExt _).trans (TopCat.Sheaf.extFreeSheafZeroAddEquiv W _)
  map_smul' a x := by
    change TopCat.Sheaf.extFreeSheafZeroAddEquiv W _
      ((WithAction.toExt _ x).comp (mk₀ (baseAction f ℱ a)) (add_zero 0)) = _
    rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀]
    rfl


variable (f' g') in
/-- `H⁰(W, g'_* g'^* ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`. -/
noncomputable def pushforwardSectionsAddEquiv (W : X.Opens) :
    WithAction (pushforwardPullbackAction f' g' ℱ) (TopCat.Sheaf.freeSheaf W) 0 ≃+
      sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W) :=
  (WithAction.toExt _).trans (TopCat.Sheaf.extFreeSheafZeroAddEquiv W _)

include H hg in
/-- In degree `0` the base change map on an affine open `W` is the base change of sections
`B ⊗_A Γ(W, ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`, hence bijective. -/
lemma bijective_cohomologyBaseChange_zero_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) 0) := by
  have key : ⇑(pushforwardSectionsAddEquiv f' g' ℱ W) ∘
      ⇑(cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) 0) =
      ⇑(sectionsModuleBaseChange H ℱ hg W) ∘ ⇑((sectionsLinearEquiv ℱ W).lTensor Γ(T, ⊤)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | add z z' hz hz' =>
      simp only [Function.comp_apply, map_add] at hz hz' ⊢
      rw [hz, hz']
    | tmul b x =>
      change TopCat.Sheaf.extFreeSheafZeroAddEquiv W _ ((WithAction.toExt _ x).comp
          (mk₀ (toSheafUnit g' ℱ ≫ pushforwardPullbackAction f' g' ℱ b)) (add_zero 0)) =
        sectionsModuleBaseChange H ℱ hg W (b ⊗ₜ sectionsLinearEquiv ℱ W x)
      rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀, sectionsModuleBaseChange_tmul]
      rfl
  refine (Function.Bijective.of_comp_iff' (pushforwardSectionsAddEquiv f' g' ℱ W).bijective
    _).mp ?_
  rw [key]
  exact (bijective_sectionsModuleBaseChange H ℱ hg hW).comp (LinearEquiv.bijective _)

include H in
omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] in
lemma isAffineHom_of_isPullback : IsAffineHom g' :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance

include H in
/-- In positive degrees, both sides of the base change map vanish on an affine open `W`. -/
lemma bijective_cohomologyBaseChange_succ_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W)
    (n : ℕ) :
    Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) (n + 1)) := by
  have := isAffineHom_of_isPullback H
  have := isQuasicoherent_pushforward_of_isAffineHom g' ((pullback g').obj ℱ)
  have : Subsingleton (WithAction (baseAction f ℱ) (TopCat.Sheaf.freeSheaf W) (n + 1)) :=
    subsingleton_H'_succ_of_isAffineOpen _ (cechAcyclicOnAffines_of_isQuasicoherent ℱ) hW n
  have : Subsingleton (WithAction (pushforwardPullbackAction f' g' ℱ)
      (TopCat.Sheaf.freeSheaf W) (n + 1)) :=
    subsingleton_H'_succ_of_isAffineOpen _ (cechAcyclicOnAffines_of_isQuasicoherent _) hW n
  have : Subsingleton (Γ(T, ⊤) ⊗[Γ(S, ⊤)]
      WithAction (baseAction f ℱ) (TopCat.Sheaf.freeSheaf W) (n + 1)) := inferInstance
  exact ⟨fun x y _ ↦ Subsingleton.elim x y, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

include H hg in
/-- The base change map is bijective on affine opens. -/
lemma bijective_cohomologyBaseChange_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W)
    (n : ℕ) : Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) n) := by
  cases n with
  | zero => exact bijective_cohomologyBaseChange_zero_of_isAffineOpen H ℱ hg hW
  | succ n => exact bijective_cohomologyBaseChange_succ_of_isAffineOpen H ℱ hg hW n

end Affine

include hg in
lemma moduleFlat_of_flat [IsAffine S] [IsAffine T] [Flat g] : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := by
  have h := g.flat_appTop
  rw [← hg, RingHom.flat_algebraMap_iff] at h
  exact h

/-- **Mayer–Vietoris step.** If the base change maps are bijective on `U`, `V` and `U ⊓ V`, then
they are bijective on `U ⊔ V`. -/
lemma bijective_cohomologyBaseChange_sup [Module.Flat Γ(S, ⊤) Γ(T, ⊤)] {U V : X.Opens}
    (hU : ∀ n, Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf U) n))
    (hV : ∀ n, Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf V) n))
    (hUV : ∀ n,
      Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf (U ⊓ V)) n))
    (n : ℕ) :
    Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf (U ⊔ V)) n) :=
  WithAction.bijective_baseChange_of_shortExact _ _ _ _
    (Opens.mayerVietorisSquare U V).shortComplex_shortExact hUV
    (fun n ↦ WithAction.bijective_baseChange_biprod _ _ _ _ (hU n) (hV n)) n

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
  [Flat g] [QuasiSeparated f]

include hg in
/-- **Flat base change on quasi-compact opens.** For a quasi-compact open `W` of `X`, the base
change map `B ⊗_A H^n(W, ℱ) ⟶ H^n(W, g'_* g'^* ℱ)` is bijective. -/
theorem bijective_cohomologyBaseChange_of_isCompact {W : X.Opens} (hW : IsCompact (W : Set X))
    (n : ℕ) : Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) n) := by
  have := moduleFlat_of_flat hg
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  revert n
  refine Scheme.induction_isCompact_of_quasiSeparatedSpace
    (fun W ↦ ∀ n, Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) n))
    (fun U hU ↦ bijective_cohomologyBaseChange_of_isAffineOpen H ℱ hg hU)
    (fun U V hU hV hUV ↦ bijective_cohomologyBaseChange_sup H ℱ hg hU hV hUV) W hW

variable [QuasiCompact f]

include hg in
/-- **Flat base change of cohomology, on `X`.** The base change map
`B ⊗_A H^n(X, ℱ) ⟶ H^n(X, g'_* g'^* ℱ)` is bijective. -/
theorem bijective_cohomologyBaseChange (n : ℕ) :
    Function.Bijective (cohomologyBaseChange H ℱ hg
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) n) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have h := bijective_cohomologyBaseChange_of_isCompact H ℱ hg (W := ⊤)
    (by rw [Opens.coe_top]; exact isCompact_univ) n
  exact WithAction.bijective_baseChange_of_iso (baseAction f ℱ)
    (pushforwardPullbackAction f' g' ℱ) (toSheafUnit g' ℱ) (baseAction_comp_toSheafUnit H ℱ hg)
    (TopCat.Sheaf.freeSheafTopIso (X := X)) h

variable (f' g') in
/-- The action of `B = Γ(T, ⊤)` on the underlying abelian sheaf of `g'^* ℱ`, through `f'^♯`. -/
noncomputable abbrev pullbackAction :
    Γ(T, ⊤) →+* End ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pullback g').obj ℱ)) :=
  (smulRingHom ((pullback g').obj ℱ)).comp f'.appTop.hom

include H in
omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] [Flat g] [QuasiSeparated f] [QuasiCompact f] in
/-- `H^n(Y, g'^* ℱ) ≅ H^n(X, g'_* g'^* ℱ)` as `B`-modules, since `g'` is affine. -/
theorem nonempty_H_linearEquiv_pushforward (n : ℕ) :
    Nonempty (WithAction (pullbackAction f' g' ℱ) ((constantSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n ≃ₗ[Γ(T, ⊤)]
      WithAction (pushforwardPullbackAction f' g' ℱ) ((constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) n) := by
  have := isAffineHom_of_isPullback H
  obtain ⟨e⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom g' n
  let G := (pullback g').obj ℱ
  let F : (cechAcyclicOnAffines Y).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf Y.ringCatSheaf).obj G, cechAcyclicOnAffines_of_isQuasicoherent G⟩
  let ε : WithAction (pullbackAction f' g' ℱ) ((constantSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n ≃+
      WithAction (pushforwardPullbackAction f' g' ℱ) ((constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) n :=
    (e.app F).addCommGroupIsoToAddEquiv
  refine ⟨{ ε with map_smul' := fun b x ↦ ?_ }⟩
  have h := NatTrans.naturality_apply e.hom (ObjectProperty.homMk
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map (G.smulHom (f'.appTop b))) : F ⟶ F) x
  exact h

include H hg in
/-- **Cohomology and flat base change** (Stacks 02KH). Consider a cartesian square
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `B ⊗_A H^n(X, ℱ) ≅ H^n(Y, g'^* ℱ)` as
`B`-modules, where `A` acts on `H^n(X, ℱ)` through `f^♯` and `B` on `H^n(Y, g'^* ℱ)` through
`f'^♯`. It is the composite of the canonical base change map
`B ⊗_A H^n(X, ℱ) ⟶ H^n(X, g'_* g'^* ℱ)` (bijective by `bijective_cohomologyBaseChange`) and the
identification `H^n(X, g'_* g'^* ℱ) ≅ H^n(Y, g'^* ℱ)` for the affine morphism `g'`.

(blueprint: `lem-pc-flat-base-change-cohom`) -/
@[stacks 02KH]
theorem nonempty_H_baseChange_linearEquiv (n : ℕ) :
    Nonempty (Γ(T, ⊤) ⊗[Γ(S, ⊤)] WithAction (baseAction f ℱ) ((constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n
          ≃ₗ[Γ(T, ⊤)]
      WithAction (pullbackAction f' g' ℱ) ((constantSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n) := by
  obtain ⟨e⟩ := nonempty_H_linearEquiv_pushforward H ℱ n
  exact ⟨(LinearEquiv.ofBijective _ (bijective_cohomologyBaseChange H ℱ hg n)).trans e.symm⟩

end BaseChange

end AlgebraicGeometry.Scheme.Modules

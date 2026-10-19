/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Balanced K-flat models and the action of the second coefficient ring

Source: Stacks Project, More on Algebra, Section 06Y5 and Lemma 06Y6
(blueprint: lem-pc-balanced-derived-tensor-model).

The bifunctor `T` is characterized by the left-derived universal property in the `R`-complex
variable. Its value on `(M, R'[0])` is `M ⊗ᴸ_R R'` in `D(A)`. The unique model isomorphism is
specified by a compatibility equation with the resolution maps, rather than just by existence
of an unspecified isomorphism. Comparing any two models through this common value gives the
canonical comparison and its cocycle identity. The bifunctor and the naturality equation for
`α` express functoriality in `M`, including morphisms in `D(A)`.
-/

@[expose] public section

universe uB wA wR

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace DerivedCategory

set_option backward.isDefEq.respectTransparency false in
private theorem mixedTotalTensor_scalar
    (R A : Type uB) [CommRing R] [CommRing A] [Algebra R A]
    (M : CochainComplex (ModuleCat.{uB} A) ℤ)
    (F : CochainComplex (ModuleCat.{uB} R) ℤ) (r : R) :
    ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj M).map (r • 𝟙 F) =
      algebraMap R A r • 𝟙 (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj M).obj F) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [ModuleCat.mixedTotalTensor, Functor.map₂HomologicalComplex_obj_map,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    HomologicalComplex.smul_f_apply, Linear.comp_smul]
  have he : (ModuleCat.extendScalars (algebraMap R A)).map (r • 𝟙 (F.X q)) =
      algebraMap R A r • 𝟙 ((ModuleCat.extendScalars (algebraMap R A)).obj (F.X q)) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    simp only [ModuleCat.ExtendScalars.map_tmul]
    let : Algebra R A := (algebraMap R A).toAlgebra
    change (1 : A) ⊗ₜ[R] (r • x) =
      algebraMap R A r • ((1 : A) ⊗ₜ[R] x)
    rw [TensorProduct.tmul_smul]
    rfl
  have hm : ((ModuleCat.mixedTensor (algebraMap R A)).obj (M.X p)).map
      (r • 𝟙 (F.X q)) =
      algebraMap R A r • 𝟙 (((ModuleCat.mixedTensor (algebraMap R A)).obj (M.X p)).obj
        (F.X q)) := by
    change (MonoidalCategory.tensorLeft (M.X p)).map
      ((ModuleCat.extendScalars (algebraMap R A)).map (r • 𝟙 (F.X q))) = _
    rw [he, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, hm]
  simp only [Linear.smul_comp, Category.id_comp]
  rfl

private theorem homology_Q_scalar
    (A : Type uB) [CommRing A] [HasDerivedCategory.{wA} (ModuleCat.{uB} A)]
    (K : CochainComplex (ModuleCat.{uB} A) ℤ) (i : ℤ) (a : A) :
    (homologyFunctor (ModuleCat A) i).map (Q.map (a • 𝟙 K)) =
      a • 𝟙 ((homologyFunctor (ModuleCat A) i).obj (Q.obj K)) := by
  apply (cancel_mono ((homologyFunctorFactors (ModuleCat A) i).hom.app K)).1
  rw [homologyFunctorFactors_hom_naturality]
  have hh : HomologicalComplex.homologyMap (a • 𝟙 K) i =
      a • 𝟙 (K.homology i) := by
    unfold HomologicalComplex.homologyMap
    rw [show (HomologicalComplex.shortComplexFunctor _ _ i).map (a • 𝟙 K) =
      a • 𝟙 (K.sc i) from rfl]
    simp only [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  rw [hh]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem mixedDerivedTensor_scalar
    (R A : Type uB) [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{wA} (ModuleCat.{uB} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{uB} R)]
    (M : CochainComplex (ModuleCat.{uB} A) ℤ)
    (L : DerivedCategory (ModuleCat.{uB} R) ⥤ DerivedCategory (ModuleCat.{uB} A))
    (ε : Q ⋙ L ⟶ (ModuleCat.mixedTotalTensor (algebraMap R A)).obj M ⋙ Q)
    (hflat : ∀ F : CochainComplex (ModuleCat.{uB} R) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat F → IsIso (ε.app F))
    (i : ℤ) (F : CochainComplex (ModuleCat.{uB} R) ℤ) (r : R) :
    (homologyFunctor (ModuleCat A) i).map (L.map (Q.map (r • 𝟙 F))) =
      algebraMap R A r • 𝟙 ((homologyFunctor (ModuleCat A) i).obj (L.obj (Q.obj F))) := by
  let H := homologyFunctor (ModuleCat A) i
  let K := Q ⋙ L ⋙ H
  have hmodel (P : CochainComplex (ModuleCat.{uB} R) ℤ)
      (hP : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat P) :
      K.map (r • 𝟙 P) = algebraMap R A r • 𝟙 (K.obj P) := by
    have := hflat P hP
    apply (cancel_mono (H.map (ε.app P))).1
    have hn := congrArg H.map (ε.naturality (r • 𝟙 P))
    simp only [Functor.comp_map, H.map_comp] at hn
    change H.map (L.map (Q.map (r • 𝟙 P))) ≫ H.map (ε.app P) = _
    rw [hn, mixedTotalTensor_scalar R A M P r, homology_Q_scalar A _ i]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
    rfl
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{uB} R))).reduced
  let P := Λ.resolutionFunctor.obj F
  let s := Λ.resolutionNatTrans.app F
  have hs : QuasiIso s := inferInstance
  have hP : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat P :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le F
  have : IsIso (Q.map s) := (isIso_Q_map_iff_quasiIso (ModuleCat R) s).2 hs
  have : IsIso (K.map s) := by change IsIso (H.map (L.map (Q.map s))); infer_instance
  change K.map (r • 𝟙 F) = algebraMap R A r • 𝟙 (K.obj F)
  apply (cancel_epi (K.map s)).1
  rw [← K.map_comp]
  have hc : s ≫ (r • 𝟙 F) = (r • 𝟙 P) ≫ s := by simp
  rw [hc, K.map_comp, hmodel P hP]
  simp only [Linear.comp_smul, Linear.smul_comp]
  rfl

variable (R A R' : Type uB) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{wA} (ModuleCat.{uB} A)]
  [HasDerivedCategory.{wR} (ModuleCat.{uB} R)]

set_option quotPrecheck false in
local notation "S" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
set_option quotPrecheck false in
local notation "E" => (S).obj (ModuleCat.of R R')
set_option quotPrecheck false in
local notation "B" => ModuleCat.mixedTotalTensor (algebraMap R A)

/-- (blueprint: lem-pc-balanced-derived-tensor-model) Balanced K-flat models of the tensor
of an `A`-module complex with the `R`-algebra `R'`, with canonical comparisons, functoriality,
and the commuting coefficient actions on cohomology. Source: Stacks Project, Lemma 06Y6.

Proof (the DAG's four steps):
1. The given quasi-isomorphisms are K-flat resolutions over `A` and `R`, respectively
   (`def-pc-kflat-complex`, `lem-pc-kflat-resolution`, ordinary-module specialization).
2. `lem-pc-derived-tensor-second-factor-functor` computes the derived tensor using the
   K-flat `R`-complex `F`. Tensoring `P → M` with `F` is a quasi-isomorphism; the signed
   symmetry interchanges the two tensor factors (`def-pc-tensor-complex-sheaves`). Thus the
   total tensor is the required model in `D(A)`. K-flatness over `A` is not confused with
   K-flatness over `R`.
3. Apply that functor to multiplication by `b : R'`. Composition, identity and addition
   give the ring homomorphism `ρ`. Naturality with multiplication by `a : A` gives commuting
   endomorphisms. The induced actions on each cohomology module agree on `R`, and the
   tensor-product universal property gives the displayed `A ⊗_R R'` action.
4. The universal property and the K-flat computation give canonical comparison maps;
   both models compare to the same derived object, so comparisons satisfy the cocycle
   identity. Naturality in both variables gives functoriality and compatibility of the
   actions (`lem-pc-derived-tensor-second-factor-functor`, clauses (2) and (3)). -/
theorem exists_balancedDerivedTensorModel :
    ∃ T : DerivedCategory (ModuleCat.{uB} A) ⥤
        DerivedCategory (ModuleCat.{uB} R) ⥤ DerivedCategory (ModuleCat.{uB} A),
      ∃ α : ∀ M : CochainComplex (ModuleCat.{uB} A) ℤ,
          Q ⋙ T.obj (Q.obj M) ⟶ (B).obj M ⋙ Q,
        (∀ M, (T.obj (Q.obj M)).IsLeftDerivedFunctor (α M)
          (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ))) ∧
        (∀ M F, (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ)).kFlat F →
          IsIso ((α M).app F)) ∧
        (∀ (M N : CochainComplex (ModuleCat.{uB} A) ℤ) (g : M ⟶ N)
            (F : CochainComplex (ModuleCat.{uB} R) ℤ),
          (T.map (Q.map g)).app (Q.obj F) ≫ (α N).app F =
            (α M).app F ≫ Q.map (((B).map g).app F)) ∧
        (∀ (M P : CochainComplex (ModuleCat.{uB} A) ℤ) (q : P ⟶ M),
          QuasiIso q → (HomologicalComplex.quasiIso (ModuleCat.{uB} A) (.up ℤ)).kFlat P →
          ∀ (F : CochainComplex (ModuleCat.{uB} R) ℤ) (f : F ⟶ E),
            QuasiIso f → (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ)).kFlat F →
            ∃! e : Q.obj (((B).obj P).obj F) ≅ (T.obj (Q.obj M)).obj (Q.obj E),
              (α P).app F ≫ e.hom =
                (T.map (Q.map q)).app (Q.obj F) ≫ (T.obj (Q.obj M)).map (Q.map f)) ∧
        (∀ M : CochainComplex (ModuleCat.{uB} A) ℤ,
          ∃ ρ : R' →+* End ((T.obj (Q.obj M)).obj (Q.obj E)),
            (∀ b : R', ρ b = (T.obj (Q.obj M)).map
              (Q.map ((S).map (ModuleCat.ofHom (LinearMap.mulLeft R b))))) ∧
            (∀ (a : A) (b : R'),
              Commute (ρ b) ((T.map (Q.map (a • 𝟙 M))).app (Q.obj E))) ∧
            ∀ i : ℤ,
              let H := homologyFunctor (ModuleCat.{uB} A) i
              ∃ m : Module (A ⊗[R] R') (H.obj ((T.obj (Q.obj M)).obj (Q.obj E))),
                ∀ (a : A) (b : R') (x : H.obj ((T.obj (Q.obj M)).obj (Q.obj E))),
                  letI := m
                  (a ⊗ₜ[R] b) • x = a • (H.map (ρ b)).hom x) :=
  by
    classical
    let B' := (ModuleCat.mixedTensor (algebraMap R A)).flip.map₂CochainComplex
    obtain ⟨_, U, ε, hder, htri, hflat, _, _, hnat, _, _, hinv⟩ :=
      exists_derivedTensor_second_factor_functor (algebraMap R A)
    let e (M : CochainComplex (ModuleCat.{uB} A) ℤ) :
        B'.flip.obj M ≅ (B).obj M :=
      NatIso.ofComponents
        (fun F ↦ HomologicalComplex.mapBifunctorFlipIso M F
          (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ))
        (fun f ↦ HomologicalComplex.mapBifunctorFlipIso_hom_naturality
          (𝟙 M) f (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ))
    have hU : (HomologicalComplex.quasiIso (ModuleCat.{uB} A) (.up ℤ)).IsInvertedBy U := by
      intro M N q hq
      exact (hinv M N q hq).2
    let T := Localization.lift U hU (Q : CochainComplex (ModuleCat.{uB} A) ℤ ⥤ _)
    let δ := Localization.fac U hU (Q : CochainComplex (ModuleCat.{uB} A) ℤ ⥤ _)
    let α (M : CochainComplex (ModuleCat.{uB} A) ℤ) :=
      Functor.whiskerLeft Q (δ.hom.app M) ≫ ε M ≫ Functor.whiskerRight (e M).hom Q
    have hαflat (M : CochainComplex (ModuleCat.{uB} A) ℤ)
        (F : CochainComplex (ModuleCat.{uB} R) ℤ)
        (hF : (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ)).kFlat F) :
        IsIso ((α M).app F) := by
      have := hflat M F hF
      dsimp [α]
      infer_instance
    refine ⟨T, α, ?_, hαflat, ?_, ?_, ?_⟩
    · intro M
      let ε' := ε M ≫ Functor.whiskerRight (e M).hom Q
      have : (U.obj M).IsLeftDerivedFunctor ε'
          (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ)) := by
        rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
        have := (hder M).isRightKanExtension
        exact (Functor.isRightKanExtension_iff_of_iso₂ (ε M) ε'
          (Functor.isoWhiskerRight (e M) Q) (Iso.refl _) (by simp [ε'])).1 inferInstance
      exact (Functor.isLeftDerivedFunctor_iff_of_iso
        (LF := T.obj (Q.obj M)) (LF' := U.obj M) (α := α M) ε'
        (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ))
        (δ.app M) (by simp [α, ε'])).2 inferInstance
    · intro M N g F
      have hd := congrArg (fun t ↦ t.app (Q.obj F)) (δ.hom.naturality g)
      have he := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
        g (𝟙 F) (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ)
      dsimp [α]
      dsimp at hd
      simp only [Category.assoc]
      rw [← Category.assoc, hd, Category.assoc, ← Category.assoc _ ((ε N).app F),
        hnat M N g F]
      simp only [Category.assoc]
      rw [← Q.map_comp, ← Q.map_comp]
      exact congrArg (fun k ↦ (δ.hom.app M).app (Q.obj F) ≫
        (ε M).app F ≫ Q.map k) he
    · intro M P q hq hP F f hf hF
      have : IsIso ((α P).app F) := hαflat P F hF
      have : IsIso (Q.map q) := (isIso_Q_map_iff_quasiIso (ModuleCat A) q).2 hq
      have : IsIso (Q.map f) := (isIso_Q_map_iff_quasiIso (ModuleCat R) f).2 hf
      refine ⟨(asIso ((α P).app F)).symm ≪≫
        asIso ((T.map (Q.map q)).app (Q.obj F)) ≪≫
        asIso ((T.obj (Q.obj M)).map (Q.map f)), ?_, ?_⟩
      · simp
      · intro e he
        apply Iso.ext
        apply (cancel_epi ((α P).app F)).1
        simpa using he
    · intro M
      obtain ⟨c, hc⟩ := htri M
      let := c
      let := hc
      have : (U.obj M).Additive := inferInstance
      have : (T.obj (Q.obj M)).Additive :=
        Functor.additive_of_iso (δ.app M).symm
      let G := (S) ⋙ Q ⋙ T.obj (Q.obj M)
      let μ : R' →+* End (ModuleCat.of R R') :=
        { toFun := fun b ↦ ModuleCat.ofHom (LinearMap.mulLeft R b)
          map_one' := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact one_mul x
          map_mul' := fun b d ↦ by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact mul_assoc b d x
          map_zero' := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact zero_mul x
          map_add' := fun b d ↦ by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact add_mul b d x }
      let κ : End (ModuleCat.of R R') →+* End (G.obj (ModuleCat.of R R')) :=
        { G.mapEnd (ModuleCat.of R R') with
          map_zero' := G.map_zero _ _
          map_add' := fun _ _ ↦ G.map_add }
      let ρ := κ.comp μ
      refine ⟨ρ, (fun _ ↦ rfl), ?_, ?_⟩
      · intro a b
        exact ((T.map (Q.map (a • 𝟙 M))).naturality
          (Q.map ((S).map (ModuleCat.ofHom (LinearMap.mulLeft R b))))).symm
      · intro i
        let H := homologyFunctor (ModuleCat A) i
        let V := H.obj ((T.obj (Q.obj M)).obj (Q.obj E))
        let κH : End ((T.obj (Q.obj M)).obj (Q.obj E)) →+* End V :=
          { H.mapEnd ((T.obj (Q.obj M)).obj (Q.obj E)) with
            map_zero' := H.map_zero _ _
            map_add' := fun _ _ ↦ H.map_add }
        let φ : R' →+* Module.End A V :=
          (ModuleCat.endRingEquiv V).toRingHom.comp (κH.comp ρ)
        have hφ (r : R) : φ (algebraMap R R' r) =
            algebraMap A (Module.End A V) (algebraMap R A r) := by
          have hm : ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R R' r)) =
              r • 𝟙 (ModuleCat.of R R') := by
            ext x
            exact (Algebra.smul_def r x).symm
          have hs : (S).map (r • 𝟙 (ModuleCat.of R R')) = r • 𝟙 E := by
            rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
          change (H.map ((T.obj (Q.obj M)).map
            (Q.map ((S).map (ModuleCat.ofHom
              (LinearMap.mulLeft R (algebraMap R R' r))))))).hom = _
          rw [hm, hs]
          exact congrArg ModuleCat.Hom.hom
            (mixedDerivedTensor_scalar R A M (T.obj (Q.obj M)) (α M) (hαflat M) i E r)
        let : Algebra R (Module.End A V) :=
          Algebra.compHom (Module.End A V) (algebraMap R A)
        let : IsScalarTower R A (Module.End A V) :=
          IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
        let f : A →ₐ[R] Module.End A V := IsScalarTower.toAlgHom R A (Module.End A V)
        let g : R' →ₐ[R] Module.End A V := { φ with commutes' := hφ }
        let ψ := Algebra.TensorProduct.lift f g (fun a b ↦ Algebra.commutes a (g b))
        let m : Module (A ⊗[R] R') V := Module.compHom V ψ.toRingHom
        refine ⟨m, ?_⟩
        intro a b x
        change (ψ (a ⊗ₜ[R] b)) x = a • (H.map (ρ b)).hom x
        rw [Algebra.TensorProduct.lift_tmul]
        rfl

end DerivedCategory

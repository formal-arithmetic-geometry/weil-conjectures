/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
public import Sheaf.Paper.StrictPerfectCoefficientPackage
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
public import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-!
# Projection-formula arrows and their specified finite-total inverse

Source: Weil conjectures blueprint, proper base change, definition 1264
(blueprint: def-weil-pbc-projection-formula-arrows).
-/

@[expose] public section

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

namespace CategoryTheory

private theorem tensor_quasiIso_of_acyclicTensor
    {D : Type*} [Category D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasCoproducts D] (F : CochainComplex D ℤ)
    (hF : ∀ Z : CochainComplex D ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z F (curriedTensor D)).Acyclic)
    {K K' : CochainComplex D ℤ} (p : K ⟶ K') (hp : QuasiIso p) :
    QuasiIso (HomologicalComplex.mapBifunctorMap p (𝟙 F) (curriedTensor D) (.up ℤ)) := by
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic p).1 hp
  have ht := hF (CochainComplex.mappingCone p) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso p F (curriedTensor D))

private lemma quasiIso_pullback_snd
    {A : Type*} [Category A] [Abelian A]
    {P Q M : CochainComplex A ℤ} (q : P ⟶ M) [Epi q] [QuasiIso q] (p : Q ⟶ M) :
    QuasiIso (pullback.snd q p) := by
  let S : ShortComplex (CochainComplex A ℤ) :=
    ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hs : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have hk : (kernel q).Acyclic := hs.acyclic_X₁ inferInstance
  have ht := hs.pullback p
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz (i : ℤ) : IsZero ((kernel q).homology i) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hk i)
  have hm : Mono (HomologicalComplex.homologyMap (pullback.snd q p) n) :=
    (ht.homology_exact₂ n).mono_g ((hz n).eq_of_src _ _)
  have he : Epi (HomologicalComplex.homologyMap (pullback.snd q p) n) :=
    (ht.homology_exact₃ n (n + 1) (by simp)).epi_f ((hz (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _


private theorem extendIso_of_resolutions
    {D E : Type*} [Category D] [Abelian D] [Category E]
    (PR : ObjectProperty (CochainComplex D ℤ))
    (G T : CochainComplex D ℤ ⥤ E) (b : PR.ι ⋙ G ≅ PR.ι ⋙ T)
    (hres : ∀ K, ∃ (P : CochainComplex D ℤ) (_hp : PR P) (p : P ⟶ K),
      QuasiIso p ∧ Epi p)
    (hG : ∀ {X Y} (p : X ⟶ Y), QuasiIso p → IsIso (G.map p))
    (hT : ∀ {X Y} (p : X ⟶ Y), QuasiIso p → IsIso (T.map p))
    (A : CochainComplex D ℤ) :
    ∃! z : G.obj A ≅ T.obj A,
      ∀ (P : CochainComplex D ℤ) (hp : PR P) (p : P ⟶ A), QuasiIso p →
        G.map p ≫ z.hom = b.hom.app ⟨P, hp⟩ ≫ T.map p := by
  obtain ⟨P₀, hp₀, q, hq, he⟩ := hres A
  have := hq
  have := he
  have := hG q hq
  have := hT q hq
  let z : G.obj A ≅ T.obj A := (asIso (G.map q)).symm ≪≫ b.app ⟨P₀, hp₀⟩ ≪≫
    asIso (T.map q)
  have hz : G.map q ≫ z.hom = b.hom.app ⟨P₀, hp₀⟩ ≫ T.map q := by
    simp only [z, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      IsIso.hom_inv_id_assoc, Iso.app_hom]
  refine ⟨z, ?_, ?_⟩
  · intro P hp p _
    obtain ⟨W, hW, r, hr, _⟩ := hres (pullback q p)
    have hs := CategoryTheory.quasiIso_pullback_snd q p
    have := hr
    have := hs
    let v : W ⟶ P := r ≫ pullback.snd q p
    let w : W ⟶ P₀ := r ≫ pullback.fst q p
    have hv : QuasiIso v := by dsimp [v]; infer_instance
    have hw : w ≫ q = v ≫ p := by
      simp only [w, v, Category.assoc, pullback.condition]
    have := hG v hv
    have nat {X Y : CochainComplex D ℤ} (hX : PR X) (hY : PR Y) (f : X ⟶ Y) :
        G.map f ≫ b.hom.app ⟨Y, hY⟩ = b.hom.app ⟨X, hX⟩ ≫ T.map f :=
      b.hom.naturality (ObjectProperty.homMk (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) f)
    apply (cancel_epi (G.map v)).1
    calc
      G.map v ≫ (G.map p ≫ z.hom) = G.map w ≫ (G.map q ≫ z.hom) := by
        rw [← Category.assoc, ← G.map_comp, ← hw, G.map_comp, Category.assoc]
      _ = G.map w ≫ (b.hom.app ⟨P₀, hp₀⟩ ≫ T.map q) := by rw [hz]
      _ = b.hom.app ⟨W, hW⟩ ≫ T.map (w ≫ q) := by
        rw [← Category.assoc, nat hW hp₀ w, Category.assoc, ← T.map_comp]
      _ = b.hom.app ⟨W, hW⟩ ≫ T.map (v ≫ p) := by rw [hw]
      _ = G.map v ≫ (b.hom.app ⟨P, hp⟩ ≫ T.map p) := by
        rw [T.map_comp, ← Category.assoc, ← nat hW hp v, Category.assoc]
  · intro z' hz'
    apply Iso.ext
    apply (cancel_epi (G.map q)).1
    exact (hz' P₀ hp₀ q hq).trans hz.symm




variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) (V : B ⥤ A) [L.Additive] [V.Additive] (adj : L ⊣ V)
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)

/-- The ordinary counit mate t_{M,P}.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionMate (M : B) (P : A) :
    V.obj M ⊗ P ⟶ V.obj (M ⊗ L.obj P) :=
  adj.homEquiv _ _ ((e (V.obj M) P).hom ≫ (adj.counit.app M ⊗ₘ 𝟙 (L.obj P)))

omit [Abelian A] [Abelian B] [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts A] [HasCoproducts B] [L.Additive] [V.Additive] in
set_option backward.isDefEq.respectTransparency false in
private lemma tensorAdjunctionMate_naturality
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (M : B) {P Q : A} (f : P ⟶ Q) :
    (𝟙 (V.obj M) ⊗ₘ f) ≫ tensorAdjunctionMate L V adj e M Q =
      tensorAdjunctionMate L V adj e M P ≫ V.map (𝟙 M ⊗ₘ L.map f) := by
  unfold tensorAdjunctionMate
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  rw [← Category.assoc, he, L.map_id]
  simp only [Category.assoc]
  congr 1
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- For finite free coefficients the ordinary mate is the finite-product comparison.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: the unit equation reduces the mate in rank one to the identity by the
adjunction triangle identity. Naturality and additivity identify rank N with the
N-fold finite-sum map. Finite sums are products and the right adjoint preserves
products, including the empty product. Thus the comparison is invertible. -/
theorem tensorAdjunctionMate_free_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (N : ℕ) :
    IsIso (tensorAdjunctionMate L V adj e M (∏ᶜ fun _ : Fin N ↦ 𝟙_ A)) := by
  classical
  let T := tensorLeft (V.obj M)
  let U := L ⋙ tensorLeft M ⋙ V
  let t : T ⟶ U :=
    { app := tensorAdjunctionMate L V adj e M
      naturality := by
        intro P Q f
        simpa only [T, U, Functor.comp_map, tensorLeft, curriedTensor_obj_map, id_tensorHom] using
          tensorAdjunctionMate_naturality L V adj e he M f }
  have ht : t.app (𝟙_ A) ≫ V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom) =
      (ρ_ (V.obj M)).hom := by
    change tensorAdjunctionMate L V adj e M _ ≫ _ = _
    unfold tensorAdjunctionMate
    rw [← adj.homEquiv_naturality_right]
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    rw [← hj]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
      Category.id_comp]
    have hcomm : adj.counit.app M ⊗ₘ j.hom =
        (𝟙 (L.obj (V.obj M)) ⊗ₘ j.hom) ≫
          (adj.counit.app M ⊗ₘ 𝟙 (𝟙_ B)) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [hcomm]
    simp only [Category.assoc, tensorHom_id]
    rw [rightUnitor_naturality]
  have : IsIso (t.app (𝟙_ A)) := by
    have : IsIso (t.app (𝟙_ A) ≫ V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom)) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom))
  have hw : t.app (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ≫
      piComparison U (fun _ : Fin N ↦ 𝟙_ A) =
      piComparison T (fun _ : Fin N ↦ 𝟙_ A) ≫
        Limits.Pi.map (fun _ : Fin N ↦ t.app (𝟙_ A)) := by
    apply Pi.hom_ext
    intro k
    simp only [Category.assoc, piComparison_comp_π, Pi.map_π, piComparison_comp_π_assoc]
    exact (t.naturality (Pi.π (fun _ : Fin N ↦ 𝟙_ A) k)).symm
  have : IsIso (t.app (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ≫
      piComparison U (fun _ : Fin N ↦ 𝟙_ A)) := by
    rw [hw]
    infer_instance
  change IsIso (t.app _)
  exact IsIso.of_isIso_comp_right _ (piComparison U (fun _ : Fin N ↦ 𝟙_ A))

/-- The specified free inverse q_{M,N}, the inverse of t and not an arbitrary map.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionFreeInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (N : ℕ) :=
  @inv _ _ _ _ (tensorAdjunctionMate L V adj e M (∏ᶜ fun _ : Fin N ↦ 𝟙_ A))
    (tensorAdjunctionMate_free_isIso L V adj e he j hj M N)

/-- The displayed splitting formula for s_{a,r}, equally for any single retract.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionRetractInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (P : A) (N : ℕ)
    (i : P ⟶ ∏ᶜ fun _ : Fin N ↦ 𝟙_ A)
    (p : (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ⟶ P) :
    V.obj (M ⊗ L.obj P) ⟶ V.obj M ⊗ P :=
  V.map (𝟙 M ⊗ₘ L.map i) ≫ tensorAdjunctionFreeInverse L V adj e he j hj M N ≫
    (𝟙 (V.obj M) ⊗ₘ p)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorAdjunctionRetractInverse_identities
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (P : A) (N : ℕ)
    (i : P ⟶ ∏ᶜ fun _ : Fin N ↦ 𝟙_ A)
    (p : (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ⟶ P) (hip : i ≫ p = 𝟙 P) :
    tensorAdjunctionMate L V adj e M P ≫
        tensorAdjunctionRetractInverse L V adj e he j hj M P N i p = 𝟙 _ ∧
      tensorAdjunctionRetractInverse L V adj e he j hj M P N i p ≫
        tensorAdjunctionMate L V adj e M P = 𝟙 _ := by
  let := tensorAdjunctionMate_free_isIso L V adj e he j hj M N
  unfold tensorAdjunctionRetractInverse tensorAdjunctionFreeInverse
  constructor
  · rw [← Category.assoc, ← tensorAdjunctionMate_naturality L V adj e he M i]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [tensorHom_comp_tensorHom, hip, Category.id_comp, id_tensorHom_id]
  · simp only [Category.assoc]
    rw [tensorAdjunctionMate_naturality L V adj e he M p]
    rw [IsIso.inv_hom_id_assoc, ← V.map_comp, tensorHom_comp_tensorHom,
      ← L.map_comp, hip, L.map_id, Category.id_comp, id_tensorHom_id, V.map_id]

/-- The chain mate whose degree maps are the sums of the ordinary t_{I^a,F^r}.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionTotal
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      F (curriedTensor A) ⟶
    (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor I ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (curriedTensor B)) := by
  letI := tensorPullbackTotal_isIso L e he V adj
    ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _
    (inv (tensorPullbackTotal L e he
      ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F) ≫
        HomologicalComplex.mapBifunctorMap
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)
          (𝟙 ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
          (curriedTensor B) (ComplexShape.up ℤ))

private noncomputable def restrictCofanIsColimit
    {D : Type*} [Category D] [HasZeroMorphisms D] {J : Type*} {f : J → D}
    (c : Cofan f) (hc : IsColimit c) (s : J → Prop)
    (hz : ∀ j, ¬s j → IsZero (f j)) :
    IsColimit (Cofan.mk c.pt (fun j : Subtype s ↦ c.inj j.val)) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc hc
      (fun j ↦ if hj : s j then t.inj ⟨j, hj⟩ else 0)) ?_ ?_
  · intro t j
    change c.inj j.val ≫ _ = t.inj j
    simpa only [dif_pos j.property] using
      Cofan.IsColimit.fac hc
        (fun j ↦ if hj : s j then t.inj ⟨j, hj⟩ else 0) j.val
  · intro t m hm
    apply Cofan.IsColimit.hom_ext hc
    intro j
    rw [Cofan.IsColimit.fac]
    by_cases hj : s j
    · rw [dif_pos hj]
      exact hm ⟨j, hj⟩
    · exact (hz j hj).eq_of_src _ _

private noncomputable def extendCofanIsColimitOfZeroOutside
    {D : Type*} [Category D] [HasZeroMorphisms D] {J : Type*} {f : J → D}
    (c : Cofan f) (s : J → Prop)
    (hc : IsColimit (Cofan.mk c.pt (fun j : Subtype s ↦ c.inj j.val)))
    (hz : ∀ j, ¬s j → IsZero (f j)) : IsColimit c := by
  refine Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc hc (fun j ↦ t.inj j.val)) ?_ ?_
  · intro t j
    by_cases hj : s j
    · exact Cofan.IsColimit.fac hc (fun j ↦ t.inj j.val) ⟨j, hj⟩
    · exact (hz j hj).eq_of_src _ _
  · intro t m hm
    apply Cofan.IsColimit.hom_ext hc
    intro j
    rw [Cofan.IsColimit.fac]
    exact hm j.val

private lemma inverse_summand
    {D : Type*} [Category D] {X Y P Q : D} (t : X ⟶ Y) [IsIso t]
    (a : P ⟶ Q) (q : Q ⟶ P) (i : P ⟶ X) (j : Q ⟶ Y)
    (ht : i ≫ t = a ≫ j) (hq : q ≫ a = 𝟙 Q) : j ≫ inv t = q ≫ i := by
  apply (cancel_mono t).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ht]
  rw [← Category.assoc, hq, Category.id_comp]

private lemma isIso_of_cofans
    {D : Type*} [Category D] {J : Type*} {X Y : J → D}
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (t : c.pt ⟶ d.pt) (a : ∀ j, X j ⟶ Y j) [∀ j, IsIso (a j)]
    (ht : ∀ j, c.inj j ≫ t = a j ≫ d.inj j) : IsIso t := by
  let s := Cofan.IsColimit.desc hd (fun j ↦ inv (a j) ≫ c.inj j)
  have hs (j : J) : d.inj j ≫ s = inv (a j) ≫ c.inj j :=
    Cofan.IsColimit.fac hd _ j
  refine ⟨s, Cofan.IsColimit.hom_ext hc _ _ (fun j ↦ ?_),
    Cofan.IsColimit.hom_ext hd _ _ (fun j ↦ ?_)⟩
  · rw [← Category.assoc, ht, Category.assoc, hs,
      IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [← Category.assoc, hs, Category.assoc, ht,
      IsIso.inv_hom_id_assoc, Category.comp_id]

private noncomputable def mapCofanIsColimit_finiteSupport
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    {J : Type*} {f : J → D} (V : D ⥤ E) [V.Additive]
    (c : Cofan f) (hc : IsColimit c) (s : J → Prop) [Finite (Subtype s)]
    (hz : ∀ j, ¬s j → IsZero (f j)) :
    IsColimit (Cofan.mk (V.obj c.pt) (fun j ↦ V.map (c.inj j))) := by
  let hr := restrictCofanIsColimit c hc s hz
  let hv := isColimitCofanMkObjOfIsColimit V _ _ hr
  exact extendCofanIsColimitOfZeroOutside _ s hv (fun j hj ↦ V.map_isZero (hz j hj))

set_option backward.isDefEq.respectTransparency false in
private lemma tensorAdjunctionTotal_summand
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (a r n : ℤ) (h : a + r = n) :
    CochainComplex.ιMapBifunctor
        ((V.mapHomologicalComplex (.up ℤ)).obj I) F (curriedTensor A) a r n h ≫
        (tensorAdjunctionTotal L V adj e he I F).f n =
      tensorAdjunctionMate L V adj e (I.X a) (F.X r) ≫
        V.map (CochainComplex.ιMapBifunctor I
          ((L.mapHomologicalComplex (.up ℤ)).obj F) (curriedTensor B) a r n h) := by
  let P := (V.mapHomologicalComplex (.up ℤ)).obj I
  let LF := (L.mapHomologicalComplex (.up ℤ)).obj F
  let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
  let β := tensorPullbackTotal L e he P F
  let := tensorPullbackTotal_isIso L e he V adj P F
  have hb : L.map (CochainComplex.ιMapBifunctor P F (curriedTensor A) a r n h) ≫
      (inv β).f n = (e (P.X a) (F.X r)).hom ≫
        CochainComplex.ιMapBifunctor LP LF (curriedTensor B) a r n h := by
    apply (cancel_mono (β.f n)).1
    simp only [Category.assoc, ← HomologicalComplex.comp_f, IsIso.inv_hom_id,
      HomologicalComplex.id_f]
    change _ = _ ≫ _ ≫ tensorPullbackTotalComponent L e P F n
    simp only [tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc,
      Iso.hom_inv_id_assoc]
    exact Category.comp_id _
  change _ ≫ adj.homEquiv _ _ ((inv β).f n ≫
    (HomologicalComplex.mapBifunctorMap
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) (𝟙 LF)
        (curriedTensor B) (.up ℤ)).f n) = _
  unfold tensorAdjunctionMate
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  rw [← Category.assoc, hb, Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, Adjunction.mapHomologicalComplex_counit_app_f,
    curriedTensor_map_app, curriedTensor_obj_map, Category.assoc, tensorHom_def]
  rfl


attribute [local irreducible] tensorAdjunctionTotal

/-- Bounded split-free coefficients make the total mate an isomorphism of complexes.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: in bidegree (a,r) the splitting formula is inverse to t. The two identities
follow by naturality of t at i_r,p_r, their splitting relation, and the inverse
identities of q. Multiplying naturality by these inverses proves compatibility
with each differential; their indices agree and so do the signs (-1)^a.
There are finitely many nonzero summands in each degree. The right adjoint preserves
these finite sums, so the degree maps of the total mate are invertible. -/
theorem tensorAdjunctionTotal_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :
    IsIso (tensorAdjunctionTotal L V adj e he I F) := by
  classical
  let LF := (L.mapHomologicalComplex (.up ℤ)).obj F
  let P := (V.mapHomologicalComplex (.up ℤ)).obj I
  let C := CochainComplex.mapBifunctor P F (curriedTensor A)
  let D := CochainComplex.mapBifunctor I LF (curriedTensor B)
  let t := tensorAdjunctionTotal L V adj e he I F
  obtain ⟨lo, hi, hF⟩ := hbounded
  have hv (n : ℤ) : IsColimit (Cofan.mk (V.obj (D.X n))
      (fun x : {x : ℤ × ℤ // x.1 + x.2 = n} ↦
        V.map (CochainComplex.ιMapBifunctor I LF (curriedTensor B)
          x.val.1 x.val.2 n x.property))) := by
    let s : {x : ℤ × ℤ // x.1 + x.2 = n} → Prop :=
      fun x ↦ lo ≤ x.val.2 ∧ x.val.2 ≤ hi
    have : Finite (Subtype s) := by
      apply Finite.of_injective
        (fun x : Subtype s ↦ (⟨x.val.val.2, x.property⟩ : Set.Icc lo hi))
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · have h := congrArg Subtype.val hxy
        have hx := x.val.property
        have hy := y.val.property
        dsimp at h hx hy ⊢
        omega
      · exact congrArg Subtype.val hxy
    apply mapCofanIsColimit_finiteSupport V _
      (GradedObject.isColimitCofanMapObj
        ((((curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj I).obj
          LF).toGradedObject _ n) s
    intro x hx
    have hz : IsZero (F.X x.val.2) := hF _ (by
      dsimp [s] at hx
      omega)
    exact (tensorLeft (I.X x.val.1)).map_isZero (L.map_isZero hz)
  have (n : ℤ) : IsIso (t.f n) := by
    let a (x : {x : ℤ × ℤ // x.1 + x.2 = n}) :=
      tensorAdjunctionMate L V adj e (I.X x.val.1) (F.X x.val.2)
    have (x : {x : ℤ × ℤ // x.1 + x.2 = n}) : IsIso (a x) := by
      let q := tensorAdjunctionRetractInverse L V adj e he j hj
        (I.X x.val.1) (F.X x.val.2) (N x.val.2) (i x.val.2) (p x.val.2)
      obtain ⟨h₁, h₂⟩ := tensorAdjunctionRetractInverse_identities L V adj e he j hj
        (I.X x.val.1) (F.X x.val.2) (N x.val.2) (i x.val.2) (p x.val.2)
        (hsplit x.val.2)
      exact ⟨q, h₁, h₂⟩
    apply isIso_of_cofans _
      (GradedObject.isColimitCofanMapObj
        ((((curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj
          F).toGradedObject _ n) _ (hv n) (t.f n) a
    intro x
    exact tensorAdjunctionTotal_summand L V adj e he I F x.val.1 x.val.2 n x.property
  exact HomologicalComplex.Hom.isIso_of_components t

/-- The finite-total chain inverse, determined uniquely by the forward chain map.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionTotalInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :=
  @inv _ _ _ _ (tensorAdjunctionTotal L V adj e he I F)
    (tensorAdjunctionTotal_isIso L V adj e he j hj I F hbounded N i p hsplit)

attribute [local irreducible] tensorAdjunctionTotalInverse

/-- The inverse just constructed has exactly the summand formula required by definition 1264.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: precompose the total inverse identity with the (a,r) coprojection.
The ordinary retract formula is inverse to the corresponding t. Cancel that
invertible t; the remaining equality is the displayed summand formula. The
finite-product identification for V is characterized by these same coprojections. -/
theorem tensorAdjunctionTotalInverse_summand
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) (a r n : ℤ) (h : a + r = n) :
    V.map (CochainComplex.ιMapBifunctor I
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) (curriedTensor B) a r n h) ≫
        (tensorAdjunctionTotalInverse L V adj e he j hj I F hbounded N i p hsplit).f n =
      tensorAdjunctionRetractInverse L V adj e he j hj (I.X a) (F.X r) (N r) (i r) (p r) ≫
        CochainComplex.ιMapBifunctor
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) F (curriedTensor A) a r n h :=
  by
    let t := tensorAdjunctionTotal L V adj e he I F
    let := tensorAdjunctionTotal_isIso L V adj e he j hj I F hbounded N i p hsplit
    unfold tensorAdjunctionTotalInverse
    rw [HomologicalComplex.Hom.inv_f_apply]
    exact inverse_summand (t.f n) _ _ _ _
      (tensorAdjunctionTotal_summand L V adj e he I F a r n h)
      (tensorAdjunctionRetractInverse_identities L V adj e he j hj
        (I.X a) (F.X r) (N r) (i r) (p r) (hsplit r)).2

set_option linter.unusedSectionVars false in
/-- The target tensor total is K-injective for the specified bounded split-free package.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: additivity transports the bounded support and each splitting through L.
The unit isomorphism j and finite-sum preservation identify L of a finite free
object with a finite free object. Hence L(F) is bounded split-free. Dualize its
finite free retracts termwise: evaluation identifies tensoring with L(F) with
Hom from its bounded dual, with the usual signed differential. That dual is
K-flat. Hom from a K-flat complex into K is K-injective, yielding the claim
(lem-weil-pbc-split-perfect-tensor-kinjective). -/
theorem tensorAdjunctionTotal_target_isKInjective
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (K : CochainComplex B ℤ) (hK : K.IsKInjective) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :
    (CochainComplex.mapBifunctor K
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) (curriedTensor B)).IsKInjective  := by
  classical
  let Q := HomotopyCategory.quotient B (.up ℤ)
  let T := ((curriedTensor B).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)).obj (Q.obj K)
  let O := (HomotopyCategory.subcategoryAcyclic B).rightOrthogonal
  let H := HomotopyCategory.singleFunctor B 0 ⋙ T
  have hunit : O (H.obj (𝟙_ B)) := by
    let e : H.obj (𝟙_ B) ≅ Q.obj K :=
      Q.mapIso (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor B) (𝟙_ B) K ≪≫
        (NatIso.mapHomologicalComplex (rightUnitorNatIso B) (.up ℤ)).app K ≪≫
        (Functor.mapHomologicalComplexIdIso B (.up ℤ)).app K)
    exact O.prop_of_iso e.symm ((CochainComplex.isKInjective_iff_rightOrthogonal K).1 hK)
  have hterm (r : ℤ) : O (H.obj (L.obj (F.X r))) := by
    let G := L ⋙ H
    have hG : O (G.obj (𝟙_ A)) :=
      O.prop_of_iso (H.mapIso j).symm hunit
    have hfree : O (G.obj (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)) := by
      intro X f hX
      apply (cancel_mono (piComparison G (fun _ : Fin (N r) ↦ 𝟙_ A))).1
      apply Pi.hom_ext
      intro k
      simp only [Category.assoc, piComparison_comp_π, zero_comp]
      exact hG _ hX
    let ri : Retract (G.obj (F.X r))
        (G.obj (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)) :=
      (⟨i r, p r, hsplit r⟩ : Retract _ _).map G
    intro X f hX
    calc
      f = (f ≫ ri.i) ≫ ri.r := by
        rw [Category.assoc, ri.retract]
        exact (Category.comp_id f).symm
      _ = 0 := by
        have hf : f ≫ ri.i = 0 := hfree (f ≫ ri.i) hX
        rw [hf, zero_comp]
  let LF : CochainComplex B ℤ := (L.mapHomologicalComplex (.up ℤ)).obj F
  obtain ⟨a, b, hb⟩ := hbounded
  have : LF.IsStrictlyGE a := (LF.isStrictlyGE_iff a).2
    (fun n hn ↦ L.map_isZero (hb n (Or.inl hn)))
  have : LF.IsStrictlyLE b := (LF.isStrictlyLE_iff b).2
    (fun n hn ↦ L.map_isZero (hb n (Or.inr hn)))
  have hh := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (O.inverseImage T) LF a b (fun n _ _ ↦ hterm n)
  exact (CochainComplex.isKInjective_iff_rightOrthogonal _).2 hh


end CategoryTheory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- The uncurried presentation of the existing right-adjoint projection map.
This only transports the bifunctor interface; the mate itself is the upstream
`CategoryTheory.Adjunction.rightAdjointProjectionMap`.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def derivedProjectionFormulaMate
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (E : B) (F : A) :
    TR.obj (V.obj E, F) ⟶ V.obj (TS.obj (E, L.obj F)) :=
  ((adj.rightAdjointProjectionMap (T_C := Functor.curry.obj TS)
    (T_D := Functor.curry.obj TR)
    (Functor.curry.map alpha.hom ≫ (Functor.curryObjProdComp L L TS).hom)).app E).app F

/-- The derived free-coefficient inverse rho_N, inverting the specified projection mate.
The isomorphism instance is the finite-sum identification, proved from preservation
of finite products in the free-coefficient case.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def derivedProjectionFormulaFreeInverse
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (E : B) (Free : A)
    [IsIso (derivedProjectionFormulaMate L V adj TR TS alpha E Free)] :
    V.obj (TS.obj (E, L.obj Free)) ⟶ TR.obj (V.obj E, Free) :=
  inv (derivedProjectionFormulaMate L V adj TR TS alpha E Free)

/-- The displayed derived splitting formula rho_{F^r}.
At a sheaf coefficient term the objects and maps here are their degree-zero
images in the derived category. The formula has no arbitrary inverse-map argument.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def derivedProjectionFormulaRetractInverse
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS) (E : B) (P Free : A)
    (i : P ⟶ Free) (p : Free ⟶ P)
    [IsIso (derivedProjectionFormulaMate L V adj TR TS alpha E Free)] :
    V.obj (TS.obj (E, L.obj P)) ⟶ TR.obj (V.obj E, P) :=
  V.map (TS.map (CategoryTheory.Prod.mkHom (𝟙 E) (L.map i))) ≫
    derivedProjectionFormulaFreeInverse L V adj TR TS alpha E Free ≫
      TR.map (CategoryTheory.Prod.mkHom (𝟙 (V.obj E)) p)

end CategoryTheory

private lemma finitePower_isDualizable
    {D : Type*} [Category D] [Preadditive D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (U : D) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∏ᶜ fun _ : Fin n ↦ U) := by
  let : HasBinaryBiproducts D := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∏ᶜ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∏ᶜ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift fun i : Fin n ↦ Pi.π _ i.succ)
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e

attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency true

set_option synthInstance.maxSize 2048

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
  (PR : ObjectProperty (CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ))
  (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
  (TR : DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) × DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
  (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
    ((@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) _ (monoidalCategory R)).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
        ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)



include hPR in
set_option backward.isDefEq.respectTransparency true in
set_option synthInstance.maxSize 2048 in
/-- The canonical tensor representative when just the coefficient factor is K-flat.
The square specifies the comparison on every K-flat resolution of the first factor.
Source: definition 1264, the displayed representations C and J
(blueprint: def-weil-pbc-projection-formula-arrows).
Proof: choose a K-flat flat-term resolution P to A. Since F is K-flat, total tensor
of that resolution with F is a quasi-isomorphism. Compose the inverse representative
comparison rR with its image under Q and the inverse image of the resolution under
TR. Common refinements of resolutions and naturality of rR give the stated square
for every resolution. Its left factor is invertible, so it also proves uniqueness. -/
theorem mixedTensorRepresentative_existsUnique
    (A F : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hf : PR F) :
    ∃! z : TR.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor A F (@curriedTensor (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _ (monoidalCategory R))),
      ∀ (P : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hp : PR P) (p : P ⟶ A), QuasiIso p →
        TR.map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
          (𝟙 (DerivedCategory.Q.obj F))) ≫ z.hom =
          (rR.inv.app (⟨P, hp⟩, ⟨F, hf⟩)) ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap p (𝟙 F)
              (@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ (monoidalCategory R)) (ComplexShape.up ℤ)) := by
  classical
  let M := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let : MonoidalCategory M := SheafOfModules.monoidalCategory R
  let : MonoidalPreadditive M := SheafOfModules.ringedTensorPreadditive R
  have hres (K : CochainComplex M ℤ) :
      ∃ (P : CochainComplex M ℤ) (hp : PR P) (p : P ⟶ K), QuasiIso p ∧ Epi p := by
    obtain ⟨P, p, hk, ht, hq, he⟩ := CochainComplex.exists_isKFlatResolutionGeneral K
    exact ⟨P, (hPR P).2 ⟨hk, ht⟩, p, hq, HomologicalComplex.epi_of_epi_f p he⟩
  have htensor {K K' : CochainComplex M ℤ} (p : K ⟶ K') (hp : QuasiIso p) :
      QuasiIso (HomologicalComplex.mapBifunctorMap p (𝟙 F)
        ((@curriedTensor M _ (monoidalCategory R))) (.up ℤ)) := by
    exact CategoryTheory.tensor_quasiIso_of_acyclicTensor F ((hPR F).1 hf).1 p hp
  let G : CochainComplex M ℤ ⥤ DerivedCategory M :=
    { obj := fun X ↦ TR.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj F)
      map := fun p ↦ TR.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 _))
      map_id := fun X ↦ by simp
      map_comp := fun f g ↦ by simp [← Functor.map_comp] }
  let : ∀ (K K' : CochainComplex M ℤ),
      HomologicalComplex.HasMapBifunctor K K' (curriedTensor M) (.up ℤ) :=
    fun K K' ↦ inferInstance
  let T : CochainComplex M ℤ ⥤ DerivedCategory M :=
    ((curriedTensor M).map₂CochainComplex.flip.obj F) ⋙ DerivedCategory.Q
  let b : PR.ι ⋙ G ≅ PR.ι ⋙ T := NatIso.ofComponents
    (fun X ↦ (rR.app (X, ⟨F, hf⟩)).symm) (by
      intro X Y f
      have hn := rR.inv.naturality (Prod.mkHom f (𝟙 (⟨F, hf⟩ : PR.FullSubcategory)))
      simpa only [G, T, Functor.comp_map, Functor.prod_map, Functor.prod_obj,
        ObjectProperty.ι_obj, ObjectProperty.ι_map, Functor.uncurry_obj_map,
        ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id,
        Category.comp_id, Functor.flip_obj_map, Iso.symm_hom, Iso.app_inv] using hn)
  have hG {X Y : CochainComplex M ℤ} (p : X ⟶ Y) (hp : QuasiIso p) :
      IsIso (G.map p) := by
    have : IsIso (DerivedCategory.Q.{w}.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso M p).2 hp
    change IsIso (TR.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 _)))
    have : IsIso (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F))) :=
      (isIso_prod_iff _ _).2 ⟨by assumption, by infer_instance⟩
    infer_instance
  have hT {X Y : CochainComplex M ℤ} (p : X ⟶ Y) (hp : QuasiIso p) :
      IsIso (T.map p) := by
    change IsIso (DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap p (𝟙 F) (curriedTensor M) (.up ℤ)))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso M _).2 (htensor p hp)
  exact CategoryTheory.extendIso_of_resolutions PR G T b hres hG hT A

set_option synthInstance.maxSize 2048 in
/-- The mixed tensor comparison is chosen from a unique, fully specified representative square.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def mixedTensorRepresentative
    (A F : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hf : PR F) :=
  Classical.choose (mixedTensorRepresentative_existsUnique R PR hPR TR rR A F hf).exists


set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- A bounded strict-perfect package is K-flat with flat terms.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: each term is a retract of its finite free sheaf by the package splitting.
Tensoring it is a retract of a finite sum of the identity functor, hence exact.
Thus each term is flat. The bounded-above flat K-flat theorem applies to the upper
bound supplied by boundedness, giving the first conclusion. -/
theorem StrictPerfectCoefficientPackage.isKFlat_flat
    (F : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (P : StrictPerfectCoefficientPackage ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R) F)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    F.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (F.X n).IsFlat := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := ringedTensorPreadditive R
  let := SheafOfModules.monoidalClosed (R := R)
  have hflat (n : ℤ) : (F.X n).IsFlat := by
    let M := SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    let : HasFiniteBiproducts M := HasFiniteBiproducts.of_hasFiniteProducts
    have hd : IsDualizable (∏ᶜ fun _ : Fin (P.N n) ↦ 𝟙_ M) :=
      finitePower_isDualizable _ isDualizable_unit _
    have ht : ObjectProperty.flat (F.X n) :=
      ObjectProperty.flat_of_retract ⟨P.i n, P.p n, P.splitting n⟩
        (ObjectProperty.flat_of_isDualizable hd)
    exact ht.2
  refine ⟨?_, hflat⟩
  obtain ⟨a, b, hb⟩ := hbounded
  exact CochainComplex.isKFlat_of_boundedAbove_flat F
    ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩ hflat

end SheafOfModules

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- The definition keeps all ordinary and derived representative identifications explicit.
/-- The pair (pi,rho) of definition 1264 on arbitrary small ringed sites.
Source: proper base change, definition 1264
(blueprint: def-weil-pbc-projection-formula-arrows).
The site morphism is uInv adjoint to uPush, with inverse-image lift I and ring map c.
The object and map equations specify ordinary module pullback uStar; am is its ordinary
module adjunction. LF,epsilon,computeL specify derived pullback; TR,TS,rR,rS specify
derived tensor. RF,eta,hRF,computeR specify the K-injective total right derived functor.
canonicalAdj fixes the derived adjunction from the ordinary one on K-injective objects.
P is the degreewise splitting package and hbounded is its finite support. K with repE
is the chosen K-injective representative. None of the ordinary or derived comparisons
is an arbitrary natural isomorphism: k has its generalized pure-tensor characterization,
alpha is selected from its unique representative square, and both mixed tensor
representatives are selected from unique resolution squares.
The first component is the explicit counit mate. The second is Q(s) between the canonical
representatives C and B. s is the inverse of the finite-total ordinary mate; the theorem
tensorAdjunctionTotalInverse_summand states its precise splitting formula on every (a,r)
summand, hence identifies it with the finite-total chain map specified in the source.
The inverse is determined uniquely, so no unconstrained data is chosen from existence. -/
noncomputable def ringedProjectionFormulaArrows
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V)
    [V.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)))
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : ∀ G : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)),
      Function.Bijective (fun b : RF ⟶ G ↦ eta ≫ Functor.whiskerLeft DerivedCategory.Qh b))
    (computeR : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      IsIso (derivedPushforwardComplexComparison V RF eta K))
    (computeL : ∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        IsIso (derivedPullbackComplexComparison uStar LF epsilon P))
    (adjD : LF ⊣ RF)
    (canonicalAdj : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      LF.map (derivedPushforwardComplexComparison V RF eta K) ≫
          adjD.counit.app (DerivedCategory.Q.obj K) =
        derivedPullbackComplexComparison uStar LF epsilon
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((am.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))) (K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ) (hK : K.IsKInjective)
    (repE : E ≅ DerivedCategory.Q.obj K)
    (F : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ)
    (P : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) F)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    (TR.obj (RF.obj E, DerivedCategory.Q.obj F) ⟶
      RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F)))) ×
    (RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) ⟶
      TR.obj (RF.obj E, DerivedCategory.Q.obj F)) := by
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  have _ := hRF
  have _ := canonicalAdj
  let hf := StrictPerfectCoefficientPackage.isKFlat_flat R F P hbounded
  let hfR : PR F := (hPR F).mpr hf
  let A := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let pullF := (uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let J := CochainComplex.mapBifunctor K pullF (curriedTensor (SheafOfModules.{u} ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
  let hfS : PS pullF := (hPS pullF).mpr
    ((ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
      hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).1 F hf.1 hf.2)
  let unitData := canonicalRingedTensorComparison_unit R S RI uInv I c uStar hobj hmap k
  let j := Classical.choose unitData.exists
  have hj := (Classical.choose_spec unitData.exists)
  let s := tensorAdjunctionTotalInverse uStar V am k.mu k.naturality j hj K F
    hbounded P.N P.i P.p P.splitting
  let eF : LF.obj (DerivedCategory.Q.obj F) ≅ DerivedCategory.Q.obj pullF :=
    @asIso _ _ _ _ (derivedPullbackComplexComparison uStar LF epsilon F)
      (computeL F hf.1 hf.2)
  let eA : RF.obj E ≅ DerivedCategory.Q.obj A := RF.mapIso repE ≪≫
    (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta K) (computeR K hK)).symm
  let eC : TR.obj (RF.obj E, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A F (curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) :=
    TR.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj F))) ≪≫
      mixedTensorRepresentative R PR hPR TR rR A F hfR
  have hJ : J.IsKInjective := tensorAdjunctionTotal_target_isKInjective uStar j K hK F
    hbounded P.N P.i P.p P.splitting
  let eB : RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) ≅
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    RF.mapIso (TS.mapIso (Iso.prod repE eF) ≪≫
      mixedTensorRepresentative S PS hPS TS rS K pullF hfS) ≪≫
        (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta J) (computeR J hJ)).symm
  let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
  exact ⟨derivedProjectionFormulaMate LF RF adjD TR TS alpha E (DerivedCategory.Q.obj F),
    eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv⟩

end SheafOfModules

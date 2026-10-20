/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.CondensedCoefficientIsoConstructible
import Sheaf.Paper.ConstructibleCompactness
import Sheaf.Paper.IntegralConstructibleCompactness
import Sheaf.Paper.IntegralConstructibleExt
import Sheaf.SixFunctors.FiniteCompactProetale
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# A small skeleton of constructible finite-Tor complexes generates its localizing closure

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-brown-hypotheses,
sk-lem-brown-hypotheses-generation.md and its proof
(blueprint: det-brown-hypotheses-generation).

Compactness is the explicit canonical map of `CategoryTheory.IsCompactObject`, written
in the ambient ordinary derived category. The closure is full and its coproducts are
ambient coproducts by `localizingClosure_exists`, so this is precisely compactness inside
the closure. Index types use the fixed small universe `u + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProEtale

open scoped CategoryTheory.Obj ZeroObject

namespace WeilConjectures

private theorem localizingClosure_detectsZero
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) (K : C) (hK : localizingClosure S K)
    (h : ∀ (M : C), S M → ∀ n : ℤ, Subsingleton (M⟦n⟧ ⟶ K)) :
    Nonempty (K ≅ 0) := by
  let P := (ObjectProperty.singleton K).shiftClosure ℤ
  have hP : IsLocalizingSubcategory P.leftOrthogonal := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I F hF hFP
    dsimp only
    let _ := hF
    intro Y f hY
    apply colimit.hom_ext
    intro j
    cases j with
    | mk j => simpa using hFP j (colimit.ι F (Discrete.mk j) ≫ f) hY
  have hSP : S ≤ P.leftOrthogonal := by
    intro M hM Y f hY
    obtain ⟨Z, n, e, hZ⟩ := hY
    have hZK : K = Z := (ObjectProperty.singleton_iff K Z).mp hZ
    subst Z
    obtain ⟨a, ha⟩ := ((shiftEquiv C n).symm.toAdjunction.homEquiv M K).surjective
      (f ≫ e.hom)
    have ha0 : a = 0 := (h M hM (-n)).elim _ _
    rw [ha0] at ha
    have hf : f ≫ e.hom = 0 := by
      simpa [Adjunction.homEquiv_unit] using ha.symm
    exact (cancel_mono e.hom).mp (by simpa using hf)
  have hKK : (𝟙 K : K ⟶ K) = 0 :=
    hK P.leftOrthogonal hP hSP (𝟙 K)
      ((ObjectProperty.singleton K).le_shiftClosure K (by simp))
  exact ⟨((IsZero.iff_id_eq_zero K).mpr hKK).isoZero⟩

open Classical in
private theorem ambientCompactness_of_full
    {C : Type v} [Category.{w} C] [Preadditive C]
    (P : ObjectProperty C) [HasCoproducts.{u} P.FullSubcategory]
    (M : P.FullSubcategory) (hM : IsCompactObject.{u} M)
    (I : Type u) (E : I → C) [HasCoproduct E]
    (hE : ∀ i : I, P (E i)) (hsum : P (∐ E)) :
    Function.Bijective
      (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp M.obj (Sigma.ι E i)) :
        (⨁ i : I, (M.obj ⟶ E i)) →+ (M.obj ⟶ ∐ E)) := by
  classical
  let EF : I → P.FullSubcategory := fun i ↦ ⟨E i, hE i⟩
  let c : Cofan EF := Cofan.mk ⟨∐ E, hsum⟩
    (fun i ↦ ObjectProperty.homMk (Sigma.ι E i))
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk _ (fun s ↦ ObjectProperty.homMk
      (Sigma.desc (fun i ↦ (s.inj i).hom))) ?_ ?_
    · intro s i
      apply ObjectProperty.hom_ext
      exact Sigma.ι_desc (fun i ↦ (s.inj i).hom) i
    · intro s m hm
      apply ObjectProperty.hom_ext
      apply Sigma.hom_ext
      intro i
      exact (congrArg (fun f ↦ f.hom) (hm i)).trans (Sigma.ι_desc (fun i ↦ (s.inj i).hom) i).symm
  let q := (colimit.isColimit (Discrete.functor EF)).coconePointUniqueUpToIso hc
  let L : ∀ i, (M ⟶ EF i) →+ (M.obj ⟶ E i) := fun _ ↦ P.ι.mapAddHom
  have hL : ∀ i, Function.Bijective (L i) :=
    fun _ ↦ P.fullyFaithfulι.homEquiv.bijective
  let B : (M ⟶ ∐ EF) →+ (M.obj ⟶ ∐ E) :=
    (Preadditive.rightComp M.obj q.hom.hom).comp P.ι.mapAddHom
  have hB : Function.Bijective B :=
    (P.ι.mapIso q).homToEquiv.bijective.comp P.fullyFaithfulι.homEquiv.bijective
  have hS : Function.Bijective (DirectSum.map L) :=
    ⟨(DirectSum.map_injective L).2 (fun i ↦ (hL i).1),
      (DirectSum.map_surjective L).2 (fun i ↦ (hL i).2)⟩
  let a := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp M.obj (Sigma.ι E i))
  let b := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp M (Sigma.ι EF i))
  have hi (i : I) : (Sigma.ι EF i).hom ≫ q.hom.hom = Sigma.ι E i := by
    exact congrArg (fun f ↦ f.hom)
      ((colimit.isColimit (Discrete.functor EF)).comp_coconePointUniqueUpToIso_hom hc
        (Discrete.mk i))
  have square : B.comp b = a.comp (DirectSum.map L) := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply, DirectSum.map_of]
    dsimp only [a, b]
    rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    change (f.hom ≫ (Sigma.ι EF i).hom) ≫ q.hom.hom = f.hom ≫ Sigma.ι E i
    rw [Category.assoc, hi]
  have hab : Function.Bijective (a.comp (DirectSum.map L)) := by
    rw [← square]
    exact hB.comp (hM I EF)
  exact ⟨fun x y hxy ↦ by
    obtain ⟨x', rfl⟩ := hS.2 x
    obtain ⟨y', rfl⟩ := hS.2 y
    exact congrArg (DirectSum.map L) (hab.1 hxy),
    fun f ↦ by
      obtain ⟨x, hx⟩ := hab.2 f
      exact ⟨DirectSum.map L x, hx⟩⟩

open Classical in
private theorem compactness_of_fullyFaithful
    {C : Type v} [Category.{w} C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (M : C) (I : Type u) (E : I → C) [HasCoproduct E]
    [HasCoproduct (fun i ↦ F.obj (E i))]
    [PreservesColimit (Discrete.functor E) F]
    (h : Function.Bijective
      (DirectSum.toAddMonoid
        (fun i ↦ Preadditive.rightComp (F.obj M) (Sigma.ι (fun i ↦ F.obj (E i)) i)) :
        (⨁ i : I, (F.obj M ⟶ F.obj (E i))) →+
          (F.obj M ⟶ ∐ (fun i ↦ F.obj (E i))))) :
    Function.Bijective
      (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp M (Sigma.ι E i)) :
        (⨁ i : I, (M ⟶ E i)) →+ (M ⟶ ∐ E)) := by
  classical
  let q := PreservesCoproduct.iso F E
  let L : ∀ i, (M ⟶ E i) →+ (F.obj M ⟶ F.obj (E i)) := fun _ ↦ F.mapAddHom
  have hL : ∀ i, Function.Bijective (L i) :=
    fun _ ↦ (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.bijective
  let B : (M ⟶ ∐ E) →+ (F.obj M ⟶ ∐ (fun i ↦ F.obj (E i))) :=
    (Preadditive.rightComp _ q.hom).comp F.mapAddHom
  have hB : Function.Bijective B := q.homToEquiv.bijective.comp
    (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.bijective
  have hS : Function.Bijective (DirectSum.map L) :=
    ⟨(DirectSum.map_injective L).2 (fun i ↦ (hL i).1),
      (DirectSum.map_surjective L).2 (fun i ↦ (hL i).2)⟩
  let a := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp M (Sigma.ι E i))
  let b := DirectSum.toAddMonoid
    (fun i ↦ Preadditive.rightComp (F.obj M) (Sigma.ι (fun i ↦ F.obj (E i)) i))
  have square : B.comp a = b.comp (DirectSum.map L) := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply, DirectSum.map_of]
    dsimp only [a, b]
    rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    change F.map (f ≫ Sigma.ι E i) ≫ q.hom = F.map f ≫ Sigma.ι (fun i ↦ F.obj (E i)) i
    rw [F.map_comp, Category.assoc]
    congr 1
    apply (cancel_mono q.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (ι_comp_sigmaComparison F E i).symm
  have hab : Function.Bijective (B.comp a) := by
    rw [square]
    exact h.comp hS
  exact ⟨fun _ _ hxy ↦ hab.1 (congrArg B hxy), fun f ↦ by
    obtain ⟨x, hx⟩ := hab.2 (B f)
    exact ⟨x, hB.1 hx⟩⟩

private theorem localizingClosure_map
    {C : Type v} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type v} [Category.{w} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesColimitsOfSize.{v, v} F]
    (S : ObjectProperty C) (T : ObjectProperty D)
    (hST : ∀ M, S M → T (F.obj M))
    (hT : IsLocalizingSubcategory (localizingClosure T)) :
    ∀ M, localizingClosure S M → localizingClosure T (F.obj M) := by
  have _ := hT.1
  have _ := hT.2.1
  have hP : IsLocalizingSubcategory ((localizingClosure T).inverseImage F) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I G hG hGP
    let _ := hG
    have hFG : HasColimit (G ⋙ F) :=
      ⟨⟨F.mapCocone (colimit.cocone G), isColimitOfPreserves F (colimit.isColimit G)⟩⟩
    have hp := hT.2.2 (G ⋙ F) hFG hGP
    exact (localizingClosure T).prop_of_iso (preservesColimitIso F G).symm hp
  intro M hM
  exact hM _ hP (fun N hN ↦ fun P hP hTP ↦ hTP _ (hST N hN))

private theorem localizingClosure_mono
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {S T : ObjectProperty C} (h : S ≤ T) : localizingClosure S ≤ localizingClosure T := by
  intro K hK P hP hTP
  exact hK P hP (h.trans hTP)

private theorem localizingClosure_coproduct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u})
    (S : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (I : Type (u + 1))
    (E : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [HasCoproduct E] (hE : ∀ i, localizingClosure S (E i)) :
    localizingClosure S (∐ E) := by
  have ht := (localizingClosure_exists Λ X S).2.2.2.1
  let EU : ULift.{u + 2} I → _ := fun i ↦ E i.down
  let c : Cofan EU := Cofan.mk (∐ E) (fun i ↦ Sigma.ι E i.down)
  have hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (Equiv.ulift : ULift.{u + 2} I ≃ I)
      (Cofan.mk (∐ E) (Sigma.ι E))).toFun (coproductIsCoproduct E)
  have hh : HasColimit (Discrete.functor EU) := ⟨⟨c, hc⟩⟩
  let _ := hh
  have hp := ht.2.2 (Discrete.functor EU) hh (fun i ↦ hE i.down)
  have : (localizingClosure S).IsClosedUnderIsomorphisms := ht.2.1
  exact (localizingClosure S).prop_of_iso
    ((colimit.isColimit (Discrete.functor EU)).coconePointUniqueUpToIso hc) hp

open Classical in
private theorem compactness_from_assertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (h : ∃ _ : HasCoproducts.{u + 1}
      (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
      ∀ C : (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
        constantModelBoundedConstructible Λ X C.obj → IsCompactObject.{u + 1} C)
    (C : ConstantModelConstructibleFiniteTor Λ X)
    (I : Type (u + 1))
    (E : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [HasCoproduct E] (hE : ∀ i, localizingClosureProEtale Λ X (E i)) :
    Function.Bijective
      (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C.obj (Sigma.ι E i)) :
        (⨁ i : I, (C.obj ⟶ E i)) →+ (C.obj ⟶ ∐ E)) := by
  obtain ⟨hc, hcompact⟩ := h
  let _ := hc
  let B := constantModelBoundedConstructible Λ X
  have hCB : localizingClosure B C.obj := fun _ _ hBP ↦ hBP _ C.property.1
  have hEB (i : I) : localizingClosure B (E i) :=
    localizingClosure_mono (fun _ h ↦ h.1) _ (hE i)
  have hsum : localizingClosure B (∐ E) := localizingClosure_coproduct Λ X B I E hEB
  exact ambientCompactness_of_full (localizingClosure B) ⟨C.obj, hCB⟩
    (hcompact ⟨C.obj, hCB⟩ C.property.1) I E hEB hsum

private theorem integral_compactness_assertion
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∃ _ : HasCoproducts.{u + 1}
      (localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X)).FullSubcategory,
      ∀ C : (localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X)).FullSubcategory,
        constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X C.obj →
          IsCompactObject.{u + 1} C := by
  classical
  have hb := (integralConstructibleExt D ℓ hℓ E X).2
  choose d hd using fun C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X ↦
    hb C.obj C.property
  let d' := fun C ↦ (d C).toNat
  have hd' (C N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (q : ℤ) (hq : (d' C : ℤ) < q) :
      Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧) :=
    hd C N.obj N.property q ((Int.self_le_toNat (d C)).trans_lt hq)
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have _ : Fact D.p.Prime := ⟨D.prime⟩
  have _ : NeZero D.a := ⟨by have := D.exponent_pos; omega⟩
  have _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have hchar : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let _ := hchar
  exact (integralConstructibleCompactness ℓ E D.k D.p D.prime.pos hℓ.symm X d' hd').2.2

private theorem rational_compactness_assertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (h : HasConstructibleCompactness Λ X) :
    ∃ _ : HasCoproducts.{u + 1}
      (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
      ∀ C : (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
        constantModelBoundedConstructible Λ X C.obj → IsCompactObject.{u + 1} C := by
  obtain ⟨hc, hh⟩ := h.1
  let _ := hc
  refine ⟨hc, ?_⟩
  intro C hC
  obtain ⟨hC', hcompact⟩ := hh C.obj hC
  exact hcompact

private noncomputable def continuousCoefficientMonIso
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let h := Profinite.continuousMapRingSheafMap e.toRingHom he
  let k := Profinite.continuousMapRingSheafMap e.symm.toRingHom hei
  let q : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := k
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply (x.down t)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply (x.down t) }
  let F := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have _ : IsMonHom (F.mapIso q).hom :=
    inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat Ab)).map h))
  exact Mon.mkIso' (F.mapIso q)

private theorem baseCoefficientIsos (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} ℚ_[ℓ]) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∧
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ℓ]) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E)) := by
  let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  let e : ℚ_[ℓ] ≃+* E :=
    (IntermediateField.botEquiv ℚ_[ℓ] (PadicAlgCl ℓ)).symm.toRingEquiv
  have hn (x : ℚ_[ℓ]) : ‖e x‖ = ‖x‖ := by
    change ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) x‖ = ‖x‖
    exact PadicAlgCl.norm_extends ℓ x
  have he : Isometry e := (AddMonoidHomClass.isometry_iff_norm e).2 hn
  have hei : Continuous e.symm := (show ℚ_[ℓ] ≃ᵢ E from ⟨e.toEquiv, he⟩).symm.continuous
  refine ⟨E, ⟨continuousCoefficientMonIso e he.continuous hei⟩, ?_⟩
  let φ := padicIntToIntegers ℓ E
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val h
    · intro x
      obtain ⟨q, hq⟩ := e.surjective x.val
      have hq' : ‖q‖ ≤ 1 := by
        rw [← hn, hq]
        exact_mod_cast x.property
      refine ⟨⟨q, hq'⟩, ?_⟩
      apply Subtype.ext
      exact hq
  let ez := RingEquiv.ofBijective φ hφ
  have hnz (x : ℤ_[ℓ]) : ‖ez x‖ = ‖x‖ := by
    change ‖e (x : ℚ_[ℓ])‖ = ‖(x : ℚ_[ℓ])‖
    exact hn _
  have hez : Isometry ez := (AddMonoidHomClass.isometry_iff_norm ez).2 hnz
  exact ⟨continuousCoefficientMonIso ez hez.continuous
    (show ℤ_[ℓ] ≃ᵢ PadicAlgCl.integers ℓ E from ⟨ez.toEquiv, hez⟩).symm.continuous⟩

open Classical in
private theorem compactness_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (hST : ∀ C : ConstantModelConstructibleFiniteTor Λ X,
      (constantModelBoundedConstructible Λ' X ⊓ DerivedCategory.finiteTorAmplitude _)
        ((Mod.comap ((upperStarFromPoint X).map e.inv.hom)).mapDerivedCategory.obj C.obj))
    (hc : ∀ (C : ConstantModelConstructibleFiniteTor Λ' X)
      (I : Type (u + 1))
      (E : I → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)))
      [HasCoproduct E], (∀ i, localizingClosureProEtale Λ' X (E i)) →
      Function.Bijective
        (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C.obj (Sigma.ι E i)) :
          (⨁ i : I, (C.obj ⟶ E i)) →+ (C.obj ⟶ ∐ E)))
    (C : ConstantModelConstructibleFiniteTor Λ X)
    (I : Type (u + 1))
    (E : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [HasCoproduct E] (hE : ∀ i, localizingClosureProEtale Λ X (E i)) :
    Function.Bijective
      (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C.obj (Sigma.ι E i)) :
        (⨁ i : I, (C.obj ⟶ E i)) →+ (C.obj ⟶ ∐ E)) := by
  let φ := (upperStarFromPoint X).map e.inv.hom
  have _ : IsIso e.inv.hom :=
    inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have _ : IsIso φ := inferInstanceAs (IsIso ((upperStarFromPoint X).map e.inv.hom))
  let H := Mod.comapEquivalenceOfIsIso (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  have _ : (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ).IsEquivalence :=
    (inferInstance : H.functor.IsEquivalence)
  let F := (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ).mapDerivedCategory
  have hT := (localizingClosure_exists Λ' X
    (constantModelBoundedConstructible Λ' X ⊓ DerivedCategory.finiteTorAmplitude _)).2.2.2.1
  let _ := (localizingClosure_exists Λ' X
    (constantModelBoundedConstructible Λ' X ⊓ DerivedCategory.finiteTorAmplitude _)).1
  have hm (M) (hM : localizingClosureProEtale Λ X M) :
      localizingClosureProEtale Λ' X (F.obj M) :=
    localizingClosure_map F _ _ (fun N hN ↦ hST ⟨N, hN⟩) hT M hM
  exact compactness_of_fullyFaithful F C.obj I E
    (hc ⟨F.obj C.obj, hST C⟩ I (fun i ↦ F.obj (E i)) (fun i ↦ hm _ (hE i)))

open Classical in
/-- A small set of isomorphism-class representatives of `Dctf(X, Λ)` consists of compact
objects in its localizing closure and detects zero objects by all integer-shifted Homs.
The six alternatives in `hΛ` are ring-object isomorphisms to the actual condensed rings.
The last one uses finite-subextension-valued sections. The coefficient algebraic closure
is the fixed `PadicAlgCl ℓ`, and finite extensions are its finite intermediate fields.
`g` takes its values in the recorded full bounded constructible finite-Tor category;
`hG` gives every isomorphism class and `hG_skeletal` gives one representative per class.

The first conclusion writes the canonical direct-sum Hom map of
`CategoryTheory.IsCompactObject` with ambient morphisms and coprojections. Clause (1) of
`det-def-localizing-closure-existence` supplies these small coproducts, and clause (2)
puts them in the full closure. Thus the coproduct binder does not impose a new existence
hypothesis. The second conclusion uses ambient shifts and zero: fullness and repleteness
identify this with the same assertion inside the closure.

Source: blueprint main-20261015, sk-lem-brown-hypotheses-generation.md and .proof.md
(blueprint: det-brown-hypotheses-generation).

Proof:
1. For finite discrete coefficients use `finiteCompactProEtale`. For rational
coefficients use internal compactness in `Loc(Dbc)` from `constructible_compactness`.
Since Dctf is contained in Dbc, its localizing closure is contained in `Loc(Dbc)`.
The full-subcategory coproduct comparison identifies the ambient canonical Hom map.
2. For integral coefficients choose nonnegative Ext bounds from
`integralConstructibleExt` and apply `integralConstructibleCompactness`. Identify
Q_l with the bottom finite intermediate field and Z_l with its valuation ring by
explicit isometric ring isomorphisms.
3. For every coefficient isomorphism, `constantModelCtf_coefficientIso` transports
Dctf and minimality transports its localizing closure. The fully faithful exact
derived restriction preserves coproducts. Its canonical Hom-map square commutes
on each direct-sum generator, so compactness reflects to the original coefficients.
4. For generation take the left orthogonal of the shift closure of the singleton K.
It is replete, triangulated, and coproduct closed. The shift adjunction and the
representative isomorphisms put Dctf in it. Minimality puts K in it too, so id_K = 0
and `IsZero.isoZero` gives the required isomorphism. -/
theorem brownHypothesesGeneration
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (G : Type (u + 1)) (g : G → ConstantModelConstructibleFiniteTor Λ X)
    (hG : ∀ C : ConstantModelConstructibleFiniteTor Λ X,
      ∃ i : G, Nonempty (C.obj ≅ (g i).obj))
    (hG_skeletal : ∀ i j : G, Nonempty ((g i).obj ≅ (g j).obj) → i = j) :
    (∀ (i : G) (I : Type (u + 1))
      (E : I → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      [HasCoproduct E],
      (∀ j : I, localizingClosureProEtale Λ X (E j)) →
        Function.Bijective
          (DirectSum.toAddMonoid
            (fun j : I ↦ Preadditive.rightComp (g i).obj (Sigma.ι E j)) :
            (⨁ j : I, ((g i).obj ⟶ E j)) →+ ((g i).obj ⟶ ∐ E))) ∧
    (∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
      (∀ (i : G) (n : ℤ), Subsingleton ((g i).obj⟦n⟧ ⟶ K)) →
        Nonempty (K ≅ 0)) := by
  classical
  have _ := hG_skeletal
  constructor
  · have hf (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
        [IsTopologicalRing A] (hA : Finite A) (r : ℕ) (hr : ∀ a : A, (ℓ ^ r) • a = 0)
        (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)) :=
      compactness_coefficientIso e X (constantModelCtf_coefficientIso e X)
        (fun C I E _ hE ↦ finiteCompactProEtale D ℓ hℓ X A hA r hr C.obj C.property
          I E hE (localizingClosure_coproduct _ X _ I E hE))
    have hi (F : PadicAlgCl.FiniteIntermediateField ℓ)
        (e : Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ F)) :=
      compactness_coefficientIso e X (constantModelCtf_coefficientIso e X)
        (compactness_from_assertion _ X (integral_compactness_assertion D ℓ hℓ F X))
    have hr (F : PadicAlgCl.FiniteIntermediateField ℓ)
        (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj F)) :=
      compactness_coefficientIso e X (constantModelCtf_coefficientIso e X)
        (compactness_from_assertion _ X (rational_compactness_assertion _ X
          (constructible_compactness D ℓ hℓ F X).1))
    rcases hΛ with h | h | h | h | h | h
    · obtain ⟨A, _, _, _, _, hA, ⟨r, hr⟩, ⟨e⟩⟩ := h
      intro i I E _ hE
      exact hf A hA r hr e (g i) I E hE
    · obtain ⟨F, _, ⟨ez⟩⟩ := baseCoefficientIsos.{u} ℓ
      obtain ⟨e⟩ := h
      intro i I E _ hE
      exact hi F (e ≪≫ ez) (g i) I E hE
    · obtain ⟨F, ⟨e⟩⟩ := h
      intro i I E _ hE
      exact hi F e (g i) I E hE
    · obtain ⟨F, ⟨eq⟩, _⟩ := baseCoefficientIsos.{u} ℓ
      obtain ⟨e⟩ := h
      intro i I E _ hE
      exact hr F (e ≪≫ eq) (g i) I E hE
    · obtain ⟨F, ⟨e⟩⟩ := h
      intro i I E _ hE
      exact hr F e (g i) I E hE
    · obtain ⟨e⟩ := h
      intro i I E _ hE
      exact compactness_coefficientIso e X (constantModelCtf_coefficientIso e X)
        (compactness_from_assertion _ X (rational_compactness_assertion _ X
          (constructible_compactness D ℓ hℓ ⟨⊥, inferInstance⟩ X).2)) (g i) I E hE
  · intro K hK hKG
    apply localizingClosure_detectsZero _ K hK
    intro M hM n
    obtain ⟨i, ⟨e⟩⟩ := hG ⟨M, hM⟩
    have := hKG i n
    exact (((shiftFunctor _ n).mapIso e).homCongr (Iso.refl K)).injective.subsingleton

end WeilConjectures

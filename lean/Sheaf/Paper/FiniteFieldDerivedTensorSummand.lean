/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.FiniteFieldDerivedTensorComparison
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.Finite.GaloisField
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.DescentSplitTensorAction
import Sheaf.Paper.SeparableFieldTensorChain
import Sheaf.Paper.ConstantFieldRestrictionRepresentatives
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Finite-field diagonal summand: proof -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace FiniteFieldDerivedTensor

variable {C : Type u} [Category.{v} C]

private theorem diagonal_idempotent (F B : Type u)
    [Field F] [Field B] [Finite F] [Finite B] [Algebra F B] :
    ∃ e : B ⊗[F] B,
      e * e = e ∧ Algebra.TensorProduct.lmul' F e = 1 ∧
      ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0 := by
  have : Algebra.FormallyUnramified F B := Algebra.FormallyUnramified.of_isSeparable F B
  obtain ⟨e, he, hμ⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := F) (S := B)).1 this
  have heq (b : B) : (1 ⊗ₜ[F] b) * e = (b ⊗ₜ[F] 1) * e := by
    exact sub_eq_zero.mp (by simpa only [sub_mul] using he b)
  have hmul (x : B ⊗[F] B) :
      x * e = (Algebra.TensorProduct.lmul' F x ⊗ₜ[F] (1 : B)) * e := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      calc
        (b ⊗ₜ[F] c) * e = (b ⊗ₜ[F] 1) * ((1 ⊗ₜ[F] c) * e) := by
          rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = (b ⊗ₜ[F] 1) * ((c ⊗ₜ[F] 1) * e) := by rw [heq]
        _ = ((b * c) ⊗ₜ[F] 1) * e := by
          rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        _ = _ := rfl
    | add x y hx hy => simp only [add_mul, map_add, TensorProduct.add_tmul, hx, hy]
  refine ⟨e, ?_, hμ, ?_⟩
  · simpa only [hμ, ← Algebra.TensorProduct.one_def, one_mul] using hmul e
  · intro b
    rw [sub_mul, ← heq b, sub_self]

private theorem presentation_nonempty (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max u v}] (A : Type (max u v)) [CommRing A]
    [HasDerivedCategory.{w} (Modules J A)] : Nonempty (Presentation J A) := by
  obtain ⟨P, hP, _, ⟨H, ⟨hH⟩, T, ⟨hT⟩⟩, _⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, max u v, w, 0, 0}
      J (coefficients J A)
  let U : (representatives J A).FullSubcategory ⥤ P.FullSubcategory :=
    { obj := fun K ↦ ⟨(HomotopyCategory.quotient (Modules J A) (.up ℤ)).obj K.obj,
        (hP _).2 ⟨K.property.1, fun n ↦
          (exactFunctor _ _).prop_of_iso
            (SheafOfModules.siteSheafTensorRightIso (coefficients J A) (K.obj.X n)).symm
            (K.property.2 n)⟩⟩
      map := fun f ↦ ObjectProperty.homMk
        ((HomotopyCategory.quotient (Modules J A) (.up ℤ)).map f.hom)
      map_id := by
        intro K
        apply ObjectProperty.hom_ext
        exact (HomotopyCategory.quotient (Modules J A) (.up ℤ)).map_id K.obj
      map_comp := by
        intro X Y Z f g
        apply ObjectProperty.hom_ext
        exact (HomotopyCategory.quotient (Modules J A) (.up ℤ)).map_comp f.hom g.hom }
  refine ⟨⟨T, ?_⟩⟩
  let h₁ := Functor.isoWhiskerRight (Functor.isoWhiskerLeft
    ((representatives J A).ι.prod (representatives J A).ι) hH.symm) DerivedCategory.Qh
  let h₂ := Functor.isoWhiskerLeft (U.prod U) hT
  let q := DerivedCategory.quotientCompQhIso (Modules J A)
  let itot : total J A ≅ CochainTensorBifunctor.rawFunctor (tensorFunctor J A) :=
    eqToIso (CochainTensorBifunctor.totalFunctor_eq_mathlib (tensorFunctor J A))
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((representatives J A).ι.prod (representatives J A).ι) itot) DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft
      (((representatives J A).ι.prod (representatives J A).ι) ⋙
        CochainTensorBifunctor.rawFunctor (tensorFunctor J A)) q.symm ≪≫
    h₁ ≪≫ h₂ ≪≫ Functor.isoWhiskerRight
      (NatIso.prod (Functor.isoWhiskerLeft (representatives J A).ι q)
        (Functor.isoWhiskerLeft (representatives J A).ι q)) T

private theorem representatives_whisker_bijective
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (A D : Type (max u v)) [CommRing A] [CommRing D]
    [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules J D)]
    (U V : Derived J A × Derived J A ⥤ Derived J D) :
    Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
      (((representatives J A).ι ⋙ DerivedCategory.Q).prod
        ((representatives J A).ι ⋙ DerivedCategory.Q)) τ) := by
  obtain ⟨P, hP, _, _, hnat⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, max u v, w,
      (max u v) + 1, w} J (coefficients J A)
  let Q := HomotopyCategory.quotient (Modules J A) (.up ℤ)
  let H : (representatives J A).FullSubcategory ⥤ P.FullSubcategory :=
    { obj := fun K ↦ ⟨Q.obj K.obj, (hP _).2 ⟨K.property.1, fun n ↦
        (exactFunctor _ _).prop_of_iso
          (SheafOfModules.siteSheafTensorRightIso (coefficients J A) (K.obj.X n)).symm
          (K.property.2 n)⟩⟩
      map := fun f ↦ ObjectProperty.homMk (Q.map f.hom)
      map_id := by intro K; apply ObjectProperty.hom_ext; exact Q.map_id _
      map_comp := by intro X Y Z f g; apply ObjectProperty.hom_ext; exact Q.map_comp _ _ }
  have : H.Full := ⟨fun {X Y} f ↦ ⟨ObjectProperty.homMk (Q.preimage f.hom), by
    apply ObjectProperty.hom_ext
    exact Q.map_preimage _⟩⟩
  have : H.EssSurj := ⟨fun X ↦ ⟨⟨X.obj.as, (hP X.obj).1 X.property |>.1,
      fun n ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (coefficients J A) (X.obj.as.X n))
        ((hP X.obj).1 X.property |>.2 n)⟩, ⟨Iso.refl _⟩⟩⟩
  have : (H.prod H).Full := ⟨fun {X Y} f ↦
    ⟨(H.preimage f.1, H.preimage f.2), by
      apply Prod.ext <;> exact H.map_preimage _⟩⟩
  have : (H.prod H).EssSurj := ⟨fun X ↦
    ⟨(H.objPreimage X.1, H.objPreimage X.2),
      ⟨(H.objObjPreimageIso X.1).prod (H.objObjPreimageIso X.2)⟩⟩⟩
  let L := (P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)
  have h₁ := hnat (Derived J D) inferInstance U V
  have h₂ := CategoryTheory.bijective_whiskerLeft_of_full_essSurj (H.prod H)
    (L ⋙ U) (L ⋙ V)
  have hc : Function.Bijective (fun τ : U ⟶ V ↦
      Functor.whiskerLeft ((H.prod H) ⋙ L) τ) := h₂.comp h₁
  let q := DerivedCategory.quotientCompQhIso (Modules J A)
  let i : ((H.prod H) ⋙ L) ≅
      (((representatives J A).ι ⋙ DerivedCategory.Q).prod
        ((representatives J A).ι ⋙ DerivedCategory.Q)) :=
    NatIso.prod (Functor.isoWhiskerLeft (representatives J A).ι q)
      (Functor.isoWhiskerLeft (representatives J A).ι q)
  exact CategoryTheory.bijective_whiskerLeft_of_iso i U V hc

private theorem restriction_derived_factor (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max u v}] (F B : Type (max u v))
    [Field F] [Field B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)] :
    ∃ res : Derived J B ⥤ Derived J F,
      Nonempty (restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res) := by
  let U := SheafOfModules.restrictScalars.{max u v} (coefficientMap J F B)
  have : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf (rings J F)) :=
      inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf (rings J B)))
    exact preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf _)
  have : PreservesFiniteColimits U := by
    have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf (rings J F)) :=
      inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf (rings J B)))
    exact preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf _)
  refine ⟨U.mapDerivedCategory, ⟨?_⟩⟩
  unfold restrictComplex
  exact U.mapDerivedCategoryFactors.symm

-- Keep the total tensor functors folded while transporting the comparison maps.
attribute [local irreducible] total restrictComplex coefficientMap

private noncomputable def representativeRestriction
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]
    (compatible : ∀ K : Complexes J B, representatives J B K →
      representatives J F ((restrictComplex J F B).obj K)) :
    (representatives J B).FullSubcategory ⥤ (representatives J F).FullSubcategory :=
    { obj := fun K ↦ ⟨(restrictComplex J F B).obj K.obj, compatible K.obj K.property⟩
      map := fun f ↦ ObjectProperty.homMk ((restrictComplex J F B).map f.hom)
      map_id := by
        intro K
        apply ObjectProperty.hom_ext
        exact (restrictComplex J F B).map_id _
      map_comp := by
        intro X Y Z f g
        apply ObjectProperty.hom_ext
        exact (restrictComplex J F B).map_comp _ _ }

private noncomputable def sourceNatComparison
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]
    (TF : Presentation J F) (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (compatible : ∀ K : Complexes J B, representatives J B K →
      representatives J F ((restrictComplex J F B).obj K)) :
    ((representatives J B).ι.prod (representatives J B).ι) ⋙
      (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F) ⋙
        DerivedCategory.Q ≅
    (((representatives J B).ι ⋙ DerivedCategory.Q).prod
      ((representatives J B).ι ⋙ DerivedCategory.Q)) ⋙ source TF res :=
  Functor.isoWhiskerLeft
      ((representativeRestriction J F B compatible).prod
        (representativeRestriction J F B compatible)) TF.comparison ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Functor.isoWhiskerLeft (representatives J B).ι r)
        (Functor.isoWhiskerLeft (representatives J B).ι r)) TF.tensor

private noncomputable def targetNatComparison
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]
    (TB : Presentation J B) (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res) :
    ((representatives J B).ι.prod (representatives J B).ι) ⋙
      (total J B ⋙ restrictComplex J F B) ⋙ DerivedCategory.Q ≅
    (((representatives J B).ι ⋙ DerivedCategory.Q).prod
      ((representatives J B).ι ⋙ DerivedCategory.Q)) ⋙ target TB res :=
  Functor.isoWhiskerLeft
      (((representatives J B).ι.prod (representatives J B).ι) ⋙ total J B) r ≪≫
    Functor.isoWhiskerRight TB.comparison res

private theorem sourceNatComparison_hom_app
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]
    (TF : Presentation J F) (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (compatible : ∀ K : Complexes J B, representatives J B K →
      representatives J F ((restrictComplex J F B).obj K))
    (K N : Complexes J B) (hK : representatives J B K) (hN : representatives J B N) :
    (sourceNatComparison J F B TF res r compatible).hom.app (⟨K, hK⟩, ⟨N, hN⟩) =
      (sourceComparison TF res r K N (compatible K hK) (compatible N hN)).hom := rfl

private theorem targetNatComparison_hom_app
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]
    (TB : Presentation J B) (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (K N : Complexes J B) (hK : representatives J B K) (hN : representatives J B N) :
    (targetNatComparison J F B TB res r).hom.app (⟨K, hK⟩, ⟨N, hN⟩) =
      (targetComparison TB res r K N hK hN).hom := rfl

attribute [local irreducible] sourceNatComparison targetNatComparison

private theorem diagonalComparison_of_chain
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]
    (TF : Presentation J F) (TB : Presentation J B) (e : B ⊗[F] B)
    (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (compatible : ∀ K : Complexes J B, representatives J B K →
      representatives J F ((restrictComplex J F B).obj K))
    (chain : ChainComparison (J := J) (F := F) (B := B))
    (act : (B ⊗[F] B) →+* End
      (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F))
    (split : total J B ⋙ restrictComplex J F B ⟶
      ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F)
    (hsb : split ≫ chain.chainBalanced = 𝟙 _)
    (hbs : chain.chainBalanced ≫ split = act e)
    (hact : ∀ (K L : Complexes J B) (x : B ⊗[F] B),
      (act x).app (K, L) = chain.chainAction K L x) : HasDiagonalComparison TF TB e := by
  let I := (representatives J B).ι.prod (representatives J B).ι
  let L := ((representatives J B).ι ⋙ DerivedCategory.Q).prod
    ((representatives J B).ι ⋙ DerivedCategory.Q)
  let A := ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F
  let T := total J B ⋙ restrictComplex J F B
  let α := sourceNatComparison J F B TF res r compatible
  let β := targetNatComparison J F B TB res r
  let W : (Complexes J B × Complexes J B ⥤ Complexes J F) ⥤
      ((representatives J B).FullSubcategory ×
        (representatives J B).FullSubcategory ⥤ Complexes J F) :=
    (Functor.whiskeringLeft _ _ _).obj I
  let V : ((representatives J B).FullSubcategory ×
        (representatives J B).FullSubcategory ⥤ Complexes J F) ⥤
      ((representatives J B).FullSubcategory ×
        (representatives J B).FullSubcategory ⥤ Derived J F) :=
    (Functor.whiskeringRight _ _ _).obj
      (DerivedCategory.Q : Complexes J F ⥤ Derived J F)
  let G := W ⋙ V
  obtain ⟨action, balanced, splitting, hsplit, hproject, ha, hb⟩ :=
    CategoryTheory.exists_splitAction_of_comparison L
      (representatives_whisker_bijective J B F) G (x := A) (y := T)
      (source TF res) (target TB res) α β e act chain.chainBalanced split hsb hbs
  refine ⟨res, r, compatible, action, balanced, splitting, chain,
    hsplit, hproject, ?_, ?_⟩
  · intro K N hK hN x
    let Z : (representatives J B).FullSubcategory ×
        (representatives J B).FullSubcategory := (⟨K, hK⟩, ⟨N, hN⟩)
    have hh := congrArg (fun t ↦ t.app Z) (ha x)
    change DerivedCategory.Q.map ((act x).app (K, N)) ≫ α.hom.app Z =
      α.hom.app Z ≫ (action x).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj N) at hh
    rw [hact] at hh
    change _ ≫ (sourceNatComparison J F B TF res r compatible).hom.app Z =
      (sourceNatComparison J F B TF res r compatible).hom.app Z ≫ _ at hh
    dsimp only [Z] at hh
    rw [sourceNatComparison_hom_app] at hh
    exact hh
  · intro K N hK hN
    let Z : (representatives J B).FullSubcategory ×
        (representatives J B).FullSubcategory := (⟨K, hK⟩, ⟨N, hN⟩)
    have hh := congrArg (fun t ↦ t.app Z) hb
    change DerivedCategory.Q.map (chain.chainBalanced.app (K, N)) ≫
      (targetNatComparison J F B TB res r).hom.app Z =
      (sourceNatComparison J F B TF res r compatible).hom.app Z ≫
        balanced.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj N) at hh
    dsimp only [Z] at hh
    rw [sourceNatComparison_hom_app, targetNatComparison_hom_app] at hh
    exact hh


/-- Finite-field derived tensor over the larger field is the diagonal idempotent summand
of derived tensor over the smaller field, naturally in both unbounded derived variables.
The two nonemptiness clauses also assert existence of the tensor presentations, so the
quantification over presentations cannot make the statement vacuous.

Source: Stacks 0C2X, finite-extension motivation; the explicit projector and derived
comparison are the agent formulation in the node. Sheaf tensor: 03EK, 0GMW;
K-flat resolutions and derived descent: 06YN, 06YS, 06YT, 06YU
(blueprint: lem-pur-finite-field-derived-tensor-summand).

Proof: finite fields are separable, so Mathlib's unramified-algebra criterion supplies
an element e annihilated by the difference of the two coefficient actions and with
multiplication(e) = 1. Tensor induction shows r e = (multiplication(r) tensor 1)e;
putting r = e proves idempotence. The site tensor-descent theorem constructs both
presentations. All sheaves over a constant field are flat; bounded upper truncations
and their exact filtered colimit show that every complex is K-flat. In particular,
restriction preserves representatives. The separate chain-level separability lemma
constructs the canonical balanced retraction on total tensors. Exact scalar restriction
factors through the derived category. Transport its action and retraction across the
two presentation comparisons and descend them by fully faithful precomposition from
K-flat representatives. Faithfulness gives the split identities; evaluation gives
the two required normalization squares.
-/
theorem exists_diagonal_derived_tensor_summand
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v))
    [Field F] [Field B] [Finite F] [Finite B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)] :
    ∃ e : B ⊗[F] B,
      e * e = e ∧ Algebra.TensorProduct.lmul' F e = 1 ∧
      (∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) ∧
      Nonempty (Presentation J F) ∧ Nonempty (Presentation J B) ∧
      ∀ (TF : Presentation J F) (TB : Presentation J B), HasDiagonalComparison TF TB e := by
  classical
  obtain ⟨e, he, hμ, hann⟩ := diagonal_idempotent F B
  refine ⟨e, he, hμ, hann, presentation_nonempty J F, presentation_nonempty J B, ?_⟩
  intro TF TB
  obtain ⟨res, ⟨r⟩⟩ := restriction_derived_factor J F B
  let compatible := restriction_preserves_representatives J F B
  obtain ⟨chain, act, split, hsb, hbs, hact⟩ :=
    exists_separableFieldTensorChain J F B e hμ hann
  exact diagonalComparison_of_chain J F B TF TB e res r compatible chain act split
    hsb hbs hact

end FiniteFieldDerivedTensor

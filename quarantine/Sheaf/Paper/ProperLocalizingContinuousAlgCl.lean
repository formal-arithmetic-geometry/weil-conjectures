/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.SixFunctors.ProperImageLocalizingProper
import Sheaf.Paper.ContinuousAlgClProperFiniteness
import Sheaf.Paper.ContinuousAlgClConstructibleTor
import Sheaf.Paper.ContinuousAlgClProperLowerTail
import Sheaf.Paper.LocalizingClosureExistence
import all Sheaf.Paper.AmbientIndDerivedSums
import Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts

/-!
# Proper direct image for the continuous-map algebraic-closure coefficient

Source: blueprint main-20261015, det-sf-comp-coherence-single, proper-image paragraph.
(blueprint: det-sf-comp-proper-continuous-algcl).
-/

@[expose] public section

set_option autoImplicit false
universe u v w s uD vD wD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
private theorem preservesCoproductsOnProperty_of_small
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [LocallySmall.{s} C]
    (P : ObjectProperty C) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hsmall : ∀ (J : Type s) (L : Discrete J ⥤ C),
      (∀ j, P (L.obj (Discrete.mk j))) → PreservesColimit L F)
    (I : Type w) (L : Discrete I ⥤ C) (hL : ∀ i, P (L.obj (Discrete.mk i))) :
    PreservesColimit L F := by
  classical
  let K : I → C := fun i ↦ L.obj (Discrete.mk i)
  have hpres : PreservesColimit (Discrete.functor K) F := by
    refine ⟨fun {t} ht ↦ ⟨?_⟩⟩
    let t₀ : Cofan K := t
    have hsupport : Small.{s} {i // ¬ IsZero (K i)} :=
      AlgebraicGeometry.ProEtale.coproduct_small_support K t₀ ht
    let J := {i // ¬ IsZero (K i)}
    let U : J → C := fun i ↦ K i.val
    let r : Cofan U := Cofan.mk t.pt (fun i ↦ t₀.inj i.val)
    have hr : IsColimit r := by
      refine Cofan.IsColimit.mk r (fun t' ↦ ht.desc (Cofan.mk t'.pt
        (fun i ↦ if hi : ¬ IsZero (K i) then t'.inj ⟨i, hi⟩ else 0))) ?_ ?_
      · intro t' i
        obtain ⟨i, hi⟩ := i
        change t.ι.app (Discrete.mk i) ≫ _ = _
        rw [ht.fac]
        simp only [Cofan.mk_ι_app, dif_pos hi]
      · intro t' m hm
        apply ht.hom_ext
        intro ⟨i⟩
        rw [ht.fac]
        by_cases hi : ¬ IsZero (K i)
        · simpa only [r, cofan_mk_inj, t₀, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
            using hm ⟨i, hi⟩
        · exact (not_not.mp hi).eq_of_src _ _
    let q : Cofan (fun i ↦ F.obj (U i)) :=
      Cofan.mk (F.obj t.pt) (fun i ↦ F.map (t₀.inj i.val))
    have hq : IsColimit q := by
      let e := Discrete.equivalence (equivShrink.{s} J).symm
      have : PreservesColimit (e.functor ⋙ Discrete.functor U) F :=
        hsmall _ _ (fun j ↦ hL _)
      have hm : IsColimit (F.mapCocone r) := by
        apply IsColimit.ofWhiskerEquivalence e
        exact IsColimit.ofIsoColimit (isColimitOfPreserves F (hr.whiskerEquivalence e))
          (Functor.mapCoconeWhisker F)
      exact (isColimitMapCoconeCofanMkEquiv F U _).toFun hm
    refine { desc := fun t' ↦ hq.desc (Cofan.mk t'.pt
        (fun i ↦ t'.ι.app (Discrete.mk i.val))), fac := ?_, uniq := ?_ }
    · intro t' ⟨i⟩
      by_cases hi : ¬ IsZero (K i)
      · exact hq.fac (Cofan.mk t'.pt (fun i ↦ t'.ι.app (Discrete.mk i.val)))
          (Discrete.mk ⟨i, hi⟩)
      · exact (F.map_isZero (not_not.mp hi)).eq_of_src _ _
    · intro t' m hm
      apply Cofan.IsColimit.hom_ext hq
      intro i
      exact (hm (Discrete.mk i.val)).trans
        (hq.fac (Cofan.mk t'.pt (fun i ↦ t'.ι.app (Discrete.mk i.val)))
          (Discrete.mk i)).symm
  let : PreservesColimit (Discrete.functor (L.obj ∘ Discrete.mk)) F := hpres
  exact preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := L)).symm


namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T


private theorem properDerived_isGE
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : DerivedCategory A) (a : ℤ) (hK : K.IsGE a) :
    (F.rightDerivedFunctor.obj K).IsGE a := by
  let L : DerivedCategory.Plus A := ⟨K, a, hK⟩
  have : L.IsGE a := (L.isGE_ι_obj_iff a).mp hK
  refine (DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ ?_
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE L a hq).of_iso
    ((DerivedCategory.homologyFunctor B q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app L)).symm

attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed upperStarFromPoint

/-- Proper direct image preserves Dctf and ambient sums of localizing objects for
all continuous maps into the topological algebraic closure.

Source: blueprint det-sf-comp-coherence-single, second proof paragraph, with the
coefficient convention of sk-def-localizing-closure.
(blueprint: det-sf-comp-proper-continuous-algcl).

Proof: use the proper-image argument for this actual continuous-map ring. Properness
and finite type over the standing field give a uniform bound on the dimensions of
geometric fibres. Establish proper finiteness for the continuous-map coefficient,
preserving bounded constant-model constructibility. Finite scalar presentations over
the algebraic-closure field are finite free, so the constant local models are flat.
The finite stratification and truncation triangles then give a finite Tor interval
for each bounded constructible output. For the direct-sum assertion, place the localizing
closure in the unbounded ind-constructible subcategory. Apply the uniform proper cohomological
window: in degree q, replace every summand and its sum by the common bounded window
[q-2d-1,q]. Exact sums commute with cohomology and these truncations. Proper bounded
continuity identifies the bounded-window comparison, so every cohomology of the
original coproduct comparison is invertible. The derived cohomology criterion makes
it invertible. For an existing larger coproduct S, discard its zero summands. Each
remaining summand has a distinct nonzero coordinate idempotent in End(S): compose its
coprojection with the projection defined by identity on that summand and zero elsewhere.
Thus its nonzero index set is small in the Hom universe. Reindex it by a small type,
apply the small-sum result, and restore the zero summands; exact pushforward preserves
zero objects. Transport from this coproduct to the specified existing ambient colimit
by its unique compatible isomorphism. This includes the empty family and zero object.
This argument must be established for this coefficient ring; it does not identify
it with the finite-subextension-valued algebraic-closure ring. -/
theorem properLocalizingHypotheses_continuousAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ProperLocalizingHypotheses
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) p := by
  let Λ := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let D := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  let F : DerivedCategory C ⥤ DerivedCategory D := (lowerStar Λ p).rightDerivedFunctor
  let Q := localizingClosureProEtale Λ X
  have hQ : IsLocalizingSubcategory Q :=
    (localizingClosure_exists Λ X
      (constantModelBoundedConstructible Λ X ⊓ fun K ↦
        DerivedCategory.finiteTorAmplitude _ K)).2.2.2.1
  let := hQ.1
  let := hQ.2.1
  have hclosed (I : Type (u + 2)) : Q.IsClosedUnderColimitsOfShape (Discrete I) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨G, hG⟩
    exact hQ.2.2 G inferInstance (fun i ↦ hG ⟨i⟩)
  have hclosedSmall (I : Type (u + 1)) :
      Q.IsClosedUnderColimitsOfShape (Discrete I) := by
    let := hclosed (ULift.{u + 2} I)
    exact ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
  have : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  have : HasColimitsOfSize.{u + 1, u + 1} D := IsGrothendieckAbelian.hasColimits D
  have : HasCoproducts.{u + 1} C := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have : HasCoproducts.{u + 1} D := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory D) := derived_hasCoproducts
  obtain ⟨c, htail⟩ := continuousAlgCl_proper_lowerTail ℓ k p
  have hc (q : ℤ) (K : DerivedCategory C) (hK : Q K) :
      IsIso ((F ⋙ DerivedCategory.homologyFunctor D q).map
        ((DerivedCategory.TStructure.t.truncGEπ (q - (c : ℤ))).app K)) := by
    let t := DerivedCategory.TStructure.t (C := C)
    let T := F.mapTriangle.obj ((t.triangleLTGE (q - (c : ℤ))).obj K)
    have hT : T ∈ Pretriangulated.distinguishedTriangles :=
      F.map_distinguished _ (t.triangleLTGE_distinguished (q - (c : ℤ)) K)
    have : T.obj₁.IsLE (q - 1) := htail q K hK
    exact DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl
      (DerivedCategory.isZero_of_isLE _ (q - 1) q (by omega))
      (DerivedCategory.isZero_of_isLE _ (q - 1) (q + 1) (by omega))
  have hsmall (I : Type (u + 1)) (A : I → DerivedCategory C) (hA : ∀ i, Q (A i)) :
      PreservesColimit (Discrete.functor A) F := by
    let := hclosedSmall I
    have hS : Q (∐ A) := Q.prop_of_isColimit (coproductIsCoproduct A) (fun i ↦ hA i.as)
    have hcomp : IsIso (sigmaComparison F A) := by
      apply (DerivedCategory.isIso_iff D _).2
      intro q
      let H := DerivedCategory.homologyFunctor D q
      let G := F ⋙ H
      let t := DerivedCategory.TStructure.t (C := C)
      let T := t.truncGE (q - (c : ℤ))
      let π := t.truncGEπ (q - (c : ℤ))
      have : PreservesColimitsOfShape (Discrete I) T :=
        truncGE_preservesCoproducts (q - (c : ℤ))
      have hbound : ∀ i, (T.obj (A i)).IsGE (q - (c : ℤ)) := fun i ↦ inferInstance
      have : PreservesColimit (Discrete.functor (fun i ↦ T.obj (A i))) F :=
        condensed_boundedBelow_preservesCoproduct Λ p I _ _ hbound
      have : PreservesColimit (Discrete.functor A ⋙ T) F :=
        preservesColimit_of_iso_diagram F
          (Discrete.natIso (fun _ ↦ Iso.refl _) :
            Discrete.functor (fun i ↦ T.obj (A i)) ≅ Discrete.functor A ⋙ T)
      have : PreservesColimit (Discrete.functor A) (T ⋙ G) := inferInstance
      let d := sigmaComparison (T ⋙ G) A
      let l := Limits.Sigma.map (fun i ↦ G.map (π.app (A i)))
      let r := G.map (π.app (∐ A))
      have hd : IsIso d := inferInstance
      have hl (i : I) : IsIso (G.map (π.app (A i))) := hc q (A i) (hA i)
      have : IsIso l := by dsimp only [l]; infer_instance
      have : IsIso r := hc q (∐ A) hS
      have square : sigmaComparison G A ≫ r = l ≫ d := by
        apply Sigma.hom_ext
        intro i
        simp only [l, d, r, ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc]
        change G.map (Sigma.ι A i) ≫ G.map (π.app (∐ A)) =
          G.map (π.app (A i)) ≫
            Sigma.ι (fun i ↦ (T ⋙ G).obj (A i)) i ≫ sigmaComparison (T ⋙ G) A
        rw [ι_comp_sigmaComparison]
        simpa only [Functor.comp_map, ← G.map_comp, Functor.id_map] using
          congrArg G.map (π.naturality (Sigma.ι A i))
      have : IsIso (sigmaComparison G A ≫ r) := by rw [square]; infer_instance
      have : IsIso (sigmaComparison G A) := IsIso.of_isIso_comp_right _ r
      have heq : sigmaComparison G A =
          sigmaComparison H (fun i ↦ F.obj (A i)) ≫ H.map (sigmaComparison F A) := by
        exact (sigmaComparison_map_desc H (fun i ↦ F.obj (A i)) _
          (fun i ↦ F.map (Sigma.ι A i))).symm
      have : IsIso (sigmaComparison H (fun i ↦ F.obj (A i)) ≫
          H.map (sigmaComparison F A)) := by rw [← heq]; infer_instance
      exact IsIso.of_isIso_comp_left (sigmaComparison H (fun i ↦ F.obj (A i))) _
    exact PreservesCoproduct.of_iso_comparison F A
  have hfinite (K : ConstantModelConstructibleFiniteTor Λ X) :
      constantModelBoundedConstructible Λ Y (F.obj K.obj) ∧
        DerivedCategory.finiteTorAmplitude _ (F.obj K.obj) := by
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    have : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    have : IsNoetherian Y := ⟨⟩
    have hcons := continuousAlgCl_proper_finiteness ℓ k p K
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1.1
    have hK : Q K.obj := fun P _ hP ↦ hP _ K.property
    have htailK := htail (b + c + 1) K.obj hK
    have : K.obj.IsLE b := hb
    have : IsIso ((DerivedCategory.TStructure.t.truncLTι (b + 1)).app K.obj) :=
      (DerivedCategory.TStructure.t.isLE_iff_isIso_truncLTι_app b (b + 1) rfl K.obj).mp hb
    let e := asIso ((DerivedCategory.TStructure.t.truncLTι (b + 1)).app K.obj)
    have hu : (F.obj K.obj).IsLE (b + c) := by
      have ht : (F.obj ((DerivedCategory.TStructure.t.truncLT (b + 1)).obj K.obj)).IsLE
          (b + c) := by
        have h₁ : b + (c : ℤ) + 1 - (c : ℤ) = b + 1 := by omega
        have h₂ : b + (c : ℤ) + 1 - 1 = b + (c : ℤ) := by omega
        simpa only [h₁, h₂] using htailK
      exact DerivedCategory.TStructure.t.isLE_of_iso (F.mapIso e) (b + c)
    have hl : (F.obj K.obj).IsGE a := properDerived_isGE (lowerStar Λ p) K.obj a ha
    have h : constantModelBoundedConstructible Λ Y (F.obj K.obj) :=
      ⟨⟨⟨a, hl⟩, ⟨b + c, hu⟩⟩, hcons⟩
    exact ⟨h, continuousAlgCl_bounded_finiteTor ℓ Y _ h⟩
  refine ⟨hfinite, ?_⟩
  intro I K
  apply preservesCoproductsOnProperty_of_small Q F
    (fun J L hL ↦ ?_) I (K ⋙ Q.ι) (fun i ↦ (K.obj ⟨i⟩).property)
  let A : J → DerivedCategory C := fun i ↦ L.obj ⟨i⟩
  have : PreservesColimit (Discrete.functor (L.obj ∘ Discrete.mk)) F := hsmall J A hL
  exact preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := L)).symm

end AlgebraicGeometry.ProEtale.CondensedRing

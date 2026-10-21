/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NQ, K7
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingSummand
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingTriangleClosure
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactHomHocolim
import WeilConjectures.CategoryTheory.CompactFactorThroughThick
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Dualizable derived modules over an arbitrary commutative ring

Source: Stacks Project, More on Algebra, Tag 0FNS, `lemma-have-dual-derived`
(blueprint: lem-zl-ring-derived-dualizable-perfect).

The tensor is the existing K-flat derived monoidal tensor, obtained by deriving the
signed direct-sum total tensor `CochainComplex.mapBifunctor` of
`def-pc-tensor-complex-sheaves`. Its unit is canonically the degree-zero complex `A[0]`.
The localization universe is independent of the module universe.
-/

@[expose] public section

universe u w v t

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace DerivedCategory

/- Compactness transfers along a natural additive Hom equivalence preserving coproducts. -/
private theorem compact_of_homEquiv
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasCoproducts.{u} A] [HasCoproducts.{u} B]
    (G : B ⥤ A)
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) G]
    (K : A) (P : B) (hK : IsCompactObject K)
    (e : ∀ M : B, (P ⟶ M) ≃+ (K ⟶ G.obj M))
    (he : ∀ {M N : B} (f : P ⟶ M) (g : M ⟶ N),
      e N (f ≫ g) = e M f ≫ G.map g) : IsCompactObject P := by
  classical
  intro I E
  let a := DirectSum.toAddMonoid
    (fun i : I ↦ Preadditive.rightComp P (Sigma.ι E i))
  let b := DirectSum.toAddMonoid
    (fun i : I ↦ Preadditive.rightComp K (Sigma.ι (fun i ↦ G.obj (E i)) i))
  let d := DirectSum.map (fun i ↦ (e (E i)).toAddMonoidHom)
  let t : (K ⟶ ∐ (fun i ↦ G.obj (E i))) ≃+ (K ⟶ G.obj (∐ E)) :=
    { (Iso.homCongr (Iso.refl K) (asIso (sigmaComparison G E))) with
      map_add' := by intros; simp }
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ (e (E i)).injective),
      (DirectSum.map_surjective _).2 (fun i ↦ (e (E i)).surjective)⟩
  have hb : Function.Bijective b := hK I (fun i ↦ G.obj (E i))
  have hcomm : (e (∐ E)).toAddMonoidHom.comp a =
      t.toAddMonoidHom.comp (b.comp d) := by
    apply DirectSum.addHom_ext
    intro i f
    dsimp [a, b, d]
    simp only [DirectSum.toAddMonoid_of, DirectSum.map_of]
    simpa [t, Iso.homCongr, Preadditive.rightComp, Category.assoc] using
      he f (Sigma.ι E i)
  have hbij : Function.Bijective ((e (∐ E)).toAddMonoidHom.comp a) := by
    rw [hcomm]
    exact t.bijective.comp (hb.comp hd)
  exact Function.Bijective.of_comp_left hbij (e (∐ E)).injective

/- An additive left adjoint preserves compactness when its right adjoint preserves coproducts. -/
private theorem compact_of_adjunction
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasCoproducts.{u} A] [HasCoproducts.{u} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) G]
    (adj : F ⊣ G) (K : A) (hK : IsCompactObject K) :
    IsCompactObject (F.obj K) := by
  apply compact_of_homEquiv G K (F.obj K) hK (fun M ↦ adj.homAddEquiv K M)
  intro M N f g
  exact adj.homEquiv_naturality_right f g


/- Compactness is invariant under isomorphism, without restricting the Hom universe. -/
private theorem compact_of_iso
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts.{u} A]
    {K P : A} (e : K ≅ P) (hK : IsCompactObject K) : IsCompactObject P := by
  apply compact_of_homEquiv (𝟭 A) K P hK
    (fun M ↦ { Iso.homCongr e.symm (Iso.refl M) with map_add' := by intros; simp })
  intro M N f g
  simp [Iso.homCongr, Category.assoc]

/- A dualizable object is compact when the tensor unit is compact. -/
private theorem compact_of_dualizable
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts.{u} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
    (K : A) (hK : IsDualizable K) (hunit : IsCompactObject (𝟙_ A)) :
    IsCompactObject K := by
  obtain ⟨d⟩ := hK
  let _ : ExactPairing d.rightDual K := BraidedCategory.exactPairing_swap K d.rightDual
  have : (tensorLeft d.rightDual).IsLeftAdjoint :=
    (tensorLeftAdjunction K d.rightDual).isLeftAdjoint
  exact compact_of_iso (ρ_ K)
    (compact_of_adjunction (tensorLeftAdjunction d.rightDual K) (𝟙_ A) hunit)

/- Cancelling unitors converts the displayed identities into the exact-pairing API. -/
private theorem exactPairing_of_identities
    {C : Type*} [Category C] [MonoidalCategory C] (X Y : C)
    (ev : Y ⊗ X ⟶ 𝟙_ C) (coev : 𝟙_ C ⟶ X ⊗ Y)
    (hX : (λ_ X).inv ≫ coev ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ev ≫ (ρ_ X).hom = 𝟙 X)
    (hY : (ρ_ Y).inv ≫ Y ◁ coev ≫ (α_ Y X Y).inv ≫ ev ▷ Y ≫ (λ_ Y).hom = 𝟙 Y) :
    Nonempty (ExactPairing X Y) := by
  exact ⟨{
    evaluation' := ev
    coevaluation' := coev
    evaluation_coevaluation' := by
      apply (cancel_epi (λ_ X).inv).1
      apply (cancel_mono (ρ_ X).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using hX
    coevaluation_evaluation' := by
      apply (cancel_epi (ρ_ Y).inv).1
      apply (cancel_mono (λ_ Y).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using hY }⟩

private theorem identities_of_exactPairing
    {C : Type*} [Category C] [MonoidalCategory C] (X Y : C) [ExactPairing X Y] :
    (λ_ X).inv ≫ (η_ X Y) ▷ X ≫ (α_ X Y X).hom ≫ X ◁ (ε_ X Y) ≫
        (ρ_ X).hom = 𝟙 X ∧
      (ρ_ Y).inv ≫ Y ◁ (η_ X Y) ≫ (α_ Y X Y).inv ≫ (ε_ X Y) ▷ Y ≫
        (λ_ Y).hom = 𝟙 Y := by
  constructor
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using congrArg
        (fun f ↦ (λ_ X).inv ≫ f ≫ (ρ_ X).hom)
        (ExactPairing.evaluation_coevaluation X Y)
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using congrArg
        (fun f ↦ (ρ_ Y).inv ≫ f ≫ (λ_ Y).hom)
        (ExactPairing.coevaluation_evaluation X Y)

/- The natural Hom--homology equivalence identifies the compactness map with a module coproduct. -/
private theorem rankOne_compact {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    IsCompactObject.{u} ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  classical
  obtain ⟨e, he⟩ := AlgebraicGeometry.derivedFreeModule_hom_homology A
  intro I E
  let H := homologyFunctor (ModuleCat.{u} A) 0
  let P := (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let c := DirectSum.toAddMonoid (fun i : I ↦ Preadditive.rightComp P (Sigma.ι E i))
  let d := DirectSum.map (fun i ↦ (e (E i)).toAddMonoidHom)
  let hc : IsColimit (Cofan.mk (H.obj (∐ E)) (fun i ↦ H.map (Sigma.ι E i))) :=
    (isColimitMapCoconeCofanMkEquiv H E (Sigma.ι E)).1
      (isColimitOfPreserves H (coproductIsCoproduct E))
  let f := (ModuleCat.coproductCoconeIsColimit (fun i ↦ H.obj (E i))).coconePointUniqueUpToIso
    hc
  have hf (i : I) : ModuleCat.ofHom (DirectSum.lof A I (fun i ↦ H.obj (E i)) i) ≫ f.hom =
      H.map (Sigma.ι E i) :=
    (ModuleCat.coproductCoconeIsColimit (fun i ↦ H.obj (E i))).comp_coconePointUniqueUpToIso_hom
      hc ⟨i⟩
  have hcomm : (e (∐ E)).toAddMonoidHom.comp c =
      f.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp d := by
    apply DirectSum.addHom_ext
    intro i x
    change e (∐ E) (c (DirectSum.of _ i x)) = f.hom (d (DirectSum.of _ i x))
    simp only [c, d, DirectSum.toAddMonoid_of, DirectSum.map_of]
    exact (he (E i) (∐ E) (Sigma.ι E i) x).trans
      (congrArg (fun g : H.obj (E i) ⟶ H.obj (∐ E) ↦ g (e (E i) x)) (hf i)).symm
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ (e (E i)).injective),
      (DirectSum.map_surjective _).2 (fun i ↦ (e (E i)).surjective)⟩
  have hbij : Function.Bijective ((e (∐ E)).toAddMonoidHom.comp c) := by
    rw [hcomm]
    exact f.toLinearEquiv.bijective.comp hd
  exact Function.Bijective.of_comp_left hbij (e (∐ E)).injective

/- Homology detects zero objects, and rank-one maps detect nonzero homology elements. -/
private theorem rankOne_generator {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    IsWeakTriangulatedGenerator
      ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  classical
  obtain ⟨e, _⟩ := AlgebraicGeometry.derivedFreeModule_hom_homology A
  intro K hK
  have hn : ∃ n : ℤ, ¬ IsZero ((homologyFunctor (ModuleCat.{u} A) n).obj K) := by
    by_contra h
    push Not at h
    exact hK (isZero_of_forall_isZero_homology K h)
  obtain ⟨n, hn⟩ := hn
  have hzero : ¬ IsZero ((homologyFunctor (ModuleCat.{u} A) 0).obj (K⟦n⟧)) := by
    intro hz
    exact hn (hz.of_iso (((homologyFunctor (ModuleCat.{u} A) 0).shiftIso n 0 n
      (add_zero n)).app K).symm)
  have hx : ∃ x : (homologyFunctor (ModuleCat.{u} A) 0).obj (K⟦n⟧), x ≠ 0 := by
    by_contra h
    push Not at h
    have : Subsingleton ((homologyFunctor (ModuleCat.{u} A) 0).obj (K⟦n⟧)) :=
      ⟨fun x y ↦ (h x).trans (h y).symm⟩
    exact hzero (ModuleCat.isZero_of_subsingleton _)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨f, hf⟩ := (e (K⟦n⟧)).surjective x
  refine ⟨n, f, ?_⟩
  intro h
  apply hx
  rw [← hf, h, map_zero]

/- Bounded termwise duality descends through the monoidal localization of K-flat complexes. -/
private theorem perfect_dualizable {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {X : DerivedCategory (ModuleCat.{u} A)} (hX : IsPerfectRingComplex X) :
    IsDualizable X := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hX
  have : P.IsStrictlyGE a := ha
  have : P.IsStrictlyLE b := hb
  have hd (n : ℤ) : IsDualizable (P.X n) := by
    have := (hP n).1
    have := (hP n).2
    exact ModuleCat.isDualizable_of_projective (P.X n)
  let _ : ∀ n, HasRightDual (P.X n) := fun n ↦ (hd n).some
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  have hd' (n : ℤ) : IsDualizable (P.rightDual.X n) :=
    ⟨{ rightDual := P.X (-n)
       exact := BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ }⟩
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)
  let F : W.kFlat.FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} A) := W.kFlat.ι ⋙ Qh
  have : IsIso (Functor.LaxMonoidal.ε F) := by
    dsimp only [F]
    rw [Functor.LaxMonoidal.comp_ε, ObjectProperty.ι_ε,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal Qh W)))
  have (U V : W.kFlat.FullSubcategory) : IsIso (Functor.LaxMonoidal.μ F U V) := by
    dsimp only [F]
    rw [Functor.LaxMonoidal.comp_μ, ObjectProperty.ι_μ,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh W U.obj V.obj U.property
  let _ := Functor.Monoidal.ofLaxMonoidal F
  let U : W.kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b (fun n ↦ (hd n).flat))⟩
  let V : W.kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a) (fun n ↦ (hd' n).flat))⟩
  let _ : ExactPairing ((ObjectProperty.ι _).obj U) ((ObjectProperty.ι _).obj V) :=
    ExactPairing.map H P P.rightDual
  let _ : ExactPairing U V := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) U V
  have h : IsDualizable (F.obj U) :=
    ⟨{ rightDual := F.obj V, exact := ExactPairing.map F U V }⟩
  exact h.of_iso ((quotientCompQhIso _).app P ≪≫ e.symm)

/- Transport a bounded finite-projective model along an isomorphism. -/
private theorem perfect_iso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] {X Y : DerivedCategory (ModuleCat.{u} A)}
    (h : IsPerfectRingComplex X) (e : X ≅ Y) : IsPerfectRingComplex Y := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ eP⟩⟩

/- Shift the model and its two bounds. -/
private theorem perfect_shift {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] {X : DerivedCategory (ModuleCat.{u} A)}
    (h : IsPerfectRingComplex X) (n : ℤ) : IsPerfectRingComplex (X⟦n⟧) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  exact ⟨P⟦n⟧, a - n, b - n, inferInstance, inferInstance, fun i ↦ hP (i + n),
    ⟨(shiftFunctor _ n).mapIso e ≪≫ ((Q.commShiftIso n).app P).symm⟩⟩

/- A split inclusion has a split distinguished triangle, so apply the perfect-summand theorem. -/
private theorem perfect_retract {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] {X Y : DerivedCategory (ModuleCat.{u} A)}
    (r : Retract X Y) (h : IsPerfectRingComplex Y) : IsPerfectRingComplex X := by
  obtain ⟨Z, f, g, hT⟩ := distinguished_cocone_triangle r.i
  let T := Triangle.mk r.i f g
  have hz : T.mor₃ = 0 := by
    change g = 0
    have he : g ≫ r.i⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ T hT
    have hir : r.i⟦(1 : ℤ)⟧' ≫ r.r⟦(1 : ℤ)⟧' = 𝟙 (X⟦(1 : ℤ)⟧) := by
      rw [← CategoryTheory.Functor.map_comp, r.retract]
      exact (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map_id X
    calc
      g = g ≫ (r.i⟦(1 : ℤ)⟧' ≫ r.r⟦(1 : ℤ)⟧') := by rw [hir, Category.comp_id]
      _ = 0 := by rw [← Category.assoc, he, zero_comp]
  obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hz
  exact (isPerfectRingComplex_summand X Z (perfect_iso h e)).1

/- The degree-zero rank-one complex is a bounded finite-projective model. -/
private theorem rankOne_perfect {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    IsPerfectRingComplex ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  refine ⟨P, 0, 0, inferInstance, inferInstance, ?_, ⟨Iso.refl _⟩⟩
  intro n
  by_cases hn : n = 0
  · subst n
    let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩
  · have : Subsingleton (P.X n) := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
    constructor <;> infer_instance

/- Perfectness is closed under triangles, shifts and retracts. -/
private theorem perfect_thick {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := IsPerfectRingComplex
    P.IsTriangulated ∧ P.IsStableUnderRetracts := by
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := IsPerfectRingComplex
  have : P.IsStableUnderRetracts := ⟨fun r h ↦ perfect_retract r h⟩
  have : P.Nonempty := ⟨_, rankOne_perfect⟩
  have : P.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun X h ↦ perfect_shift h n⟩⟩
  have : P.IsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    isPerfectRingComplex_obj₂_of_distTriang T hT h₁ h₃
  exact ⟨{ }, inferInstance⟩

/- Stacks, Derived Categories, proposition-generator-versus-classical-generator (converse). -/
private theorem compact_mem_thick
    {C : Type t} [Category.{u} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{u} C]
    (G : C) (hG : IsCompactObject G) (hgen : IsWeakTriangulatedGenerator G)
    (K : C) (hK : IsCompactObject K) : (ObjectProperty.singleton G).triangEnvelope K := by
  classical
  let E : PUnit.{u + 1} → C := fun _ ↦ G
  have hgenerate : IsTriangulatedGeneratingFamily E := by
    intro L hL
    obtain ⟨n, f, hf⟩ := hgen L hL
    refine ⟨n, Sigma.desc (fun _ ↦ f), ?_⟩
    intro h
    have := congrArg (fun g ↦ Sigma.ι E PUnit.unit ≫ g) h
    simp only [Sigma.ι_desc, comp_zero] at this
    exact hf this
  obtain ⟨X, t, hi, hs, q, r, hT⟩ :=
    compactGenerators_buildObjects E (fun _ ↦ hG) hgenerate K
  let F := CategoryTheory.Functor.ofSequence t
  have hT' : Triangle.mk
      (𝟙 (∐ fun n : ULift.{u} ℕ ↦ F.obj n.down) -
        Sigma.desc (fun n : ULift.{u} ℕ ↦ F.map (homOfLE (Nat.le_succ n.down)) ≫
          Sigma.ι (fun k : ULift.{u} ℕ ↦ F.obj k.down) ⟨n.down + 1⟩)) q r ∈ distTriang C := by
    simpa [F, CategoryTheory.Functor.ofSequence,
      CategoryTheory.Functor.OfSequence.map_le_succ] using hT
  obtain ⟨φ, hφ, hbij⟩ := compact_hom_hocolim K hK F K q r hT'
  obtain ⟨z, hz⟩ := hbij.2 (𝟙 K)
  obtain ⟨n, f, hf⟩ := Types.jointly_surjective' z
  have hfactor : f ≫ Sigma.ι (fun k : ULift.{u} ℕ ↦ X k.down) ⟨n⟩ ≫ q = 𝟙 K := by
    simpa [F, CategoryTheory.Functor.ofSequence] using
      (hφ n f).symm.trans ((congrArg φ hf).trans hz)
  obtain ⟨S, V, a, b, hV, hab⟩ :=
    compact_factorThrough_thickClosure E (fun _ ↦ hG) X t hi hs K hK n f
  let P := (ObjectProperty.singleton G).triangEnvelope
  have hG' : P G := (ObjectProperty.singleton G).le_triangEnvelope _ (by simp)
  have hsum : P (∐ fun i : {i : PUnit.{u + 1} // i ∈ S} ↦ E i.val) := by
    let B := fun i : {i : PUnit.{u + 1} // i ∈ S} ↦ E i.val
    have : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
    apply P.prop_of_iso ((biproduct.isoCoproduct B).symm ≪≫ biproduct.isoProduct B).symm
    exact P.prop_product (fun _ ↦ hG')
  have hVP : P V := (ObjectProperty.triangEnvelope_le_iff _).mpr
    (ObjectProperty.singleton_le_iff.mpr hsum) V hV
  apply P.prop_of_retract (show Retract K V from
    ⟨a, b ≫ Sigma.ι (fun k : ULift.{u} ℕ ↦ X k.down) ⟨n⟩ ≫ q, ?_⟩) hVP
  rw [← Category.assoc a b, hab, hfactor]

/- Shrink Hom universes before applying the compact-generator thick-closure argument. -/
private theorem compact_perfect {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsCompactObject.{u} K) : IsPerfectRingComplex K := by
  let e := ShrinkHoms.equivalence.{u} (DerivedCategory (ModuleCat.{u} A))
  obtain ⟨z, s, p, a, t, i, c, hT⟩ := triangulatedEquivalenceTransfer e
  let := z
  let := s
  let := p
  let := a
  let := t
  let := i
  let := c
  let := e.commShiftInverse ℤ
  let := hT.1
  let := hT.2
  let : HasCoproducts.{u} (ShrinkHoms (DerivedCategory (ModuleCat.{u} A))) :=
    fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  let G := (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  have hG' : IsCompactObject (e.functor.obj G) :=
    compact_of_adjunction e.toAdjunction G rankOne_compact
  have hK' : IsCompactObject (e.functor.obj K) :=
    compact_of_adjunction e.toAdjunction K hK
  have hgen : IsWeakTriangulatedGenerator (e.functor.obj G) := by
    intro L hL
    have hn : ¬ IsZero (e.inverse.obj L) := by
      intro hz
      exact hL ((e.functor.map_isZero hz).of_iso (e.counitIso.app L).symm)
    obtain ⟨n, f, hf⟩ := rankOne_generator (e.inverse.obj L) hn
    let q := (e.functor.commShiftIso n).app (e.inverse.obj L) ≪≫
      (shiftFunctor _ n).mapIso (e.counitIso.app L)
    refine ⟨n, e.functor.map f ≫ q.hom, ?_⟩
    intro h
    apply hf
    apply (CategoryTheory.Functor.map_eq_zero_iff e.functor).1
    exact (cancel_mono q.hom).1 (by simpa using h)
  obtain ⟨htri, hret⟩ := perfect_thick (A := A)
  let := htri
  let := hret
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := IsPerfectRingComplex
  let R := P.inverseImage e.inverse
  have : R.IsStableUnderRetracts := ⟨fun r h ↦ perfect_retract (r.map e.inverse) h⟩
  have hG : R (e.functor.obj G) := perfect_iso rankOne_perfect (e.unitIso.app G)
  have henv := compact_mem_thick (e.functor.obj G) hG' hgen (e.functor.obj K) hK'
  have hR : R (e.functor.obj K) :=
    (ObjectProperty.triangEnvelope_le_iff _).mpr
      (ObjectProperty.singleton_le_iff.mpr hG) _ henv
  exact perfect_iso hR (e.unitIso.app K).symm

/-- An object has evaluation and coevaluation satisfying both triangle identities exactly
when it has a bounded finite-projective model. No Noetherianity or nonzero-ring assumption
is made. Source: Stacks Project, More on Algebra, Tag 0FNS, `lemma-have-dual-derived`
(blueprint: lem-zl-ring-derived-dualizable-perfect).

Proof:
1. A bounded finite-projective complex is termwise dualizable. Its signed dual complex
   has the usual exact pairing. Both complexes are K-flat since they are bounded with
   flat terms. The localization functor restricted to K-flat complexes is monoidal,
   so it maps this pairing to the derived category. Transport along the model isomorphism.
2. The natural additive equivalence Hom(A[0], X) = H^0(X) and preservation of coproducts
   by homology show that A[0] is compact. Nonzero objects have nonzero homology in some
   degree, so shifts of A[0] detect every nonzero object.
3. Tensor with a dualizable object is adjoint to tensor with its dual. The latter
   preserves coproducts, so the compactness of the unit implies compactness of Q.
4. Apply the compact-generator telescope theorem to the singleton generator A[0].
   Compactness factors the identity of Q through a finite stage. The finite-stage
   factorization theorem then factors it through an object in the thick closure of a
   finite sum of A[0]. Thus Q is in the thick closure of A[0]. This is the converse
   direction of Stacks Project, Derived Categories,
   `proposition-generator-versus-classical-generator`, using Tags 09SN, 09SP and 094A.
   Transfer along ShrinkHoms first so that the Hom and coproduct universes agree.
5. Perfect complexes contain A[0] and are closed under shifts, distinguished triangles
   and retracts. For retracts, complete the split inclusion to a triangle; the shifted
   retraction makes the third map zero, so the triangle splits as a biproduct. Apply
   the existing perfect-summand theorem. Therefore the thick closure in step 4 is perfect.
6. Finally, inserting or cancelling the unitors identifies the two displayed triangle
   identities with ExactPairing. All arguments allow the zero ring and arbitrary
   commutative rings, with the localization universe independent of the module universe. -/
theorem dualizable_iff_isPerfectRingComplex {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (Q : DerivedCategory (ModuleCat.{u} A)) :
    (∃ (D : DerivedCategory (ModuleCat.{u} A))
      (ev : D ⊗ Q ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
      (coev : 𝟙_ (DerivedCategory (ModuleCat.{u} A)) ⟶ Q ⊗ D),
      (λ_ Q).inv ≫ coev ▷ Q ≫ (α_ Q D Q).hom ≫ Q ◁ ev ≫ (ρ_ Q).hom = 𝟙 Q ∧
      (ρ_ D).inv ≫ D ◁ coev ≫ (α_ D Q D).inv ≫ ev ▷ D ≫ (λ_ D).hom = 𝟙 D) ↔
      IsPerfectRingComplex Q := by
  constructor
  · rintro ⟨D, ev, coev, hQ, hD⟩
    obtain ⟨pair⟩ := exactPairing_of_identities Q D ev coev hQ hD
    let : BraidedCategory (DerivedCategory (ModuleCat.{u} A)) :=
      DerivedMonoidal.braidedCategory' Qh (HomotopyCategory.quasiIso _ (.up ℤ))
    have hdual : IsDualizable Q := ⟨{ rightDual := D, exact := pair }⟩
    have hunit : IsCompactObject.{u} (𝟙_ (DerivedCategory (ModuleCat.{u} A))) :=
      compact_of_iso (singleFunctorObjUnitIso (ModuleCat.{u} A)) rankOne_compact
    exact compact_perfect Q (compact_of_dualizable Q hdual hunit)
  · intro h
    obtain ⟨d⟩ := perfect_dualizable h
    exact ⟨d.rightDual, ε_ Q d.rightDual, η_ Q d.rightDual,
      identities_of_exactPairing Q d.rightDual⟩

end DerivedCategory

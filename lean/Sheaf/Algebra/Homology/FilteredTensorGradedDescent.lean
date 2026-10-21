/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Algebra.Homology.FilteredTensorLocalizationSetup
import Sheaf.Algebra.Homology.FilteredTensorGradedCocone
import Mathlib.Data.Int.Interval

/-! # Descent of the convolution graded comparison

Source: Stacks Project, More on Algebra, Tag 0H7Y, and Derived Categories, Tags 05S2--05S3.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor

namespace CochainComplex

variable {R : Type u} [CommRing R]

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

private noncomputable def supportCofan {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasFiniteBiproducts C] (A : ℤ → C) (s : Finset ℤ) :
    Cofan A := by
  classical
  exact Cofan.mk (⨁ fun i : ↥s ↦ A i.1)
    (fun i ↦ if hi : i ∈ s then biproduct.ι (fun j : ↥s ↦ A j.1) ⟨i, hi⟩ else 0)

private noncomputable def supportCofanIsColimit {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasFiniteBiproducts C] (A : ℤ → C) (s : Finset ℤ)
    (hs : ∀ i : ℤ, i ∉ s → IsZero (A i)) : IsColimit (supportCofan A s) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun t ↦ biproduct.desc (fun i : ↥s ↦ t.inj i.1)) ?_ ?_
  · intro t i
    by_cases hi : i ∈ s
    · simp [supportCofan, hi]
    · exact (hs i hi).eq_of_src _ _
  · intro t f hf
    apply biproduct.hom_ext'
    intro i
    have hi := hf i.1
    simpa [supportCofan, Cofan.inj, i.2] using hi

private theorem finiteCocone_isIso {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasFiniteBiproducts C] {A : ℤ → C}
    (t : Cofan A) (ht : IsColimit t) (s : Finset ℤ)
    (hs : ∀ i : ℤ, i ∉ s → IsZero (A i)) :
    IsIso (biproduct.desc (fun i : ↥s ↦ t.inj i.1)) := by
  let e := (supportCofanIsColimit A s hs).coconePointUniqueUpToIso ht
  have he : e.hom = biproduct.desc (fun i : ↥s ↦ t.inj i.1) := by
    apply biproduct.hom_ext'
    intro i
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom
      (supportCofanIsColimit A s hs) ht (Discrete.mk i.1)
    dsimp only [e]
    simpa [supportCofan, Cofan.inj, i.2] using h
  rw [← he]
  infer_instance

private theorem graded_zero_of_equal {C : Type*} [Category* C] [Abelian C]
    {Z : C} {X Y : Subobject Z} (h : X ≤ Y) (e : X = Y) :
    IsZero (cokernel (Subobject.ofLE X Y h)) := by
  subst Y
  simp only [Subobject.ofLE_refl]
  exact isZero_cokernel_of_epi _

private theorem finite_graded_support {C : Type*} [Category* C] [Abelian C]
    {X : C} (F : DecreasingFiltration X) (hF : F.IsFinite) :
    ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s → IsZero (F.gradedPiece i) := by
  classical
  obtain ⟨n, m, hn, hm⟩ := hF
  refine ⟨Finset.Ico n m, ?_⟩
  intro i hi
  have heq : F.F (i + 1) = F.F i := by
    by_cases hlow : i < n
    · have h₁ : F.F (i + 1) = ⊤ := top_unique (hn ▸ F.antitone (by omega))
      have h₂ : F.F i = ⊤ := top_unique (hn ▸ F.antitone (by omega))
      exact h₁.trans h₂.symm
    · have hhigh : m ≤ i := by
        have hnot : ¬ (n ≤ i ∧ i < m) := by simpa using hi
        omega
      have h₁ : F.F (i + 1) = ⊥ := bot_unique (hm ▸ F.antitone (by omega))
      have h₂ : F.F i = ⊥ := bot_unique (hm ▸ F.antitone hhigh)
      exact h₁.trans h₂.symm
  change IsZero (cokernel (Subobject.ofLE _ _ (F.F_succ_le i)))
  exact graded_zero_of_equal _ heq


private theorem localized_graded_support
    (gr : ℤ → (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (Fgr : ℤ → FiniteFilteredModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R))
    (hgr : ∀ i : ℤ, Localization.Lifting (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) (Fgr i) (gr i))
    (hgro : ∀ (i : ℤ) (K : FiniteFilteredModuleHomotopy R), (Fgr i).obj K =
      HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
          (K.as.obj.filtration.gradedPiece i)))
    (U : (finiteFilteredModuleQuasiIso R).Localization) :
    ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s → IsZero ((gr i).obj U) := by
  obtain ⟨K, rfl⟩ :=
    (Localization.Construction.objEquiv (finiteFilteredModuleQuasiIso R)).surjective U
  obtain ⟨s, hs⟩ := finite_graded_support K.as.obj.filtration K.as.property
  refine ⟨s, ?_⟩
  intro i hi
  let := hgr i
  let e := (Localization.Lifting.iso (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) (Fgr i) (gr i)).app K ≪≫
    eqToIso (hgro i K) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app
      (K.as.obj.filtration.gradedPiece i)
  exact (DerivedCategory.Q.map_isZero (hs i hi)).of_iso e

private theorem tensor_zero_left (X Y : DerivedCategory (ModuleCat.{u} R))
    (hX : IsZero X) : IsZero (X ⊗ Y) :=
  ((tensoringRight (DerivedCategory (ModuleCat.{u} R))).obj Y).map_isZero hX


/-- The associated graded of the localized convolution tensor is the finite sum
of the derived tensors of the graded pieces, naturally and with its canonical
representative normalization.
Source: Stacks Project, More on Algebra, convolution comparison before Tag 0H7W
and Tag 0H7Y; Derived Categories, Tags 05S2--05S3.
(blueprint: lem-kun-filtered-tensor-graded-descent).

Proof. Take the particular comparison e selected in
kunnethRepresentativeGradedComparison, together with its coproduct cocone from
filteredTensor_graded_comparison. Its legs are the lax monoidal comparisons
followed by Q applied to the complex coprojections. Naturality of these legs and
of e identifies the induced map with the sum of the tensors of the graded maps.
The formula hm makes m the unique filtered map with the indicated underlying
tensor map, so this naturality applies to the supplied m as well.

Forgetting to each graded piece factors through the filtered homotopy quotient.
Use hgrmap and the canonical representative lift isomorphisms to transport this
coproduct comparison to the good homotopy category. Since every denominator is
inverted, each naturality square for a denominator also gives the square for its
inverse. Localization in both variables therefore descends the comparison, with
its coproduct legs, to B. Transport along E.inverse in both variables, then along
the counit of E and the comparison tau, to obtain the comparison for star.

Every finite filtration has a lower whole bound and an upper zero bound. Outside
the corresponding finite interval its successive quotient is zero. The good
replacement equivalence transports this vanishing to every localized object.
Thus each diagonal tensor family has finite support (one factor's finite support
already suffices). For any finite support s, the coproduct cocone restricted to s
is a finite biproduct cocone: the omitted legs have zero source. Its universal
property gives e on s. A map between two such families on a common support is
biproduct.map of the component maps. This proves naturality. For s contained in t,
the canonical map is the map with the displayed coprojections; the same universal
property proves compatibility with support enlargement. This includes empty s.

On a good representative the lift-two component formula and the equivalence unit
cancel the two inverse replacement maps. What remains is exactly Q(e).inv,
preceded by the fixed star representative isomorphism and the fixed graded lift.
Composing the finite biproduct comparison with its cocone legs gives the final
normalization equation. No bound on cochain degrees or common global support is
used. -/
theorem filteredTensor_localized_graded_comparison
    (E :
    (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (eE :
    (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
      goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q)
    (F :
    GoodFiniteFilteredModuleHomotopy R ⥤
      GoodFiniteFilteredModuleHomotopy R ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (B :
    (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
      (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (hB : Localization.Lifting₂
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R)
    (goodFiniteFilteredModuleQuasiIso R) F B)
    (hconv : ∀ P Q : KunnethFilteredComplex R,
    HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (hrep : ∀ P Q : KunnethFilteredComplex R,
    (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
      (goodFiniteFilteredModuleQuasiIso R).Q.obj
        (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q)))
    (m : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (_f : P ⟶ P') (_g : Q ⟶ Q'),
    kunnethConvolutionObject P.obj Q.obj ⟶
      kunnethConvolutionObject P'.obj Q'.obj)
    (hm : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (f : P ⟶ P') (g : Q ⟶ Q'),
    (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom)
    (hFmap : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (f : P ⟶ P') (g : Q ⟶ Q'),
    (F.map (kunnethGoodRepresentativeMap f)).app
          (kunnethGoodRepresentative Q) ≫
        (F.obj (kunnethGoodRepresentative P')).map
          (kunnethGoodRepresentativeMap g) =
      eqToHom (hrep P Q) ≫
        (goodFiniteFilteredModuleQuasiIso R).Q.map
          (kunnethGoodRepresentativeMap
            (kunnethConvolutionRepresentativeMap hconv
              (m P P' Q Q' f g))) ≫
        eqToHom (hrep P' Q').symm)
    (star :
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      (finiteFilteredModuleQuasiIso R).Localization ⥤
        (finiteFilteredModuleQuasiIso R).Localization)
    (τ : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
    (star.obj U).obj V ≅
      E.functor.obj ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V)))
    (hτ : ∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
      (f : U ⟶ U') (g : V ⟶ V'),
    (τ U V).hom ≫
        E.functor.map ((B.map (E.inverse.map f)).app (E.inverse.obj V) ≫
          (B.obj (E.inverse.obj U')).map (E.inverse.map g)) =
      (star.map f).app V ≫ (star.obj U').map g ≫ (τ U' V').hom)
    (gr : ℤ →
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (Fgr : ∀ _a : ℤ, FiniteFilteredModuleHomotopy R ⥤
    DerivedCategory (ModuleCat.{u} R))
    (hgr : ∀ a : ℤ, Localization.Lifting
    (finiteFilteredModuleQuasiIso R).Q
    (finiteFilteredModuleQuasiIso R)
    (Fgr a) (gr a))
    (hgro : ∀ (a : ℤ) (K : FiniteFilteredModuleHomotopy R),
    (Fgr a).obj K =
      HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
          (K.as.obj.filtration.gradedPiece a)))
    (hgrmap : ∀ (a : ℤ) (K L : FiniteFilteredModuleHomotopy R)
      (f : K.as ⟶ L.as),
    (Fgr a).map ((finiteFilteredModuleHomotopyQuotient R).map f) =
      eqToHom
        (hgro a ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
        HomologicalComplexUpToQuasiIso.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
            (FilteredObject.gradedMapSteps f.hom a)) ≫
        eqToHom
          (hgro a
            ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
        ) :
    ∃ (e : ∀ (a : ℤ)
        (U V : (finiteFilteredModuleQuasiIso R).Localization)
        (s : Finset ℤ),
        (∀ i : ℤ, i ∉ s →
          IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))) →
        ((gr a).obj ((star.obj U).obj V) ≅
          (⨁ fun i : ↥s =>
            ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)))),
      (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization),
        ∃ s : Finset ℤ,
          (∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))) ∧
      (∀ (a : ℤ)
          (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
          (f : U ⟶ U') (g : V ⟶ V') (s : Finset ℤ)
          (hs : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
          (hs' : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U') ⊗ ((gr (a - i)).obj V'))),
        (e a U V s hs).hom ≫ biproduct.map (fun i : ↥s =>
          (gr i.1).map f ⊗ₘ (gr (a - i.1)).map g) =
          (gr a).map ((star.map f).app V ≫
            (star.obj U').map g) ≫ (e a U' V' s hs').hom)
      ∧ (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization)
          (s t : Finset ℤ) (hst : s ⊆ t)
          (hs : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
          (ht : ∀ i : ℤ, i ∉ t →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))),
        ∃ (ι :
            (⨁ fun i : ↥s =>
              ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)) ⟶
            (⨁ fun i : ↥t =>
              ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V))),
          (∀ i : ↥s,
            biproduct.ι (fun j : ↥s =>
              ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V)) i ≫ ι =
            biproduct.ι (fun j : ↥t =>
              ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V))
              ⟨i.1, hst i.2⟩) ∧
          (e a U V s hs).hom ≫ ι =
            (e a U V t ht).hom)
      ∧ (∀ (P Q : KunnethFilteredComplex R) (a : ℤ)
          (s : Finset ℤ)
          (hs : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj (kunnethLocalizedRepresentative E P)) ⊗
              ((gr (a - i)).obj (kunnethLocalizedRepresentative E Q)))),
        ∃ (cgr : ∀ i : ℤ,
          kunnethDerivedGraded P.obj Q.obj a i ≅
            DerivedCategory.Q.obj
              (kunnethTensorGraded P.obj Q.obj a i)),
        (∀ i : ℤ, (cgr i).hom =
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (P.obj.filtration.gradedPiece i)
            (Q.obj.filtration.gradedPiece (a - i))) ∧
        (e a (kunnethLocalizedRepresentative E P)
            (kunnethLocalizedRepresentative E Q) s hs).hom ≫
          biproduct.desc (fun i : ↥s ↦
            ((kunnethRepresentativeLiftIso E eE (gr i.1) (Fgr i.1)
              (hgr i.1) (fun K ↦ K.as.obj.filtration.gradedPiece i.1)
              (hgro i.1) P).hom ⊗ₘ
            (kunnethRepresentativeLiftIso E eE (gr (a - i.1))
              (Fgr (a - i.1)) (hgr (a - i.1))
              (fun K ↦ K.as.obj.filtration.gradedPiece (a - i.1))
              (hgro (a - i.1)) Q).hom) ≫
            (cgr i.1).hom ≫ DerivedCategory.Q.map
              (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i.1)) =
          (gr a).map
            (kunnethStarRepresentativeIso E F B hB hconv hrep
              star τ P Q).hom ≫
          (kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
            (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a)
            (kunnethConvolutionRepresentative hconv P Q)).hom ≫
          (DerivedCategory.Q.mapIso
            (kunnethRepresentativeGradedComparison P Q a)).inv) := by
  classical
  obtain ⟨ι, hcolim, hι, hpin⟩ := filteredTensor_localized_graded_cocone
    E eE F B hB hconv hrep m hm hFmap star τ hτ gr Fgr hgr hgro hgrmap
  have hIso (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization)
      (s : Finset ℤ)
      (hs : ∀ i : ℤ, i ∉ s → IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))) :
      IsIso (biproduct.desc (fun i : ↥s ↦ ι a U V i.1)) :=
    finiteCocone_isIso _ (hcolim a U V).some s hs
  let e (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization)
      (s : Finset ℤ)
      (hs : ∀ i : ℤ, i ∉ s → IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))) :
      (gr a).obj ((star.obj U).obj V) ≅
        ⨁ (fun i : ↥s ↦ ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)) := by
    let := hIso a U V s hs
    exact (asIso (biproduct.desc (fun i : ↥s ↦ ι a U V i.1))).symm
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro a U V
    obtain ⟨s, hs⟩ := localized_graded_support gr Fgr hgr hgro U
    exact ⟨s, fun i hi ↦ tensor_zero_left _ _ (hs i hi)⟩
  · intro a U U' V V' f g s hs hs'
    apply (cancel_epi (e a U V s hs).inv).1
    apply (cancel_mono (e a U' V' s hs').inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
    change biproduct.map (fun i : ↥s ↦ (gr i.1).map f ⊗ₘ (gr (a - i.1)).map g) ≫
      biproduct.desc (fun i : ↥s ↦ ι a U' V' i.1) =
        biproduct.desc (fun i : ↥s ↦ ι a U V i.1) ≫
          (gr a).map ((star.map f).app V ≫ (star.obj U').map g)
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc]
    exact hι a i.1 U U' V V' f g
  · intro a U V s t hst hs ht
    let j := biproduct.desc (fun i : ↥s ↦ biproduct.ι
      (fun k : ↥t ↦ ((gr k.1).obj U) ⊗ ((gr (a - k.1)).obj V)) ⟨i.1, hst i.2⟩)
    refine ⟨j, fun i ↦ biproduct.ι_desc _ i, ?_⟩
    apply (cancel_epi (e a U V s hs).inv).1
    apply (cancel_mono (e a U V t ht).inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
    change j ≫ biproduct.desc (fun i : ↥t ↦ ι a U V i.1) =
      biproduct.desc (fun i : ↥s ↦ ι a U V i.1)
    apply biproduct.hom_ext'
    intro i
    simp [j]
  · intro P Q a s hs
    obtain ⟨cgr, hcgr, hp⟩ := hpin P Q a
    refine ⟨cgr, hcgr, ?_⟩
    apply (cancel_epi
      (e a (kunnethLocalizedRepresentative E P) (kunnethLocalizedRepresentative E Q) s hs).inv).1
    simp only [Iso.inv_hom_id_assoc]
    symm
    change biproduct.desc (fun i : ↥s ↦ ι a (kunnethLocalizedRepresentative E P)
        (kunnethLocalizedRepresentative E Q) i.1) ≫ _ = _
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_desc_assoc, biproduct.ι_desc]
    exact hp i.1

end CochainComplex

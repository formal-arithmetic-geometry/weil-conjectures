module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-! # Normalized comparison on a common augmented resolution

Source: Stacks Project, derived.tex, Tags 05TI, 05TH, 05SA; the normalization
calculation extracted from the site-comparison sentence of the rank-one purity calculation.
(blueprint: lem-pur-normalized-comparison-augmented-resolution)
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB uD vD wD

open CategoryTheory

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vD} D]
  [Abelian A] [Abelian B] [Abelian D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wD} D]

/-- The single complex in degree zero, bundled as a bounded-below complex.
Source: Stacks 05TI, the augmentation used in an injective computation.
(blueprint: lem-pur-normalized-comparison-augmented-resolution) -/
noncomputable def augmentedResolutionSingle (A : Type uA) [Category.{vA} A] [Abelian A] :
    A ⥤ CochainComplex.Plus A :=
  (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
    (fun _ ↦ ⟨0, inferInstance⟩)

/-- Localization inverts a quasi-isomorphism of bounded-below augmented complexes.
Source: Stacks 05SA, 05TI. Apply the localization of complexes at quasi-isomorphisms;
its factorization through the homotopy category is the functor `DerivedCategory.Plus.Q`.
This is the inverse-existence step of the normalized comparison calculation.
(blueprint: lem-pur-normalized-comparison-augmented-resolution) -/
@[instance] theorem augmentedResolution_isIso_Q_map {K L : CochainComplex.Plus A} (a : K ⟶ L)
    [QuasiIso a.hom] : IsIso (DerivedCategory.Plus.Q.map a) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map a)) := by
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map a.hom))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ (by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact inferInstanceAs (QuasiIso a.hom))
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

variable [EnoughInjectives A] [EnoughInjectives B]
  (U : B ⥤ A) (E : A ⥤ D) (H : B ⥤ D) [U.Additive] [E.Additive] [H.Additive]
  (RU : DerivedCategory.Plus B ⥤ DerivedCategory.Plus A)
  (RE : DerivedCategory.Plus A ⥤ DerivedCategory.Plus D)
  (RH : DerivedCategory.Plus B ⥤ DerivedCategory.Plus D)
  (αU : U.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
    DerivedCategory.Plus.Qh ⋙ RU)
  (αE : E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
    DerivedCategory.Plus.Qh ⋙ RE)
  (αH : H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
    DerivedCategory.Plus.Qh ⋙ RH)
  [RU.IsRightDerivedFunctor αU (HomotopyCategory.Plus.quasiIso B)]
  [RE.IsRightDerivedFunctor αE (HomotopyCategory.Plus.quasiIso A)]
  [RH.IsRightDerivedFunctor αH (HomotopyCategory.Plus.quasiIso B)]

/-- The computation map determined by the given augmentation, with no new resolution choice.
Source: Stacks 05TH, 05TI, 05SA: localize the augmentation, apply the fixed derived functor,
and invert its comparison at the injective complex.
(blueprint: lem-pur-normalized-comparison-augmented-resolution) -/
noncomputable def augmentedResolutionComputation (M : A) (I : CochainComplex.Plus A)
    [∀ n : ℤ, Injective (I.obj.X n)] (a : (augmentedResolutionSingle A).obj M ⟶ I)
    [QuasiIso a.hom] :
    RE.obj (DerivedCategory.Plus.Q.obj ((augmentedResolutionSingle A).obj M)) ≅
      DerivedCategory.Plus.Q.obj (E.mapCochainComplexPlus.obj I) :=
  asIso (RE.map (DerivedCategory.Plus.Q.map a)) ≪≫
    (asIso (αE.app ((HomotopyCategory.Plus.quotient A).obj I))).symm

/-- The isomorphism e from the common resolution to the chosen derived U of N[0].
Source: Stacks 05TH and 05TI, injective computation followed by inverse augmentation.
(blueprint: lem-pur-normalized-comparison-augmented-resolution) -/
noncomputable def augmentedResolutionTransport (N : B) (J : CochainComplex.Plus B)
    [∀ n : ℤ, Injective (J.obj.X n)]
    (h : (augmentedResolutionSingle B).obj N ⟶ J) [QuasiIso h.hom] :
    DerivedCategory.Plus.Q.obj (U.mapCochainComplexPlus.obj J) ≅
      RU.obj (DerivedCategory.Plus.Q.obj ((augmentedResolutionSingle B).obj N)) :=
  asIso (αU.app ((HomotopyCategory.Plus.quotient B).obj J)) ≪≫
    (RU.mapIso (asIso (DerivedCategory.Plus.Q.map h))).symm

set_option backward.isDefEq.respectTransparency false in
private theorem augmentedResolutionComputation_naturality_aux
    (M M' : A) (I I' : CochainComplex.Plus A)
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (I'.obj.X n)]
    (a : (augmentedResolutionSingle A).obj M ⟶ I) [QuasiIso a.hom]
    (a' : (augmentedResolutionSingle A).obj M' ⟶ I') [QuasiIso a'.hom]
    (f : M ⟶ M') (t : I ⟶ I')
    (ht : a ≫ t = (augmentedResolutionSingle A).map f ≫ a') :
    RE.map (DerivedCategory.Plus.Q.map ((augmentedResolutionSingle A).map f)) ≫
        (augmentedResolutionComputation E RE αE M' I' a').hom =
      (augmentedResolutionComputation E RE αE M I a).hom ≫
        DerivedCategory.Plus.Q.map (E.mapCochainComplexPlus.map t) := by
  have hnat := αE.naturality ((HomotopyCategory.Plus.quotient A).map t)
  change DerivedCategory.Plus.Q.map (E.mapCochainComplexPlus.map t) ≫
      αE.app ((HomotopyCategory.Plus.quotient A).obj I') =
    αE.app ((HomotopyCategory.Plus.quotient A).obj I) ≫
      RE.map (DerivedCategory.Plus.Q.map t) at hnat
  dsimp only [augmentedResolutionComputation, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv]
  apply (cancel_mono (αE.app ((HomotopyCategory.Plus.quotient A).obj I'))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hnat, IsIso.inv_hom_id_assoc, ← RE.map_comp, ← RE.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, ht]

set_option backward.isDefEq.respectTransparency false in
/-- A normalized composite comparison is represented by the specified termwise isomorphism
on the specified common augmented resolution. This is an equality in `D⁺`, before cohomology.
Source: Stacks 05TH, 05TI, 05SA, and the agent-formulated normalization calculation.

Proof: (1) The injective-computation clause of lem-weil-pbc-right-derived-plus-injective
inverts αU, αH at J and αE at UJ; localization inverts a and h. Functors preserve these
inverses. (2) Naturality of b at Qh moves RH(Qh) past b and cancels RE(RU(Qh)) against
its inverse in e. (3) Substitute the stipulated normalization at J, then cancel αE
and αH. The remaining map is exactly Q(σJ) between the two specified computations.
When σ is the identity its termwise map, hence its localized representative, is the identity.
(blueprint: lem-pur-normalized-comparison-augmented-resolution) -/
theorem normalizedComparison_augmentedResolution
    (σ : U ⋙ E ≅ H) (b : RU ⋙ RE ≅ RH)
    (hb : ∀ (K : HomotopyCategory.Plus B)
      [∀ n : ℤ, Injective (K.obj.as.X n)]
      [∀ n : ℤ, Injective ((U.mapHomotopyCategoryPlus.obj K).obj.as.X n)],
      αE.app (U.mapHomotopyCategoryPlus.obj K) ≫ RE.map (αU.app K) ≫
          b.hom.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso σ).hom.app K) ≫
          αH.app K)
    (M : A) (N : B) (J : CochainComplex.Plus B)
    [∀ n : ℤ, Injective (J.obj.X n)]
    [∀ n : ℤ, Injective ((U.mapCochainComplexPlus.obj J).obj.X n)]
    (h : (augmentedResolutionSingle B).obj N ⟶ J) [QuasiIso h.hom]
    (a : (augmentedResolutionSingle A).obj M ⟶ U.mapCochainComplexPlus.obj J)
    [QuasiIso a.hom] :
    RE.map (DerivedCategory.Plus.Q.map a ≫
        (augmentedResolutionTransport U RU αU N J h).hom) ≫
      b.hom.app (DerivedCategory.Plus.Q.obj ((augmentedResolutionSingle B).obj N)) ≫
      (augmentedResolutionComputation H RH αH N J h).hom =
    (augmentedResolutionComputation E RE αE M (U.mapCochainComplexPlus.obj J) a).hom ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso σ).hom.app
        ((HomotopyCategory.Plus.quotient B).obj J)) := by
  have : ∀ n : ℤ, Injective
      ((U.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient B).obj J)).obj.as.X n) :=
    fun n ↦ inferInstanceAs (Injective ((U.mapCochainComplexPlus.obj J).obj.X n))
  have hnorm := hb ((HomotopyCategory.Plus.quotient B).obj J)
  have hnat := b.hom.naturality (DerivedCategory.Plus.Q.map h)
  dsimp only [augmentedResolutionTransport, augmentedResolutionComputation,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat]
  simp only [Functor.map_inv, IsIso.inv_hom_id_assoc]
  have hnorm' := congrArg (fun z ↦
    inv (αE.app (U.mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient B).obj J))) ≫ z ≫
      inv (αH.app ((HomotopyCategory.Plus.quotient B).obj J))) hnorm
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id,
    Category.comp_id] at hnorm'
  exact congrArg (fun z ↦ RE.map (DerivedCategory.Plus.Q.map a) ≫ z) hnorm'

set_option backward.isDefEq.respectTransparency false in
/-- The two computations and their termwise comparison are natural in maps of augmented data.
Source: Stacks 05SA, naturality of derived computations; 05TH and 05TI for their inverses.

Proof: (4) Apply naturality of αE at U(t), invert the two injective-computation units,
and use U(t)a = a'f to obtain the E equation. (5) Apply naturality of αH at t and use
th = h'g for the H equation. Naturality of σ degree by degree gives the last square
of complexes, and localization preserves it. No lift of a map is chosen, and all
three equalities are in D⁺ rather than merely on cohomology.
(blueprint: lem-pur-normalized-comparison-augmented-resolution) -/
theorem augmentedResolutionComputation_naturality
    (σ : U ⋙ E ≅ H) (M M' : A) (N N' : B) (J J' : CochainComplex.Plus B)
    [∀ n : ℤ, Injective (J.obj.X n)] [∀ n : ℤ, Injective (J'.obj.X n)]
    [∀ n : ℤ, Injective ((U.mapCochainComplexPlus.obj J).obj.X n)]
    [∀ n : ℤ, Injective ((U.mapCochainComplexPlus.obj J').obj.X n)]
    (h : (augmentedResolutionSingle B).obj N ⟶ J) [QuasiIso h.hom]
    (h' : (augmentedResolutionSingle B).obj N' ⟶ J') [QuasiIso h'.hom]
    (a : (augmentedResolutionSingle A).obj M ⟶ U.mapCochainComplexPlus.obj J)
    [QuasiIso a.hom]
    (a' : (augmentedResolutionSingle A).obj M' ⟶ U.mapCochainComplexPlus.obj J')
    [QuasiIso a'.hom]
    (f : M ⟶ M') (g : N ⟶ N') (t : J ⟶ J')
    (ht : h ≫ t = (augmentedResolutionSingle B).map g ≫ h')
    (ha : a ≫ U.mapCochainComplexPlus.map t = (augmentedResolutionSingle A).map f ≫ a') :
    (RE.map (DerivedCategory.Plus.Q.map ((augmentedResolutionSingle A).map f)) ≫
        (augmentedResolutionComputation E RE αE M' (U.mapCochainComplexPlus.obj J') a').hom =
      (augmentedResolutionComputation E RE αE M (U.mapCochainComplexPlus.obj J) a).hom ≫
        DerivedCategory.Plus.Q.map
          (E.mapCochainComplexPlus.map (U.mapCochainComplexPlus.map t))) ∧
    (RH.map (DerivedCategory.Plus.Q.map ((augmentedResolutionSingle B).map g)) ≫
        (augmentedResolutionComputation H RH αH N' J' h').hom =
      (augmentedResolutionComputation H RH αH N J h).hom ≫
        DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map t)) ∧
    (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso σ).hom.app
          ((HomotopyCategory.Plus.quotient B).obj J)) ≫
        DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map t) =
      DerivedCategory.Plus.Q.map
          (E.mapCochainComplexPlus.map (U.mapCochainComplexPlus.map t)) ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso σ).hom.app
          ((HomotopyCategory.Plus.quotient B).obj J'))) := by
  refine ⟨augmentedResolutionComputation_naturality_aux E RE αE
    M M' _ _ a a' f (U.mapCochainComplexPlus.map t) ha,
    augmentedResolutionComputation_naturality_aux H RH αH N N' J J' h h' g t ht, ?_⟩
  have hnat := (Functor.mapHomotopyCategoryPlusCompIso σ).hom.naturality
    ((HomotopyCategory.Plus.quotient B).map t)
  have hnat' := (DerivedCategory.Plus.Qh.congr_map hnat).symm
  rw [Functor.map_comp, Functor.map_comp] at hnat'
  change DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso σ).hom.app
        ((HomotopyCategory.Plus.quotient B).obj J)) ≫
      DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map t) =
    DerivedCategory.Plus.Q.map
      (E.mapCochainComplexPlus.map (U.mapCochainComplexPlus.map t)) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso σ).hom.app
          ((HomotopyCategory.Plus.quotient B).obj J')) at hnat'
  exact hnat'

end CategoryTheory

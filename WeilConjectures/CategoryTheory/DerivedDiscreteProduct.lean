/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-! # Derived categories of discrete products

Source: Stacks Project, Tags 04VI, 04VJ, 05RU and 015F; the coordinate roof argument
in the DAG (blueprint: lem-sf-derived-discrete-product).
-/

@[expose] public section

set_option autoImplicit false

universe t u v w w' u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- The assertions of the discrete-product derived comparison, for the given abelian structure
on the category of families with exact evaluations, and the given derived category of it.
All maps below are induced by the actual evaluation functors, rather than chosen
equivalences. The shift comparison is pinned to the canonical comparisons of
`mapDerivedCategory`. The triangle assertion is coordinatewise, so it requires no separate
triangulated structure on the category of derived families.

Source: Stacks Project, Tags 04VI, 04VJ, 05RU and 015F, coordinate localization argument
(blueprint: lem-sf-derived-discrete-product). -/
structure DerivedDiscreteProductComparison
    (I : Type t) (A : I → Type u) [∀ i, Category.{v} (A i)] [∀ i, Abelian (A i)]
    [∀ i, HasDerivedCategory.{w} (A i)] [Abelian (∀ i, A i)]
    [∀ i, (Pi.eval A i).Additive] [∀ i, PreservesFiniteLimits (Pi.eval A i)]
    [∀ i, PreservesFiniteColimits (Pi.eval A i)]
    [HasDerivedCategory.{w'} (∀ i, A i)] : Prop where
  isEquivalence : (Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory)).IsEquivalence
  map_add : ∀ (X Y : DerivedCategory (∀ i, A i)) (f g : X ⟶ Y) (i : I),
    (Pi.eval A i).mapDerivedCategory.map (f + g) =
      (Pi.eval A i).mapDerivedCategory.map f + (Pi.eval A i).mapDerivedCategory.map g
  map_zero : ∀ (X Y : DerivedCategory (∀ i, A i)) (i : I),
    (Pi.eval A i).mapDerivedCategory.map (0 : X ⟶ Y) = 0
  shift : ∀ n : ℤ,
    ∃ e : shiftFunctor (DerivedCategory (∀ i, A i)) n ⋙
        Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory) ≅
      Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory) ⋙
        Functor.pi (fun i ↦ shiftFunctor (DerivedCategory (A i)) n),
      ∀ (X : DerivedCategory (∀ i, A i)) (i : I),
        e.hom.app X i = ((Pi.eval A i).mapDerivedCategory.commShiftIso n).hom.app X
  distinguished : ∀ (T : Triangle (DerivedCategory (∀ i, A i))),
    T ∈ distTriang (DerivedCategory (∀ i, A i)) → ∀ i : I,
      (Pi.eval A i).mapDerivedCategory.mapTriangle.obj T ∈ distTriang (DerivedCategory (A i))
  hom_bijective : ∀ X Y : DerivedCategory (∀ i, A i),
    Function.Bijective (fun f : X ⟶ Y ↦ fun i ↦ (Pi.eval A i).mapDerivedCategory.map f)
  hom_natural : ∀ (X' X Y Y' : DerivedCategory (∀ i, A i))
      (a : X' ⟶ X) (f : X ⟶ Y) (b : Y ⟶ Y') (i : I),
    (Pi.eval A i).mapDerivedCategory.map (a ≫ f ≫ b) =
      (Pi.eval A i).mapDerivedCategory.map a ≫
        (Pi.eval A i).mapDerivedCategory.map f ≫ (Pi.eval A i).mapDerivedCategory.map b

end CategoryTheory

end

set_option autoImplicit false

universe t u v w w' u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

namespace DerivedDiscreteProductProof

variable {I : Type t} {A : I → Type u} [∀ i, Category.{v} (A i)]

private instance piPreadditive [∀ i, Preadditive (A i)] : Preadditive (∀ i, A i) where
  homGroup _ _ := Pi.addCommGroup
  add_comp _ _ _ _ _ _ := funext fun _ ↦ Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := funext fun _ ↦ Preadditive.comp_add _ _ _ _ _ _

private instance evalAdditive [∀ i, Preadditive (A i)] (i : I) :
    (Pi.eval A i).Additive where
  map_add := rfl

section Limits

variable {J : Type} [SmallCategory J] (F : J ⥤ ∀ i, A i)

private noncomputable def familyCone [∀ i, HasLimit (F ⋙ Pi.eval A i)] : Cone F where
  pt i := limit (F ⋙ Pi.eval A i)
  π :=
    { app := fun j i ↦ limit.π (F ⋙ Pi.eval A i) j
      naturality := fun _ _ f ↦ funext fun i ↦ (limit.cone (F ⋙ Pi.eval A i)).π.naturality f }

private noncomputable def familyConeIsLimit [∀ i, HasLimit (F ⋙ Pi.eval A i)] :
    IsLimit (familyCone F) where
  lift s i := limit.lift _ ((Pi.eval A i).mapCone s)
  fac s j := funext fun i ↦ limit.lift_π ((Pi.eval A i).mapCone s) j
  uniq s m hm := by
    funext i
    apply limit.hom_ext
    intro j
    exact (congrFun (hm j) i).trans (limit.lift_π ((Pi.eval A i).mapCone s) j).symm

private noncomputable def familyCocone [∀ i, HasColimit (F ⋙ Pi.eval A i)] : Cocone F where
  pt i := colimit (F ⋙ Pi.eval A i)
  ι :=
    { app := fun j i ↦ colimit.ι (F ⋙ Pi.eval A i) j
      naturality := fun _ _ f ↦ funext fun i ↦ (colimit.cocone (F ⋙ Pi.eval A i)).ι.naturality f }

private noncomputable def familyCoconeIsColimit [∀ i, HasColimit (F ⋙ Pi.eval A i)] :
    IsColimit (familyCocone F) where
  desc s i := colimit.desc _ ((Pi.eval A i).mapCocone s)
  fac s j := funext fun i ↦ colimit.ι_desc ((Pi.eval A i).mapCocone s) j
  uniq s m hm := by
    funext i
    apply colimit.hom_ext
    intro j
    exact (congrFun (hm j) i).trans (colimit.ι_desc ((Pi.eval A i).mapCocone s) j).symm

end Limits

private instance piFiniteLimits [∀ i, HasFiniteLimits (A i)] : HasFiniteLimits (∀ i, A i) where
  out _ _ _ := ⟨fun F ↦ ⟨⟨familyCone F, familyConeIsLimit F⟩⟩⟩

private instance piFiniteColimits [∀ i, HasFiniteColimits (A i)] :
    HasFiniteColimits (∀ i, A i) where
  out _ _ _ := ⟨fun F ↦ ⟨⟨familyCocone F, familyCoconeIsColimit F⟩⟩⟩

private instance evalFiniteLimits [∀ i, HasFiniteLimits (A i)] (i : I) :
    PreservesFiniteLimits (Pi.eval A i) where
  preservesFiniteLimits J _ _ :=
    ⟨fun {F} ↦ preservesLimit_of_preserves_limit_cone (familyConeIsLimit F)
      (by exact limit.isLimit (F ⋙ Pi.eval A i))⟩

private instance evalFiniteColimits [∀ i, HasFiniteColimits (A i)] (i : I) :
    PreservesFiniteColimits (Pi.eval A i) where
  preservesFiniteColimits J _ _ :=
    ⟨fun {F} ↦ preservesColimit_of_preserves_colimit_cocone (familyCoconeIsColimit F)
      (by exact colimit.isColimit (F ⋙ Pi.eval A i))⟩

@[instance_reducible]
private noncomputable def piAbelian [∀ i, Abelian (A i)] : Abelian (∀ i, A i) := by
  have : ∀ {X Y : ∀ i, A i} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    apply (isIso_pi_iff _).2
    intro i
    exact (Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso (Pi.eval A i) f).hom).2 inferInstance
  exact Abelian.ofCoimageImageComparisonIsIso

section Complexes

variable [∀ i, Preadditive (A i)]

private def assembleComplex (K : ∀ i, CochainComplex (A i) ℤ) :
    CochainComplex (∀ i, A i) ℤ where
  X n i := (K i).X n
  d n m i := (K i).d n m
  shape n m h := funext fun i ↦ (K i).shape n m h
  d_comp_d' n m k _ _ := funext fun i ↦ (K i).d_comp_d n m k

private def homotopyEval :
    HomotopyCategory (∀ i, A i) (.up ℤ) ⥤ ∀ i, HomotopyCategory (A i) (.up ℤ) :=
  Functor.pi' (fun i ↦ (Pi.eval A i).mapHomotopyCategory (.up ℤ))

private theorem homotopyEval_surjective :
    Function.Surjective (homotopyEval (A := A)).obj := by
  intro K
  refine ⟨(HomotopyCategory.quotient _ _).obj (assembleComplex (fun i ↦ (K i).as)), ?_⟩
  rfl

private instance homotopyEvalFull : (homotopyEval (A := A)).Full where
  map_surjective {X Y} f := by
    let g : X.as ⟶ Y.as :=
      { f := fun n i ↦ (f i).out.f n
        comm' := fun n m _ ↦ funext fun i ↦ (f i).out.comm n m }
    refine ⟨(HomotopyCategory.quotient _ _).map g, ?_⟩
    funext i
    exact HomotopyCategory.quotient_map_out (f i)

private instance homotopyEvalFaithful : (homotopyEval (A := A)).Faithful where
  map_injective {X Y} f g h := by
    let H (i : I) : Homotopy
        (((Pi.eval A i).mapHomologicalComplex (.up ℤ)).map f.out)
        (((Pi.eval A i).mapHomologicalComplex (.up ℤ)).map g.out) :=
      HomotopyCategory.homotopyOfEq _ _ (by
        simpa only [homotopyEval, Functor.pi'_map, ← Functor.mapHomotopyCategory_map,
          HomotopyCategory.quotient_map_out]
          using congrFun h i)
    let HH : Homotopy f.out g.out :=
      { hom := fun n m i ↦ (H i).hom n m
        zero := fun n m h ↦ funext fun i ↦ (H i).zero n m h
        comm := fun n ↦ funext fun i ↦ (H i).comm n }
    simpa using HomotopyCategory.eq_of_homotopy f.out g.out HH

private instance homotopyEvalEquivalence : (homotopyEval (A := A)).IsEquivalence where
  essSurj := ⟨fun K ↦ by obtain ⟨X, rfl⟩ := homotopyEval_surjective K; exact ⟨X, ⟨Iso.refl _⟩⟩⟩

end Complexes

attribute [local instance] piAbelian

section QuasiIsomorphisms

variable [∀ i, Abelian (A i)]

private theorem shortQuasiIso {S T : ShortComplex (∀ i, A i)} (f : S ⟶ T) :
    ShortComplex.QuasiIso f ↔ ∀ i,
      ShortComplex.QuasiIso ((Pi.eval A i).mapShortComplex.map f) := by
  refine ⟨fun _ _ ↦ inferInstance, fun hf ↦ ?_⟩
  rw [ShortComplex.quasiIso_iff, isIso_pi_iff]
  intro i
  exact ((MorphismProperty.isomorphisms (A i)).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso
      (ShortComplex.homologyFunctorIso (Pi.eval A i))).app (Arrow.mk f))).1
        ((ShortComplex.quasiIso_iff _).1 (hf i))

private theorem complexQuasiIso {K L : CochainComplex (∀ i, A i) ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ i,
      QuasiIso (((Pi.eval A i).mapHomologicalComplex (.up ℤ)).map f) := by
  simp only [quasiIso_iff, quasiIsoAt_iff,
    shortQuasiIso]
  exact forall_comm

private theorem homotopyQuasiIso
    {X Y : HomotopyCategory (∀ i, A i) (.up ℤ)} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso (∀ i, A i) (.up ℤ) f ↔ ∀ i,
      HomotopyCategory.quasiIso (A i) (.up ℤ) ((homotopyEval (A := A)).map f i) := by
  conv_lhs => rw [← HomotopyCategory.quotient_map_out f]
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff, complexQuasiIso]
  apply forall_congr'
  intro i
  conv_rhs => rw [← HomotopyCategory.quotient_map_out f]
  change _ ↔ HomotopyCategory.quasiIso (A i) (.up ℤ)
    ((HomotopyCategory.quotient _ _).map
      (((Pi.eval A i).mapHomologicalComplex (.up ℤ)).map f.out))
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).symm

end QuasiIsomorphisms

section Localizations

variable {C D : Type*} [Category* C] [Preadditive C] [Category* D] [Preadditive D]
  {B : I → Type u₁} {E : I → Type u₂}
  [∀ i, Category.{v₁} (B i)] [∀ i, Preadditive (B i)]
  [∀ i, Category.{v₂} (E i)] [∀ i, Preadditive (E i)]

variable (P : C ⥤ ∀ i, B i) [P.IsEquivalence] [P.Additive]
  (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W] [Q.Additive]
  [W.HasRightCalculusOfFractions]
  (M : ∀ i, B i ⥤ E i) (V : ∀ i, MorphismProperty (B i))
  [∀ i, (M i).IsLocalization (V i)] [∀ i, (V i).HasRightCalculusOfFractions]
  [∀ i, (M i).Additive]
  (F : D ⥤ ∀ i, E i) [F.Additive]
  (e : Q ⋙ F ≅ P ⋙ Functor.pi M)
  (hW : ∀ {X Y : C} (s : X ⟶ Y), W s ↔ ∀ i, IsIso ((M i).map (P.map s i)))

include P Q W M V e hW

omit [F.Additive] in
private theorem localized_zero (X Y : C) (f : Q.obj X ⟶ Q.obj Y)
    (hf : F.map f = 0) : f = 0 := by
  classical
  obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction Q W f
  have hn : F.map (Q.map φ.f) = 0 := by
    rw [← φ.map_s_comp_map Q (Localization.inverts Q W), Functor.map_comp, hf, comp_zero]
  have hz (i : I) : (M i).map (P.map φ.f i) = 0 := by
    have he := congrFun (e.hom.naturality φ.f) i
    change F.map (Q.map φ.f) i ≫ (e.hom.app Y) i =
      (e.hom.app φ.X') i ≫ (M i).map (P.map φ.f i) at he
    rw [hn] at he
    change (0 : (F.obj (Q.obj φ.X')) i ⟶ (F.obj (Q.obj Y)) i) ≫
      (e.hom.app Y) i = (e.hom.app φ.X') i ≫ (M i).map (P.map φ.f i) at he
    apply (cancel_epi (Pi.isoApp (e.app φ.X') i).hom).1
    simpa using he.symm
  have ht (i : I) : ∃ (R : B i) (t : R ⟶ P.obj φ.X' i),
      V i t ∧ t ≫ P.map φ.f i = 0 := by
    obtain ⟨R, t, ht, hh⟩ :=
      (MorphismProperty.map_eq_iff_precomp (M i) (V i) (P.map φ.f i) 0).1
        (by simpa using hz i)
    exact ⟨R, t, ht, by simpa using hh⟩
  choose R t ht hkill using ht
  let Z := P.objPreimage R
  let r := P.objObjPreimageIso R
  let a : Z ⟶ φ.X' := P.preimage (r.hom ≫ t)
  have ha : W a := by
    apply (hW a).2
    intro i
    dsimp only [a]
    rw [P.map_preimage]
    change IsIso ((M i).map (r.hom i ≫ t i))
    have : IsIso (r.hom i) := (Pi.isoApp r i).isIso_hom
    have := Localization.inverts (M i) (V i) (t i) (ht i)
    rw [Functor.map_comp]
    infer_instance
  have hk : a ≫ φ.f = 0 := by
    apply P.map_injective
    rw [Functor.map_comp, P.map_zero]
    dsimp only [a]
    rw [P.map_preimage]
    funext i
    change (r.hom i ≫ t i) ≫ P.map φ.f i = 0
    rw [Category.assoc, hkill, comp_zero]
  have := Localization.inverts Q W a ha
  have hnum : Q.map φ.f = 0 := by
    apply (cancel_epi (Q.map a)).1
    rw [← Q.map_comp, hk, Q.map_zero, comp_zero]
  simp only [MorphismProperty.RightFraction.map, hnum, comp_zero]

omit [Preadditive C] [Preadditive D] [P.Additive] [Q.Additive]
  [W.HasRightCalculusOfFractions] [∀ i, (M i).Additive] [F.Additive]
  [∀ i, Preadditive (B i)] [∀ i, Preadditive (E i)] in
private theorem localized_full_rep (X Y : C) (f : F.obj (Q.obj X) ⟶ F.obj (Q.obj Y)) :
    ∃ g : Q.obj X ⟶ Q.obj Y, F.map g = f := by
  classical
  let u := (e.inv.app X) ≫ f ≫ (e.hom.app Y)
  have hφ (i : I) : ∃ φ : (V i).RightFraction (P.obj X i) (P.obj Y i),
      u i = φ.map (M i) (Localization.inverts (M i) (V i)) :=
    Localization.exists_rightFraction (M i) (V i) (u i)
  choose φ hφ using hφ
  let Z := P.objPreimage (fun i ↦ (φ i).X')
  let r := P.objObjPreimageIso (fun i ↦ (φ i).X')
  let s : Z ⟶ X := P.preimage (r.hom ≫ fun i ↦ (φ i).s)
  let n : Z ⟶ Y := P.preimage (r.hom ≫ fun i ↦ (φ i).f)
  have hs : W s := by
    apply (hW s).2
    intro i
    dsimp only [s]
    rw [P.map_preimage]
    change IsIso ((M i).map (r.hom i ≫ (φ i).s))
    have : IsIso (r.hom i) := (Pi.isoApp r i).isIso_hom
    rw [Functor.map_comp]
    infer_instance
  have he : (P ⋙ Functor.pi M).map s ≫ u = (P ⋙ Functor.pi M).map n := by
    dsimp only [Functor.comp_map, Functor.pi_map, s, n]
    rw [P.map_preimage, P.map_preimage]
    funext i
    change (M i).map (r.hom i ≫ (φ i).s) ≫ u i =
      (M i).map (r.hom i ≫ (φ i).f)
    rw [hφ i, Functor.map_comp, Functor.map_comp, Category.assoc,
      MorphismProperty.RightFraction.map_s_comp_map]
  have hh : F.map (Q.map s) ≫ f = F.map (Q.map n) := by
    apply (cancel_mono (e.app Y).hom).1
    change (F.map (Q.map s) ≫ f) ≫ e.hom.app Y =
      F.map (Q.map n) ≫ e.hom.app Y
    have hn := e.hom.naturality n
    change F.map (Q.map n) ≫ e.hom.app Y =
      e.hom.app Z ≫ (P ⋙ Functor.pi M).map n at hn
    rw [Category.assoc, hn]
    have hh := e.hom.naturality s
    change F.map (Q.map s) ≫ e.hom.app X =
      e.hom.app Z ≫ (P ⋙ Functor.pi M).map s at hh
    have hfu : f ≫ e.hom.app Y = e.hom.app X ≫ u := by simp [u]
    rw [hfu, ← Category.assoc, hh, Category.assoc, he]
  have := Localization.inverts Q W s hs
  refine ⟨inv (Q.map s) ≫ Q.map n, ?_⟩
  apply (cancel_epi (F.map (Q.map s))).1
  rw [← F.map_comp, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  exact hh.symm

private theorem localized_equivalence : F.IsEquivalence := by
  classical
  have := Localization.essSurj Q W
  have : F.Faithful := ⟨by
    intro X Y f g h
    let X₀ := Q.objPreimage X
    let Y₀ := Q.objPreimage Y
    let x := Q.objObjPreimageIso X
    let y := Q.objObjPreimageIso Y
    have hz : F.map (x.hom ≫ (f - g) ≫ y.inv) = 0 := by
      simp [Functor.map_sub, h]
    have hz' := localized_zero P Q W M V F e hW X₀ Y₀ _ hz
    have : f - g = 0 := by
      apply (cancel_epi x.hom).1
      apply (cancel_mono y.inv).1
      simpa using hz'
    exact sub_eq_zero.mp this⟩
  have : F.Full := ⟨by
    intro X Y f
    let x := Q.objObjPreimageIso X
    let y := Q.objObjPreimageIso Y
    obtain ⟨g, hg⟩ := localized_full_rep P Q W M V F e hW
      (Q.objPreimage X) (Q.objPreimage Y) (F.map x.hom ≫ f ≫ F.map y.inv)
    exact ⟨x.inv ≫ g ≫ y.hom, by simp [hg]⟩⟩
  have : F.EssSurj := ⟨by
    intro T
    have (i : I) := Localization.essSurj (M i) (V i)
    let S := fun i ↦ (M i).objPreimage (T i)
    let X := P.objPreimage S
    refine ⟨Q.obj X, ⟨e.app X ≪≫ (Functor.pi M).mapIso (P.objObjPreimageIso S) ≪≫
      Pi.isoMk (fun i ↦ (M i).objObjPreimageIso (T i))⟩⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end Localizations

section Comparison

variable [∀ i, Abelian (A i)] [∀ i, HasDerivedCategory.{w} (A i)]
  [HasDerivedCategory.{w'} (∀ i, A i)]

private instance homotopyEvalAdditive : (homotopyEval (A := A)).Additive where
  map_add {_X _Y f g} := funext fun i ↦
    ((Pi.eval A i).mapHomotopyCategory (.up ℤ)).map_add (f := f) (g := g)

private instance derivedEvalAdditive :
    (Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory)).Additive where
  map_add {_X _Y f g} := funext fun i ↦
    (Pi.eval A i).mapDerivedCategory.map_add (f := f) (g := g)

private theorem derivedEvalEquivalence :
    (Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory)).IsEquivalence := by
  let F := Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory)
  let P := homotopyEval (A := A)
  let M := fun i ↦ @DerivedCategory.Qh (A i) _ _ _
  let V := fun i ↦ HomotopyCategory.quasiIso (A i) (.up ℤ)
  let e : DerivedCategory.Qh ⋙ F ≅ P ⋙ Functor.pi M :=
    NatIso.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategoryFactorsh)
  apply localized_equivalence P DerivedCategory.Qh
    (HomotopyCategory.quasiIso (∀ i, A i) (.up ℤ)) M V F e
  intro X Y f
  change HomotopyCategory.quasiIso (∀ i, A i) (.up ℤ) f ↔ ∀ i,
    IsIso (DerivedCategory.Qh.map ((homotopyEval (A := A)).map f i))
  simpa only [DerivedCategory.isIso_Qh_map_iff] using homotopyQuasiIso f

end Comparison

end DerivedDiscreteProductProof

end CategoryTheory

@[expose] public section

namespace CategoryTheory

/-- Derived localization commutes with arbitrary discrete products of abelian categories.
Source: Stacks Project, Tags 04VI, 04VJ, 05RU and 015F; the coordinate roof consequence
(blueprint: lem-sf-derived-discrete-product).

Proof: (1) Finite limits, colimits and the abelian axioms in the category of families
are coordinatewise. Complexes, chain maps and homotopies assemble coordinatewise too,
so its homotopy category is the product of the homotopy categories, and quasi-isomorphisms
are detected in every coordinate (`def-sp-abelian`, `def-weil-abstract-derived-category`).
(2) Derive each exact evaluation functor, with the canonical termwise factorization and
shift comparison (`lem-weil-pbc-exact-functor-derived-factorization`). Quasi-isomorphisms
have a right calculus of fractions (`lem-pc-quasi-isomorphisms-multiplicative-system`).
(3) Represent an arbitrary family of derived arrows by individual right roofs and assemble
their complexes, numerators and denominators (`lem-pc-right-fraction-representation`).
This proves surjectivity of the Hom map without any common denominator inside a factor.
(4) Equality in every coordinate gives coordinate common refinements; assemble these in
the product homotopy category and apply the converse refinement criterion there
(`lem-pc-right-fraction-common-refinement`). Thus the Hom map is injective.
(5) Choose a complex representative in each coordinate and assemble it, proving essential
surjectivity. The Hom bijections lift arrows uniquely and give an inverse equivalence.
Naturality is the composition law of the derived evaluations.
(6) Each derived evaluation is additive and triangulated with its canonical shifts; their
shift comparisons assemble and satisfy coherence coordinatewise. The same functors give
the coordinate distinguished-triangle assertion (`def-weil-triangulated-category`).
The abelian structure with exact evaluations is asserted; the comparison then holds for
every derived category of the families, in any morphism universe.
For the empty index set all families are empty and all Hom sets are singletons.
No exact infinite products within a factor and no cochain bounds are used. -/
theorem derived_discrete_product
    (I : Type t) (A : I → Type u) [∀ i, Category.{v} (A i)] [∀ i, Abelian (A i)]
    [∀ i, HasDerivedCategory.{w} (A i)] :
    ∃ (_ : Abelian (∀ i, A i)) (_ : ∀ i, (Pi.eval A i).Additive)
      (_ : ∀ i, PreservesFiniteLimits (Pi.eval A i))
      (_ : ∀ i, PreservesFiniteColimits (Pi.eval A i)),
      ∀ [HasDerivedCategory.{w'} (∀ i, A i)],
        DerivedDiscreteProductComparison.{t, u, v, w, w'} I A := by
  let := DerivedDiscreteProductProof.piAbelian (A := A)
  let := fun i ↦ DerivedDiscreteProductProof.evalAdditive (A := A) i
  let := fun i ↦ DerivedDiscreteProductProof.evalFiniteLimits (A := A) i
  let := fun i ↦ DerivedDiscreteProductProof.evalFiniteColimits (A := A) i
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro _
  have := DerivedDiscreteProductProof.derivedEvalEquivalence (A := A)
  refine
    { isEquivalence := inferInstance
      map_add := fun _ _ _ _ i ↦ (Pi.eval A i).mapDerivedCategory.map_add
      map_zero := fun X Y i ↦ (Pi.eval A i).mapDerivedCategory.map_zero X Y
      shift := ?_
      distinguished := fun T h i ↦
        (Pi.eval A i).mapDerivedCategory.map_distinguished T h
      hom_bijective := fun _ _ ↦
        ⟨(Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory)).map_injective,
          (Functor.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory)).map_surjective⟩
      hom_natural := fun _ _ _ _ a f b i ↦ by simp only [Functor.map_comp] }
  intro n
  exact ⟨NatIso.pi' (fun i ↦ (Pi.eval A i).mapDerivedCategory.commShiftIso n),
    fun _ _ ↦ rfl⟩

end CategoryTheory

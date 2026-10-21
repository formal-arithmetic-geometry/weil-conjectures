module

public import Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport
public import Sheaf.Paper.IntegralConstructibleSequentialHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import all Sheaf.Paper.IntegralConstructibleSequentialHom

/-! Private proof helpers moved from
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`
by the upstream sync of 2026-10-20. -/

-- This archive deliberately preserves private proof helpers without adding public declarations.
set_option linter.privateModule false

/-!

# Bounded constructible `E`-coefficients as `𝒪_E`-coefficients with `ℓ` inverted

Let `X` be a scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) with ring of integers `𝒪_E`. The condensed rings
`𝒪̲_E = Profinite.padicIntegersRingObj ℓ E` and `E̲ = Profinite.continuousMapRingObj E`, for the
norm of `E` restricted from `ℚ̄_ℓ`, pull back along `p_X : X_proét ⟶ *_proét` to the
coefficient ring objects `𝒪_{E,X} = p_X^* 𝒪̲_E` and `E_X = p_X^* E̲` of abelian pro-étale sheaves
on `X` (`ProEtale.condensedRingObj`), and the pullback of the inclusion `𝒪̲_E ⟶ E̲`
(`ProEtale.padicIntegersRingObjToContinuousMapRingObj`) is a morphism of ring objects
`φ : 𝒪_{E,X} ⟶ E_X` (`ProEtale.padicIntegersToPadicSubfield`).

The derived extension of scalars
```
E ⊗ᴸ_{𝒪_E} - = L(extendScalars φ) : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})
```
of `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` preserves bounded
constructible complexes (`ProEtale.boundedConstructible_derivedExtendScalars_obj`), so it
restricts to a functor
`D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)` (`ProEtale.boundedConstructibleExtendScalars`) on
the bounded constructible derived categories `ProEtale.BoundedConstructible` of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.

For `X` topologically noetherian, this file states that the restricted functor exhibits
`D_cons(X_proét, E)` as `D_cons(X_proét, 𝒪_E)` with `ℓ` inverted: it is a localization functor
with respect to the class
`CategoryTheory.Rationalization.W (Submonoid.powers ℓ) D_cons(X_proét, 𝒪_E)` of morphisms whose
mapping cone is killed by some power `ℓⁿ`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`). Consequently
`D_cons(X_proét, E)` is equivalent to the rationalization of `D_cons(X_proét, 𝒪_E)` at the
powers of `ℓ` (`ProEtale.rationalizationEquivalence`), compatibly with the localization
functors (`ProEtale.rationalizationQCompEquivalenceIso`).

The statement is made on bounded constructible complexes only: on the full derived categories
`D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` is not a localization at the morphisms with `ℓ`-power-torsion
mapping cone in general. The rationalization statements below retain the upstream
triangulated instance. Its arbitrary-coefficient form is disputed in its defining module;
the valid integral-coefficient specialization is proved separately in
`Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated`.

Neither description is taken as a definition: `E_X` is defined by its sections, not as
`𝒪_{E,X}[1/ℓ]`, following `WeilConjectures/RefactorInstruction.tex`. Finiteness of `E` is what
makes inverting `ℓ` the right statement: `𝒪_E` is then a discrete valuation ring in which every
nonzero element divides a power of `ℓ`.

## Sorried input

* `ProEtale.isLocalization_boundedConstructibleExtendScalars`: on bounded constructible
  complexes, `L(extendScalars φ)` is a localization functor for the morphisms with
  `ℓ`-power-torsion mapping cone.

The remaining `sorry`s are inherited from
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`,
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory

open CategoryTheory.Category

private theorem essSurj_of_subcategory_models
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (L : C ⥤ D)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) (e : F ⋙ Q.ι ≅ P.ι ⋙ L)
    (h : ∀ K : Q.FullSubcategory, ∃ M : P.FullSubcategory,
      Nonempty (L.obj M.obj ≅ K.obj)) : F.EssSurj := ⟨fun K ↦ by
  obtain ⟨M, ⟨eM⟩⟩ := h K
  exact ⟨M, ⟨Q.isoMk (e.app M ≪≫ eM)⟩⟩⟩

private theorem scalar_power_isIso
    {R C : Type*} [CommRing R] [Category C] [Preadditive C] [Linear R C]
    (p : R) (Y : C) [IsIso (p • 𝟙 Y)] (n : ℕ) : IsIso (p ^ n • 𝟙 Y) := by
  induction n with
  | zero => simpa using (inferInstance : IsIso (𝟙 Y))
  | succ n ih =>
    have h : p ^ (n + 1) • 𝟙 Y = (p ^ n • 𝟙 Y) ≫ (p • 𝟙 Y) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, pow_succ, mul_smul]
      exact smul_comm _ _ _
    rw [h]
    infer_instance

private lemma scalar_sequence_map
    {C : Type*} [Category C] [Preadditive C] (ℓ : ℕ) (B : C) (k : ℕ) :
    (Functor.ofSequence (fun _ ↦ ℓ • 𝟙 B)).map (homOfLE (Nat.zero_le k)) =
      ℓ ^ k • 𝟙 B := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
    rw [show homOfLE (Nat.zero_le (k + 1)) =
      homOfLE (Nat.zero_le k) ≫ homOfLE (Nat.le_succ k) from rfl,
      Functor.map_comp, ih, Functor.ofSequence_map_homOfLE_succ]
    change (ℓ ^ k • 𝟙 B) ≫ (ℓ • 𝟙 B) = ℓ ^ (k + 1) • 𝟙 B
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, pow_succ, mul_smul]
    exact smul_comm _ _ _

private lemma scalar_unit_cocone_zero
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (ℓ : ℕ) {L : A ⥤ B} {U : B ⥤ A} [U.Additive] (adj : L ⊣ U) (K : A)
    [IsIso (ℓ • 𝟙 (L.obj K))] :
    (AlgebraicGeometry.ProEtale.CondensedRing.scalarLocalizationUnitCocone ℓ adj K).ι.app 0 =
      adj.unit.app K := by
  simp only [AlgebraicGeometry.ProEtale.CondensedRing.scalarLocalizationUnitCocone,
    NatTrans.ofSequence_app, pow_zero, End.one_def]
  change adj.unit.app K ≫ U.map (𝟙 (L.obj K)) = adj.unit.app K
  rw [U.map_id]
  exact Category.comp_id _

private theorem rationalization_inverts_of_scalar
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (M : Submonoid ℤ) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hUnits : ∀ m ∈ M, ∀ Y : D, IsIso (m • 𝟙 Y)) :
    (Rationalization.W M C).IsInvertedBy F := by
  rintro A B f ⟨Z, g, h, hT, m, hm, hZ⟩
  have : IsIso (m • 𝟙 (F.obj Z)) := hUnits m hm _
  have he : m • 𝟙 (F.obj Z) = 0 := by
    simpa only [F.map_zsmul, F.map_id, F.map_zero] using congrArg F.map hZ
  have hz : IsZero (F.obj Z) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi (m • 𝟙 (F.obj Z))).1
    simp only [Category.comp_id, Limits.comp_zero, he]
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (F.mapTriangle.obj (Pretriangulated.Triangle.mk f g h))
    (F.map_distinguished _ hT)).1 hz

-- Clear scalar fractions to prove that the functor induced on the rationalization is
-- fully faithful, then use essential surjectivity and uniqueness of localization.
private theorem rationalization_localization_of_hom
    {R : Type*} [CommRing R]
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R]
    [Pretriangulated C] [IsTriangulated C]
    (M : Submonoid R) (F : C ⥤ D) [F.Additive] [F.Linear R] [F.EssSurj]
    (hInv : (Rationalization.W M C).IsInvertedBy F)
    (hUnits : ∀ m ∈ M, ∀ Y : D, IsIso (m • 𝟙 Y))
    (hSurj : ∀ (X Y : C) (f : F.obj X ⟶ F.obj Y),
      ∃ m ∈ M, ∃ g : X ⟶ Y, m • f = F.map g)
    (hEq : ∀ (X Y : C) (f g : X ⟶ Y), F.map f = F.map g →
      ∃ m ∈ M, m • f = m • g) :
    F.IsLocalization (Rationalization.W M C) := by
  let Q := Rationalization.Q M C
  let W := Rationalization.W M C
  let G := Localization.lift F hInv Q
  let e : Q ⋙ G ≅ F := Localization.fac F hInv Q
  have : (Q ⋙ G).Additive := Functor.additive_of_iso e.symm
  have : G.Additive := (Localization.functor_additive_iff Q W G).2 inferInstance
  let : Localization.Lifting Q W F G := ⟨e⟩
  have : G.Linear R :=
    (Localization.functor_linear_iff Q W R F G).1 inferInstance
  let H (X Y : C) (f : Q.obj X ⟶ Q.obj Y) :=
    e.inv.app X ≫ G.map f ≫ e.hom.app Y
  have hMap (X Y : C) (f : X ⟶ Y) : H X Y (Q.map f) = F.map f := by
    simp only [H, ← Functor.comp_map, e.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hSmul (X Y : C) (m : R) (f : Q.obj X ⟶ Q.obj Y) :
      H X Y (m • f) = m • H X Y f := by
    simp only [H, G.map_smul, Linear.comp_smul, Linear.smul_comp]
  have hBij (X Y : C) : Function.Bijective (H X Y) := by
    constructor
    · intro f g h
      obtain ⟨m₁, hm₁, f₁, hf₁⟩ := Rationalization.exists_smul_eq_map f
      obtain ⟨m₂, hm₂, f₂, hf₂⟩ := Rationalization.exists_smul_eq_map g
      have e₁ : (m₁ * m₂) • f = Q.map (m₂ • f₁) := by
        rw [mul_comm, mul_smul, hf₁, Q.map_smul]
      have e₂ : (m₁ * m₂) • g = Q.map (m₁ • f₂) := by
        rw [mul_smul, hf₂, Q.map_smul]
      have he : F.map (m₂ • f₁) = F.map (m₁ • f₂) := by
        rw [← hMap, ← hMap, ← e₁, ← e₂, hSmul, hSmul, h]
      apply Rationalization.smul_left_injective (M.mul_mem hm₁ hm₂)
      dsimp only
      rw [e₁, e₂]
      exact (Rationalization.map_eq_map_iff _ _).2 (hEq X Y _ _ he)
    · intro f
      obtain ⟨m, hm, g, hg⟩ := hSurj X Y f
      have : IsIso (m • 𝟙 (Q.obj X)) := Rationalization.isIso_smul_id hm _
      have : IsIso (m • 𝟙 (F.obj X)) := hUnits m hm _
      let g' := inv (m • 𝟙 (Q.obj X)) ≫ Q.map g
      have hg' : m • g' = Q.map g := by
        calc
          m • g' = (m • 𝟙 (Q.obj X)) ≫ g' := by simp
          _ = Q.map g := by dsimp only [g']; rw [IsIso.hom_inv_id_assoc]
      refine ⟨g', ?_⟩
      apply (cancel_epi (m • 𝟙 (F.obj X))).1
      simp only [Linear.smul_comp, Category.id_comp]
      rw [← hSmul, hg', hMap, hg]
  have : G.Full := ⟨fun {A B} f ↦ by
    let eA := Q.objObjPreimageIso A
    let eB := Q.objObjPreimageIso B
    obtain ⟨g, hg⟩ := (hBij _ _).2
      (e.inv.app _ ≫ G.map eA.hom ≫ f ≫ G.map eB.inv ≫ e.hom.app _)
    have h : G.map g = G.map eA.hom ≫ f ≫ G.map eB.inv := by
      rw [← cancel_mono (e.hom.app _)]
      simpa [H] using hg
    refine ⟨eA.inv ≫ g ≫ eB.hom, ?_⟩
    rw [G.map_comp, G.map_comp, h]
    simp only [Category.assoc, ← G.map_comp_assoc, eA.inv_hom_id,
      ← G.map_comp, eB.inv_hom_id, G.map_id, Category.id_comp, Category.comp_id]⟩
  have : G.Faithful := ⟨fun {A B} f g h ↦ by
    let eA := Q.objObjPreimageIso A
    let eB := Q.objObjPreimageIso B
    have he : eA.hom ≫ f ≫ eB.inv = eA.hom ≫ g ≫ eB.inv :=
      (hBij _ _).1 (by simp only [H, G.map_comp, Category.assoc, h])
    simpa using he⟩
  have : G.EssSurj := ⟨fun Y ↦
    ⟨Q.obj (F.objPreimage Y), ⟨e.app _ ≪≫ F.objObjPreimageIso Y⟩⟩⟩
  have : G.IsEquivalence := {}
  exact Functor.IsLocalization.of_equivalence_target Q W F G.asEquivalence e

-- Work through the inclusion isomorphism rather than unfolding the concrete coefficient
-- functors. The rational full subcategory needs no triangulated structure here.
private theorem rationalization_of_subcategory_models
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (ℓ : ℕ) (P : ObjectProperty C) [P.IsTriangulated] (Q : ObjectProperty D)
    (L : C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    (F : P.FullSubcategory ⥤ Q.FullSubcategory)
    (e : F ⋙ Q.ι ≅ P.ι ⋙ L)
    (hmodels : ∀ K : Q.FullSubcategory, ∃ M : P.FullSubcategory,
      Nonempty (L.obj M.obj ≅ K.obj))
    (hUnits : ∀ Y : D, IsIso (ℓ • 𝟙 Y))
    (hSurj : ∀ (A B : P.FullSubcategory) (f : L.obj A.obj ⟶ L.obj B.obj),
      ∃ (n : ℕ) (g : A ⟶ B), ℓ ^ n • f = L.map g.hom)
    (hEq : ∀ (A B : P.FullSubcategory) (f g : A.obj ⟶ B.obj), L.map f = L.map g →
      ∃ n : ℕ, ℓ ^ n • f = ℓ ^ n • g) :
    F.IsLocalization (Rationalization.W (Submonoid.powers (ℓ : ℤ)) P.FullSubcategory) := by
  have : (F ⋙ Q.ι).Additive := Functor.additive_of_iso e.symm
  have : F.Additive := Functor.additive_of_comp_faithful F Q.ι
  have : F.EssSurj := essSurj_of_subcategory_models P Q L F e hmodels
  let T := P.ι ⋙ L
  let M := Submonoid.powers (ℓ : ℤ)
  have hu (m : ℤ) (hm : m ∈ M) (Y : D) : IsIso (m • 𝟙 Y) := by
    obtain ⟨n, rfl⟩ := hm
    have : IsIso ((ℓ : ℤ) • 𝟙 Y) := by
      simpa only [natCast_zsmul] using hUnits Y
    exact scalar_power_isIso (ℓ : ℤ) Y n
  have hInvT : (Rationalization.W M P.FullSubcategory).IsInvertedBy T :=
    rationalization_inverts_of_scalar M T hu
  have hInvComp : (Rationalization.W M P.FullSubcategory).IsInvertedBy (F ⋙ Q.ι) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ e).2 hInvT
  have hInv : (Rationalization.W M P.FullSubcategory).IsInvertedBy F := by
    intro A B f hf
    have hi : IsIso ((F ⋙ Q.ι).map f) := hInvComp f hf
    change IsIso (Q.ι.map (F.map f)) at hi
    exact isIso_of_reflects_iso (F.map f) Q.ι
  have hU (m : ℤ) (hm : m ∈ M) (Y : Q.FullSubcategory) : IsIso (m • 𝟙 Y) := by
    have : IsIso (Q.ι.map (m • 𝟙 Y)) := by
      simpa only [Functor.map_zsmul, Functor.map_id] using hu m hm (Q.ι.obj Y)
    exact isIso_of_reflects_iso _ Q.ι
  let H (A B : P.FullSubcategory) (f : F.obj A ⟶ F.obj B) :=
    (e.app A).inv ≫ f.hom ≫ (e.app B).hom
  have hMap (A B : P.FullSubcategory) (g : A ⟶ B) :
      H A B (F.map g) = L.map g.hom := by
    change e.inv.app A ≫ (F ⋙ Q.ι).map g ≫ e.hom.app B = (P.ι ⋙ L).map g
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hSmul (A B : P.FullSubcategory) (n : ℕ) (f : F.obj A ⟶ F.obj B) :
      H A B (n • f) = n • H A B f := by
    simp only [H, show (n • f).hom = n • f.hom from rfl,
      Preadditive.comp_nsmul, Preadditive.nsmul_comp]
  have hInj (A B : P.FullSubcategory) : Function.Injective (H A B) := by
    intro f g h
    apply Q.ι.map_injective
    exact (cancel_mono (e.app B).hom).1 ((cancel_epi (e.app A).inv).1 h)
  apply rationalization_localization_of_hom M F hInv hU
  · intro A B f
    obtain ⟨n, g, hg⟩ := hSurj A B (H A B f)
    refine ⟨(ℓ : ℤ) ^ n, ⟨n, rfl⟩, g, ?_⟩
    apply hInj A B
    simpa only [← Int.natCast_pow, natCast_zsmul, hSmul, hMap] using hg
  · intro A B f g hfg
    have he : L.map f.hom = L.map g.hom := by rw [← hMap, ← hMap, hfg]
    obtain ⟨n, hn⟩ := hEq A B f.hom g.hom he
    refine ⟨(ℓ : ℤ) ^ n, ⟨n, rfl⟩, ?_⟩
    apply P.ι.map_injective
    rw [Functor.map_zsmul, Functor.map_zsmul]
    change (ℓ : ℤ) ^ n • f.hom = (ℓ : ℤ) ^ n • g.hom
    simpa only [← Int.natCast_pow, natCast_zsmul] using hn

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace CondensedRing

open Opposite CategoryTheory.Category

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

-- Hom continuity for the scalar telescope detects equality after scalar extension:
-- two equal representatives agree at a finite stage, where the transition is ℓ^n.
set_option backward.isDefEq.respectTransparency false in
private theorem integral_scalar_map_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (K B : integralConstructible ℓ E X) (f g : K.obj ⟶ B.obj)
    (hfg : (integralScalarExtension ℓ E X).map f =
      (integralScalarExtension ℓ E X).map g) :
    ∃ n : ℕ, ℓ ^ n • f = ℓ ^ n • g := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X)
  let H := preadditiveCoyoneda.obj (op K.obj)
  let t := integralLocalizationCocone ℓ E X B.obj
  let J := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor
  have : HasColimitsOfShape (ULift.{u + 1} ℕ) A := inferInstance
  obtain ⟨m⟩ := exists_integralLocalization_complex_model ℓ E X B.obj B.property.1.1
  have hcol : Nonempty (IsColimit (H.mapCocone (t.whisker J))) := by
    apply localizationCocone_isColimit_of_model ℓ B.obj t m H
    intro C a hC
    have : C.IsStrictlyGE a := hC
    have : HasColimitsOfShape (ULift.{u + 1} ℕ) (CochainComplex A ℤ) := inferInstance
    let : IsFiltered (ULift.{u + 1} ℕ) :=
      IsFiltered.of_equivalence
        (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
    let D := integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C
    let π := Functor.whiskerLeft D
      ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
    have : ∀ i, IsIso (π.app i) := fun i ↦
      (HomologicalComplex.isIso_πTruncGE_iff C _).2 hC
    have : IsIso π := NatIso.isIso_of_isIso_app π
    have : HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) :=
      HasColimitsOfShape.has_colimit _
    let c := condensedContinuityCocone D a
    have hc : IsColimit c :=
      (IsColimit.precomposeHomEquiv (asIso π) _).symm (colimit.isColimit _)
    let ei : AsSmall.{u + 1} ℕ ≌ ULift.{u + 1} ℕ :=
      (AsSmall.equiv : ℕ ≌ AsSmall.{u + 1} ℕ).symm.trans
        (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
    let D' := ei.functor ⋙ D
    let c' := c.whisker ei.functor
    have hc' : IsColimit c' := hc.whiskerEquivalence ei
    have hD' : ∃ a : ℤ, ∀ i, (DerivedCategory.Q.obj (D'.obj i)).IsGE a :=
      ⟨a, fun _ ↦ (DerivedCategory.isGE_Q_obj_iff C a).2 inferInstance⟩
    let P := ObjectProperty.isoClosure
      (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X))
    have hK : homColimitProperty (D' ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.mapCocone c') K.obj := by
      apply CategoryTheory.homColimit_bounded _ _ P
      · rintro M ⟨N, hN, ⟨e⟩⟩
        apply CategoryTheory.homColimit_iso _ _
          ((DerivedCategory.singleFunctor _ 0).mapIso e)
        exact integralConstructible_sheaf_hom_colimit ℓ E X N hN D' c' ⟨hc'⟩ hD'
      · exact K.property.1
      · exact fun n ↦ ⟨_, K.property.2 n, ⟨Iso.refl _⟩⟩
    obtain ⟨hc0⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (hK 0)
    let e0 : shiftFunctor (DerivedCategory A) (0 : ℤ) ⋙ H ≅ H :=
      Functor.isoWhiskerRight (shiftFunctorZero _ ℤ) H ≪≫ H.leftUnitor
    exact ⟨IsColimit.ofWhiskerEquivalence ei (IsColimit.mapCoconeEquiv e0 hc0)⟩
  obtain ⟨hc⟩ := hcol
  let : IsFiltered (ULift.{u + 1} ℕ) :=
    IsFiltered.of_equivalence
      (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (integralScalarMap ℓ E) X)
  have he : f ≫ adj.unit.app B.obj = g ≫ adj.unit.app B.obj := by
    have h := congrArg (adj.homEquiv K.obj _) hfg
    change adj.unit.app K.obj ≫ _ = adj.unit.app K.obj ≫ _ at h
    exact (adj.unit.naturality f).trans (h.trans (adj.unit.naturality g).symm)
  have : IsIso (ℓ • 𝟙 ((integralScalarExtension ℓ E X).obj B.obj)) :=
    derived_nsmul_isIso ℓ E X _
  change IsIso (ℓ • 𝟙
    ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).leftDerivedFunctor.obj
      B.obj)) at this
  have he0 : (H.mapCocone (t.whisker J)).ι.app (ULift.up 0) f =
      (H.mapCocone (t.whisker J)).ι.app (ULift.up 0) g := by
    change f ≫ t.ι.app 0 = g ≫ t.ι.app 0
    have hz : t.ι.app 0 = adj.unit.app B.obj := scalar_unit_cocone_zero ℓ adj B.obj
    simpa only [hz] using he
  obtain ⟨n, α, β, hn⟩ := Concrete.isColimit_exists_of_rep_eq
    (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ B.obj ⋙ H) hc f g he0
  have hα : α = homOfLE (show (ULift.up 0 : ULift.{u + 1} ℕ) ≤ n by exact Nat.zero_le n.down) :=
    Subsingleton.elim _ _
  have hβ : β = α := Subsingleton.elim _ _
  rw [hβ, hα] at hn
  change f ≫ (integralLocalizationSequence ℓ B.obj).map
      (homOfLE (show 0 ≤ n.down by omega)) =
    g ≫ (integralLocalizationSequence ℓ B.obj).map
      (homOfLE (show 0 ≤ n.down by omega)) at hn
  have hmap (k : ℕ) : (integralLocalizationSequence ℓ B.obj).map
      (homOfLE (show 0 ≤ k by omega)) = ℓ ^ k • 𝟙 B.obj :=
    scalar_sequence_map ℓ B.obj k
  rw [hmap] at hn
  exact ⟨n.down, by simpa only [Preadditive.comp_nsmul, Category.comp_id] using hn⟩

end CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-! ### The inclusion `𝒪_{E,X} ⟶ E_X` -/

/-! ### Extension of scalars on bounded constructible complexes -/

/-! ### `E` as `𝒪_E` with `ℓ` inverted -/

variable [TopologicalSpace.NoetherianSpace X]

-- Keep the coefficient pullback and derived functors abstract during proof elaboration.
attribute [local irreducible] upperStarFromPoint Mod.extendScalars
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

end AlgebraicGeometry.ProEtale

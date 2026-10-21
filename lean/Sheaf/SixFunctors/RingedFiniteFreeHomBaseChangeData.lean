/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import Sheaf.Algebra.Homology.ScalarHomExtensionKFlat
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
/-! # Normalized tensor comparison for scalar extension

Source: Stacks Project, Tags 07A4 and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

open MonoidalCategory in
private theorem tensorMap_factor
    {A : Type c} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasCoproducts.{0} A]
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor A) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor A) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

open MonoidalCategory in
private theorem tensorPullbackTotal_naturality
    {A : Type c} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    {B : Type r} [Category.{w} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom =
        (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap
      ((L.mapHomologicalComplex (.up ℤ)).map f)
      ((L.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor B) (.up ℤ) ≫
        tensorPullbackTotal L e he P' Q' =
      tensorPullbackTotal L e he P Q ≫ (L.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)) := by
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (L.map a ⊗ₘ L.map b) ≫ (e X' Y').inv =
        (e X Y).inv ≫ L.map (a ⊗ₘ b) := by
    apply (cancel_mono (e X' Y').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, tensorPullbackTotal,
    HomologicalComplex.ι_mapBifunctorMap_assoc, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc]
  change (L.map (f.f a) ▷ L.obj (Q.X b)) ≫
    (L.obj (P'.X a) ◁ L.map (g.f b)) ≫ _ = _
  rw [← tensorHom_def_assoc]
  change (L.map (f.f a) ⊗ₘ L.map (g.f b)) ≫ (e (P'.X a) (Q'.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P' Q' (curriedTensor A) a b n hab) =
    (e (P.X a) (Q.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n hab) ≫
        L.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)).f n)
  rw [← Category.assoc, hi, Category.assoc, ← L.map_comp]
  congr 2
  rw [← L.map_comp]
  congr 1
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rw [tensorHom_def, Category.assoc]
  rfl

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

/-- A pure scalar-extension section, transported along the specified object equality.
It is the sheafification unit applied to s tensor x; no basis is used.
Source: Stacks 03EK, 08J9
(blueprint: lem-sf-ringed-finite-free-hom-base-change). -/
def ringedFiniteFreeScalarSection
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U)
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))


/-- The actual scalar tensor comparison on complexes and preservation of K-flatness.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 06YT and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-complex).

Proof: on sheafified pure tensors send s tensor (x tensor y) to
(s tensor x) tensor (1 tensor y). The inverse multiplies the scalars.
Balanced relations make both maps well-defined, and sheafification extends them.
Naturality in both factors gives a map on total complexes: the two tensor
differentials are preserved separately, including the sign on the second one.
Extension is a left adjoint and preserves the coproducts in each total degree,
so these mutually inverse maps assemble to a natural chain isomorphism.
For an acyclic S-complex F, restriction is exact and U(F) is acyclic.
The cancellation isomorphism U(F tensor_S E(P)) = U(F) tensor_R P
identifies the signed total differentials. K-flatness of P makes the right side
acyclic. Faithful exact restriction detects acyclicity, proving E(P) K-flat.
The generator formula is the same pure-tensor formula at scalar 1.
The argument includes the zero algebra and all unbounded complexes. -/
theorem ringedFiniteFreeHomBaseChange_complex
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ) :
    ∃ (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          D.E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (D.E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (D.E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S),
      (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y)) ∧
      (∀ (P : CochainComplex (SheafOfModules.{max c v r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
          CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    open MonoidalCategory WeilConjectures SheafOfModules in by
  classical
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients S
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  rcases D with ⟨E, hobj, hmap, _⟩
  dsimp only [DerivedChangeOfRingsCochainModel.E,
    DerivedChangeOfRingsCochainModel.obj_eq]
  let (A : Sheaf J CommRingCat.{max c v r}) :=
    HasDerivedCategory.standard (scalarModules J A)
  obtain ⟨s⟩ : Nonempty (ScalarDerivedPair φ) := by
    obtain ⟨M, _, _⟩ := scalarInternalHomAdjunction_exists.{c, v, r} (J := J)
    exact ⟨M.scalar φ⟩
  have hE : E = s.extension := by
    refine Functor.ext (fun N ↦ (hobj N).trans (s.extension_obj N).symm) ?_
    intro N N' f
    rw [hmap, s.extension_map]
    simp
  subst E
  let A := scalarModules J R
  let B := scalarModules J S
  let := monoidalCategory R
  let := monoidalCategory S
  let := symmetricCategory R
  let := symmetricCategory S
  let := s.extension_additive
  have (X : A) : (tensorLeft X).Additive := tensorLeft_additive_independent R X
  have (X : A) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  have (X : B) : (tensorLeft X).Additive := tensorLeft_additive_independent S X
  have (X : B) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  let : MonoidalPreadditive A :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let : MonoidalPreadditive B :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  obtain ⟨e, he, hgen⟩ :=
    SheafOfModules.ScalarHomOrdinary.scalarOrdinaryTensorComparison_exists φ s
  let F := scalarComplex s.extension s.extension_additive
  let tR := coefficientTotalTensor.{r, c, v} J R
  let tS := coefficientTotalTensor.{r, c, v} J S
  have hiso (P Q : CochainComplex A ℤ) :
      IsIso (tensorPullbackTotal s.extension e he P Q) :=
    tensorPullbackTotal_isIso s.extension e he (scalarRestriction φ) s.ordinaryAdjunction P Q
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (tensorPullbackTotal s.extension e he X.1 X.2)
      (hiso X.1 X.2)) (by
        intro X Y f
        dsimp only [F, tR, tS, scalarComplex, Functor.comp_map, Functor.prod_map]
        simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
        exact tensorPullbackTotal_naturality s.extension e he f.1 f.2)
  let b := b0.symm
  have hg (P Q : CochainComplex A ℤ) (p q k : ℤ) (h : p + q = k)
      (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
      ((b.app (P, Q)).hom.f k).val.app V
          (((s.ordinaryAdjunction.unit.app _).val.app V)
            (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
        coefficientTensorGenerator.{r, c, v} J S (F.obj P) (F.obj Q) p q k h V
          (((s.ordinaryAdjunction.unit.app _).val.app V) x)
          (((s.ordinaryAdjunction.unit.app _).val.app V) y) := by
    let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q k h
    let ι' := CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q) (curriedTensor B) p q k h
    let z := (HomologicalComplex.eval B (.up ℤ) k).mapIso (b0.app (P, Q))
    have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ s.extension.map ι := by
      change ι' ≫ tensorPullbackTotalComponent s.extension e P Q k = _
      exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
    have hi : s.extension.map ι ≫ z.inv = (e (P.X p) (Q.X q)).hom ≫ ι' := by
      apply (cancel_mono z.hom).mp
      erw [Category.assoc, z.inv_hom_id, Category.comp_id, Category.assoc, hz,
        Iso.hom_inv_id_assoc]
    have hu := congrArg (fun f ↦ f.val.app V
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))
      (s.ordinaryAdjunction.unit.naturality ι)
    have hh := congrArg (fun f ↦ f.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) hi
    change z.inv.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) = _
    change ((s.ordinaryAdjunction.unit.app _).val.app V)
      (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) =
      (s.extension.map ι).val.app V (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) at hu
    erw [hu]
    exact hh.trans (congrArg (ι'.val.app V) (hgen _ _ V x y))
  have hunit (N : scalarModules J R) (V : Cᵒᵖ) (x : N.val.obj V) :
      ringedFiniteFreeScalarSection.{c, v, r} J φ s.extension hobj N V 1 x =
        (s.ordinaryAdjunction.unit.app N).val.app V x := by
    have hh := s.ordinaryUnit N V x
    change (eqToHom (s.extension_obj N)).val.app V
        ((s.ordinaryAdjunction.unit.app N).val.app V x) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        (changeOfRingsPresheaf φ N)).app V)
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) at hh
    unfold ringedFiniteFreeScalarSection
    rw [← hh]
    exact congrArg (fun f ↦ f.val.app V
      ((s.ordinaryAdjunction.unit.app N).val.app V x))
        (eqToIso (s.extension_obj N)).hom_inv_id
  refine ⟨b, ?_, ?_⟩
  · intro P Q p q V x y
    exact (congrArg (fun z ↦ ((b.hom.app (P, Q)).f (p + q)).val.app V z)
      (hunit (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q)) V
        (coefficientTensorGenerator.{r, c, v} J R
          P Q p q (p + q) rfl V x y))).trans
      ((hg P Q p q (p + q) rfl V x y).trans
        (congrArg₂ (fun x' y' ↦ coefficientTensorGenerator.{r, c, v} J S
          (F.obj P) (F.obj Q) p q (p + q) rfl V x' y')
            (hunit (P.X p) V x).symm (hunit (Q.X q) V y).symm))
  · exact fun P hP ↦ scalarExtension_preservesKFlat φ s P hP

end Site
end CategoryTheory

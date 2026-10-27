/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.LocalizedStrictTensorData
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Sheaf.SecSmoothPurity.CochainTensorCoherenceData
import all Sheaf.SecSmoothPurity.CochainTensoratorExistence
import Sheaf.SecSmoothPurity.ModuleTensorGenerators
import Mathlib.Algebra.Homology.Functor

/-! # Strict coefficient augmentation and homotopical reduction

Source: Stacks Project, Tags 03EK, 06YT, 02MZ, 04VG and 04VK; completed-pullback
invocation in the CBC blueprint proof.
(blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r b w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.StrictCoefficientAugmentation

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.sheafCompose

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})

/-- Flat-term K-flat inputs, with their full chain-map category.
Source: Stacks 06YS (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
abbrev Inputs := ObjectProperty.FullSubcategory (Resolving.{c, v, r} O)

/-- The inclusion retains all chain maps, not only quasi-isomorphisms.
Source: Stacks 06YS (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
abbrev inclusion : Inputs.{c, v, r} O ⥤ CochainComplex (Modules.{c, v, r} O) ℤ :=
  ObjectProperty.ι (Resolving.{c, v, r} O)

/-- Constant strict towers of complexes, with identity transitions.
Source: Stacks 02MZ (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
abbrev constantComplex : CochainComplex (Modules.{c, v, r} O) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, r} O) ℤ :=
  (Functor.const ℕᵒᵖ : Modules.{c, v, r} O ⥤ _).mapHomologicalComplex (.up ℤ)

/-- The already constructed strict tensor tower, applied degreewise.
Source: Stacks 03EK (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
abbrev reductionComplex (S : AlgebraTowers.{c, v, r} O) :=
  (reduction.{c, v, r} O S).mapHomologicalComplex (.up ℤ)

/-- The unit sections of the coefficient tower define its canonical module unit.
Source: Stacks 03EK (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
def coefficientUnit (S : AlgebraTowers.{c, v, r} O) :
    (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules.{c, v, r} O)) ⟶
      S ⋙ algebraModules.{c, v, r} O where
  app n :=
    { val := PresheafOfModules.homMk
        (Functor.whiskerRight (S.obj n).hom.hom
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
          intro U a x
          change O.obj.obj U at a x
          change (S.obj n).hom.hom.app U (a * x) =
            (S.obj n).hom.hom.app U a * (S.obj n).hom.hom.app U x
          exact map_mul _ _ _) }
  naturality {m n} f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (S.obj n).hom.hom.app U x =
      (S.map f).right.hom.app U ((S.obj m).hom.hom.app U x)
    exact (congrArg (fun t ↦ t.hom.app U x) (Under.w (S.map f))).symm

/-- The module augmentation of constant towers: the inverse right unitor followed by
tensoring with the coefficient unit, so a section x maps to x tensor 1 at every level.
Source: Stacks 03EK (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
def towerAugmentation (S : AlgebraTowers.{c, v, r} O) :
    Functor.const ℕᵒᵖ ⟶ reduction.{c, v, r} O S :=
  Functor.whiskerLeft (Functor.const ℕᵒᵖ)
    ((rightUnitorNatIso (ℕᵒᵖ ⥤ Modules.{c, v, r} O)).inv ≫
      (curriedTensor (ℕᵒᵖ ⥤ Modules.{c, v, r} O)).flip.map
        (coefficientUnit.{c, v, r} O S))

/-- The canonical augmentation x maps to x tensor 1, lifted degreewise.
Source: Stacks 03EK (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
def augmentation (S : AlgebraTowers.{c, v, r} O) :
    constantComplex.{c, v, r} O ⟶ reductionComplex.{c, v, r} O S :=
  NatTrans.mapHomologicalComplex
    (towerAugmentation.{c, v, r} O S) (.up ℤ)

/-- Quasi-isomorphisms in the full category of resolving inputs.
Source: Stacks 05RU (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
def weakEquivalences : MorphismProperty (Inputs.{c, v, r} O) :=
  (HomologicalComplex.quasiIso (Modules.{c, v, r} O) (.up ℤ)).inverseImage
    (inclusion.{c, v, r} O)


/-- The actual augmentation after passage to chain homotopy classes.
Source: Stacks derived.tex, complexes and homotopies
(blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
def homotopyAugmentation (S : AlgebraTowers.{c, v, r} O) :
    (Functor.const ℕᵒᵖ : Modules.{c, v, r} O ⥤ _).mapHomotopyCategory (.up ℤ) ⟶
      (reduction.{c, v, r} O S).mapHomotopyCategory (.up ℤ) :=
  NatTrans.mapHomotopyCategory
    (towerAugmentation.{c, v, r} O S) (.up ℤ)

/-- Constant inputs followed by the localization of strict tower complexes.
Source: Stacks 05RU (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
abbrev constantLocalized :=
  inclusion.{c, v, r} O ⋙ constantComplex.{c, v, r} O ⋙ DerivedCategory.Q

/-- Tensor reduction followed by the localization of strict tower complexes.
Source: Stacks 05RU (blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality). -/
abbrev reductionLocalized (S : AlgebraTowers.{c, v, r} O) :=
  inclusion.{c, v, r} O ⋙ reductionComplex.{c, v, r} O S ⋙ DerivedCategory.Q

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

private theorem tensor_quasiIso {P P' : CochainComplex (Modules.{c, v, r} O) ℤ}
    (f : P ⟶ P') (hP : P.IsKFlatIndependentCoefficients)
    (hP' : P'.IsKFlatIndependentCoefficients) (hf : QuasiIso f)
    (N : Modules.{c, v, r} O) :
    QuasiIso (((tensorRight N).mapHomologicalComplex (.up ℤ)).map f) := by
  have hk := isKFlat_mappingCone_independent f hP hP'
  have ha := (CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf
  let K := CochainComplex.mappingCone f
  have ht := tensor_acyclic_of_isKFlat_independent K hk ha
    ((HomologicalComplex.single _ (.up ℤ) 0).obj N)
  have hleft : (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
    intro i
    exact (ht i).of_iso (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) N K)
  have hright : (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
    exact HomologicalComplex.Acyclic.of_iso hleft
      ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight N)
        (.up ℤ)).app K)
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  exact HomologicalComplex.Acyclic.of_iso hright
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (tensorRight N))

/-- Strict coefficient augmentation, homotopy and quasi-isomorphism descent, and
termwise additive compatibility, including shifts and the actual cone triangles.
The level indexed by n is the paper's level n+1. AlgebraTowers packages precisely
p_n, q_n and q_n p_(n+1)=p_n, with no flatness imposed on a coefficient.

Source: CBC completed-extension-zero comparison proof, completed-pullback invocation;
Stacks Tags 03EK, 06YT, 02MZ, 04VG and 04VK.
(blueprint: lem-cbc-strict-coefficient-augmentation-homotopicality).

Proof:
1. Use the existing algebraModules and reduction constructions. In degree i their
   sections are the sheafified tensors P^i tensor B_n, the differentials are d tensor 1,
   transitions are 1 tensor q_n, and chain maps are f tensor 1. The compatibility of
   the algebra maps makes every transition O-linear. Tensor functoriality gives all
   complex, strict-tower and functor laws.
2. The coefficientUnit has section map p_n and preserves 1. The right inverse unitor
   followed by tensoring that unit sends x to x tensor 1. The ring-map and tensor
   relations give strict transition compatibility, the chain relation, and naturality.
3. For a homotopy h use its constant tower for Delta and h tensor 1 for reduction.
   Additivity gives the homotopy equation and the latter commutes with transitions.
   Applying mapHomotopyCategory gives the displayed compatible homotopy augmentation.
4. Apply lem-pur-change-of-rings-kflat-quasi-iso levelwise (Stacks 06YT). Restriction
   of scalars retains the abelian sheaf, hence preserves cohomology and quasi-isos.
   This uses K-flatness only before reduction, with arbitrary coefficient rings.
5. By lem-weil-tower-category-levelwise-abelian, cohomology is levelwise, so Delta(f)
   and R(f) are quasi-isomorphisms of strict tower complexes.
6. Apply clauses (1) and (2) of lem-weil-pbc-localization-universal-property to the
   two localized functors and their augmentation. The unique descended component is
   phi_Delta followed by Q(a) followed by phi_R inverse. Naturality also applies to
   inverted quasi-isomorphisms by multiplying its square by the component inverses.
7. For additive E apply E degreewise and levelwise. E(id)=id retains constant
   transitions. Applying E to f-g=dh+hd gives homotopy descent. Additivity preserves
   the signed shifted differential and supplies the canonical commuting-shift maps.
8. The canonical biproduct comparison identifies E(Y^i directsum X^(i+1)) with
   E(Y^i) directsum E(X^(i+1)). It sends the cone differential matrix to the cone
   differential of E(f), including the inclusion and signed projection. These maps
   commute with tower transitions, giving the asserted isomorphism of cone triangles.
-/
theorem strict_coefficient_augmentation_homotopicality
    (S : AlgebraTowers.{c, v, r} O) :
    (∀ (P : Inputs.{c, v, r} O) (i : ℤ) (n : ℕᵒᵖ) (U : Cᵒᵖ)
      (x : (P.obj.X i).val.obj U),
      ((((augmentation.{c, v, r} O S).app P.obj).f i).app n).val.app U x =
        LocalizedStrictTensor.pure.{c, v, r} O (P.obj.X i)
          ((S ⋙ algebraModules.{c, v, r} O).obj n) U x
          (1 : (S.obj n).right.obj.obj U)) ∧
    (∀ (P P' : Inputs.{c, v, r} O) (f : P ⟶ P'),
      (augmentation.{c, v, r} O S).app P.obj ≫
          (reductionComplex.{c, v, r} O S).map f.hom =
        (constantComplex.{c, v, r} O).map f.hom ≫
          (augmentation.{c, v, r} O S).app P'.obj) ∧
    (∀ (P P' : Inputs.{c, v, r} O) (f g : P ⟶ P'),
      Nonempty (Homotopy f.hom g.hom) →
        Nonempty (Homotopy ((constantComplex.{c, v, r} O).map f.hom)
          ((constantComplex.{c, v, r} O).map g.hom)) ∧
        Nonempty (Homotopy ((reductionComplex.{c, v, r} O S).map f.hom)
          ((reductionComplex.{c, v, r} O S).map g.hom))) ∧
    (∀ P : Inputs.{c, v, r} O,
      ((Functor.const ℕᵒᵖ : Modules.{c, v, r} O ⥤ _).mapHomotopyCategoryFactors
          (.up ℤ)).hom.app P.obj ≫
          (HomotopyCategory.quotient _ (.up ℤ)).map
            ((augmentation.{c, v, r} O S).app P.obj) =
        (homotopyAugmentation.{c, v, r} O S).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P.obj) ≫
          ((reduction.{c, v, r} O S).mapHomotopyCategoryFactors (.up ℤ)).hom.app P.obj) ∧
    (∀ (P P' : Inputs.{c, v, r} O) (f : P ⟶ P'),
      QuasiIso f.hom →
        QuasiIso ((constantComplex.{c, v, r} O).map f.hom) ∧
        QuasiIso ((reductionComplex.{c, v, r} O S).map f.hom)) ∧
    (∃ (FΔ FR : (weakEquivalences.{c, v, r} O).Localization ⥤
          DerivedCategory (ℕᵒᵖ ⥤ Modules.{c, v, r} O))
      (φΔ : (weakEquivalences.{c, v, r} O).Q ⋙ FΔ ≅ constantLocalized.{c, v, r} O)
      (φR : (weakEquivalences.{c, v, r} O).Q ⋙ FR ≅ reductionLocalized.{c, v, r} O S),
      ∃! a : FΔ ⟶ FR, ∀ P : Inputs.{c, v, r} O,
        a.app ((weakEquivalences.{c, v, r} O).Q.obj P) =
          φΔ.hom.app P ≫ DerivedCategory.Q.map
            ((augmentation.{c, v, r} O S).app P.obj) ≫ φR.inv.app P) ∧
    (∀ (B : Type b) [Category.{w} B] [Abelian B]
      (E : Modules.{c, v, r} O ⥤ B) [E.Additive],
      Nonempty (constantComplex.{c, v, r} O ⋙
          (CategoryTheory.StrictReduction.termwise E).mapHomologicalComplex (.up ℤ) ≅
        E.mapHomologicalComplex (.up ℤ) ⋙
          (Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ)) ∧
      (∀ (P : CochainComplex (Modules.{c, v, r} O) ℤ) (i : ℤ)
        (m n : ℕᵒᵖ) (f : m ⟶ n),
        ((((CategoryTheory.StrictReduction.termwise E).mapHomologicalComplex (.up ℤ)).obj
          ((constantComplex.{c, v, r} O).obj P)).X i).map f = 𝟙 (E.obj (P.X i))) ∧
      Nonempty (HomotopyCategory.quotient _ (.up ℤ) ⋙
          (CategoryTheory.StrictReduction.termwise E).mapHomotopyCategory (.up ℤ) ≅
        (CategoryTheory.StrictReduction.termwise E).mapHomologicalComplex (.up ℤ) ⋙
          HomotopyCategory.quotient _ (.up ℤ)) ∧
      Nonempty (((CategoryTheory.StrictReduction.termwise E).mapHomotopyCategory
          (.up ℤ)).CommShift ℤ) ∧
      (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, r} O) ℤ) (f : X ⟶ Y),
        Nonempty (((CategoryTheory.StrictReduction.termwise E).mapHomotopyCategory
            (.up ℤ)).mapTriangle.obj (CochainComplex.mappingCone.triangleh f) ≅
          CochainComplex.mappingCone.triangleh
            (((CategoryTheory.StrictReduction.termwise E).mapHomologicalComplex
              (.up ℤ)).map f)))) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P i n U x
    change (P.obj.X i ◁ ((coefficientUnit.{c, v, r} O S).app n)).val.app U
      ((ρ_ (P.obj.X i)).inv.val.app U x) = _
    have hu := CochainTensorComparison.UnitConstruction.unitor_pure O (P.obj.X i) U x 1
    have hi := congrArg ((ρ_ (P.obj.X i)).inv.val.app U) hu
    have hi' : (ρ_ (P.obj.X i)).inv.val.app U x =
        LocalizedStrictTensor.pure.{c, v, r} O (P.obj.X i) (𝟙_ _) U x (1 : O.obj.obj U) := by
      have hh := (by
        simpa only [one_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
          ← comp_val, Iso.hom_inv_id, id_val, PresheafOfModules.id_app,
          ModuleCat.id_apply] using hi.symm : _)
      convert hh using 1
      rfl
    rw [hi']
    rw [← id_tensorHom]
    have hm := CategoryTheory.CochainPullback.moduleTmul_map (R := O)
      (𝟙 (P.obj.X i)) ((coefficientUnit.{c, v, r} O S).app n) U x
        (1 : O.obj.obj U)
    change _ = CategoryTheory.CochainPullback.moduleTmul (P.obj.X i)
      ((S ⋙ algebraModules.{c, v, r} O).obj n) U x
        ((S.obj n).hom.hom.app U (1 : O.obj.obj U)) at hm
    rw [map_one] at hm
    convert hm using 1 <;> rfl
  · intro P P' f
    exact ((augmentation.{c, v, r} O S).naturality f.hom).symm
  · intro P P' f g ⟨h⟩
    exact ⟨⟨(Functor.const ℕᵒᵖ).mapHomotopy h⟩,
      ⟨(reduction.{c, v, r} O S).mapHomotopy h⟩⟩
  · intro P
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  · intro P P' f hf
    constructor
    · exact (HomologicalComplex.quasiIso_iff_evaluation _).2 (fun _ ↦ hf)
    · apply (HomologicalComplex.quasiIso_iff_evaluation _).2
      intro n
      exact tensor_quasiIso.{c, v, r} O f.hom P.property.1 P'.property.1 hf
        ((S ⋙ algebraModules.{c, v, r} O).obj n)
  · let W := weakEquivalences.{c, v, r} O
    let L := W.Q
    have hΔ : W.IsInvertedBy (constantLocalized.{c, v, r} O) := by
      intro P P' f hf
      have hq : QuasiIso ((constantComplex.{c, v, r} O).map f.hom) :=
        (HomologicalComplex.quasiIso_iff_evaluation _).2 (fun _ ↦ hf)
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
    have hR : W.IsInvertedBy (reductionLocalized.{c, v, r} O S) := by
      intro P P' f hf
      have hq : QuasiIso ((reductionComplex.{c, v, r} O S).map f.hom) := by
        apply (HomologicalComplex.quasiIso_iff_evaluation _).2
        intro n
        exact tensor_quasiIso.{c, v, r} O f.hom P.property.1 P'.property.1 hf
          ((S ⋙ algebraModules.{c, v, r} O).obj n)
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
    let FΔ := Localization.lift (constantLocalized.{c, v, r} O) hΔ L
    let FR := Localization.lift (reductionLocalized.{c, v, r} O S) hR L
    let τ : constantLocalized.{c, v, r} O ⟶ reductionLocalized.{c, v, r} O S :=
      Functor.whiskerLeft (inclusion.{c, v, r} O)
        (Functor.whiskerRight (augmentation.{c, v, r} O S) DerivedCategory.Q)
    refine ⟨FΔ, FR, Localization.fac _ hΔ L, Localization.fac _ hR L,
      Localization.liftNatTrans L W _ _ FΔ FR τ, ?_, ?_⟩
    · intro P
      exact Localization.liftNatTrans_app L W _ _ FΔ FR τ P
    · intro a ha
      apply Localization.natTrans_ext L W
      intro P
      exact (ha P).trans (Localization.liftNatTrans_app L W _ _ FΔ FR τ P).symm
  · intro B _ _ E _
    refine ⟨?_, ?_, ?_, ⟨inferInstance⟩, ?_⟩
    · exact ⟨Functor.mapHomologicalComplexCompIso
        (CategoryTheory.StrictReduction.constantSquare E) (.up ℤ)⟩
    · intro P i m n f
      exact E.map_id _
    · exact ⟨(CategoryTheory.StrictReduction.termwise E).mapHomotopyCategoryFactors _⟩
    · intro X Y f
      exact ⟨CochainComplex.mappingCone.mapTrianglehIso f
        (CategoryTheory.StrictReduction.termwise E)⟩

end SheafOfModules.StrictCoefficientAugmentation

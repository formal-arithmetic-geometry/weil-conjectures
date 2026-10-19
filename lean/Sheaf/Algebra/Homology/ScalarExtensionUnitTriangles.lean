/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.Algebra.Homology.DerivedCoefficientMapDescent
import Sheaf.Algebra.Homology.ScalarExtensionCounitProperties

/-! # The derived scalar-extension unit and distinguished triangles

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT, 06YY;
derived.tex, Tags 014V, 015F and 06XN
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles).

The ordinary functor is specified by its existing tensor objects and maps. The
universal derived pair is arbitrary, with the counit-compatible canonical shift.
Restriction's exactness is asserted, rather than assumed. The roof predicate
specifies its comparison by the derived counit, including every K-flat resolution.
-/

@[expose] public section

set_option autoImplicit false

universe u v r wR wS a b va vb

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules

/-- Apply an ordinary coefficient natural transformation termwise to complexes.
The identity and composite comparison maps have identity components, so its component
in degree `n` is precisely `ι.app (P.X n)`.
Source: Stacks Project, Tag 03EK and the explicit complex map in Tag 06YY
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles). -/
noncomputable def scalarExtensionCoefficientComplexMap
    {A : Type a} [Category.{va} A] [Preadditive A]
    {B : Type b} [Category.{vb} B] [Preadditive B]
    (E : A ⥤ B) [E.Additive] (V : B ⥤ A) [V.Additive]
    (ι : 𝟭 A ⟶ E ⋙ V) (P : CochainComplex A ℤ) :
    P ⟶ (V.mapHomologicalComplex (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app P ≫
    (NatTrans.mapHomologicalComplex ι (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ V)) (.up ℤ)).inv.app P

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def scalarCoefficientMap (φ : R ⟶ S)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) :
    M ⟶ (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (changeOfRings.{v, u, r} φ M) := by
  let t := (PresheafOfModules.sheafificationAdjunction.{r}
    (J := J) (R := derivedChangeRingIndependentCoefficients J S)
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
    (changeOfRingsPresheaf.{v, u, r} φ M)
  refine ⟨{ app := fun U ↦
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U) ≫
      (ModuleCat.restrictScalars (φ.hom.app U).hom).map (t.app U)
            naturality := ?_ }⟩
  intro U V f
  ext x
  have ht := PresheafOfModules.naturality_apply t f
    ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U) x)
  dsimp at ht ⊢
  erw [← ht]
  change (t.app V) ((@TensorProduct.tmul (R.obj.obj V) _ _ _ _ _
      (Module.compHom _ (φ.hom.app V).hom) _ (1 : S.obj.obj V))
      (show M.val.obj V from M.val.map f x)) = (t.app V) (changeOfRingsMap.{v, u, r} φ M f
      ((@TensorProduct.tmul (R.obj.obj U) _ _ _ _ _
      (Module.compHom _ (φ.hom.app U).hom) _ (1 : S.obj.obj U)) x))
  congr 1
  change (@TensorProduct.tmul (R.obj.obj V) _ _ _ _ _
      (Module.compHom _ (φ.hom.app V).hom) _ (1 : S.obj.obj V))
      (show M.val.obj V from M.val.map f x) =
    changeOfRingsMap.{v, u, r} φ M f
      ((@TensorProduct.tmul (R.obj.obj U) _ _ _ _ _
      (Module.compHom _ (φ.hom.app U).hom) _ (1 : S.obj.obj U)) x)
  simpa! only [changeOfRingsMap, map_one] using
    (Classical.choose_spec (exists_changeOfRingsMap φ M f) (1 : S.obj.obj U) x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCoefficientMap_naturality
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    {M N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)} (f : M ⟶ N) :
    f ≫ scalarCoefficientMap φ N = scalarCoefficientMap φ M ≫
      (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
        (changeOfRingsHom.{v, u, r} φ M f) := by
  let g : changeOfRingsPresheaf.{v, u, r} φ M ⟶ changeOfRingsPresheaf.{v, u, r} φ N :=
    { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality φ M f }
  have hn := (PresheafOfModules.sheafificationAdjunction.{r}
    (J := J) (R := derivedChangeRingIndependentCoefficients J S)
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.naturality g
  ext U x
  have he := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app U) hn)
      ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U) x)
  dsimp [scalarCoefficientMap, changeOfRingsHom]
  change ((PresheafOfModules.sheafificationAdjunction.{r}
    (J := J) (R := derivedChangeRingIndependentCoefficients J S)
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
    (changeOfRingsPresheaf φ N)).app U
    ((@TensorProduct.tmul (R.obj.obj U) _ _ _ _ _
      (Module.compHom _ (φ.hom.app U).hom) _ (1 : S.obj.obj U)) (f.val.app U x)) = _
  have he' :
      ((PresheafOfModules.sheafificationAdjunction.{r}
        (J := J) (R := derivedChangeRingIndependentCoefficients J S)
        (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (changeOfRingsPresheaf φ N)).app U
        ((@TensorProduct.tmul (R.obj.obj U) _ _ _ _ _
      (Module.compHom _ (φ.hom.app U).hom) _ (1 : S.obj.obj U)) (f.val.app U x)) =
      ((PresheafOfModules.sheafification.{r}
        (J := J) (R := derivedChangeRingIndependentCoefficients J S)
        (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).map g).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{r}
          (J := J) (R := derivedChangeRingIndependentCoefficients J S)
          (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
          (changeOfRingsPresheaf φ M)).app U
          ((@TensorProduct.tmul (R.obj.obj U) _ _ _ _ _
      (Module.compHom _ (φ.hom.app U).hom) _ (1 : S.obj.obj U)) x)) := by
    exact he
  exact he'


set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarCoefficientNatTrans (φ : R ⟶ S)
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M, E.obj M = changeOfRings.{v, u, r} φ M)
    (hmap : ∀ {M N} (f : M ⟶ N),
      E.map f = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M f ≫ eqToHom (h N).symm) :
    𝟭 (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⟶
      E ⋙ restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) where
  app M := scalarCoefficientMap φ M ≫
    (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
      (eqToHom (h M).symm)
  naturality {M N} f := by
    dsimp only [Functor.id_map, Functor.comp_map]
    rw [hmap]
    simp only [Functor.map_comp, Category.assoc]
    have hc : (eqToHom (h M).symm) ≫ eqToHom (h M) = 𝟙 _ := by simp
    rw [← Functor.map_comp_assoc, hc, CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun z ↦ z ≫
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
          (eqToHom (h N).symm)) (scalarCoefficientMap_naturality φ f)

private theorem scalarRestriction_exact
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    exactFunctor _ _ (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  let R' := derivedChangeRingIndependentCoefficients J R
  let S' := derivedChangeRingIndependentCoefficients J S
  let V := restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have hcol (A : Sheaf J RingCat.{r}) : PreservesFiniteColimits (toSheaf.{r} A) := by
    constructor
    intro K _ _
    constructor
    intro F
    let L := PresheafOfModules.sheafification.{r} (𝟙 A.obj)
    let adj := PresheafOfModules.sheafificationAdjunction.{r} (𝟙 A.obj)
    let G := F ⋙ (SheafOfModules.forget A ⋙ PresheafOfModules.restrictScalars (𝟙 A.obj))
    let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
    have : PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{r}) :=
      (sheafificationAdjunction J AddCommGrpCat.{r}).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have : PreservesColimit G (L ⋙ toSheaf.{r} A) :=
      preservesColimit_of_natIso G (PresheafOfModules.sheafificationCompToSheaf (𝟙 A.obj)).symm
    let hc := colimit.isColimit G
    have : PreservesColimit (G ⋙ L) (toSheaf.{r} A) :=
      preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
        (isColimitOfPreserves (L ⋙ toSheaf.{r} A) hc)
    exact preservesColimit_of_iso_diagram (toSheaf.{r} A) e
  have := hcol R'
  have := hcol S'
  have : PreservesFiniteLimits (V ⋙ toSheaf R') :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{r} S'))
  have : PreservesFiniteColimits (V ⋙ toSheaf R') :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{r} S'))
  have : ReflectsFiniteColimits (toSheaf.{r} R') := inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves V (toSheaf R'),
    preservesFiniteColimits_of_reflects_of_preserves V (toSheaf R')⟩

/-- The coefficient roof characterization, including its canonical comparison.
`c` is the inverse of the derived image of the resolution followed by the counit:
`F(Qp) ≫ c.hom = ε_P`. The second equality says that the roof with denominator `Qp`
and numerator the termwise coefficient map represents `η_C`. The comparison is an
isomorphism for every K-flat resolution, with no flatness condition on its terms.
Source: Stacks Project, Tags 06YS, 06YT and 06YY
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles). -/
def ScalarExtensionUnitRoof
    (φ : R ⟶ S)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)) [E.Additive]
    [PreservesFiniteLimits
      (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))]
    [PreservesFiniteColimits
      (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))]
    (F : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ι : 𝟭 (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⟶
      E ⋙ restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))
    (η : 𝟭 (DerivedCategory
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))) ⟶
      F ⋙ (restrictScalars.{r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory) : Prop :=
  ∀ (P K : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (p : P ⟶ K), CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      QuasiIso p →
    ∃ c : F.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P),
      F.map (DerivedCategory.Q.map p) ≫ c.hom = ε.app P ∧
      DerivedCategory.Q.map p ≫ η.app (DerivedCategory.Q.obj K) ≫
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          φ)).mapDerivedCategory.map
          c.hom ≫
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          φ)).mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map (scalarExtensionCoefficientComplexMap E
          (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) ι P)

/-- The canonical derived coefficient transformation is independent of resolutions,
commutes with the canonical shift and gives morphisms of distinguished triangles.
The parameters `E,h,hmap` specify ordinary tensor extension exactly, and `F,ε`
specify its universal left derived functor. The shift hypothesis on `ε` specifies
its canonical shift structure, rather than an arbitrary triangulated structure.
Source: Stacks Project, Tags 03EK, 06YS, 06YT, 06YY and derived.tex Tags 014V, 015F
(blueprint: lem-weil-pbc-scalar-extension-unit-triangles).

Proof:
1. Define the ordinary scalar map sectionwise by x to 1 tensor x, followed by
sheafification (def-pur-sheaf-tensor-product). It is linear and natural and commutes
with differentials. Termwise tensor preserves homotopies. Restriction preserves the
same kernels and sheafified cokernels, so is exact (def-pc-sheaf-restrict-scalars).
The exact derived factorization (lem-weil-pbc-exact-functor-derived-factorization)
identifies derived restriction of a complex with its termwise restriction.
2. Restrict to K-flat homotopy complexes with flat terms. They localize to D(R)
(lem-weil-pbc-site-derived-tensor-descent); the counit is invertible there
(lem-pur-derived-change-of-rings, lem-pur-left-derived-from-kflat-class). Compose
the localized scalar map with the inverse counit and restriction comparison.
The localization universal property (lem-weil-pbc-localization-universal-property)
extends this uniquely to a natural transformation eta on D(R).
3. Naturality at a flat-term K-flat resolution gives precisely the displayed roof.
Every complex has such a resolution (lem-pc-kflat-resolution), proving uniqueness.
4. For an arbitrary K-flat resolution P to K, resolve P by a flat-term K-flat T.
Both tensor images of T to P are quasi-isomorphic (lem-pur-derived-change-of-rings).
The equation E(t)i_T = i_P t and counit naturality identify the two roof formulas.
Thus the characterization covers all K-flat resolutions and is independent of them.
5. K-flatness is stable under shift (def-pc-kflat-complex). Scalar extension and
restriction have identity termwise shift comparisons and i_(P[1]) = i_P[1].
The counit-compatible shift (lem-sbc-derived-scalar-extension-counit-shift) and
exact derived restriction comparison turn these into the asserted equation on
K-flat models; localization extends the equality to all derived objects.
6. Both functors with these canonical shifts are triangulated. The first two
triangle squares are naturality. Naturality at the connecting arrow followed by
step 5 gives the third square, including its sign. No flatness of S, bounds,
constructibility, or points enter the argument. -/
theorem exists_scalarExtensionUnit_triangles
    (φ : R ⟶ S)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R),
      E.obj M = changeOfRings.{v, u, r} φ M)
    (hmap : ∀ {M N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)}
      (f : M ⟶ N),
      E.map f = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M f ≫ eqToHom (h N).symm)
    [E.Additive]
    (F : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ))]
    [F.CommShift ℤ] [NatTrans.CommShift ε ℤ] :
    ∃ (_ : PreservesFiniteLimits
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)))
      (_ : PreservesFiniteColimits
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))),
      F.IsTriangulated ∧
      ∃ ι : 𝟭 (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⟶
          E ⋙ restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ),
        (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
          (U : Cᵒᵖ) (x : M.val.obj U),
          (eqToHom (h M)).val.app U ((ι.app M).val.app U x) =
            (((PresheafOfModules.sheafificationAdjunction.{r}
              (J := J) (R := derivedChangeRingIndependentCoefficients J S)
              (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
              (changeOfRingsPresheaf.{v, u, r} φ M)).app U
              ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
                (M.val.obj U) x))) ∧
        ∃ η : 𝟭 (DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))) ⟶
            F ⋙ (restrictScalars.{r}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory,
          ScalarExtensionUnitRoof φ E F ε ι η ∧
          (∀ η' : 𝟭 (DerivedCategory (ringedSiteModules.{r}
            (derivedChangeRingIndependentCoefficients J R))) ⟶
              F ⋙ (restrictScalars.{r}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory,
            ScalarExtensionUnitRoof φ E F ε ι η' → η' = η) ∧
          (∀ X : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients
            J R)),
            η.app ((shiftFunctor _ (1 : ℤ)).obj X) ≫
            ((F ⋙ (restrictScalars.{r}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map
                φ)).mapDerivedCategory).commShiftIso
                (1 : ℤ)).hom.app X = (shiftFunctor _ (1 : ℤ)).map (η.app X)) ∧
          (∀ T : Triangle (DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))),
            T ∈ distTriang _ →
            (F ⋙ (restrictScalars.{r}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map
                φ)).mapDerivedCategory).mapTriangle.obj
                T ∈ distTriang _ ∧
            ∃ m : T ⟶ (F ⋙ (restrictScalars.{r}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map
                  φ)).mapDerivedCategory).mapTriangle.obj
                T,
              m.hom₁ = η.app T.obj₁ ∧ m.hom₂ = η.app T.obj₂ ∧ m.hom₃ = η.app T.obj₃) := by
  classical
  obtain ⟨hlim, hcol⟩ := scalarRestriction_exact φ
  let := hlim
  let := hcol
  let V := restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : PreservesFiniteLimits V := hlim
  have : PreservesFiniteColimits V := hcol
  obtain ⟨htri, hε⟩ := scalarExtension_counit_properties φ E h hmap F ε
  let := htri
  let ι := scalarCoefficientNatTrans φ E h hmap
  obtain ⟨η, hη, hshift⟩ := Functor.exists_derivedCoefficientMap E V ι F ε
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (fun K ↦ by
      obtain ⟨P, p, hP, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
      exact ⟨P, p, hP, hp⟩) hε
  have hroof : ScalarExtensionUnitRoof φ E F ε ι η := by
    intro P K p hP hp
    let := hp
    have := hε P hP
    have : IsIso (DerivedCategory.Q.map p) := inferInstance
    refine ⟨(asIso (F.map (DerivedCategory.Q.map p))).symm ≪≫ asIso (ε.app P), ?_, ?_⟩
    · simp
    · have hn := η.naturality (DerivedCategory.Q.map p)
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      change DerivedCategory.Q.map p ≫ η.app (DerivedCategory.Q.obj K) ≫
        V.mapDerivedCategory.map
          (inv (F.map (DerivedCategory.Q.map p)) ≫ ε.app P) ≫ _ = _
      rw [reassoc_of% hn]
      rw [V.mapDerivedCategory.map_comp]
      simp only [Category.assoc]
      rw [← V.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
        V.mapDerivedCategory.map_id, Category.id_comp]
      exact hη P
  refine ⟨hlim, hcol, htri, ι, ?_, η, hroof, ?_, hshift, ?_⟩
  · intro M U x
    have hh : ι.app M ≫ V.map (eqToHom (h M)) = scalarCoefficientMap φ M := by
      dsimp [ι, scalarCoefficientNatTrans]
      rw [Category.assoc, ← V.map_comp, eqToHom_trans, eqToHom_refl, V.map_id,
        Category.comp_id]
    have he := congrArg (fun f ↦ f.val.app U x) hh
    exact he
  · intro η' hroof'
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro K
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
    let := hp
    have : IsIso (DerivedCategory.Q.map p) := inferInstance
    obtain ⟨c, hc, he⟩ := hroof P K p hP hp
    obtain ⟨c', hc', he'⟩ := hroof' P K p hP hp
    have hcc : c'.hom = c.hom := (cancel_epi (F.map (DerivedCategory.Q.map p))).1
      (hc'.trans hc.symm)
    rw [hcc] at he'
    have heq := he'.trans he.symm
    apply (cancel_epi (DerivedCategory.Q.map p)).1
    apply (cancel_mono (V.mapDerivedCategory.map c.hom)).1
    apply (cancel_mono (V.mapDerivedCategoryFactors.hom.app
      ((E.mapHomologicalComplex (.up ℤ)).obj P))).1
    simpa only [Category.assoc] using heq
  · intro T hT
    refine ⟨Functor.map_distinguished _ T hT, ?_⟩
    refine ⟨{ hom₁ := η.app T.obj₁
              hom₂ := η.app T.obj₂
              hom₃ := η.app T.obj₃
              comm₁ := ?_
              comm₂ := ?_
              comm₃ := ?_ }, rfl, rfl, rfl⟩
    · exact η.naturality T.mor₁
    · exact η.naturality T.mor₂
    · change T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (η.app T.obj₁) =
        η.app T.obj₃ ≫ (F ⋙ V.mapDerivedCategory).map T.mor₃ ≫
          ((F ⋙ V.mapDerivedCategory).commShiftIso (1 : ℤ)).hom.app T.obj₁
      rw [← hshift, ← Category.assoc]
      simpa only [Functor.id_map, Category.assoc] using congrArg (fun f ↦ f ≫
        ((F ⋙ V.mapDerivedCategory).commShiftIso (1 : ℤ)).hom.app T.obj₁)
          (η.naturality T.mor₃)

end SheafOfModules

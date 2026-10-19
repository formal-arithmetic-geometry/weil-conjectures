/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Bounded-below filtered-colimit continuity of pro-etale direct images

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
`det-pe-bounded-continuity-direct-image.md` (blueprint:
`det-pe-bounded-continuity-direct-image`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The standard localization of module complexes at quasi-isomorphisms, as in the
recorded derived category of an abelian category.
Source: Stacks Project, Tag 05RU (blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable instance ringModuleSheaves_hasDerivedCategory {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    HasDerivedCategory (SheafOfModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- The module direct image over the direct-image coefficient sheaf.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable def ringModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ⥤
      SheafOfModules.{u + 1} ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := topology Y) (K := topology X)
    (S := (proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
    (R := R) (𝟙 _)

noncomputable instance ringModuleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (ringModuleDirectImage f R).Additive :=
  ⟨by intros; rfl⟩

/-- K-injective resolutions exist for sheaves of modules over the pro-etale ringed site.
Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: det-pe-bounded-continuity-direct-image).
Proof: transport the site to `proEtaleSiteModel X`, which only enlarges the Hom universe.
There `SheafOfModules.isGrothendieckAbelian` applies to the transported ring sheaf, so
`CochainComplex.kInjectiveResolutionFunctor` gives K-injective quasi-isomorphic
resolutions. Transport back along the inverse sectionwise equivalence, which preserves
acyclicity, homotopies and quasi-isomorphisms. No commutativity, boundedness or
finiteness condition is imposed. -/
theorem ringModuleDirectImage_hasKInjectiveResolutions {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    ∀ L : CochainComplex (SheafOfModules.{u + 1} R) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u + 1} R) ℤ) (s : L ⟶ I),
        I.IsKInjective ∧ QuasiIso s := by
  exact boundedRingModuleDirectImage_hasKInjectiveResolutions R

/-- The right derived module direct image.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable abbrev ringDerivedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    DerivedCategory (SheafOfModules.{u + 1} R) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)) :=
  Functor.rightDerivedFunctorOfQuasiIsoResolutions (ringModuleDirectImage f R)
    (by
      let h := ringModuleDirectImage_hasKInjectiveResolutions R
      exact fun L : CochainComplex (SheafOfModules.{u + 1} R) ℤ ↦
        h L)

/-- The higher direct image in degree `q`.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable abbrev ringHigherDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} R) ⥤
      SheafOfModules.{u + 1}
        ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  ringDerivedDirectImage f R ⋙
    DerivedCategory.homologyFunctor _ q

/-- Affine evaluations detect invertibility after sheafification. Transport that
colimit cocone through the natural bounded presheaf/direct-image comparison.
Source: the affine-cover and sheafification paragraph of the blueprint proof of
`det-pe-bounded-continuity-direct-image`. -/
private theorem boundedContinuityDirectImage_of_affine_evaluations
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (R : Sheaf (topology X) RingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex (SheafOfModules.{u + 1} R) ℤ)
    (a : ℤ) (hD : ∀ i : I, ∀ n : ℤ, n < a → IsZero ((D.obj i).X n)) (q : ℤ)
    (hAffine : ∀ V : Y.ProEt, IsAffine V.left →
      IsIso ((colimit.post D (inverseImageCohomologyPresheaf f R q)).app (op V))) :
    IsIso (colimit.desc
      ((D ⋙ DerivedCategory.Q) ⋙ ringHigherDirectImage f R q)
      ((ringHigherDirectImage f R q).mapCocone
        (DerivedCategory.Q.mapCocone (colimit.cocone D)))) := by
  classical
  let P := inverseImageCohomologyPresheaf f R q
  let A := presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}
  let T := SheafOfModules.toSheaf.{u + 1}
    ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
  let H := DerivedCategory.Q ⋙ ringHigherDirectImage f R q
  let φ := colimit.post D P
  have hinj : Presheaf.IsLocallyInjective (topology Y) φ := by
    constructor
    intro V x y hxy
    let C := V.unop.left.affineOpenCover.openCover
    apply mem_topology_of_openImmersion _ C.f
    · intro x
      exact ⟨C.idx x, C.covers x⟩
    · intro i
      let W := ofOpenImmersion V.unop (C.f i)
      have : IsIso (φ.app (op W)) := hAffine W (by
        change IsAffine (C.X i)
        dsimp only [C]
        infer_instance)
      apply (ConcreteCategory.bijective_of_isIso (φ.app (op W))).1
      change φ.app (op W) ((colimit (D ⋙ P)).map
        (ofOpenImmersionHom V.unop (C.f i)).op x) =
        φ.app (op W) ((colimit (D ⋙ P)).map
          (ofOpenImmersionHom V.unop (C.f i)).op y)
      rw [φ.naturality_apply, φ.naturality_apply, hxy]
  have hsurj : Presheaf.IsLocallySurjective (topology Y) φ := by
    constructor
    intro V s
    let C := V.left.affineOpenCover.openCover
    apply mem_topology_of_openImmersion _ C.f
    · intro x
      exact ⟨C.idx x, C.covers x⟩
    · intro i
      let W := ofOpenImmersion V (C.f i)
      have : IsIso (φ.app (op W)) := hAffine W (by
        change IsAffine (C.X i)
        dsimp only [C]
        infer_instance)
      exact (ConcreteCategory.bijective_of_isIso (φ.app (op W))).2 _
  have : IsIso (A.map φ) :=
    ((topology Y).W_iff φ).mp ((topology Y).W_of_isLocallyBijective φ)
  have hK : ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero ((colimit D).X n) := by
    refine ⟨a, fun n hn ↦ ?_⟩
    exact (isColimitOfPreserves
      (HomologicalComplex.eval (SheafOfModules.{u + 1} R) (.up ℤ) n)
      (colimit.isColimit D)).isZero_pt
        (Functor.isZero _ (fun i ↦ hD i n hn))
  let e (K : CochainComplex (SheafOfModules.{u + 1} R) ℤ)
      (hK : ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (K.X n)) :
      A.obj (P.obj K) ≅ T.obj (H.obj K) :=
    boundedComplexDirectImagePresheafIso f R q K hK
  let η : (D ⋙ P) ⋙ A ≅ (D ⋙ H) ⋙ T :=
    NatIso.ofComponents (fun i ↦ e (D.obj i) ⟨a, hD i⟩)
      (fun {i j} t ↦ boundedComplexDirectImagePresheaf f R q _ _
        ⟨a, hD i⟩ ⟨a, hD j⟩ (D.map t))
  let c := T.mapCocone (H.mapCocone (colimit.cocone D))
  let ept : A.obj (colimit (D ⋙ P)) ≅ c.pt :=
    asIso (A.map φ) ≪≫ e (colimit D) hK
  have hc : IsColimit ((Cocone.precompose η.hom).obj c) := by
    apply IsColimit.ofIsoColimit
      (isColimitOfPreserves A (colimit.isColimit (D ⋙ P)))
    refine Cocone.ext ept (fun i ↦ ?_)
    change A.map (colimit.ι (D ⋙ P) i) ≫
        (A.map φ ≫ (e (colimit D) hK).hom) =
      (e (D.obj i) ⟨a, hD i⟩).hom ≫ T.map (H.map (colimit.ι D i))
    rw [← Category.assoc, ← A.map_comp, colimit.ι_post]
    exact boundedComplexDirectImagePresheaf f R q _ _
      ⟨a, hD i⟩ hK (colimit.ι D i)
  have hc' : IsColimit c := (IsColimit.precomposeHomEquiv η c) hc
  have : PreservesColimitsOfShape I T :=
    (moduleSheaves_colimits_forgetful _).2.2.2.2.2 I |>.2.1
  have : ReflectsColimit (D ⋙ H) T :=
    reflectsColimit_of_reflectsIsomorphisms (D ⋙ H) T
  have hcH : IsColimit (H.mapCocone (colimit.cocone D)) := isColimitOfReflects T hc'
  change IsIso (colimit.desc (D ⋙ H) (H.mapCocone (colimit.cocone D)))
  exact hcH.coconePointUniqueUpToIso (colimit.isColimit (D ⋙ H)) |>.isIso_inv

/-- For a quasi-compact, quasi-separated morphism, higher direct images commute with
filtered colimits of complexes sharing a common lower bound.
Source: the Weil conjectures blueprint, snapshot main-20261015,
`det-pe-bounded-continuity-direct-image.md` (blueprint: det-pe-bounded-continuity-direct-image).
Proof: evaluate the cohomology presheaf on affine objects. The pullback is qcqs, so
bounded continuity of sections makes the presheaf comparison invertible there. Affine
open covers give local bijectivity, hence invertibility after abelian sheafification.
The termwise colimit retains the lower bound. Naturality of the presheaf/direct-image
comparison identifies the sheafified cocone with the direct-image cocone; the exact
module forgetful functor preserves and reflects its colimit property. -/
theorem boundedContinuityDirectImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (R : Sheaf (topology X) RingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (SheafOfModules.{u + 1} R) ℤ)
    (a : ℤ) (hD : ∀ i : I, ∀ n : ℤ, n < a → IsZero ((D.obj i).X n)) (q : ℤ) :
    IsIso (colimit.desc
      ((D ⋙ DerivedCategory.Q) ⋙ ringHigherDirectImage f R q)
      ((ringHigherDirectImage f R q).mapCocone
        (DerivedCategory.Q.mapCocone (colimit.cocone D)))) := by
  classical
  let P := inverseImageCohomologyPresheaf f R q
  have hAffine (V : Y.ProEt) (hV : IsAffine V.left) :
      IsIso ((colimit.post D P).app (op V)) := by
    let : IsAffine V.left := hV
    let U := (proEtaleBaseChange f).obj V
    let : CompactSpace V.left := Scheme.compactSpace_of_isAffine V.left
    let : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_isAffine V.left
    let : CompactSpace ((𝟭 Scheme).obj V.left) := by
      simpa using (Scheme.compactSpace_of_isAffine V.left)
    let : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) := by
      simpa using (quasiSeparatedSpace_of_isAffine V.left)
    let : CompactSpace U.left := by
      dsimp [U, proEtaleBaseChange]
      exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom f)
    let : QuasiSeparatedSpace U.left := by
      dsimp [U, proEtaleBaseChange]
      let : QuasiSeparated (pullback.fst V.hom f) :=
        MorphismProperty.pullback_fst _ _ inferInstance
      exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom f)
    let E := (CategoryTheory.evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)
    have : IsIso (colimit.post D (P ⋙ E)) :=
      isIso_ringHypercohomology_colimitPost X R U D a hD q
    have : IsIso (colimit.post (D ⋙ P) E ≫ E.map (colimit.post D P)) := by
      rw [colimit.post_post]
      infer_instance
    exact IsIso.of_isIso_comp_left (colimit.post (D ⋙ P) E) (E.map (colimit.post D P))
  exact boundedContinuityDirectImage_of_affine_evaluations f R D a hD q
    (fun V hV ↦ hAffine V hV)

end AlgebraicGeometry.Scheme.ProEt

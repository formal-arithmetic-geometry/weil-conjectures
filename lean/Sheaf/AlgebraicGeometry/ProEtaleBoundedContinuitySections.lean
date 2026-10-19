/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex
import Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Bounded-below filtered-colimit continuity of pro-etale hypercohomology

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
det-pe-bounded-continuity-sections.md and its proof
(blueprint: det-pe-bounded-continuity-sections).

## Main definitions

- `ringHypercohomology`: integer-degree derived sections with arbitrary ring-sheaf coefficients.

## Main statements

- `ringHypercohomology_transport_preservesZeroMorphisms`: transport acts on complexes.
- `isIso_ringHypercohomology_colimitPost`: the canonical bounded-below continuity map is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The published sectionwise transport preserves zero maps, as needed to apply it
termwise to complexes. Source: the blueprint's small-site size convention and
Stacks Project, Tag 03D1 (blueprint: det-pe-bounded-continuity-sections).
Proof: transport precomposes every component with `AsSmall.down`; a zero module-sheaf
map has a zero component at every object, which remains zero after precomposition. -/
theorem ringHypercohomology_transport_preservesZeroMorphisms (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext V x
  rfl

attribute [instance] ringHypercohomology_transport_preservesZeroMorphisms

/-- Hypercohomology at an object of the small pro-etale site, with arbitrary ring-sheaf
coefficients. Transport to the published small site model is sectionwise precomposition;
then take the published functorial K-injective resolution, evaluate its underlying abelian
section complex, and take its integer-degree homology. On bounded-below complexes this is
canonically the evaluation of a bounded-below injective resolution: both compute the right
derived evaluation functor, and comparison with a K-injective resolution is unique up to
homotopy. This construction retains all original site objects and the original coefficients.

Source: the blueprint, det-pe-bounded-continuity-sections.md, convention for `H^q(U,-)`;
Stacks Project, Tags 079P and 09A2 (blueprint: det-pe-bounded-continuity-sections). -/
noncomputable def ringHypercohomology (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) (q : ℤ) :
    CochainComplex (ringedSiteModules.{u + 1} R) ℤ ⥤ AddCommGrpCat.{u + 1} :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    CochainComplex.kInjectiveResolutionFunctor.{u + 1} (ringedSiteModules.{u + 1} S) ⋙
    (SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
      forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U))))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q

private noncomputable def moduleModelEquiv (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R) := by
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm.functor.IsContinuous
      (proEtaleModelTopology X) (topology X) :=
    inferInstanceAs ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsContinuous _ _)
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm.inverse.IsContinuous
      (topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm
    (𝟙 _) (𝟙 _) (by
      ext V x
      change (R.obj.map (𝟙 V)) x = x
      simp) (by
      ext V x
      change (R.obj.map (𝟙 (op (ULift.down V.unop)))) x = x
      simp)

private noncomputable def derivedSectionsUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h where
  app K := (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
      ((DerivedCategory.quotientCompQhIso C).hom.app K)
  naturality K L f := by
    have hn := (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).naturality
      ((HomotopyCategory.quotient C (.up ℤ)).map f)
    simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at hn
    simp only [Functor.comp_map, DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
      Category.assoc]
    rw [reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_hom_naturality]

private theorem derivedSectionsUnit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsIso ((derivedSectionsUnit F h).app K) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h K
  dsimp only [derivedSectionsUnit]
  infer_instance

private noncomputable def resolutionDerivedIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (J : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (s : 𝟭 _ ⟶ J)
    (hJ : ∀ K, (J.obj K).IsKInjective) (hs : ∀ K, QuasiIso (s.app K)) :
    DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
      J ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let v := Functor.whiskerLeft J (derivedSectionsUnit F h)
  have : ∀ K, IsIso (v.app K) := fun K ↦ by
    have := hJ K
    exact derivedSectionsUnit_isIso F h (J.obj K)
  have : IsIso v := NatIso.isIso_of_isIso_app _
  let t := Functor.whiskerRight (Functor.whiskerRight s DerivedCategory.Q)
    (F.rightDerivedFunctorOfQuasiIsoResolutions h)
  have : ∀ K, IsIso (t.app K) := fun K ↦ by
    have := hs K
    change IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutions h).map
      (DerivedCategory.Q.map (s.app K)))
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t ≪≫ (asIso v).symm

private instance ringEvaluation_additive (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) :
    (SheafOfModules.evaluation.{u + 1} R (op U)).Additive := ⟨by intros; rfl⟩

private noncomputable def ringHypercohomologyDerivedIso (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) (q : ℤ)
    [HasDerivedCategory (ringedSiteModules.{u + 1} R)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    ringHypercohomology X R U q ≅ DerivedCategory.Q ⋙
      Functor.rightDerivedFunctorOfQuasiIsoResolutions
        (hypercoverAbelianEvaluation.{u, u + 1, 0} X R U)
        (moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0} X R) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q := by
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  let e := moduleModelEquiv X R
  have : e.functor.Additive := ⟨by intros; rfl⟩
  have : e.inverse.Additive := ⟨by intros; rfl⟩
  let A := e.functor.mapHomologicalComplex (.up ℤ)
  let B := e.inverse.mapHomologicalComplex (.up ℤ)
  let J := A ⋙ CochainComplex.kInjectiveResolutionFunctor.{u + 1}
    (ringedSiteModules.{u + 1} S) ⋙ B
  let s : 𝟭 _ ⟶ J := (e.mapHomologicalComplex (.up ℤ)).unitIso.hom ≫
    Functor.whiskerRight (Functor.whiskerLeft A
      (CochainComplex.toKInjectiveResolution.{u + 1} (ringedSiteModules.{u + 1} S))) B
  have hJ (K) : CochainComplex.IsKInjective (J.obj K) := by
    change CochainComplex.IsKInjective ((e.inverse.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.kInjectiveResolutionFunctor.{u + 1}
        (ringedSiteModules.{u + 1} S)).obj (A.obj K)))
    infer_instance
  have hs (K) : QuasiIso (s.app K) := by
    have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1}
        (ringedSiteModules.{u + 1} S)).app (A.obj K)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
        (ringedSiteModules.{u + 1} S) (A.obj K)).2
    have : QuasiIso (B.map ((CochainComplex.toKInjectiveResolution.{u + 1}
        (ringedSiteModules.{u + 1} S)).app (A.obj K))) := by
      change QuasiIso ((e.inverse.mapHomologicalComplex (.up ℤ)).map _)
      infer_instance
    change QuasiIso ((e.mapHomologicalComplex (.up ℤ)).unitIso.hom.app K ≫
      B.map ((CochainComplex.toKInjectiveResolution.{u + 1}
        (ringedSiteModules.{u + 1} S)).app (A.obj K)))
    infer_instance
  let E := hypercoverAbelianEvaluation.{u, u + 1, 0} X R U
  have : E.Additive := ⟨by intros; rfl⟩
  let c := resolutionDerivedIso E
    (moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0} X R) J s hJ hs
  let cH := Functor.isoWhiskerRight c
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q)
  let cQ := Functor.isoWhiskerLeft (J ⋙ E.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} q)
  let smallE := SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
    forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U))))
      AddCommGrpCat.{u + 1}
  have : smallE.Additive := ⟨by intros; rfl⟩
  let ee : e.inverse ⋙ E ≅ smallE := Iso.refl _
  let ec := Functor.mapHomologicalComplexCompIso ee (.up ℤ)
  let cE : J ⋙ E.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q ≅
      ringHypercohomology X R U q := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (A ⋙ CochainComplex.kInjectiveResolutionFunctor.{u + 1}
      (ringedSiteModules.{u + 1} S)) ec)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q)
  exact cE.symm ≪≫ cQ.symm ≪≫ cH.symm

private theorem ringHypercoverTotal_preservesColimits (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt)
    (W : SimplicialObject (Over U))
    (haff : ∀ n : ℕ, IsAffine (W.obj (op (SimplexCategory.mk n))).left.left)
    (hweak : ∀ n : ℕ,
      (topology X).IsWeaklyContractible.{u + 1}
        (W.obj (op (SimplexCategory.mk n))).left)
    (I : Type (u + 1)) [SmallCategory I] :
    PreservesColimitsOfShape I (hypercoverAbelianTotal.{u, u + 1, 0} X R U W) := by
  have hw (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G)
      (hf : Epi f) :
      Function.Surjective (f.hom.app (op (W.obj (op (SimplexCategory.mk n))).left)) :=
    hweak n f ((Sheaf.isLocallySurjective_iff_epi f).2 hf)
  have := abelianHypercoverTotal_preservesColimits X U W haff hw
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u + 1} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.2.2.2 I |>.2.1
  have : (SheafOfModules.toSheaf.{u + 1} R).Additive := ⟨by intros; rfl⟩
  let e : SheafOfModules.toSheaf.{u + 1} R ⋙ abelianHypercoverRows X U W ≅
      hypercoverAbelianRows.{u, u + 1, 0} X R U W := Iso.refl _
  let ec := Functor.mapHomologicalComplexCompIso e (.up ℤ)
  let et := Functor.isoWhiskerRight ec
    (HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor _ _ _ (.up ℤ))
  let et' : (SheafOfModules.toSheaf.{u + 1} R).mapHomologicalComplex (.up ℤ) ⋙
      abelianHypercoverTotal X U W ≅ hypercoverAbelianTotal.{u, u + 1, 0} X R U W := et
  exact preservesColimitsOfShape_of_natIso et'

/-- Hypercohomology on every qcqs pro-etale object commutes with filtered colimits of
complexes having one common strict lower bound. The map is `colimit.post`, whose composite
with each colimit inclusion is the hypercohomology of the original complex colimit leg.
Complex colimits are termwise sheaf colimits by `HomologicalComplex`'s colimit construction.

Source: Weil conjectures blueprint, snapshot main-20261015,
det-pe-bounded-continuity-sections.md and its proof
(blueprint: det-pe-bounded-continuity-sections).

Proof for stage 3:
1. Module sheaves have small colimits by lem-weil-pbc-ring-sheaves-grothendieck.
   Form the termwise colimit complex using the universal cocone in every degree.
   Its differential is induced by the differentials of the diagram. The chain identities
   and square-zero identity follow on every colimit leg. Its terms below a are zero.
2. By det-pe-hypercover-existence choose one affine weakly contractible hypercover of U,
   fixed for the entire diagram. By det-pe-hypercover-complex its section totals compute
   the hypercohomology of each complex and the colimit, naturally. In degree n only
   the finitely many hypercover degrees 0 through n-a contribute, with none when n<a.
3. Apply det-pe-sections-limits-colimits in every bidegree. The underlying abelian-group
   colimit is also the module colimit: scalar multiplication is induced on the additive
   colimit by its universal property, and the module laws and linearity are checked on
   its legs. These comparisons commute with face restrictions and complex differentials.
4. Exchange the finite diagonal sums with the colimit. The resulting degreewise
   isomorphisms commute with both alternating-face and signed vertical differentials,
   so identify the total complexes, including empty diagonals.
5. Filtered colimits of abelian groups are exact by
   lem-weil-pbc-filtered-colimit-abelian-groups-exact. Apply this to the compatible short
   exact sequences of cycles, boundaries and cohomology. It identifies cohomology of
   the colimit total with the colimit of its cohomology, with the canonical cycle maps.
6. Naturality of det-pe-hypercover-complex identifies the composite isomorphism on every
   colimit leg with hypercohomology of that leg. The colimit universal property makes
   it exactly colimit.post below, in every integer degree, also q<a. -/
theorem isIso_ringHypercohomology_colimitPost (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (ringedSiteModules.{u + 1} R) ℤ)
    (a : ℤ) (hK : ∀ (i : I) (b : ℤ), b < a → IsZero ((K.obj i).X b)) (q : ℤ) :
    IsIso (colimit.post K (ringHypercohomology X R U q)) := by
  classical
  let := HasDerivedCategory.standard (ringedSiteModules.{u + 1} R)
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  obtain ⟨W, hW, hzero, hmatching⟩ :=
    (AlgebraicGeometry.exists_proetale_hypercover_single_affine X U
      inferInstance inferInstance).2.2
  have haff (n : ℕ) : IsAffine (W.obj (op (SimplexCategory.mk n))).left.left := by
    obtain ⟨D, f, hf, _, heq, _⟩ := hW n
    rw [heq]
    exact inferInstanceAs (IsAffine (Spec D))
  have hweak (n : ℕ) :
      (topology X).IsWeaklyContractible.{u + 1} (W.obj (op (SimplexCategory.mk n))).left := by
    obtain ⟨D, f, hf, hD, heq, _⟩ := hW n
    have := hD
    apply isWeaklyContractible_of_iso (R := D)
    exact eqToIso (congrArg (fun V : X.ProEt ↦ V.left) heq)
  let T := hypercoverAbelianTotal.{u, u + 1, 0} X R U W
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q
  have : PreservesColimitsOfShape I T :=
    ringHypercoverTotal_preservesColimits X R U W haff hweak I
  let e := Functor.isoWhiskerLeft (CochainComplex.Plus.ι (ringedSiteModules.{u + 1} R))
      (ringHypercohomologyDerivedIso X R U q) ≪≫
    Functor.isoWhiskerRight
      (hypercover_complex_natural_iso.{u, u + 1, 0} X R U W hweak hzero hmatching).some
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι (ringedSiteModules.{u + 1} R) ⋙ T)
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} q)
  have hb (i : I) : (K.obj i).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ _).2 (hK i)
  let KP : I ⥤ CochainComplex.Plus (ringedSiteModules.{u + 1} R) :=
    ObjectProperty.lift _ K (fun i ↦ ⟨a, hb i⟩)
  have hc : (colimit K).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro b hb
    rw [IsZero.iff_id_eq_zero]
    apply (isColimitOfPreserves (HomologicalComplex.eval _ _ b)
      (colimit.isColimit K)).hom_ext
    intro i
    exact (hK i b hb).eq_of_src _ _
  let c : Cocone KP :=
    { pt := ⟨colimit K, ⟨a, hc⟩⟩
      ι :=
        { app i := ObjectProperty.homMk (colimit.ι K i)
          naturality i j f := by
            apply (CochainComplex.Plus.ι _).map_injective
            exact (colimit.cocone K).w f } }
  have ht : IsColimit (((CochainComplex.Plus.ι _ ⋙ T ⋙ H)).mapCocone c) :=
    isColimitOfPreserves (T ⋙ H) (colimit.isColimit K)
  have hr := IsColimit.mapCoconeEquiv e.symm ht
  have : PreservesColimit K (ringHypercohomology X R U q) :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K) hr
  infer_instance

end AlgebraicGeometry.Scheme.ProEt

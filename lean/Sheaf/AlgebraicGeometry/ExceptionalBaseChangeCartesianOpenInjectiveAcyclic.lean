/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

import Sheaf.AlgebraicGeometry.CartesianOpenFiniteStageHypercohomologyModel
import Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections

/-!
# Proper acyclicity after extension by zero on a Cartesian open

Source: blueprint `prop-exc-base-change-proper`, Steps 2--4; Stacks Project,
Tag 0F7B (the etale analogue), and proetale Tags 09AE and 09BN
(blueprint: lem-exc-proetale-cartesian-open-injective-acyclic).
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

set_option autoImplicit false

@[expose] public section

private theorem evaluation_higherDirectImage
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (W : Y.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology Y) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (Opposite.op W))) (q : ℤ) :
    IsZero (((SheafOfModules.evaluation
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A)) (Opposite.op W)) ⋙
        forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleConstantDerivedDirectImage f A).obj (DerivedCategory.Q.obj K)))) ↔
      IsZero ((ProEt.ringHypercohomology X
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing X A)) ((proEtaleBaseChange f).obj W) q).obj K) := by
  let RX := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A)
  let RY := (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing Y A)
  let F := proEtaleConstantModuleDirectImage f A
  let E : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤ AddCommGrpCat.{u + 1} :=
    SheafOfModules.evaluation.{u + 1} RY (Opposite.op W) ⋙
      forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}
  let : (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)).PreservesHomology :=
    ProEt.weaklyContractible_evaluation_preservesHomology Y (proEtaleConstantRing Y A) W hW
  let : PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)) :=
    (ProEt.affine_weaklyContractible_evaluation_colimits Y (proEtaleConstantRing Y A) W hW).1
  let : PreservesFiniteLimits E := comp_preservesFiniteLimits
    (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W))
    (forget₂ (ModuleCat.{u + 1} (RY.obj.obj (Opposite.op W))) AddCommGrpCat.{u + 1})
  let : E.PreservesEpimorphisms := by
    dsimp only [E]
    infer_instance
  let : E.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels E
  let I := (ProEt.ringModuleResolutionFunctor RX).obj K
  have : I.IsKInjective := (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).1
  have : QuasiIso (ProEt.ringModuleResolutionMap RX K) :=
    (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).2
  let e := F.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map (ProEt.ringModuleResolutionMap RX K))) ≪≫
    F.rightDerivedFunctorObjQIso I
  let h := (DerivedCategory.homologyFunctorFactors _ q).app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  let c := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q).mapIso
    (HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _)
      (by intros; rfl) :
      (E.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
        ((ProEt.ringModuleModelEvaluation RX ((proEtaleBaseChange f).obj W)).mapHomologicalComplex
          (.up ℤ)).obj ((ProEt.ringModuleModelResolutionFunctor RX).obj K))
  let : E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (.up ℤ)).obj I).sc q) := inferInstance
  exact (E.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e ≪≫ h) ≪≫
    ((((F.mapHomologicalComplex (.up ℤ)).obj I).sc q).mapHomologyIso E).symm ≪≫ c).isZero_iff


private theorem detect (T : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules T (proEtaleConstantRing T A))
    (h : ∀ (W : T.ProEt), IsAffine W.left →
      (∀ (G H : Sheaf (ProEt.topology T) (Type (u + 1))) (e : G ⟶ H),
        Epi e → Function.Surjective (e.hom.app (Opposite.op W))) →
      Subsingleton ((SheafOfModules.evaluation
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T A)) (Opposite.op W)).obj F)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext V x
  change x = 0
  obtain ⟨I, W, f, hc, ha, hw⟩ :=
    Scheme.ProEt.exists_affine_weaklyContractible_covering_family T V.unop
  apply F.isSheaf.isSeparated _ _ (Precoverage.generate_mem_toGrothendieck hc)
  rintro Z g ⟨_, a, _, ⟨j⟩, rfl⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg _ ((h (W j) (ha j) (hw j)).elim _ _)

private theorem isZero_hypercohomology_colimit
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (U : X.ProEt) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (ringedSiteModules.{u + 1} R) ℤ)
    (a q : ℤ) (hK : ∀ (i : I) (b : ℤ), b < a → IsZero ((K.obj i).X b))
    (hz : ∀ i : I, IsZero ((ProEt.ringHypercohomology X R U q).obj (K.obj i))) :
    IsZero ((ProEt.ringHypercohomology X R U q).obj (colimit K)) := by
  let H := ProEt.ringHypercohomology X R U q
  have : IsIso (colimit.post K H) :=
    ProEt.isIso_ringHypercohomology_colimitPost X R U K a hK q
  have hcol : IsZero (colimit (K ⋙ H)) := by
    rw [IsZero.iff_id_eq_zero]
    apply colimit.hom_ext
    intro i
    exact (hz i).eq_of_src _ _
  exact hcol.of_iso (asIso (colimit.post K H)).symm

/--
For a proper morphism and an arbitrary open of the target, extension by zero of an
injective module sheaf on the Cartesian inverse image is acyclic for proper direct
image.  The finite cohomological-dimension assumption is retained exactly as in the
node, although the reduction through quasi-compact principal opens does not use it.

Source: blueprint `prop-exc-base-change-proper`, Steps 2--4; Stacks Project,
Tag 0F7B, case (b), with the pro-etale open functors of Tags 09AE and 09BN
(blueprint: lem-exc-proetale-cartesian-open-injective-acyclic).

Proof plan, following the six steps of the node.
1. Choose a bounded-below injective resolution using
   `prop-pur-kinjective-resolutions-exist` and `lem-weil-pbc-dplus-injective-representative`.
   The derived-computation lemma `lem-weil-pbc-right-derived-plus-injective`, exact
   evaluation (`lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits`), and
   `lem-weil-pbc-proetale-restriction-injectives` identify the value of the higher
   direct image on an affine weakly contractible object Q with cohomology on
   P = V times_T Q. The same calculation applies at the terminal object of Q's site.
2. Exhaust W times_T Q by finite unions W_E of principal opens of the affine Q.
   Their inverse images U_E in P are quasi-compact opens. Properness survives base
   change. Restriction of J to U_E is injective by the restriction lemma. The
   weakly-etale localization and normalized open-base-change lemmas identify the
   restriction of k_!J to P with extension by zero of J restricted to U times_T Q.
3. Apply `lem-sp-proetale-open-injective-proper-acyclic` to each finite stage.
   Step 1 identifies its positive cohomology on P with zero.
4. The adjunction `lem-weil-extension-by-zero-adjunction` gives transition maps
   between the finite-stage extensions. Its Hom bijection and sheaf gluing on
   the open cover exhibit their filtered colimit as the restriction of k_!J to P.
   Composition of open extensions follows from their composite right adjoints.
5. Properness over the affine Q makes P qcqs. Apply
   `det-pe-bounded-continuity-sections` to the finite-stage complexes concentrated
   in degree zero, with common lower bound zero. Their positive cohomology and
   hence that of their colimit vanish by Step 3.
6. `lem-sf-proetale-vanishing-detection` detects zero sheaves on affine weakly
   contractible objects, so Step 1 gives vanishing of each positive higher image.
The empty open, whole open, zero ring, and identity proper morphism are included.
-/
theorem isZero_higherDirectImage_cartesianOpen_injective
    (A : Type u) [CommRing A] [Finite A]
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)
    [IsProper p] [IsOpenImmersion i]
    (hcd : ∃ d : ℕ, ∀ (F : proEtaleRingModules V (proEtaleConstantRing V A))
      (q : ℕ), d < q →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) (q : ℤ)).obj
          ((proEtaleConstantDerivedDirectImage p A).obj
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj F))))
    (J : proEtaleRingModules (pullback p i)
      (proEtaleConstantRing (pullback p i) A)) [Injective J] :
    ∀ q : ℕ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) (q : ℤ)).obj
        ((proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj
            ((sfIntrinsicExtensionByZero (pullback.fst p i) A).obj J)))) := by
  have _ := hcd
  intro q hq
  apply detect T A
  intro Q hQa hQ
  let : IsAffine Q.left := hQa
  obtain ⟨hc, hs, I, hI, hf, K, hb, hz, he⟩ :=
    exists_cartesianOpen_finiteStage_hypercohomology_model A p i J Q hQ
  let : SmallCategory I := hI
  let : IsFiltered I := hf
  let P := ((proEtaleBaseChange p).obj Q).left
  let : CompactSpace P := hc
  let : QuasiSeparatedSpace P := hs
  let R := (sheafCompose (ProEt.topology P)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing P A)
  let U : P.ProEt := ProEt.mk (𝟙 P)
  let : CompactSpace U.left := hc
  let : QuasiSeparatedSpace U.left := hs
  have hcol := isZero_hypercohomology_colimit P R U K 0 (q : ℤ) hb
    (fun a ↦ hz a q hq)
  obtain ⟨e⟩ := he (q : ℤ)
  have hhyper := hcol.of_iso e
  let M := (sfIntrinsicExtensionByZero (pullback.fst p i) A).obj J
  let C := (CochainComplex.singleFunctor
    (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj M
  have heval := (evaluation_higherDirectImage A p C Q hQ (q : ℤ)).2 hhyper
  let E := SheafOfModules.evaluation
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T A)) (Opposite.op Q) ⋙
      forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}
  let eSingle := (DerivedCategory.singleFunctorIsoCompQ
    (proEtaleRingModules V (proEtaleConstantRing V A)) 0).app M
  have heval' := heval.of_iso
    (E.mapIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((proEtaleConstantDerivedDirectImage p A).mapIso eSingle)))
  exact AddCommGrpCat.isZero_iff_subsingleton.mp heval'

end

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition

/-!
# The selected canonical composition comparison

Source: Stacks Project, Tag 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The original-site coefficient transports require the same budget as the source theorem.
/-- The unique derived comparison with exactly the original theorem's ordinary,
termwise and K-flat normalization, with the derived comparison returned first.
Source: Stacks Project, Tag 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).
Proof: use proEtaleRingDerivedPullbackComposition for existence. The displayed
sectionwise direct-image equation fixes d; the module unit normalization fixes each
adjunction, hence conjugation fixes a. Its degree maps fix b. Flat K-flat resolutions
exist for every input, and localization of b with the factorization isomorphisms
fixes the component of comparison on each resolution. Naturality across resolution
quasi-isomorphisms therefore fixes its component on every derived object. Thus the
natural isomorphism is unique. This is the same characterization with the unique
comparison exposed first, rather than repeatedly extracting nested witnesses. -/
theorem proEtaleCanonicalPullbackComposition_existsUnique
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z)
    (c_hk : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z)
    (hc_hk : c_hk = proEtaleRingCompositeCoefficients h k R_V R_W R_Z c_k c_h) :
    ∃! comparison : proEtaleRingDerivedPullback (h ≫ k) R_V R_Z c_hk ≅
        proEtaleRingDerivedPullback k R_V R_W c_k ⋙
          proEtaleRingDerivedPullback h R_W R_Z c_h,
    ∃ (adj_k : proEtaleRingModulePullback k R_V R_W c_k ⊣
          proEtaleRingModuleDirectImage k R_V R_W c_k)
      (adj_h : proEtaleRingModulePullback h R_W R_Z c_h ⊣
          proEtaleRingModuleDirectImage h R_W R_Z c_h)
      (adj_hk : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ⊣
          proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
      proEtaleRingModuleAdjunctionNormalized k R_V R_W c_k adj_k ∧
      proEtaleRingModuleAdjunctionNormalized h R_W R_Z c_h adj_h ∧
      proEtaleRingModuleAdjunctionNormalized (h ≫ k) R_V R_Z c_hk adj_hk ∧
      ∃ (d : proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k ≅
              proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
        (∀ (N : proEtaleRingModules Z R_Z) (U : V.ProEt)
            (m : ((proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
              proEtaleRingModuleDirectImage k R_V R_W c_k).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m) ∧
        ∃ (a : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ≅
              proEtaleRingModulePullback k R_V R_W c_k ⋙
                proEtaleRingModulePullback h R_W R_Z c_h),
          conjugateIsoEquiv (adj_k.comp adj_h) adj_hk a = d ∧
          ∃ (b : (proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              (proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                (ComplexShape.up ℤ) ⋙
              (proEtaleRingModulePullback h R_W R_Z c_h).mapHomologicalComplex
                (ComplexShape.up ℤ)),
            (∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ) (n : ℤ),
              (b.hom.app K).f n = a.hom.app (K.X n)) ∧
              ∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ),
                CochainComplex.IsAcyclicTensorKFlat K →
                (∀ n : ℤ,
                  SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := R_V) (K.X n)) →
                CochainComplex.IsAcyclicTensorKFlat
                  (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K) ∧
                (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := R_W)
                  ((((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K).X n)) ∧
                (proEtaleRingDerivedPullbackFactors (h ≫ k) R_V R_Z c_hk).hom.app K ≫
                    DerivedCategory.Q.map (b.hom.app K) =
                  comparison.hom.app (DerivedCategory.Q.obj K) ≫
                    (proEtaleRingDerivedPullback h R_W R_Z c_h).map
                      ((proEtaleRingDerivedPullbackFactors k R_V R_W c_k).hom.app K) ≫
                    (proEtaleRingDerivedPullbackFactors h R_W R_Z c_h).hom.app
                      (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj K) := by
  sorry

/-- Select the comparison characterized by the normalized ordinary adjunctions,
fibre-product pasting, and the termwise K-flat comparison. Each witness in the existing
theorem is determined by those requirements, up to the equality used here.
Source: Stacks Project, Tag 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition). -/
def proEtaleCanonicalPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ) :
    proEtaleRingDerivedPullback (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) ≅
      proEtaleRingDerivedPullback k RV RW ck ⋙ proEtaleRingDerivedPullback h RW RZ ch :=
  Classical.choose (proEtaleCanonicalPullbackComposition_existsUnique h k RV RW RZ ck ch
    (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl).exists

end AlgebraicGeometry.Scheme

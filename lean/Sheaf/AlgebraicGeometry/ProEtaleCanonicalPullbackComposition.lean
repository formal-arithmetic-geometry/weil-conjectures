/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# The selected canonical composition comparison

Source: Stacks Project, Tag 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModulePullback
  proEtaleRingModuleUnitSection proEtaleRingDerivedPullbackFactors
  CochainComplex.IsAcyclicTensorKFlat SheafOfModules.IsFlatOnSite

private theorem normalizedAdjunction_ext
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a b : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c)
    (ha : proEtaleRingModuleAdjunctionNormalized f R S c a)
    (hb : proEtaleRingModuleAdjunctionNormalized f R S c b) : a = b := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (ha M U.unop m).trans (hb M U.unop m).symm

private theorem derivedTransformation_ext
    {V : Scheme.{u}} (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    {E : Type*} [Category E] {F G : DerivedCategory (proEtaleRingModules V R) ⥤ E}
    (α β : F ⟶ G)
    (h : ∀ (P : CochainComplex (proEtaleRingModules V R) ℤ),
      CochainComplex.IsAcyclicTensorKFlat P →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := R) (P.X n)) →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules V R) (.up ℤ))
  intro K
  obtain ⟨P, p, hP, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
  have := hp
  have h' := h P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)
    (fun n ↦ by
      unfold SheafOfModules.IsFlatOnSite
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hflat n))
  apply (cancel_epi (F.map (DerivedCategory.Q.map p))).1
  rw [α.naturality, β.naturality, h']

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
  classical
  obtain ⟨adjk, adjh, adjhk, nk, nh, nhk, d, hd, a, ha, b, hb, c, hc⟩ :=
    proEtaleRingDerivedPullbackComposition h k R_V R_W R_Z c_k c_h c_hk hc_hk
  refine ⟨c, ⟨adjk, adjh, adjhk, nk, nh, nhk, d, hd, a, ha, b, hb, hc⟩, ?_⟩
  intro c' hc'
  obtain ⟨adjk', adjh', adjhk', nk', nh', nhk', d', hd', a', ha', b', hb', hc'⟩ := hc'
  have ek := normalizedAdjunction_ext k R_V R_W c_k adjk' adjk nk' nk
  have eh := normalizedAdjunction_ext h R_W R_Z c_h adjh' adjh nh' nh
  have ehk := normalizedAdjunction_ext (h ≫ k) R_V R_Z c_hk adjhk' adjhk nhk' nhk
  subst adjk'
  subst adjh'
  subst adjhk'
  have ed : d' = d := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    exact (hd' N U.unop m).trans (hd N U.unop m).symm
  have ea : a' = a := (conjugateIsoEquiv (adjk.comp adjh) adjhk).injective
    (ha'.trans (ed.trans ha.symm))
  have eb : b'.hom = b.hom := by
    apply NatTrans.ext
    funext K
    apply HomologicalComplex.Hom.ext
    funext n
    exact (hb' K n).trans ((congrArg (fun e ↦ e.hom.app (K.X n)) ea).trans
      (hb K n).symm)
  apply Iso.ext
  apply derivedTransformation_ext R_V
  intro K hK hflat
  have e' := (hc' K hK hflat).2.2
  rw [eb] at e'
  have e := e'.symm.trans ((hc K hK hflat).2.2)
  apply (cancel_mono
    ((proEtaleRingDerivedPullback h R_W R_Z c_h).map
        ((proEtaleRingDerivedPullbackFactors k R_V R_W c_k).hom.app K) ≫
      (proEtaleRingDerivedPullbackFactors h R_W R_Z c_h).hom.app
        (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))).1
  simpa only [Category.assoc] using e

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

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Composition of derived pro-etale module pullbacks

Source: Stacks Project, sites-cohomology.tex, Lemma 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The induced identification on the composite, with no independent third choice.
Source: Stacks, Tags 03D8 and 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition). -/
noncomputable def proEtaleRingCompositeCoefficients
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z) :
    (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z :=
  (proEtaleRingInverseImageComp h k).app R_V ≪≫
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso c_k ≪≫ c_h

/-- Section of the canonical module unit: the model-site inverse-image unit followed
by the sheafification of `1 ⊗ m`. The model only enlarges the Hom universe.
Source: Stacks, Tags 03D2, 03EK and 03D8
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition). -/
noncomputable def proEtaleRingModuleUnitSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) (U : Y.ProEt) (m : M.val.obj (Opposite.op U)) :
    ((proEtaleRingModuleDirectImage f R S c).obj
      ((proEtaleRingModulePullback f R S c).obj M)).val.obj (Opposite.op U) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.changeOfRingsPresheaf c.hom
      ((proEtaleModuleInverseImage f R).obj M)).presheaf).app
        (Opposite.op ((proEtaleBaseChange f).obj U))
    ((1 : S.obj.obj (Opposite.op ((proEtaleBaseChange f).obj U))) ⊗ₜ[
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R).obj.obj
        (Opposite.op ((proEtaleBaseChange f).obj U)),
      (c.hom.hom.app (Opposite.op ((proEtaleBaseChange f).obj U))).hom]
      (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
            (Opposite.op (AsSmall.up.obj U)) m))

/-- Normalization of the module adjunction by its constructed unit on every section.
Source: Stacks, Tag 03D2 (blueprint: lem-weil-pbc-proetale-derived-pullback-composition). -/
def proEtaleRingModuleAdjunctionNormalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c) :
    Prop :=
  ∀ (M : proEtaleRingModules Y R) (U : Y.ProEt) (m : M.val.obj (Opposite.op U)),
    (adj.unit.app M).val.app (Opposite.op U) m = proEtaleRingModuleUnitSection f R S c M U m

set_option maxHeartbeats 800000 in
-- Comparing the nested derived and termwise functors unfolds several sheaf transports.
/-- The canonical composition isomorphism, including its K-flat representative formula.
The existential adjunctions have their units fixed sectionwise by the construction;
`d` is fixed by fibre-product pasting, `a` by conjugation, and `b` degree by degree.
Thus these witnesses express the ordinary canonical comparison, not arbitrary isomorphisms.
Source: Stacks, sites-cohomology.tex, Lemma 0D6D and Modules on Sites, Lemma 03D8
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).
Proof: (1) On each test object the fibre-product pasting isomorphism identifies the two
module direct images. The induced coefficient identification makes it linear. The
module adjunctions have the displayed tensor units; form their composite using
`def-weil-pbc-composite-adjunction`. Apply `lem-weil-pbc-conjugate-iso-unit-equation`
to obtain `a`. In inverse-image/tensor coordinates its forward map sends `m ⊗ r` to
`(m ⊗ 1) ⊗ r`; its inverse sends `(m ⊗ s) ⊗ r` to `m ⊗ c_h(s)r`. Balancing proves
the inverse identities and compatibility with restrictions and morphisms.
(2) Apply this comparison termwise to obtain `b`. All three module pullbacks are exact
by `def-weil-pbc-proetale-operations`. Their termwise functors invert quasi-isomorphisms.
Use `lem-weil-pbc-localization-universal-property` to descend `b`, with the stated
factorization isomorphisms, to the unique compatible derived comparison `c`.
(3) Use `lem-pc-kflat-resolution` to represent an input by a K-flat complex with flat
terms. By `lem-weil-pbc-ringed-pullback-preserves-kflat`, its pullback along `k` remains
K-flat with flat terms, so the iterated pullback computes the iterated derived functor.
The factorization equation is exactly the class of the termwise comparison. For an
input already K-flat with flat terms use the identity resolution. No boundedness,
properness, or flatness of either scheme morphism enters. -/
theorem proEtaleRingDerivedPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z)
    (c_hk : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z)
    (hc_hk : c_hk = proEtaleRingCompositeCoefficients h k R_V R_W R_Z c_k c_h) :
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
            ∃ (c : proEtaleRingDerivedPullback (h ≫ k) R_V R_Z c_hk ≅
                proEtaleRingDerivedPullback k R_V R_W c_k ⋙
                  proEtaleRingDerivedPullback h R_W R_Z c_h),
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
                  c.hom.app (DerivedCategory.Q.obj K) ≫
                    (proEtaleRingDerivedPullback h R_W R_Z c_h).map
                      ((proEtaleRingDerivedPullbackFactors k R_V R_W c_k).hom.app K) ≫
                    (proEtaleRingDerivedPullbackFactors h R_W R_Z c_h).hom.app
                      (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj K) := by
  sorry

end AlgebraicGeometry.Scheme

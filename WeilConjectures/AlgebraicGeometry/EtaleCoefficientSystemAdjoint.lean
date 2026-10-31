/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictEtaleSystemInterfaces
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.CoefficientSystemDerivedComparison
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.EtaleExceptionalConstantTensor
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.EtaleSystemBrownConstruction
import WeilConjectures.AlgebraicGeometry.EtaleSystemEvaluationBound
import WeilConjectures.AlgebraicGeometry.EtaleSystemQuotientNormalization
import WeilConjectures.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.ExchangeMateCube
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientTransportInterfaces
import WeilConjectures.AlgebraicGeometry.StrictEtaleCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.StrictEtaleIsomorphicStageProjection
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientSystemAdjointCore
/-!
# The strict étale coefficient-system adjoint
Source: Zheng, Six Operations and Lefschetz--Verdier, Constructions 5.14--5.15,
Lemmas 5.16 and 5.22, and Proposition 5.24 (blueprint:
lem-pur-etale-coefficient-system-adjoint).
The structure records the actual compact-support system functor, its right adjoint,
the finite-level adjunctions, and the asserted coefficient-system coherences.
* `StrictEtaleCompactSupport` specifies the ordinary and unbounded derived functors.
* `StrictEtaleExceptionalAdjoint` records the exact linear adjoint and finite-level mates.
* `StrictEtaleExceptionalTransport` specifies the scalar and cofinal comparison maps.
* `etaleCoefficientSystemAdjoint` and its scalar/cofinal companions assert existence.
* The identity/composition theorems state coherence with canonical tensor identifications.
The records, the integer-ring and coefficient-change definitions, the scalar transport
projection and the identity/composition theorems are in
`WeilConjectures.AlgebraicGeometry.EtaleCoefficientSystemAdjointCore`, re-exported here (split for the per-file
compile limit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option linter.all false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
open SheafOfModules
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local irreducible] CategoryTheory.constantSheaf SheafOfModules.siteCoefficientTensor
  SheafOfModules.siteCoefficientTensorAdj
set_option backward.defeqAttrib.useBackward true
private instance strictCoefficientTensorAdditive (T : Scheme.{u})
    (O : Type (u + 1)) [CommRing O] (ell : O) {m n : ℕ} (h : n ≤ m) :
    (coefficientTensor (J := T.smallEtaleTopology) (O := O) (ell := ell) h).Additive :=
  siteCoefficientTensor_additive.{u + 1, u, u + 1}
    (coefficientQuotientMap (J := T.smallEtaleTopology) O ell h)

private instance strictCoefficientRestrictionAdditive (T : Scheme.{u})
    (O : Type (u + 1)) [CommRing O] (ell : O) {m n : ℕ} (h : n ≤ m) :
    (coefficientRestriction (J := T.smallEtaleTopology) O ell h).Additive :=
  inferInstance

attribute [local instance 9000] strictEtaleProperInverseAdditive strictEtaleProperDirectAdditive

section EfficientRealization
set_option backward.isDefEq.respectTransparency.types true
section BrownAssembly
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem brownEvaluation_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {E : A ⥤ C} {F : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (s : L ⋙ F ≅ E ⋙ L') (t : R ⋙ E ≅ F ⋙ R')
    (h : ∀ M, L'.map (t.hom.app M) ≫ adj'.counit.app (F.obj M) =
      s.inv.app (R.obj M) ≫ F.map (adj.counit.app M)) :
    t.hom = (mateEquiv adj adj' (.mk _ _ _ _ s.inv)).natTrans := by
  ext M
  apply (adj'.homEquiv _ _).symm.injective
  exact (h M).trans (mateEquiv_counit adj adj' (.mk _ _ _ _ s.inv) M).symm

private def brownConstantUnderlying (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    Etale.SystemProjection.constantModule T A ⋙
      sheafCompose T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
        AddCommGrpCat.{u + 1}) ≅
      SheafOfModules.toSheaf.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj A)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext U x; rfl)

private theorem brownConstant_exact (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    PreservesFiniteLimits (Etale.SystemProjection.constantModule T A) ∧
      PreservesFiniteColimits (Etale.SystemProjection.constantModule T A) := by
  let F := Etale.SystemProjection.constantModule T A
  let V := sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits (F ⋙ V) :=
    preservesFiniteLimits_of_natIso (brownConstantUnderlying T A).symm
  have : PreservesFiniteColimits (F ⋙ V) :=
    preservesFiniteColimits_of_natIso (brownConstantUnderlying T A).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F V,
    preservesFiniteColimits_of_reflects_of_preserves F V⟩

private theorem brownConstant_faithful (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (Etale.SystemProjection.constantModule T A).Faithful where
  map_injective {M N} {f g} h := by
    ext U x
    exact congrArg (fun k ↦ k.hom.app U x) h

private theorem brownRealization_isLE_iff
    {O : Type (u + 1)} [CommRing O] {t : O} {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O t} (R : StrictEtaleBrownRealization O t T P)
    (n : ℕ) (K : DerivedCategory (strictEtaleLevel T O t n)) (b : ℤ) :
    ((R.derived n).obj K).IsLE b ↔ K.IsLE b := by
  let := strictEtaleLevelDerived T O t n
  let F : strictEtaleLevel T O t n ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) :=
    strictEtaleBrownConstant O t T n
  have : F.Additive := R.val.ordinaryAdditive n
  have : PreservesFiniteLimits F :=
    (brownConstant_exact T (.of (strictEtaleBrownRing O t n))).1
  have : PreservesFiniteColimits F :=
    (brownConstant_exact T (.of (strictEtaleBrownRing O t n))).2
  have : F.Faithful := brownConstant_faithful T (.of (strictEtaleBrownRing O t n))
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O t n) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (R.derived n) := ⟨R.factors n⟩
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O t n) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors⟩
  let e : R.derived n ≅ F.mapDerivedCategory := Localization.liftNatIso
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (R.derived n) F.mapDerivedCategory (Iso.refl _)
  constructor
  · intro h
    have := h
    have hm := DerivedCategory.TStructure.t.isLE_of_iso (e.app K) b
    apply (DerivedCategory.isLE_iff K b).mpr
    intro i hi
    exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isLE_iff _ b).mp hm i hi)
  · intro h
    have := h
    have := F.isLE_mapDerivedCategory_obj K b
    exact DerivedCategory.TStructure.t.isLE_of_iso (e.app K).symm b

private theorem brownFiniteAmplitude
    (k : Type u) [Field k] [IsAlgClosed k] (p l : ℕ) [Fact p.Prime] [Fact l.Prime]
    [CharP k p] (hl : l ≠ p)
    {X Y : Scheme.{u}} (xk : X ⟶ Spec (.of k)) (yk : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType xk] [LocallyOfFiniteType yk]
    [QuasiCompact xk] [QuasiCompact yk]
    (f : X ⟶ Y) (hf : f ≫ yk = xk)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ N : ℕ, ∀ (c : Compactification f) (A : Type (u + 1)) [CommRing A] [Finite A],
      (∃ r : ℕ, (l : A) ^ r = 0) →
      ∀ (b : ℤ) (K : Etale.DerivedCategoryModule A X), K.IsLE b →
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K).IsLE (b + (N : ℤ)) := by
  obtain ⟨N, hN⟩ := Etale.exceptionalConstantTensor k p l hl xk yk f hf
  refine ⟨N, fun c A _ _ ht ↦ (hN c A ?_).1⟩
  obtain ⟨r, hr⟩ := ht
  exact ⟨r, fun z ↦ by rw [hr, zero_mul]⟩

private theorem brownFiniteQuotient
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ha : ∃ r : ℕ, (l : A) ^ r = 0) (hb : ∃ r : ℕ, (l : B) ^ r = 0)
    (a : A →+* B)
    (ga : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (gb : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X)
    (aa : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ ga)
    (ab : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ gb) :
    ∃ q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
          Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c,
      q.hom = Etale.compactScalarMap a c ∧
        IsIso (mateEquiv aa ab (.mk _ _ _ _ q.inv)).natTrans := by
  obtain ⟨q, hq, r, _, rho, _, _, b, hb, _⟩ :=
    Etale.etaleCoefficientQuotientNormalization D l hl f c A B
      (by simpa only [Nat.cast_pow] using ha)
      (by simpa only [Nat.cast_pow] using hb) a ga gb aa ab
  refine ⟨q, hq, ?_⟩
  change IsIso (Etale.etaleCoefficientQuotientMate a c aa ab q)
  rw [← hb]
  infer_instance

private theorem brownInverseWord {C : Type*} [Category C]
    {V₀ V₁ V₂ V₃ V₄ V₅ : C}
    (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (c : V₂ ≅ V₃)
    (d : V₃ ≅ V₄) (e : V₄ ≅ V₅) (q : V₀ ≅ V₅)
    (h : a ≫ b ≫ c.hom ≫ d.hom ≫ e.hom = q.hom) :
    e.inv ≫ d.inv ≫ c.inv = q.inv ≫ a ≫ b := by
  apply (cancel_epi q.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id,
    Iso.hom_inv_id]

private theorem brownCubeMate_isIso
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [c.ReflectsIsomorphisms]
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (hF : IsIso (mateEquiv adj adj' (.mk _ _ _ _ pF.inv)).natTrans)
    (hK : IsIso (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).natTrans)
    (hθ : IsIso (mateEquiv adj' adjK' (.mk _ _ _ _ θ')).natTrans) :
    IsIso (mateEquiv adj adjK (.mk _ _ _ _ θ)).natTrans := by
  have hFapp (M : B) : IsIso ((mateEquiv adj adj'
      (.mk _ _ _ _ pF.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hKapp (M : D) : IsIso ((mateEquiv adjK adjK'
      (.mk _ _ _ _ pK.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hθapp (M : B') : IsIso ((mateEquiv adj' adjK'
      (.mk _ _ _ _ θ')).app M) := NatIso.isIso_app_of_isIso _ M
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have he := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc M
  have hi : IsIso
      (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M) ≫
        (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M)) := by
    rw [he]
    infer_instance
  have : IsIso (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M))
  exact isIso_of_reflects_iso _ c

private theorem brownQuotientMate_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {O : Type (u + 1)} [CommRing O] {t : O}
    (S : StrictEtaleCompactSupport O t c) (B : StrictEtaleBrownConstruction O t c S)
    (hfinite : ∀ n, Finite (strictEtaleBrownRing O t n))
    (htorsion : ∀ n, ∃ r : ℕ, (l : strictEtaleBrownRing O t n) ^ r = 0)
    (g : ∀ n, DerivedCategory (strictEtaleLevel Y O t n) ⥤
      DerivedCategory (strictEtaleLevel X O t n))
    (adjN : ∀ n, S.levelFunctor n ⊣ g n) {m n : ℕ} (h : n ≤ m) :
    IsIso (strictEtaleBrownQuotientMate B adjN h) := by
  have : Finite (strictEtaleBrownRing O t m) := hfinite m
  have : Finite (strictEtaleBrownRing O t n) := hfinite n
  have := B.realizationX.val.equivalence m
  have := B.realizationY.val.equivalence m
  have := B.realizationX.val.equivalence n
  have := B.realizationY.val.equivalence n
  let Fm := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c
  let Fn := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c
  have : Fm.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  have : Fn.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  let am : Fm ⊣ Fm.rightAdjoint := Adjunction.ofIsLeftAdjoint Fm
  let an : Fn ⊣ Fn.rightAdjoint := Adjunction.ofIsLeftAdjoint Fn
  obtain ⟨q, hq, hib⟩ := brownFiniteQuotient D l hl f c
    (strictEtaleBrownRing O t m) (strictEtaleBrownRing O t n)
    (htorsion m) (htorsion n) (strictEtaleBrownRingMap O t h)
    Fm.rightAdjoint Fn.rightAdjoint am an
  have him := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN m) am (B.realizationX.derived m) (B.realizationY.derived m)
    (B.levelComparison m).symm
  have hin := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN n) an (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison n).symm
  have hc (P : DerivedCategory (strictEtaleLevel X O t m)) :
      Fn.map ((B.realizationX.scalar h).inv.app P) ≫
        (B.levelComparison n).inv.app ((S.PX.scalar h).derived.obj P) ≫
        (B.realizationY.derived n).map ((B.projection h).hom.app P) =
      q.inv.app ((B.realizationX.derived m).obj P) ≫
        (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
          ((B.levelComparison m).inv.app P) ≫
        (B.realizationY.scalar h).inv.app ((S.levelFunctor m).obj P) := by
    have he := B.projection_recorded_q h P
    rw [← hq] at he
    exact brownInverseWord _ _
      ((B.realizationY.derived n).mapIso ((B.projection h).app P)).symm
      ((B.levelComparison n).app ((S.PX.scalar h).derived.obj P))
      (Fn.mapIso ((B.realizationX.scalar h).app P))
      (q.app ((B.realizationX.derived m).obj P)) he
  exact brownCubeMate_isIso (adjN m) (adjN n) am an
    (B.realizationX.derived m) (B.realizationY.derived m)
    (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison m) (B.realizationX.scalar h)
    (B.realizationY.scalar h) (B.levelComparison n)
    (B.projection h).hom q.inv hc him hin hib

/-- Ordinary etale exceptional adjoint on strict coefficient systems.
Source: Zheng, Constructions 5.14--5.15, Lemmas 5.16 and 5.22, Proposition 5.24
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof plan (the node's nine steps):
1. The finite coefficient rings are finite ell-primary rings over the finite-field
base. Completeness of the integer ring and finite-type Noetherianity supply the
coefficient-system comparison. Extension by zero is exact, so Rp_* j_! is defined.
The system-level left-extension lemma supplies the Grothendieck system category.
2. For any finite coefficient map form derived tensor left adjoint to exact scalar
restriction. Derived direct-image composition and open extension identify the
restriction square. Its tensor mate is the proper projection formula and is an
isomorphism, including for nonflat coefficient quotients. On K-flat representatives,
units and the tensor associator show its identity and composition coherences.
3. These squares identify F LE_n with LE_n F_n. Proper direct image preserves
coproducts at every finite level; exact open extension does too. Evaluations detect
isomorphisms and compute coproducts. Grothendieck-derived Brown representability
therefore gives G. Transposition supplies its additive, O-linear, and shift
structures. The triangulated-right-adjoint lemma proves exactness.
4. Apply LE_n left adjoint to e_n, F left adjoint to G, and F_n left adjoint to G_n.
The resulting natural Hom bijections identify e_n G with G_n e_n. Transposition
identifies units, counits, and coefficient transitions, including composites.
5. Let N_f be the uniform finite-level upper cohomological amplitude of F. If M is
in degrees at least a and H in degrees at most a-N_f-1, then Hom(F H,M)=0.
Adjunction and standard truncation orthogonality give G M in degrees at least
 a-N_f. The same N_f works for every level.
6. The canonical tensor comparison for G is the transpose of the inverse projection
square followed by the scalar extension of the F/G counit. After restriction of
scalars it is the finite-level constant-tensor comparison, hence an isomorphism.
The evaluated adjoint transitions of G M are these comparisons followed by G_n of
the input adjoint transitions. They are invertible for normalized M. Step 5 gives
the asserted boundedness below. No quotient-flatness assumption is used.
7. Uniqueness of the extended absolute value embeds O in O'. DVR factorization
writes varpi=u*(varpi')^e, e positive. Completeness and the finite residue quotient
make O' finite over O; torsion-freeness and the DVR freeness theorem make it finite
free. Its reductions are finite free and its varpi powers are cofinal.
8. Apply the same counit-transpose construction to the exact scalar extension on
systems. Evaluations identify the comparison with the finite-level comparisons,
so it is invertible. For an identity its transpose is the counit. For composites,
naturality of the counit and the projection-square associativity identify the two
transposes. Injectivity of the Hom bijection proves coherence on system maps, also
for diagrams involving derived quotient tensors and their canonical associators.
9. Cofinal subsequence restriction U_r has the left extension L_r. Projection
squares identify F_full L_r with L_r F_r, including transitions. Apply L_r/U_r and
F/G adjunctions to obtain U_r G_full isomorphic to G_r U_r. The Hom bijection fixes
its counit and map action and gives composition coherence. For r(n)=e*n, the ideal
identity from step 7 identifies this with the varpi-power construction. All maps
are defined by actual derived operations and transposes, hence are independent of
resolutions. No inverse limit, integral output, or constructible restriction enters. -/
theorem etaleCoefficientSystemAdjoint
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) c,
      Nonempty (StrictEtaleExceptionalAdjoint _ _ c S) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := hdvr.2.2.2.1
  have : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({t} : Set O) = IsLocalRing.maximalIdeal O :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec.trans
      (IsLocalRing.eq_maximalIdeal (R := O) hdvr.2.2.2.2.1)
  have ht : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr hgen.symm
  obtain ⟨hfinite, htorsion, _, _, ⟨S⟩, hB⟩ :=
    etaleSystemBrownConstruction D l _hl E t ht.ne_zero ht.not_isUnit f c
  obtain ⟨B⟩ := hB S
  have : B.right.Additive := B.rightAdditive
  have : B.right.CommShift ℤ := B.rightShift
  have hleft (n : ℕ) : (S.levelFunctor n).IsLeftAdjoint := by
    let : CommRing (strictEtaleBrownRing O t n) :=
      Ideal.Quotient.commRing ((Ideal.span ({t} : Set O)) ^ (n + 1))
    have : Finite (strictEtaleBrownRing O t n) := hfinite n
    have := B.realizationX.val.equivalence n
    have := B.realizationY.val.equivalence n
    have := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
      (strictEtaleBrownRing O t n) c
    have : (S.levelFunctor n ⋙ B.realizationY.derived n).IsLeftAdjoint :=
      Functor.isLeftAdjoint_of_iso (B.levelComparison n).symm
    exact (Functor.isLeftAdjoint_comp_iff_left (S.levelFunctor n)
      (B.realizationY.derived n)).mp inferInstance
  let g (n : ℕ) := @Functor.rightAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  let adjN (n : ℕ) : S.levelFunctor n ⊣ g n :=
    @Adjunction.ofIsLeftAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  obtain ⟨H⟩ := etaleSystemEvaluationBound D l _hl E t ht.ne_zero ht.not_isUnit
    f c S B B.right B.adjunction g adjN
  have : Fact D.p.Prime := ⟨D.prime⟩
  let := Fintype.ofFinite D.k₀
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  obtain ⟨N, hN⟩ := brownFiniteAmplitude D.k D.p l _hl
    (X ↘ Spec (.of D.k)) (Y ↘ Spec (.of D.k)) f (comp_over f _)
  have hamp (n : ℕ) (b : ℤ) (K : DerivedCategory (strictEtaleLevel X O t n))
      (hK : K.IsLE b) : ((S.levelFunctor n).obj K).IsLE (b + (N : ℤ)) := by
    have : Finite (strictEtaleBrownRing O t n) := hfinite n
    have hb := @hN c (strictEtaleBrownRing O t n)
      (Ideal.Quotient.commRing ((Ideal.span ({t} : Set O)) ^ (n + 1))) (hfinite n)
      (htorsion n) b ((B.realizationX.derived n).obj K)
      ((brownRealization_isLE_iff B.realizationX n K b).mpr hK)
    apply (brownRealization_isLE_iff B.realizationY n _ _).mp
    exact ⟨(DerivedCategory.TStructure.t.le (b + (N : ℤ))).prop_of_iso
      ((B.levelComparison n).app K).symm hb.le⟩
  have hbound := H.lower_bound N hamp
  have hquot {m n : ℕ} (h : n ≤ m) :
      IsIso (strictEtaleBrownQuotientMate B adjN h) :=
    brownQuotientMate_isIso D l _hl f c S B hfinite htorsion g adjN h
  let data : StrictEtaleExceptionalAdjointData O t c S :=
    { right := B.right
      rightAdditive := B.rightAdditive
      shift := B.rightShift
      adjunction := B.adjunction
      scalarX := B.scalarX
      scalarY := B.scalarY
      levelRight := g
      levelAdjunction := adjN
      evaluation := H.theta
      quotientOpen := B.openProjection
      quotientProper := B.properProjection
      quotientProjection := B.projection
      quotientComparison := fun h ↦ @asIso _ _ _ _
        (strictEtaleBrownQuotientMate B adjN h) (hquot h) }
  refine ⟨S, ⟨⟨data, ?_⟩⟩⟩
  refine ⟨B.rightExact, B.rightLinear, ?_, B.openMate, B.properMate,
    B.projection_def, ?_, H.coefficient_identity, H.coefficient_composition,
    ?_, ⟨N, hbound⟩, ?_⟩
  · intro n
    exact brownEvaluation_mate B.adjunction (adjN n) (S.evaluation n)
      (H.theta n) (H.counit n)
  · intro m n h
    rfl
  · intro m n h M
    change (S.PX.scalar h).derived.map ((H.theta m).hom.app M) ≫
      (strictEtaleBrownQuotientMate B adjN h).app ((S.PY.evaluation m).obj M) ≫
      (g n).map (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PY.transition h).app M)) = _
    exact (H.transition h M).symm
  · intro M hM hnormalized
    obtain ⟨a, ha⟩ := hM
    exact ⟨⟨a - N, hbound a M ha⟩,
      etaleSystemQuotientNormalization D l _hl E t ht.ne_zero ht.not_isUnit
        f c S B B.right B.adjunction g adjN H M hnormalized⟩
end BrownAssembly

/-- The real quotient module induced by the coefficient-ring map.
Source: Zheng, Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleScalarLevelModule {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    (ell : O) (phi : O →+* O') (n : ℕ) :=
  (ModuleCat.restrictScalars.{u + 1} (strictCoefficientRingMap ell phi n)).obj
    (ModuleCat.of (O' ⧸ (Ideal.span ({phi ell} : Set O')) ^ (n + 1))
      (O' ⧸ (Ideal.span ({phi ell} : Set O')) ^ (n + 1)))
/-- Each target quotient is finite free over the source quotient.
Source: Zheng, Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: the integer-ring embedding is the restriction of the field embedding.
Completeness and the finite residue quotient make the target integer ring finite
over the source. It is torsion-free since it embeds in a field. A finite torsion-free
module over a DVR has a finite basis. Reducing that basis modulo the source
uniformizer power gives the displayed basis of the actual restricted quotient module. -/
theorem strictEtaleScalarLevelModule_finiteFree
    (l : ℕ) [Fact l.Prime] {E F : Type (u + 1)} [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (n : ℕ) :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r)
      ((Padic.coefficientExtensionIntegers l E) ⧸
        (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E))) ^ (n + 1))
      (strictEtaleScalarLevelModule (Padic.coefficientExtensionUniformizer l E)
        (strictEtaleIntegerMap l i) n)) := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l F
  let phi : A →+* B := strictEtaleIntegerMap l i
  let : Algebra E F := i.toRingHom.toAlgebra
  let : Algebra A F := (i.toRingHom.comp A.subtype).toAlgebra
  let : Algebra A B := phi.toAlgebra
  have : IsScalarTower A E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Padic l) E F :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (i.commutes x).symm
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite (Padic l) E F
  have hA := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsFractionRing A E := hA.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing A := hA.2.2.2.2.2.2.2.2.1
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  have : IsIntegrallyClosed A := inferInstance
  have : IsNoetherianRing A := inferInstance
  have : Algebra.IsSeparable E F := inferInstance
  have : IsIntegralClosure B A F := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    change x ∈ integralClosure A F ↔ ∃ y : B, (y : F) = x
    rw [← Padic.padic_integers_integralClosure l E F i x]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : Module.IsTorsionFree A F := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    intro x y hxy
    apply Subtype.val_injective
    exact i.injective hxy
  have : Module.Finite A B := IsIntegralClosure.finite A E F B
  have : Module.Free A B := IsIntegralClosure.module_free A E F B
  let I : Ideal A := (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A)) ^
    (n + 1)
  let J : Ideal B := (Ideal.span ({phi (Padic.coefficientExtensionUniformizer l E)} : Set B)) ^
    (n + 1)
  have hJ : I.map (algebraMap A B) = J := by
    simp only [I, J, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl
  let Q := strictEtaleScalarLevelModule (Padic.coefficientExtensionUniformizer l E) phi n
  let : Module (A ⧸ I) (B ⧸ J) :=
    Module.compHom (B ⧸ J) (strictCoefficientRingMap
      (Padic.coefficientExtensionUniformizer l E) phi n)
  let : Module (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := inferInstance
  let e : (B ⧸ I.map (algebraMap A B)) ≃ₗ[A ⧸ I] Q :=
    (Ideal.quotEquivOfEq hJ).toAddEquiv.toLinearEquiv (by
      intro a x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  exact ⟨Module.finrank A B,
    ⟨((Module.finBasis A B).baseChange (A ⧸ I)).map
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv.trans e)⟩⟩
end EfficientRealization

section TransportAssembly
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SheafOfModules.coefficientQuotientMap
  AlgebraicGeometry.StrictEtaleCoefficientChange.sheaf

private theorem inverseProjectionCube {C : Type*} [Category C]
    {A B C' D E F : C}
    (a : A ≅ B) (b : B ≅ C') (c : C' ≅ D)
    (d : A ≅ E) (e : E ≅ F) (f : F ≅ D)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    f.inv ≫ e.inv ≫ d.inv = c.inv ≫ b.inv ≫ a.inv := by
  have hi : a ≪≫ b ≪≫ c = d ≪≫ e ≪≫ f := Iso.ext h
  simpa only [Iso.trans_inv, Category.assoc] using (congrArg Iso.inv hi).symm

private def adjointQuotientProjection
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    (G : StrictEtaleExceptionalAdjoint O ell c S) : StrictEtaleQuotientProjection S where
  openProjection := G.val.quotientOpen
  proper := G.val.quotientProper
  open_mate := G.property.2.2.2.1
  proper_mate := G.property.2.2.2.2.1

private theorem adjointQuotientProjection_eq
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    (G : StrictEtaleExceptionalAdjoint O ell c S) {m n : ℕ} (h : n ≤ m) :
    (adjointQuotientProjection G).projection h = G.val.quotientProjection h :=
  (G.property.2.2.2.2.2.1 h).symm

attribute [local irreducible] adjointQuotientProjection
  StrictEtaleQuotientProjection.projection

private theorem exceptionalTransportOfProjection
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SA : StrictEtaleCompactSupport O ell c} {SB : StrictEtaleCompactSupport O' mu c}
    {TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX}
    {TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY}
    {TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ}
    (GA : StrictEtaleExceptionalAdjoint O ell c SA)
    (GB : StrictEtaleExceptionalAdjoint O' mu c SB)
    (P : StrictEtaleTransportProjection a c SA SB TX TY TZ)
    (hi : ∀ n, IsIso (mateEquiv (GA.levelAdjunction (index n)) (GB.levelAdjunction n)
      (.mk _ _ _ _ (P.level n).inv)).natTrans) :
    Nonempty (StrictEtaleExceptionalTransport a c SA SB TX TY TZ GA GB) := by
  let tau : GA.right ⋙ TX.derived ⟶ TY.derived ⋙ GB.right :=
    (mateEquiv GA.adjunction GB.adjunction
    (.mk _ _ _ _ P.compact.projection.inv)).natTrans
  let rho n : GA.levelRight (index n) ⋙ (TX.level n).derived ≅
      (TY.level n).derived ⋙ GB.levelRight n := @asIso _ _ _ _
    (mateEquiv (GA.levelAdjunction (index n)) (GB.levelAdjunction n)
      (.mk _ _ _ _ (P.level n).inv)).natTrans (hi n)
  have heval n M :
      (SB.PX.evaluation n).map (tau.app M) ≫
        (GB.evaluation n).hom.app (TY.derived.obj M) ≫
        (GB.levelRight n).map ((TY.derivedEvaluation n).hom.app M) =
      (TX.derivedEvaluation n).hom.app (GA.right.obj M) ≫
        (TX.level n).derived.map ((GA.evaluation (index n)).hom.app M) ≫
        (rho n).hom.app ((SA.PY.evaluation (index n)).obj M) := by
    have hc K := inverseProjectionCube
      ((TY.derivedEvaluation n).app (SA.functor.obj K))
      ((TY.level n).derived.mapIso ((SA.evaluation (index n)).app K))
      ((P.level n).app ((SA.PX.evaluation (index n)).obj K))
      ((SB.PY.evaluation n).mapIso (P.compact.projection.app K))
      ((SB.evaluation n).app (TX.derived.obj K))
      ((SB.levelFunctor n).mapIso ((TX.derivedEvaluation n).app K))
      (P.evaluation n K)
    have h := exchangeMate_cube GA.adjunction GB.adjunction
      (GA.levelAdjunction (index n)) (GB.levelAdjunction n)
      (SA.PX.evaluation (index n)) (SA.PY.evaluation (index n))
      (SB.PX.evaluation n) (SB.PY.evaluation n)
      (SA.evaluation (index n)) (TX.derivedEvaluation n)
      (TY.derivedEvaluation n) (SB.evaluation n)
      P.compact.projection.inv (P.level n).inv hc M
    rw [GA.property.2.2.1 (index n), GB.property.2.2.1 n]
    exact h
  have htau : IsIso tau := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    apply (SB.openDerived.detectsIso (tau.app M)).2
    intro n
    have hword : IsIso ((SB.PX.evaluation n).map (tau.app M) ≫
        (GB.evaluation n).hom.app (TY.derived.obj M) ≫
        (GB.levelRight n).map ((TY.derivedEvaluation n).hom.app M)) := by
      rw [heval]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((GB.evaluation n).hom.app (TY.derived.obj M) ≫
        (GB.levelRight n).map ((TY.derivedEvaluation n).hom.app M))
  let data : StrictEtaleExceptionalTransportData a c SA SB TX TY TZ GA GB :=
    { compact := P.compact
      right := @asIso _ _ _ _ tau htau
      levelProjection := P.level
      levelRight := rho
      quotientX := P.quotientX
      quotientY := P.quotientY }
  refine ⟨⟨data, rfl, P.evaluation, fun _ ↦ rfl, ?_, fun n M ↦ (heval n M).symm⟩⟩
  intro m n h M
  have hc K := P.quotient_cube (adjointQuotientProjection GA)
    (adjointQuotientProjection GB) h K
  simp only [adjointQuotientProjection_eq] at hc
  have hcube := exchangeMate_cube (GA.levelAdjunction (index m))
    (GB.levelAdjunction m) (GA.levelAdjunction (index n)) (GB.levelAdjunction n)
    (SA.PX.scalar (index.monotone h)).derived
    (SA.PY.scalar (index.monotone h)).derived
    (SB.PX.scalar h).derived (SB.PY.scalar h).derived
    (GA.val.quotientProjection (index.monotone h)).symm (P.quotientX.derived h).symm
    (P.quotientY.derived h).symm (GB.val.quotientProjection h).symm
    (P.level m).inv (P.level n).inv hc M
  dsimp only [data]
  rw [GA.property.2.2.2.2.2.2.1 (index.monotone h),
    GB.property.2.2.2.2.2.2.1 h]
  simpa only [rho, asIso_hom, Iso.symm_hom, Iso.symm_inv] using hcube

end TransportAssembly

/-- The canonical finite-extension comparison is invertible on actual derived systems.
The target uses the image of the original uniformizer, not the target uniformizer.
Source: Zheng, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: uniqueness of absolute values embeds integer rings. Completeness, finite
residue quotients and torsion-freeness make O' finite free over O. The induced
termwise tensor is exact. Construct the geometric inverse-image scalar squares on
tensor generators; their open/proper mates give the compact-support projection.
Transpose its inverse followed by the extended counit. Evaluation identifies this
map with the invertible finite-level constant-tensor comparison. Evaluation detects
isomorphisms, so this actual system map is invertible. All representative maps are
normalized by the universal derived counits and hence are independent of resolutions. -/
theorem etaleCoefficientSystemAdjoint_scalar
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : Type (u + 1)) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (i : E →ₐ[Padic l] F)
    (SA : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) c)
    (GA : StrictEtaleExceptionalAdjoint _ _ c SA) :
    ∃ (SB : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l F)
        (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) c)
      (GB : StrictEtaleExceptionalAdjoint _ _ c SB)
      (TX : StrictEtaleCoefficientTransport
        (strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
          (strictEtaleIntegerMap l i)) X SA.PX SB.PX)
      (TY : StrictEtaleCoefficientTransport
        (strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
          (strictEtaleIntegerMap l i)) Y SA.PY SB.PY)
      (TZ : StrictEtaleCoefficientTransport
        (strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
          (strictEtaleIntegerMap l i)) c.Z SA.PZ SB.PZ),
      Nonempty (StrictEtaleExceptionalTransport _ c SA SB TX TY TZ GA GB) := by
  obtain ⟨SB, GB, TX, TY, TZ, P, hi⟩ := strictEtaleScalarTransportProjection
    D l _hl E (f := f) c F i SA GA
  refine ⟨SB, GB, TX, TY, TZ, ?_⟩
  exact exceptionalTransportOfProjection GA GB P hi
section CofinalTransport
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SheafOfModules.coefficientQuotientMap
  AlgebraicGeometry.StrictEtaleCoefficientChange.sheaf

/-- Restriction to the ramified cofinal subsequence agrees with the construction
using powers of the original uniformizer, as functors and on all derived maps.
Source: Zheng, Construction 4.1 and the adjunction following Lemma 5.16
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: DVR factorization writes the original uniformizer as a unit times the e-th
power of the new uniformizer, with e positive. Thus the displayed quotient ideals
agree at every positive exponent. Their canonical quotient equivalences define the
coefficient transport. Cofinal restriction has the left extension L_r; projection
squares identify F_full L_r with L_r F_r including transitions. Apply both
adjunctions to obtain the displayed G comparison by the natural Hom bijection.
Its transpose is the inverse projection followed by the counit, which fixes the
map, its evaluations, and resolution independence. Positivity makes r(n)+1=e*(n+1),
so level zero retains the exponent e, and no positive level is silently discarded. -/
theorem etaleCoefficientSystemAdjoint_cofinal
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : Type (u + 1)) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (i : E →ₐ[Padic l] F)
    (SF : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l F)
      (Padic.coefficientExtensionUniformizer l F) c)
    (GF : StrictEtaleExceptionalAdjoint _ _ c SF)
    (SB : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l F)
      (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) c)
    (GB : StrictEtaleExceptionalAdjoint _ _ c SB) :
    ∃ (e : ℕ) (_he : 0 < e)
      (h : ∀ n, (Ideal.span ({Padic.coefficientExtensionUniformizer l F} :
          Set (Padic.coefficientExtensionIntegers l F))) ^
          (strictEtaleRamifiedIndex e n + 1) =
        (Ideal.span ({strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)} :
          Set (Padic.coefficientExtensionIntegers l F))) ^ (n + 1))
      (RX : StrictEtaleCoefficientTransport
        (strictEtaleRamifiedChange (Padic.coefficientExtensionUniformizer l F)
          (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) e h)
        X SF.PX SB.PX)
      (RY : StrictEtaleCoefficientTransport
        (strictEtaleRamifiedChange (Padic.coefficientExtensionUniformizer l F)
          (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) e h)
        Y SF.PY SB.PY)
      (RZ : StrictEtaleCoefficientTransport
        (strictEtaleRamifiedChange (Padic.coefficientExtensionUniformizer l F)
          (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) e h)
        c.Z SF.PZ SB.PZ),
      Nonempty (StrictEtaleExceptionalTransport _ c SF SB RX RY RZ GF GB) := by
  let : Algebra E F := i.toRingHom.toAlgebra
  have : IsScalarTower (Padic l) E F :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (i.commutes x).symm
  have hcompat (x : E) :
      Padic.coefficientExtensionAbsoluteValue l F (algebraMap E F x) =
        Padic.coefficientExtensionAbsoluteValue l E x := by
    change spectralNorm (Padic l) F (i x) = spectralNorm (Padic l) E x
    unfold spectralNorm
    rw [minpoly.algHom_eq i i.injective]
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec
  obtain ⟨j, hj, _, _, e, _w, he, _hpower, hstages, _⟩ :=
    Padic.local_field_coefficient_stages l E F hcompat
      (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l F)
      hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hj' : j = strictEtaleIntegerMap l i := by
    apply RingHom.ext
    intro x
    apply Subtype.val_injective
    exact hj x
  have h n :
      (Ideal.span ({Padic.coefficientExtensionUniformizer l F} :
        Set (Padic.coefficientExtensionIntegers l F))) ^
        (strictEtaleRamifiedIndex e n + 1) =
      (Ideal.span ({strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l F))) ^ (n + 1) := by
    have hn : strictEtaleRamifiedIndex e n + 1 = e * (n + 1) :=
      Nat.sub_add_cancel (Nat.mul_pos he (Nat.succ_pos n))
    rw [hn, Ideal.span_singleton_pow, Ideal.span_singleton_pow, ← hj']
    exact (hstages (n + 1) (Nat.succ_pos n)).1.symm
  let a := strictEtaleRamifiedChange (Padic.coefficientExtensionUniformizer l F)
    (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) e h
  have ha n : Function.Bijective (a.ring n) := (Ideal.quotEquivOfEq (h n)).bijective
  obtain ⟨RX, RY, RZ, P, hi⟩ := strictEtaleIsomorphicStageProjection a ha c SF SB
  refine ⟨e, he, h, RX, RY, RZ, ?_⟩
  apply exceptionalTransportOfProjection GF GB P
  intro n
  have := (hi n).1
  have := (hi n).2
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (GF.levelAdjunction (strictEtaleRamifiedIndex e n)) (GB.levelAdjunction n)
    (RX.level n).derived (RY.level n).derived (P.level n).symm
end CofinalTransport
end AlgebraicGeometry

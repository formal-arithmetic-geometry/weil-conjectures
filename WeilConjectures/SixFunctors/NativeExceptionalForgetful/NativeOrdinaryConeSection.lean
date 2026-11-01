/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeOrdinaryConeRetraction
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleDirectFiniteness
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Native.NativeCondensedDerivedComparison
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Section half of the native ordinary cone criterion -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures.AdicQbarRealization

open scoped AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/--
Constructible finite stalks turn the split injection from the cone into a
section of the underlying ordinary map when the common-stage objects are
isomorphic.

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`,
final exceptional-adjunction sentence. Transport the common-stage isomorphism
through the fully faithful ordinary realization. Compose the split injection
with the inverse of this isomorphism. On each constructible cohomology sheaf,
stratify and trivialize; square matrices over a commutative ring turn a left
inverse into a two-sided inverse. Restriction conservativity and derived
cohomology then show that the original map is invertible, hence has a section.
(blueprint: lem-sf-native-ordinary-cone-section).
-/
theorem native_ordinary_cone_section (R : Family l D) (T : Space D)
    (V : ForgetModel D l R T) (H M : W D l T) (q : H ⟶ M)
    (e : Nonempty (V.functor.obj H ≅ V.functor.obj M))
    (hq : ∀ (K : W D l T) (v : K ⟶ H),
      WeilComplex.forget.map (v ≫ q) = 0 → V.functor.map v = 0) :
    Nonempty (SplitEpi (WeilComplex.forget.map q)) := by
  classical
  obtain ⟨sm⟩ := native_ordinary_cone_retraction D l R T V H M q e hq
  let : IsSplitMono (WeilComplex.forget.map q) := IsSplitMono.mk' sm
  let r := (R.data (geometric D T)).realization
  let := r.commutative
  let := r.sectionsAdditive
  let := r.sectionsLimits
  let := r.sectionsColimits
  let S := sectionFunctor l (geometric D T).base.left r
  let : S.Additive := r.sectionsAdditive
  let : PreservesFiniteLimits S := r.sectionsLimits
  let : PreservesFiniteColimits S := r.sectionsColimits
  let : S.IsEquivalence := (R.data (geometric D T)).presentation
  let e₀ := (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingEquiv
  let : IsIso (CommRingCat.ofHom e₀.toRingHom) := e₀.toCommRingCatIso.isIso_hom
  have : IsIso (closureMap D T) := by
    dsimp only [closureMap]
    infer_instance
  let G := ProEtale.adicLowerStar l (closureMap D T)
  let F := G.mapDerivedCategory ⋙ S.mapDerivedCategory
  have : F.Full := inferInstance
  have : F.Faithful := inferInstance
  let χ : U D l R T ≅ WeilComplex.forget ⋙ F :=
    Functor.isoWhiskerLeft WeilComplex.forget
      (Functor.isoWhiskerRight G.rightDerivedFunctorIsoMapDerivedCategory
        S.mapDerivedCategory)
  obtain ⟨i⟩ := e
  let j := χ.symm.app H ≪≫ V.realization.symm.app H ≪≫
    (rho D l R T).mapIso i ≪≫ V.realization.app M ≪≫ χ.app M
  let k : WeilComplex.forget.obj H ≅ WeilComplex.forget.obj M := F.preimageIso j
  let a := WeilComplex.forget.map q ≫ k.inv
  have : IsSplitMono a := inferInstance
  have : CompactSpace T.base.hom.geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace T.base.hom.geometricFiberToAlgebraicClosure
  let X := T.base.hom.geometricFiber
  let : X.Over (Spec (CommRingCat.of (AlgebraicClosure D.k₀))) :=
    ⟨T.base.hom.geometricFiberToAlgebraicClosure⟩
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian T.base.hom.geometricFiberToAlgebraicClosure
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of (AlgebraicClosure D.k₀))) :=
    inferInstanceAs (LocallyOfFiniteType T.base.hom.geometricFiberToAlgebraicClosure)
  have : QuasiCompact (X ↘ Spec (CommRingCat.of (AlgebraicClosure D.k₀))) :=
    inferInstanceAs (QuasiCompact T.base.hom.geometricFiberToAlgebraicClosure)
  have : IsSeparated (X ↘ Spec (CommRingCat.of (AlgebraicClosure D.k₀))) :=
    inferInstanceAs (IsSeparated (pullback.snd T.base.hom _))
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫
    (T.base.hom.geometricFiberProj ≫ T.base.hom).appTop
  have hunit : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k₀
        (Fact.out : l.Prime) (Fact.out : ringChar D.k₀ ≠ l))).map ρ.hom
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        ((hunit.map (X.presheaf.germ ⊤ x trivial).hom).map (X.residue x).hom)).invertible
  let E := ProEtale.nativeCondensedModules l X
  let Q := E.mapDerivedCategory
  let hH := ((WeilComplex.forgetBoundedConstructibleAdic D.k₀ l T.base.left).obj H).property
  have hK : ProEtale.constantModelBoundedConstructible
      (Profinite.padicAlgClRingObj l) X (Q.obj (WeilComplex.forget.obj H)) := by
    refine ⟨E.bounded_mapDerivedCategory_obj hH.1, fun n ↦ ?_⟩
    have := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
      (Profinite.padicAlgClRingObj l) X).1
    exact ObjectProperty.prop_of_iso _
      ((E.mapDerivedCategoryHomologyFunctorIso n).app (WeilComplex.forget.obj H))
      (ProEtale.nativeCondensed_constructible D.k₀ (AlgebraicClosure D.k₀) l
        (Ne.symm (Fact.out : ringChar D.k₀ ≠ l)) X _ (hH.2 n))
  have hab : Q.map a ≫ Q.map (retraction a) = 𝟙 _ := by
    rw [← Q.map_comp, IsSplitMono.id, Q.map_id]
  have hba := ProEtale.condensed_constructible_direct_finiteness l X
    (Q.obj (WeilComplex.forget.obj H)) hK (Q.map a) (Q.map (retraction a)) hab
  have ha : IsIso a := by
    have : IsIso (Q.map a) := ⟨⟨Q.map (retraction a), hab, hba⟩⟩
    exact isIso_of_reflects_iso a Q
  have : WeilComplex.forget.map q = a ≫ k.hom := by simp [a]
  have : IsIso (WeilComplex.forget.map q) := by
    rw [this]
    infer_instance
  exact IsSplitEpi.exists_splitEpi

end WeilConjectures.NativeExceptionalForgetful

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstantExtensionWeilHeartData
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions

public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree

import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.Finiteness
import WeilConjectures.PointCount

/-! # Finite constant extension of ordinary condensed Weil sheaves

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

The geometric fibre is identified by constantExtensionFiberIso; its Frobenius identity
is constantExtensionFiber_return. The extended Weil structure is the ordered pullback
iterate in extend. The compact-support operators below are constructed directly from
the powered scheme automorphisms. They act directly on the recorded compact-support
coefficient complex condensedQbarCompactSections of def-weil-ordinary-compact-cohomology,
with values in the ordinary derived category of Qbar_ell-modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedWeil

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

set_option maxHeartbeats 2000000 in
-- Check the two definitionally equal presentations of the base-changed open immersion.
end WeilConjectures.CondensedWeil

namespace WeilConjectures.CondensedWeil

private theorem free_fibre_finite_local (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj ell) T) M) :
    FiniteDimensional (PadicAlgCl ell)
      ((CondensedQbarGeometricEvaluation.fieldFiber K ell).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) x).obj M)) := by
  let F := CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) x ⋙
    CondensedQbarGeometricEvaluation.fieldFiber K ell
  let r : F.obj (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
      ≃ₗ[PadicAlgCl ell] PadicAlgCl ell :=
    ((CondensedQbarGeometricEvaluation.fieldFiber K ell).mapIso
      (condensedQbarRegularPullbackIso ell x)).toLinearEquiv |>.trans
        (CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ell)
  obtain ⟨n, ⟨e⟩⟩ := hM
  let b : F.obj (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ell) T) n)
      ≃ₗ[PadicAlgCl ell] (Fin n → PadicAlgCl ell) :=
    ((F.mapBiproduct (fun _ : Fin n ↦
        Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ell) T)) ≪≫
      ModuleCat.biproductIsoPi _).toLinearEquiv).trans
        (LinearEquiv.piCongrRight (fun _ ↦ r))
  exact Module.Finite.equiv (((F.mapIso e).toLinearEquiv).trans b).symm

private theorem lisse_fibre_finite_local (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M) :
    FiniteDimensional (PadicAlgCl ell)
      ((CondensedQbarGeometricEvaluation.fieldFiber K ell).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) x).obj M)) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨i, g, hg⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale x
  have hfin := free_fibre_finite_local ell g _ (hU i)
  have h : FiniteDimensional (PadicAlgCl ell)
      ((CondensedQbarGeometricEvaluation.fieldFiber K ell).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) (g ≫ U.f i)).obj M)) := by
    apply (Module.Finite.equiv_iff (Iso.toLinearEquiv
      ((CondensedQbarGeometricEvaluation.fieldFiber K ell).mapIso
        ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell) g (U.f i)).app M)))).mpr
    exact hfin
  rw [← hg]
  exact h

private theorem eigenvalue_of_intertwining {R : Type*} [Field R]
    {V W : ModuleCat R} (A : End V) (B : End W) (b : V ≅ W)
    (hab : A ≫ b.hom = b.hom ≫ B) {α : R}
    (hα : Module.End.HasEigenvalue A.hom α) : Module.End.HasEigenvalue B.hom α := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := b.hom v)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv ⊢
  refine ⟨?_, ?_⟩
  · have hh := congrArg (fun f : V ⟶ W ↦ f v) hab
    change b.hom (A.hom v) = B.hom (b.hom v) at hh
    rw [← hh, hv.1, map_smul]
  · intro hz
    apply hv.2
    apply b.toLinearEquiv.injective
    simpa using hz

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [hsep : IsSeparated X₀.hom] (M : WeilModule D l X₀)
    (hc : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (hlis : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (e : ℕ) (he : 1 ≤ e)

-- The pullback projection is locally of finite type using only the original model.
-- In particular this does not require the coefficient or constructibility hypotheses.
private local instance constantExtensionModel_lft_local (e : ℕ) (he : 1 ≤ e) :
    LocallyOfFiniteType (constantExtensionModel D e he X₀).hom := by
  change LocallyOfFiniteType (pullback.snd X₀.hom _)
  infer_instance

include hsep hl hc hlis he

omit hl hc in
/-- Punctual purity is preserved for every field embedding and every real weight.
Source: latest blueprint, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

Proof: stalks are finite-dimensional and the spectrum of F_x^f consists of the
fth powers of its eigenvalues, without semisimplicity. Conjugacy preserves spectra.
For each embedding iota, |iota(alpha^f)| = |iota(alpha)|^f and q_z=q_x^f;
therefore the weight remains w. The zero stalk contributes no eigenvalue. -/
theorem constantExtension_pure (iota : PadicAlgCl l →+* ℂ) (w : ℝ) :
    Pure D l X₀ M iota w →
      Pure (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀)
        (extend D l X₀ e he M) iota w := by
  intro hp z iz hiz α hα
  let Z₀ := constantExtensionModel D e he X₀
  let π := constantExtensionProjection D e he X₀
  let x := constantExtensionClosedImage D e he X₀ z
  let ix : X₀.left.residueField x.val →+* D.k :=
    iz.comp (π.left.residueFieldMap z.val).hom
  have hcomp : (algebraMap (constantExtensionDatum D e he).k₀
      (constantExtensionDatum D e he).k).comp (D.extensionEmbedding e he) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k e he).choose_spec.2.2.2.2.2.2.choose_spec
  have hr : Scheme.Hom.residueFieldAlgebraMap
      (Z₀.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))) z.val =
      (Z₀.hom.residueFieldAlgebraMap z.val).comp (D.extensionEmbedding e he) := by
    have h := Scheme.Hom.specMap_residueFieldAlgebraMap
      (Z₀.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))) z.val
    rw [← Category.assoc, ← Z₀.hom.specMap_residueFieldAlgebraMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h)
  have hw : π.left ≫ X₀.hom =
      Z₀.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)) := Over.w π
  have hix : ix.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k := by
    change (iz.comp (π.left.residueFieldMap z.val).hom).comp
      (X₀.hom.residueFieldAlgebraMap (π.left z.val)) = _
    rw [RingHom.comp_assoc, ← Scheme.Hom.residueFieldAlgebraMap_comp,
      hw, hr, ← RingHom.comp_assoc, hiz]
    exact hcomp
  let : Algebra (constantExtensionDatum D e he).k₀ (Z₀.left.residueField z.val) :=
    (Z₀.hom.residueFieldAlgebraMap z.val).toAlgebra
  have : Module.Finite (constantExtensionDatum D e he).k₀
      (Z₀.left.residueField z.val) :=
    Z₀.hom.finite_residueField_of_isClosed z.val z.property
  have : Finite (Z₀.left.residueField z.val) :=
    Module.finite_of_finite (constantExtensionDatum D e he).k₀
  let : Algebra (X₀.left.residueField x.val) (Z₀.left.residueField z.val) :=
    (π.left.residueFieldMap z.val).hom.toAlgebra
  have hf : 0 < constantExtensionResidueDegree D e he X₀ z.val := by
    exact Module.finrank_pos (R := X₀.left.residueField x.val)
      (M := Z₀.left.residueField z.val)
  have hcard : Nat.card (Z₀.left.residueField z.val) =
      Nat.card (X₀.left.residueField x.val) ^
        constantExtensionResidueDegree D e he X₀ z.val :=
    Module.natCard_eq_pow_finrank
  have : FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x ix hix) :=
    lisse_fibre_finite_local l (localClosedPoint D X₀ x ix hix) M.carrier hlis
  obtain ⟨b, hb⟩ := constantExtension_local_conjugacy D l hl X₀ M hc hlis e he
    z x rfl iz hiz ix hix
  have hpow := eigenvalue_of_intertwining _ _ b hb hα
  have hhom : (closedOperator D l X₀ M x ix hix ^
      constantExtensionResidueDegree D e he X₀ z.val).hom =
      (closedOperator D l X₀ M x ix hix).hom ^
        constantExtensionResidueDegree D e he X₀ z.val :=
    (ModuleCat.endRingEquiv _).map_pow _ _
  rw [hhom] at hpow
  obtain ⟨β, hβ, rfl⟩ := hpow.exists_pow_eq hf
  rw [map_pow, norm_pow, hp x ix hix β hβ, hcard, Nat.cast_pow]
  exact Real.rpow_pow_comm (Nat.cast_nonneg _) _ _

end WeilConjectures.CondensedWeil

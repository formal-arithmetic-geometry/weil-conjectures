/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectCharacterization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.PbcUniformCompleteTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Integral finite-Tor representatives of rational constructible objects

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
thm-pur-rational-and-qbar-purity.proof.md, Step 1.
(blueprint: lem-pur-rational-lattice-adic-domain).

The integral coefficient comparison is the published projection-normalized transport.
Reduction index n means exponent n+1; index zero is the residue reduction.
The rational category is the raw scalar localization, retaining every integral object.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- A separated finite-type scheme over the fixed geometric field satisfies the base
conditions for the raw rational category.
Source: purity transport proof, Step 1
(blueprint: lem-pur-rational-lattice-adic-domain).
Proof (node step 1): a field is Noetherian. Apply finite-type ascent of Noetherianity
(Stacks 01T6) to the structure morphism. Finite-type dimension gives a finite bound.
The characteristic is p and ell differs from p, so Bezout supplies an inverse of ell
in every local ring, by the structure map from the base field. -/
theorem rational_lattice_adic_base (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of P.field.k))] :
    IsNoetherian T ∧
      (∃ m : ℕ, topologicalKrullDim T ≤ m) ∧
      ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x) := by
  exact ⟨isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k)),
    exists_topologicalKrullDim_le (T ↘ Spec (CommRingCat.of P.field.k)),
    P.coefficientPrime_isUnit_stalk T (T ↘ Spec (CommRingCat.of P.field.k))⟩

/-- The two integral object conditions agree over their canonical completed coefficient
comparison, which is fixed by every quotient projection and hence uses the same reductions.
Source: purity transport proof, Step 1; Bhatt--Scholze, Definition 6.5.1 and
Proposition 6.8.11(3) (blueprint: lem-pur-rational-lattice-adic-domain).
Proof (node step 2): the preceding geometric applicability supplies Noetherianity,
finite dimension and invertibility of ell. Apply integralStratifiedPerfectDetailed.
Its coefficient comparison identifies the completed sheaves by the quotient projections,
so the comparison concerns the actual reductions, including compatible etale origins. -/
theorem rational_lattice_integral_comparison (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of P.field.k))]
    (K : DerivedCategory (scalarReductionSource.{u, u}
      P.coefficients.l P.extension T)) :
    sfIntegralConstructible P.coefficients.l P.extension T K ↔
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum P.coefficients.l P.extension)
        ((integralDetailedTransport T P.coefficients.l P.extension).obj K) := by
  obtain ⟨hnoeth, hdim, hinv⟩ := rational_lattice_adic_base P T
  let : IsNoetherian T := hnoeth
  apply integralStratifiedPerfectDetailed T P.coefficients.l P.extension hdim _ K
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using hinv x

private noncomputable def restrictionIsoRoundTrip
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} e.inv ⋙
      SheafOfModules.restrictScalars.{u + 1} e.hom ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars e.hom).obj
          ((SheafOfModules.restrictScalars e.inv).obj M)).val.obj U)
        (Y := M.val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro a x
          change M.val.obj U at x
          change e.inv.hom.app U (e.hom.hom.app U a) • x = a • x
          have h := ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app U) e.hom_inv_id) a
          change e.inv.hom.app U (e.hom.hom.app U a) = a at h
          rw [h] }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := M.val.obj U)
        (Y := ((SheafOfModules.restrictScalars e.hom).obj
          ((SheafOfModules.restrictScalars e.inv).obj M)).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro a x
          change M.val.obj U at x
          change a • x = e.inv.hom.app U (e.hom.hom.app U a) • x
          have h := ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app U) e.hom_inv_id) a
          change e.inv.hom.app U (e.hom.hom.app U a) = a at h
          rw [h] }
      naturality := by intros; ext; rfl } }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }) (by intros; ext; rfl)

private theorem restrictionIso_isEquivalence
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).IsEquivalence := by
  let E : SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
    CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
      (SheafOfModules.restrictScalars e.inv)
      (restrictionIsoRoundTrip e.symm).symm (restrictionIsoRoundTrip e)
  exact E.isEquivalence_functor

/-- Every interval bounding residue cohomology bounds the Tor amplitude of all positive
reductions, with the interval fixed before the reduction level is quantified.
Source: purity transport proof, Step 1; Stacks 06YT, 06YY and the residue Tor test
(blueprint: lem-pur-rational-lattice-adic-domain).
Proof (node step 3): map the coefficient-prime unit in each stalk to its residue
field and choose its inverse. Apply integral_residue_tor to the given integral
constructible object and residue interval. That theorem identifies successive reduction
with direct residue reduction by the normalized coefficient tensor associator and applies
the residue Tor test at every positive level. No torsion-freeness assumption is made. -/
theorem rational_lattice_reduction_tor (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of P.field.k))]
    (K : DerivedCategory (scalarReductionSource.{u, u}
      P.coefficients.l P.extension T))
    (_hK : sfIntegralConstructible P.coefficients.l P.extension T K)
    (r s : ℤ) (_hrs : r ≤ s)
    (_hres : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} P.coefficients.l P.extension T 0).obj K)
        ⊆ Set.Icc r s) :
    ∀ n : ℕ, HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
      ((scalarReductionDerivedExtension.{u, u} P.coefficients.l P.extension T n).obj K)
      r s := by
  classical
  have hinv (x : T) : IsUnit (P.coefficients.l : T.residueField x) := by
    simpa only [map_natCast] using
      (P.coefficientPrime_isUnit_stalk T (T ↘ Spec (CommRingCat.of P.field.k)) x).map
        (T.residue x).hom
  let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) :=
    fun x ↦ (hinv x).invertible
  exact (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension T).1 K _hK r s _hrs (fun _ hi ↦ _hres hi)

/-- Every integral object has a residue interval and a uniform Tor interval. Every
integral representative retained by raw rationalization has this finite-Tor property,
including torsion representatives; its detailed presentation uses the canonical transport.
Source: purity transport proof, Step 1
(blueprint: lem-pur-rational-lattice-adic-domain).
Proof (node step 4): the common cohomological interval of integral constructibility
bounds the first reduction; for zero take [0,0]. The preceding residue Tor statement
makes this same interval a Tor interval for all levels. This is precisely
finiteTorConstructibleIntegral. Restriction along the inverse of the normalized completed
coefficient isomorphism gives each PBC integral object its detailed presentation, and the
integral comparison identifies its constructibility. Raw localization changes only Hom
modules, retaining every integral object, so this applies to each rational representative.
For example O_E/(varpi) on a geometric point has reductions [A_n --varpi--> A_n] in
degrees -1 and 0, giving the uniform interval [-1,0]; torsion representatives are included. -/
theorem rational_lattice_adic_domain (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of P.field.k))] :
    (∀ K : DerivedCategory (scalarReductionSource.{u, u}
        P.coefficients.l P.extension T),
      sfIntegralConstructible P.coefficients.l P.extension T K →
        (∃ r s : ℤ, r ≤ s ∧ proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u}
            P.coefficients.l P.extension T 0).obj K) ⊆ Set.Icc r s) ∧
        finiteTorConstructibleIntegral P.coefficients.l P.extension T K) ∧
    (∀ L : PbcRationalCategory T (pbcIntegralDatum P.coefficients.l P.extension)
        (pbcUniformizer P.coefficients.l P.extension),
      ∃ K : DerivedCategory (scalarReductionSource.{u, u}
          P.coefficients.l P.extension T),
        Nonempty (((integralDetailedTransport T P.coefficients.l P.extension).obj K)
          ≅ L.obj.obj) ∧
        finiteTorConstructibleIntegral P.coefficients.l P.extension T K) := by
  classical
  have hfinite (K : DerivedCategory (scalarReductionSource.{u, u}
      P.coefficients.l P.extension T))
      (hK : sfIntegralConstructible P.coefficients.l P.extension T K) :
      (∃ r s : ℤ, r ≤ s ∧ proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u}
          P.coefficients.l P.extension T 0).obj K) ⊆ Set.Icc r s) ∧
      finiteTorConstructibleIntegral P.coefficients.l P.extension T K := by
    obtain ⟨r, s, hrs, hlevels⟩ := hK.2
    have hres := (hlevels 0).2
    exact ⟨⟨r, s, hrs, hres⟩, hK, r, s, hrs,
      rational_lattice_reduction_tor P T K hK r s hrs hres⟩
  refine ⟨hfinite, ?_⟩
  intro L
  obtain ⟨hnoeth, hdim, hinv⟩ := rational_lattice_adic_base P T
  let : IsNoetherian T := hnoeth
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete T
        (pbcIntegralDatum P.coefficients.l P.extension)) :=
    (pbcIntegralUniformComplete_isTriangulated P.coefficients.l P.extension T hdim hinv).1
  have : Functor.IsEquivalence (SheafOfModules.restrictScalars.{u + 1}
      (integralDetailedCoefficientComparison T P.coefficients.l P.extension).hom) :=
    restrictionIso_isEquivalence _
  have : (integralDetailedTransport T P.coefficients.l P.extension).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory _
  let F := integralDetailedTransport T P.coefficients.l P.extension
  let K := F.objPreimage L.obj.obj
  let e := F.objObjPreimageIso L.obj.obj
  let W : ObjectProperty (PbcCompletedDerived T
      (pbcIntegralDatum P.coefficients.l P.extension)) :=
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum P.coefficients.l P.extension)
  have hK : sfIntegralConstructible P.coefficients.l P.extension T K :=
    (rational_lattice_integral_comparison P T K).mpr
      (W.prop_of_iso e.symm L.obj.property)
  exact ⟨K, ⟨e⟩, (hfinite K hK).2⟩

end WeilConjectures

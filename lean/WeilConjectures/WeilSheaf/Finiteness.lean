/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.LowerStarPairing
public import WeilConjectures.WeilSheaf.PoincareDuality
public import WeilConjectures.WeilSheaf.ProperCohomology
import Sheaf.WeilSheaf.AdicFiniteCoefficientBound
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.WeilSheaf.Operations
import WeilConjectures.WeilSheaf.OpenClosedTriangle
import WeilConjectures.WeilSheaf.UpperStarConstant
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.ConstructibleSheaf.LisseLocus

/-!
# Finiteness of the cohomology of Weil complexes and Frobenius

Let `X` be a separated scheme of finite type over a finite field `k₀` with algebraic closure
`k̄`, and `K` a Weil complex on `X`. Its ordinary and compactly supported cohomology groups
`Hʳ(X ⊗ k̄, K)` and `Hʳ_c(X ⊗ k̄, K)` are finite-dimensional `ℚ̄_ℓ`-vector spaces with a geometric
Frobenius automorphism (`FrobeniusModule`), vanishing outside a finite interval. If `X` is
proper over `k₀` they agree, Frobenius-equivariantly. For the constant Weil sheaf `ℚ̄_ℓ` they
vanish outside `[0, 2e]`, `e` the dimension of `X ⊗ k̄`, and if `X` is geometrically connected
then `H⁰(X ⊗ k̄, ℚ̄_ℓ)` is `ℚ̄_ℓ` with trivial Frobenius.

## Main statements

All of them are blueprint `prop-cohomological-finiteness`.

- `AlgebraicGeometry.WeilComplex.exists_subsingleton_compactlySupportedCohomology`,
  `AlgebraicGeometry.WeilComplex.exists_subsingleton_cohomology`: the cohomology vanishes
  outside a finite interval.
- `AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology`: for
  `X` proper, `Hʳ_c(X ⊗ k̄, K) ≅ Hʳ(X ⊗ k̄, K)` compatibly with Frobenius.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant`,
  `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_isProper`: the
  cohomology of the constant Weil sheaf vanishes outside `[0, 2e]`.
- `AlgebraicGeometry.WeilSheaf.finrank_cohomology_zero_adicConstant`,
  `AlgebraicGeometry.WeilSheaf.frobenius_cohomology_zero_adicConstant`: for `X` geometrically
  connected, `H⁰(X ⊗ k̄, ℚ̄_ℓ)` is one-dimensional with trivial Frobenius.

## Implementation notes

The blueprint states the proposition for Weil complexes with coefficients in a finite
extension `E` of `ℚ_ℓ`; the Weil complexes of the repository have coefficients in `ℚ̄_ℓ`. The
finite dimensionality of the cohomology groups is part of the structure `FrobeniusModule` that
they are valued in, so it is not restated here.

For proper `X` the comparison is induced by the isomorphism `Ra_! ≅ Ra_*` of
`AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoOfIsProper`; the statement
`AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology` records
only that a Frobenius-equivariant isomorphism exists.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The global sections of a zero Weil sheaf vanish. -/
theorem WeilSheaf.subsingleton_globalSections_of_isZero {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : Limits.IsZero F) : Subsingleton F.globalSections.carrier :=
  ModuleCat.subsingleton_of_isZero <| Functor.map_isZero
    (ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l) ⋙ WeilCoefficients.toModuleCat l) hF

/-- The cohomology `Hʳ(Spec k̄, M)` of a Weil complex on `Spec k₀` vanishes outside a finite
interval of degrees, a Weil complex being bounded. -/
theorem WeilComplex.exists_subsingleton_cohomologyFrobeniusModule
    (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) :
    ∃ a b : ℤ, ∀ r, r < a ∨ b < r → Subsingleton (M.cohomologyFrobeniusModule r).carrier := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := M.property.1
  refine ⟨a, b, fun r hr ↦ WeilSheaf.subsingleton_globalSections_of_isZero ?_⟩
  refine Limits.IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ?_
  rcases hr with hr | hr
  · exact _root_.DerivedCategory.isZero_of_isGE (hX := ha) _ a r hr
  · exact _root_.DerivedCategory.isZero_of_isLE (hX := hb) _ b r hr

section UnitSection

open MonoidalCategory Functor.LaxMonoidal ProEtale

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- A unit `η : 𝟙 ⟶ R` of the underlying sheaf of a Weil sheaf `R` is *compatible with the Weil
structure* if `𝟙 ⟶ Fr^* 𝟙 ⟶ Fr^* R ⟶ R` is `η`, the first map being the unit of the lax
monoidal `Fr^* = (Fr⁻¹)_*`. -/
def WeilSheaf.IsUnitCompatible (R : WeilSheaf k₀ l Y) (η : 𝟙_ _ ⟶ R.obj.carrier.X) : Prop :=
  ε ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l] ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map η ≫
        R.obj.str.hom.hom = η

/-- A compatible unit transports along a morphism of Weil sheaves. -/
lemma WeilSheaf.IsUnitCompatible.comp {R R' : WeilSheaf k₀ l Y} {η : 𝟙_ _ ⟶ R.obj.carrier.X}
    (hη : R.IsUnitCompatible η) (f : R ⟶ R') : R'.IsUnitCompatible (η ≫ f.hom.hom.f.hom) := by
  have h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
      f.hom.hom.f.hom ≫ R'.obj.str.hom.hom = R.obj.str.hom.hom ≫ f.hom.hom.f.hom :=
    congrArg (fun φ ↦ φ.hom) f.hom.hom.h
  rw [IsUnitCompatible, Functor.map_comp, Category.assoc, h]
  simpa only [Category.assoc] using congrArg (· ≫ f.hom.hom.f.hom) hη

/-- The Frobenius of the global sections of a Weil sheaf fixes the global section of a unit
compatible with the Weil structure. -/
lemma WeilSheaf.IsUnitCompatible.globalSections_frobenius
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] {R : WeilSheaf k₀ l Y}
    {η : 𝟙_ _ ⟶ R.obj.carrier.X} (hη : R.IsUnitCompatible η) :
    R.globalSections.frobenius (globalSectionOfHom η) = globalSectionOfHom η := by
  have hε := NatTrans.IsMonoidal.unit (τ := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).hom)
  have key : ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (Sheaf.Γ _ _).map η ≫
      (globalSectionsLowerStarIso _
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app _ ≫
      (Sheaf.Γ _ _).map R.obj.str.hom.hom =
      ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (Sheaf.Γ _ _).map η := by
    have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.naturality η
    have hε' : ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (globalSectionsLowerStarIso _
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app (𝟙_ _) =
        ε (((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_] ⋙
          Sheaf.Γ _ (WeilCoefficients.{u} l)) := by
      rw [← hε, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    erw [reassoc_of% n, reassoc_of% hε']
    rw [Functor.LaxMonoidal.comp_ε, Category.assoc]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp]
    rw [Category.assoc] at *
    exact congrArg (fun m ↦ ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (Sheaf.Γ _ _).map m) hη
  exact congrArg (fun m ↦ m.hom (1 : ULift.{u + 1} (PadicAlgCl l))) key

/-- A compatible unit of a Weil sheaf pushes forward to a compatible unit of its direct image:
`𝟙 ⟶ φ̄_* 𝟙 ⟶ φ̄_* F`. -/
lemma WeilSheaf.IsUnitCompatible.lowerStar {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ Z) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l Y} {η : 𝟙_ _ ⟶ F.obj.carrier.X} (hη : F.IsUnitCompatible η) :
    ((WeilSheaf.lowerStar (k₀ := k₀) (l := l) φ).obj F).IsUnitCompatible
      (ε (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))_*[
          WeilCoefficients.{u} l] ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))_*[_].map η) := by
  -- Stay with the named exchange isomorphism `τ`: unfolding the Weil structure of the
  -- pushforward to module objects produces compositions whose implicit objects differ
  -- syntactically from those of the naturality squares, which is very slow for the kernel.
  set τ := lowerStarGeometricFiberMapCompFrobeniusIso (WeilCoefficients.{u} l) φ
    (comp_over φ (Spec (CommRingCat.of k₀)))
  rw [IsUnitCompatible, lowerStar_obj_obj_str_hom_hom]
  have hu := NatTrans.IsMonoidal.unit (τ := τ.hom)
  have nat := τ.hom.naturality η
  simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Category.assoc] at hu nat
  rw [Functor.map_comp, Category.assoc, reassoc_of% nat, reassoc_of% hu, ← Functor.map_comp,
    ← Functor.map_comp]
  exact congrArg (fun m ↦
    ε (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))_*[
        WeilCoefficients.{u} l] ≫
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map m) hη

end UnitSection

omit [Finite k₀] in
/-- The geometric fiber of a geometrically connected `k₀`-scheme is connected. -/
lemma connectedSpace_geometricFiber {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (Y ↘ Spec (CommRingCat.of k₀))] :
    ConnectedSpace (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  have : Subsingleton (Scheme.specAlgebraicClosure k₀).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of (AlgebraicClosure k₀))))
  have : Nonempty (Scheme.specAlgebraicClosure k₀).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of (AlgebraicClosure k₀))))
  GeometricallyConnected.connectedSpace_of_subsingleton
    (f := Limits.pullback.snd (Y ↘ Spec (CommRingCat.of k₀)) (Scheme.specAlgebraicClosure k₀).hom)

/-- The cohomology sheaf `𝓗⁰(Rφ_* F)` of the derived pushforward of a Weil sheaf is its
pushforward `φ_* F`, the pushforward being left exact. -/
noncomputable def WeilSheaf.homologySheafZeroDerivedLowerStarIso {Y Z : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ Z) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y) :
    (WeilComplex.homologySheaf 0).obj ((WeilComplex.derivedLowerStar φ).obj
      (toComplex.obj F)) ≅ (lowerStar φ).obj F :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.lowerStar k₀ l φ).homologyRightDerivedFunctorObjSingleFunctorIso
        F.obj 0 ≪≫ (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedZeroIsoSelf.app _)

/-- Transfer the finite etale bound to a complex with constant adic underlying object. -/
private theorem unitOrdinaryBound {Y : Scheme.{u}}
    [Y.Over (Spec (.of k₀))] [QuasiCompact (Y ↘ Spec (.of k₀))]
    [QuasiSeparated (Y ↘ Spec (.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (.of k₀))]
    (K : WeilComplex k₀ l Y) (e : ℕ)
    (he : topologicalKrullDim (Y ↘ Spec (.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (hK : WeilComplex.forget.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (Y ↘ Spec (.of k₀)).geometricFiber)) :
    (WeilComplex.forget.obj
      ((WeilComplex.derivedLowerStar (Y ↘ Spec (.of k₀))).obj K)).IsLE (2 * e : ℕ) := by
  let a := Y ↘ Spec (.of k₀)
  let f := Scheme.Hom.geometricFiberMap a (comp_over a (Spec (.of k₀)))
  let s := (Spec (.of k₀) ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  have : IsIso s := by
    change IsIso (pullback.snd (𝟙 (Spec (.of k₀))) _)
    infer_instance
  have hb := ProEtale.isLE_rightDerivedFunctor_adicLowerStar_unit_of_finite_bound s f
    (ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)) (2 * e)
    (fun Λ _ _ F ↦ by
      rw [DerivedCategory.isLE_iff]
      intro r hr
      have hvan := Etale.hasUniformDirectImageVanishingLE_two_mul Λ f
        a.geometricFiberToAlgebraicClosure s
        (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure a
          (comp_over a (Spec (.of k₀)))) e he F r hr
      let C := (DerivedCategory.Plus.singleFunctor _ 0).obj F
      let νX := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) a.geometricFiber
      let νY := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ)
        (Spec (.of k₀) ↘ Spec (.of k₀)).geometricFiber
      refine IsZero.of_iso (Functor.map_isZero νY hvan)
        ((DerivedCategory.homologyFunctor _ r).mapIso
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.mapIso
            ((νX.mapDerivedCategorySingleFunctor 0).app F).symm ≪≫
            ((ProEtale.rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).app
              C).symm) ≪≫
          ((νY.mapDerivedCategoryHomologyFunctorIso r).app _).symm))
  obtain ⟨E⟩ := WeilComplex.nonempty_derivedLowerStar_comp_forget_iso
    (k₀ := k₀) (l := l) a
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (E.app K ≪≫ (ProEtale.adicLowerStar l f).rightDerivedFunctor.mapIso hK).symm _

/-- Forgetting the Weil action identifies the constant complex with the adic unit. -/
private noncomputable def forgetConstantIso (Y : Scheme.{u}) [Y.Over (Spec (.of k₀))] :
    WeilComplex.forget.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ProEtale.AdicSheaf.unit l (Y ↘ Spec (.of k₀)).geometricFiber) :=
  ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app _

/-- Pullback preserves the constant underlying adic object. -/
private noncomputable def pullbackConstantIso {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k₀))] [Z.Over (Spec (.of k₀))]
    (g : Z ⟶ Y) [g.IsOver (Spec (.of k₀))] :
    WeilComplex.forget.obj ((WeilComplex.upperStar g).obj
      (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ProEtale.AdicSheaf.unit l (Z ↘ Spec (.of k₀)).geometricFiber) :=
  WeilComplex.forget.mapIso
    ((WeilSheaf.toComplexCompUpperStarIso g).app (WeilSheaf.adicConstant k₀ l Y) ≪≫
      WeilSheaf.toComplex.mapIso (WeilSheaf.upperStarAdicConstantIso g)) ≪≫
    forgetConstantIso Z

/-- A zero underlying homology object has zero geometric sections. -/
private theorem subsingleton_cohomology_of_forget_homology_isZero
    (K : WeilComplex k₀ l (Spec (.of k₀))) (r : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor _ r).obj (WeilComplex.forget.obj K))) :
    Subsingleton (K.cohomologyFrobeniusModule r).carrier := by
  apply WeilSheaf.subsingleton_globalSections_of_isZero
  rw [WeilSheaf.isZero_iff_isZero_carrier]
  exact hz.of_iso
    (((Endofunctor.IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso r).app K.obj)

/-- For a proper scheme the constant ordinary upper bound also bounds compact support. -/
private theorem properUnitVanishing {Y : Scheme.{u}}
    [Y.Over (Spec (.of k₀))] [IsProper (Y ↘ Spec (.of k₀))]
    (K : WeilComplex k₀ l Y) (e : ℕ)
    (he : topologicalKrullDim (Y ↘ Spec (.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (hK : WeilComplex.forget.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (Y ↘ Spec (.of k₀)).geometricFiber))
    (r : ℤ) (hr : 2 * (e : ℤ) < r) :
    Subsingleton (K.compactlySupportedCohomology r).carrier := by
  have := unitOrdinaryBound K e he hK
  apply subsingleton_cohomology_of_forget_homology_isZero
  exact (DerivedCategory.isZero_of_isLE _ (2 * e : ℕ) r hr).of_iso
    ((DerivedCategory.homologyFunctor _ r).mapIso
      (WeilComplex.forget.mapIso (WeilComplex.derivedLowerShriekObjIsoOfIsProper K)))

/-- Empty geometric fibers have zero compactly supported cohomology. -/
private theorem properEmptyVanishing {Y : Scheme.{u}}
    [Y.Over (Spec (.of k₀))] [IsProper (Y ↘ Spec (.of k₀))]
    [IsEmpty (Y ↘ Spec (.of k₀)).geometricFiber]
    (K : WeilComplex k₀ l Y) (r : ℤ) :
    Subsingleton (K.compactlySupportedCohomology r).carrier := by
  obtain ⟨E⟩ := WeilComplex.nonempty_derivedLowerStar_comp_forget_iso
    (k₀ := k₀) (l := l) (Y ↘ Spec (.of k₀))
  have hz : IsZero (WeilComplex.forget.obj
      ((WeilComplex.derivedLowerStar (Y ↘ Spec (.of k₀))).obj K)) :=
    (Functor.map_isZero _ (ProEtale.isZero_of_isEmpty l (WeilComplex.forget.obj K))).of_iso
      (E.app K)
  apply subsingleton_cohomology_of_forget_homology_isZero
  exact (Functor.map_isZero (DerivedCategory.homologyFunctor _ r) hz).of_iso
    ((DerivedCategory.homologyFunctor _ r).mapIso
      (WeilComplex.forget.mapIso (WeilComplex.derivedLowerShriekObjIsoOfIsProper K)))

section Separated

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

The compactly supported cohomology `Hʳ_c(X ⊗ k̄, K)` of a Weil complex vanishes outside a finite
interval of degrees `r`. -/
theorem exists_subsingleton_compactlySupportedCohomology (K : WeilComplex k₀ l X) :
    ∃ a b : ℤ, ∀ r, r < a ∨ b < r → Subsingleton (K.compactlySupportedCohomology r).carrier :=
  exists_subsingleton_cohomologyFrobeniusModule _

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

The ordinary cohomology `Hʳ(X ⊗ k̄, K)` of a Weil complex vanishes outside a finite interval of
degrees `r`. -/
theorem exists_subsingleton_cohomology (K : WeilComplex k₀ l X) :
    ∃ a b : ℤ, ∀ r, r < a ∨ b < r → Subsingleton (K.cohomology r).carrier :=
  exists_subsingleton_cohomologyFrobeniusModule _

end WeilComplex

namespace WeilSheaf

variable (k₀ l X)

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If the geometric fiber `X ⊗ k̄` has dimension at most `e`, the compactly supported cohomology
`Hʳ_c(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf vanishes for `r < 0` and for `r > 2e`. -/
theorem subsingleton_compactlySupportedCohomology_adicConstant (e : ℕ)
    (he : topologicalKrullDim (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (r : ℤ) (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l X).compactlySupportedCohomology r).carrier := by
  rcases hr with hr | hr
  · let F := adicConstant k₀ l X
    let a := X ↘ Spec (.of k₀)
    let c := HasCompactification.compactification a
      (hf := hasCompactification_of_over (k₀ := k₀) a)
    let := c.over (k₀ := k₀)
    let i := ProEtaleWeilSheaf.extensionByZero k₀ l c.i
    let g := ProEtaleWeilSheaf.lowerStar k₀ l c.g
    have : (g.rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (i.obj F.obj))).IsGE 0 :=
      g.isGE_rightDerivedFunctor_obj_singleFunctor _
    let E := g.rightDerivedFunctor.mapIso
      ((i.mapDerivedCategorySingleFunctor 0).app F.obj)
    apply subsingleton_globalSections_of_isZero
    apply (WeilComplex.isZero_homologySheaf_obj_iff r _).2
    exact (DerivedCategory.isZero_of_isGE
      (g.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj (i.obj F.obj)))
      0 r hr).of_iso ((DerivedCategory.homologyFunctor _ r).mapIso E)
  · classical
    obtain ⟨Y, p, j, hp, hj, hcomm, hdense, hdim⟩ :=
      exists_dense_compactification (X ↘ Spec (.of k₀))
    let : Y.Over (Spec (.of k₀)) := ⟨p⟩
    let : p.IsOver (Spec (.of k₀)) := ⟨Category.comp_id p⟩
    let : IsProper p := hp
    let : IsProper (Y ↘ Spec (.of k₀)) := hp
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
    have : IsNoetherian Y := ⟨⟩
    let : IsOpenImmersion j := hj
    let : j.IsOver (Spec (.of k₀)) := ⟨hcomm⟩
    let U := j.opensRange
    let Z := (Scheme.IdealSheafData.vanishingIdeal U.compl).subscheme
    let i : Z ⟶ Y := U.closedComplement
    let : Z.Over (Spec (.of k₀)) := ⟨i ≫ p⟩
    let : i.IsOver (Spec (.of k₀)) := ⟨rfl⟩
    have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion U.closedComplement)
    have : IsProper (Z ↘ Spec (.of k₀)) := inferInstanceAs (IsProper (i ≫ p))
    have hY : topologicalKrullDim (Y ↘ Spec (.of k₀)).geometricFiber ≤
        (e : WithBot ℕ∞) := by
      have hy := topologicalKrullDim_pullback_eq_of_field p (Scheme.specAlgebraicClosure k₀).hom
      have hx := topologicalKrullDim_pullback_eq_of_field
        (X ↘ Spec (.of k₀)) (Scheme.specAlgebraicClosure k₀).hom
      change topologicalKrullDim (pullback p (Scheme.specAlgebraicClosure k₀).hom : Scheme) ≤ _
      rw [hy, hdim]
      exact hx.symm.le.trans he
    let K := toComplex.obj (adicConstant k₀ l Y)
    have : QuasiCompact (j ≫ p) := hcomm.symm ▸ inferInstance
    have : QuasiCompact j := QuasiCompact.of_comp j p
    obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
      WeilComplex.exists_distTriang_derivedLowerShriek_openClosed j i
        (by
          change IsCompl (U : Set Y) (Set.range U.closedComplement.base)
          rw [U.range_closedComplement]
          exact isCompl_compl) p K
    let E₁ : T.obj₁ ≅ (WeilComplex.derivedLowerShriek k₀ l
        (X ↘ Spec (.of k₀))).obj ((WeilComplex.upperStar j).obj K) :=
      e₁ ≪≫ (WeilComplex.derivedLowerShriekIsoOfEq hcomm).app _
    let E₃ : T.obj₃ ≅ (WeilComplex.derivedLowerShriek k₀ l
        (Z ↘ Spec (.of k₀))).obj ((WeilComplex.upperStar i).obj K) :=
      e₃
    have h₂' := properUnitVanishing K e hY (forgetConstantIso Y) r hr
    have h₂ : Subsingleton (T.obj₂.cohomologyFrobeniusModule r).carrier :=
      ⟨fun x y ↦ (WeilComplex.cohomologyEquivOfIso e₂ r).toLinearEquiv.injective
        (h₂'.elim _ _)⟩
    have h₃' : Subsingleton
        (((WeilComplex.upperStar i).obj K).compactlySupportedCohomology (r - 1)).carrier := by
      by_cases hne : Nonempty (Z ↘ Spec (.of k₀)).geometricFiber
      · have : Nonempty Z := ⟨(Z ↘ Spec (.of k₀)).geometricFiberProj hne.some⟩
        have : Nonempty Y := ⟨i (Nonempty.some inferInstance)⟩
        have hzdim : topologicalKrullDim Z < (e : WithBot ℕ∞) := by
          rw [i.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range]
          change topologicalKrullDim (Set.range U.closedComplement.base) < _
          rw [U.range_closedComplement]
          have hlt := topologicalKrullDim_compl_lt_of_dense
            (topologicalKrullDim_ne_top_of_compactSpace p) hdense j.isOpenEmbedding.isOpen_range
          refine hlt.trans_le ?_
          rw [hdim]
          exact (topologicalKrullDim_pullback_eq_of_field
            (X ↘ Spec (.of k₀)) (Scheme.specAlgebraicClosure k₀).hom).symm.le.trans he
        obtain ⟨z, hz⟩ : ∃ z : ℕ, topologicalKrullDim Z = (z : WithBot ℕ∞) := by
          obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1
            (ne_bot_of_le_ne_bot (by simp) (topologicalKrullDim_nonneg (X := Z)))
          obtain ⟨z, rfl⟩ := ENat.ne_top_iff_exists.1
            (show d ≠ ⊤ by
              intro h
              subst d
              rw [← hd] at hzdim
              exact not_lt_of_ge le_top hzdim)
          exact ⟨z, hd.symm⟩
        have hze : z < e := by exact_mod_cast hz ▸ hzdim
        have hZdim : topologicalKrullDim
            (Z ↘ Spec (.of k₀)).geometricFiber ≤ (z : WithBot ℕ∞) := by
          change topologicalKrullDim
            (pullback (Z ↘ Spec (.of k₀)) (Scheme.specAlgebraicClosure k₀).hom : Scheme) ≤ _
          rw [topologicalKrullDim_pullback_eq_of_field, hz]
        apply properUnitVanishing ((WeilComplex.upperStar i).obj K) z hZdim
          (pullbackConstantIso i)
        omega
      · let := not_nonempty_iff.1 hne
        exact properEmptyVanishing ((WeilComplex.upperStar i).obj K) (r - 1)
    have h₃ : Subsingleton (T.obj₃.cohomologyFrobeniusModule (r - 1)).carrier :=
      ⟨fun x y ↦ (WeilComplex.cohomologyEquivOfIso E₃ (r - 1)).toLinearEquiv.injective
        (h₃'.elim _ _)⟩
    have hinj : Function.Injective (WeilComplex.cohomologyMap T.mor₁ r) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ :=
        (WeilComplex.exact_cohomologyδ_right T (r - 1) r (by omega) hT x).1 hx
      rw [h₃.elim y 0, map_zero]
    let eU : (WeilComplex.upperStar j).obj K ≅
        toComplex.obj (adicConstant k₀ l X) :=
      (toComplexCompUpperStarIso j).app (adicConstant k₀ l Y) ≪≫
        toComplex.mapIso (upperStarAdicConstantIso j)
    let EU := WeilComplex.cohomologyEquivOfIso
      (E₁ ≪≫ (WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (.of k₀))).mapIso eU) r
    have : Subsingleton (T.obj₁.cohomologyFrobeniusModule r).carrier :=
      ⟨fun x y ↦ hinj (h₂.elim _ _)⟩
    exact EU.toLinearEquiv.symm.injective.subsingleton

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is geometrically connected over `k₀`, then `H⁰(X ⊗ k̄, ℚ̄_ℓ)` is one-dimensional: the
constant sheaf is the lisse sheaf of the trivial representation of the fundamental group of the
connected scheme `X ⊗ k̄`, whose invariants are `ℚ̄_ℓ`. Neither properness nor smoothness is
needed. -/
theorem finrank_cohomology_zero_adicConstant
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    Module.finrank (PadicAlgCl l) ((adicConstant k₀ l X).cohomology 0).carrier =
      1 := by
  set a := X ↘ Spec (CommRingCat.of k₀)
  have := connectedSpace_geometricFiber (k₀ := k₀) (Y := X)
  let G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilCoefficients.{u} l :=
    ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
    Sheaf.Γ _ (WeilCoefficients.{u} l)
  -- `H⁰ = Γ(Spec k̄, 𝓗⁰(Ra_* ℚ̄_ℓ)) ≅ Γ(Spec k̄, a_* ℚ̄_ℓ) ≅ Γ(X̄, ℚ̄_ℓ)`
  let e : G.obj ((WeilComplex.homologySheaf 0).obj ((WeilComplex.derivedLowerStar a).obj
      (toComplex.obj (adicConstant k₀ l X)))) ≅
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj (ProEtale.adicConstantSheaf l a.geometricFiber) :=
    G.mapIso (homologySheafZeroDerivedLowerStarIso a _) ≪≫
      (ProEtale.globalSectionsLowerStarIso _ (Scheme.Hom.geometricFiberMap a (comp_over a _))).app
        (ProEtale.adicConstantSheaf l a.geometricFiber)
  exact (WeilCoefficients.linearEquivOfIso e).finrank_eq.trans
    (ProEtale.finrank_globalSections_adicConstantSheaf _)

open MonoidalCategory Functor.LaxMonoidal ProEtale in
/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is geometrically connected over `k₀`, the geometric Frobenius acts as the identity on
`H⁰(X ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ`: the Weil structure of the constant Weil sheaf is the identity on the
constants. -/
theorem frobenius_cohomology_zero_adicConstant
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    ((adicConstant k₀ l X).cohomology 0).frobenius = LinearEquiv.refl _ _ := by
  set a := X ↘ Spec (CommRingCat.of k₀)
  have := connectedSpace_geometricFiber (k₀ := k₀) (Y := X)
  set e₁ := homologySheafZeroDerivedLowerStarIso a (adicConstant k₀ l X)
  set a' := Scheme.Hom.geometricFiberMap a (comp_over a (Spec (CommRingCat.of k₀)))
  -- the unit section `1` of `H⁰`, image of the unit of `ℚ̄_ℓ`
  have hX : (adicConstant k₀ l X).IsUnitCompatible
      (MonObj.one (X := ProEtale.adicConstantSheaf l a.geometricFiber)) :=
    adicConstant_unit_str
  have hW := (hX.lowerStar a).comp e₁.inv
  set η := ((ε (a')_*[WeilCoefficients.{u} l] ≫ (a')_*[_].map
    (MonObj.one (X := ProEtale.adicConstantSheaf l a.geometricFiber))) ≫ e₁.inv.hom.hom.f.hom)
  have hfix := hW.globalSections_frobenius
  -- it is nonzero: it maps to the global section `1` of `ℚ̄_ℓ` on `X̄`
  let v : ((adicConstant k₀ l X).cohomology 0).carrier := globalSectionOfHom η
  have hne : v ≠ 0 := by
    intro h
    have h' := congrArg (fun s ↦
      ((ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l) a').hom.app _).hom
        (((Sheaf.Γ _ _).map e₁.symm.inv.hom.hom.f.hom).hom s)) h
    simp only [map_zero] at h'
    have hinv : e₁.inv.hom.hom.f.hom ≫ e₁.symm.inv.hom.hom.f.hom = 𝟙 _ := by
      exact congrArg (fun m ↦ m.hom.hom.f.hom) e₁.inv_hom_id
    refine oneGlobalSection_ne_zero (l := l) a.geometricFiber ?_
    rw [← h']
    change _ = ((globalSectionsLowerStarIso (WeilCoefficients.{u} l) a').hom.app _).hom
      (((Sheaf.Γ _ (WeilCoefficients.{u} l)).map e₁.symm.inv.hom.hom.f.hom).hom
        (globalSectionOfHom η))
    rw [← globalSectionOfHom_comp, Category.assoc, hinv]
    erw [Category.comp_id, globalSectionsLowerStarIso_hom_app_globalSectionOfHom]
    rfl
  have h1 : Module.finrank (PadicAlgCl l) ((adicConstant k₀ l X).cohomology 0).carrier = 1 :=
    finrank_cohomology_zero_adicConstant k₀ l X
  refine LinearEquiv.ext fun x ↦ ?_
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 h1 x
  rw [map_smul]
  exact congrArg (c • ·) hfix

end WeilSheaf

end Separated

section Proper

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is proper over `k₀`, the compactly supported and the ordinary cohomology
`Hʳ_c(X ⊗ k̄, K)` and `Hʳ(X ⊗ k̄, K)` are isomorphic as Frobenius modules.

The isomorphism is induced by `Ra_! ≅ Ra_*` for the proper `a`
(`AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoOfIsProper`): for the chosen
compactification `X ⟶[i] Z ⟶[g] Spec k₀` the open immersion `i` is also closed, so that
`Rg_*(i_! K) ≅ Rg_*(i_* K) ≅ Ra_* K`. -/
theorem nonempty_equiv_compactlySupportedCohomology_cohomology
    (K : WeilComplex k₀ l X) (r : ℤ) :
    Nonempty ((K.compactlySupportedCohomology r).Equiv (K.cohomology r)) :=
  ⟨WeilSheaf.globalSectionsEquivOfIso
    ((homologySheaf r).mapIso (derivedLowerShriekObjIsoOfIsProper K))⟩

end WeilComplex

namespace WeilSheaf

variable (k₀ l X)

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is proper over `k₀` and the geometric fiber `X ⊗ k̄` has dimension at most `e`, the
cohomology `Hʳ(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf vanishes for `r < 0` and for `r > 2e`.
For `X` smooth of pure dimension `d` the same vanishing, without properness, is
`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant`. -/
theorem subsingleton_cohomology_adicConstant_of_isProper (e : ℕ)
    (he : topologicalKrullDim (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (r : ℤ) (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l X).cohomology r).carrier := by
  obtain ⟨E⟩ := WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology
    (toComplex.obj (adicConstant k₀ l X)) r
  have : Subsingleton ((toComplex.obj (adicConstant k₀ l X)).compactlySupportedCohomology
      r).carrier := subsingleton_compactlySupportedCohomology_adicConstant k₀ l X e he r hr
  exact E.toLinearEquiv.symm.injective.subsingleton

end WeilSheaf

end Proper

end AlgebraicGeometry

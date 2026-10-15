/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Sheaf.RingTheory.FiniteWContractible

/-!
# Vanishing of direct images of Weil sheaves

The derived direct image `Rf₀*G` and the direct image with compact support `Rf₀!G` of a Weil
sheaf are concentrated in degrees `≥ 0`. For a finite morphism `p` the higher direct images
`Rʳp₀*G` vanish for `r > 0`, and so, by Zariski's main theorem, do the higher direct images with
compact support `Rʳf₀!G` along a separated quasi-finite morphism `f`. These statements do not
involve weights; they are used both by the weight reductions of
`WeilConjectures.DeligneLaumon.Reduction.FormalSteps` and by the computation of the local
Frobenius of quasi-finite direct images in
`WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg` and
  `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg`: vanishing in
  negative degrees.
- `AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`: blueprint
  `lemma-weil-pbc-finite-direct-image-exact`.
- `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite`: blueprint
  `sk-l-dl-general-quasifinite`, `lem-zl-quasi-finite`, part 1.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private def wContractibleAffine {Y : Scheme.{u}} (W : Y.ProEt) : Prop :=
  ∃ (R : CommRingCat.{u}) (_ : IsWContractibleRing R), Nonempty (W.left ≅ Spec R)

private theorem exists_wContractibleAffine_cover {B : Scheme.{u}} (V : B.ProEt) :
    ∃ (ι : Type u) (W : ι → B.ProEt) (f : ∀ i, W i ⟶ V),
      (∀ i, wContractibleAffine (W i)) ∧
      Sieve.ofArrows W f ∈ Scheme.ProEt.topology B V := by
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let U (x : 𝒜.I₀) := Scheme.ProEt.ofOpenImmersion V (𝒜.f x)
  let W (x : 𝒜.I₀) : B.ProEt := Scheme.ProEt.mk (Spec.map (φ x) ≫ (U x).hom)
  let w (x : 𝒜.I₀) : W x ⟶ U x := MorphismProperty.Over.homMk (Spec.map (φ x)) rfl
  refine ⟨𝒜.I₀, W, fun x ↦ w x ≫ Scheme.ProEt.ofOpenImmersionHom V (𝒜.f x),
    fun x ↦ ⟨CommRingCat.of (S x), hw x, ⟨Iso.refl _⟩⟩, ?_⟩
  · have hU : Sieve.ofArrows U (fun x ↦ Scheme.ProEt.ofOpenImmersionHom V (𝒜.f x)) ∈
        Scheme.ProEt.topology B V :=
      Scheme.ProEt.mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
        (fun x ↦ Sieve.ofArrows_mk _ _ x)
    refine (Scheme.ProEt.topology B).transitive hU _ fun V₁ g hg ↦ ?_
    obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hg
    rw [Sieve.pullback_comp]
    refine (Scheme.ProEt.topology B).pullback_stable c
      ((Scheme.ProEt.topology B).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x)) ?_))
    · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
      rw [Sieve.pullback_apply, Category.assoc]
      exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ x) d
    · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
        inferInstance

private theorem wContractibleAffine_isWeaklyContractible {Y : Scheme.{u}} (W : Y.ProEt)
    (hW : wContractibleAffine W) :
    (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} W := by
  obtain ⟨R, hR, ⟨e⟩⟩ := hW
  exact Scheme.ProEt.isWeaklyContractible_of_iso e

private theorem wContractibleAffine_pullback {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsFinite p] [LocallyOfFinitePresentation p] (W : Y.ProEt)
    (hW : wContractibleAffine W) :
    wContractibleAffine ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj W) := by
  obtain ⟨R, hR, ⟨e⟩⟩ := hW
  let Z := ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj W).left
  let q : Z ⟶ Spec R := pullback.fst W.hom p ≫ e.hom
  have : IsFinite q := inferInstanceAs (IsFinite (pullback.fst W.hom p ≫ e.hom))
  have : LocallyOfFinitePresentation q :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst W.hom p ≫ e.hom))
  have : IsAffine Z := isAffine_of_isAffineHom q
  let φ : R ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ q)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ q := Spec.map_preimage _
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hfp : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  let : Algebra R Γ(Z, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff φ).mp hfin)
  have : Algebra.FinitePresentation R Γ(Z, ⊤) :=
    RingHom.finitePresentation_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp hfp)
  exact ⟨Γ(Z, ⊤), isWContractibleRing_of_finite_finitePresentation R Γ(Z, ⊤),
    ⟨Z.isoSpec⟩⟩

private theorem preservesFiniteColimits_proEtaleLowerStar_of_isFinite
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [LocallyOfFinitePresentation p]
    (R : Type (u + 1)) [CommRing R] :
    PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} R) p) := by
  have h : (ProEtale.lowerStar (ModuleCat.{u + 1} R) p).PreservesHomology :=
    Functor.preservesHomology_of_map_exact _ (fun S hS ↦ by
      apply (GrothendieckTopology.exact_iff_of_forall_exists
        wContractibleAffine exists_wContractibleAffine_cover
        wContractibleAffine_isWeaklyContractible _).mpr
      intro W hW
      have hB := wContractibleAffine_pullback p W hW
      exact (GrothendieckTopology.exact_iff_of_forall_exists
        wContractibleAffine exists_wContractibleAffine_cover
        wContractibleAffine_isWeaklyContractible S).mp hS _ hB)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section UpperStar

variable {W X : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (h : W ⟶ X) [h.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the sheaf, placed in
degree zero. -/
noncomputable def WeilComplex.upperStarToComplexIso (G : WeilSheaf k₀ l X) :
    (WeilComplex.upperStar h).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.upperStar h).obj G) :=
  ObjectProperty.isoMk _
    (((ProEtaleWeilSheaf.upperStar k₀ l h).mapDerivedCategorySingleFunctor 0).app G.obj)

end UpperStar

/-- The derived direct image `Rf₀*G` of a Weil sheaf is concentrated in degrees `≥ 0`: it is
computed by `f₀*` applied to an injective resolution of `G`. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {n : ℤ} (hn : n < 0) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerStar f).obj (WeilSheaf.toComplex.obj G))) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  have : ((WeilComplex.derivedLowerStar f).obj (WeilSheaf.toComplex.obj G)).obj.IsGE 0 :=
    (ProEtaleWeilSheaf.lowerStar k₀ l f).isGE_rightDerivedFunctor_obj_singleFunctor G.obj
  exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn

section LowerShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over in
/-- The direct image with compact support `Rf₀!G` of a Weil sheaf is concentrated in degrees
`≥ 0`: it is `Rḡ_*` applied to the extension by zero of `G`, a sheaf. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg (G : WeilSheaf k₀ l X) {n : ℤ}
    (hn : n < 0) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj G))) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have e := (Functor.mapDerivedCategorySingleFunctor
    (ProEtaleWeilSheaf.extensionByZero k₀ l c.i) 0).app G.obj
  have h := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).isGE_rightDerivedFunctor_obj_singleFunctor
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj G.obj)
  have : _root_.DerivedCategory.TStructure.t.IsGE
      ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i ⋙ _root_.DerivedCategory.singleFunctor _ 0).obj
          G.obj)) 0 := h
  have h' := _root_.DerivedCategory.TStructure.t.isGE_of_iso
    ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso e.symm) 0
  have h'' : ((WeilComplex.derivedLowerShriek k₀ l f).obj
      (WeilSheaf.toComplex.obj G)).obj.IsGE 0 := h'
  exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn

end LowerShriek

/-- **Finite direct images are exact** (blueprint: `lemma-weil-pbc-finite-direct-image-exact`,
with the passage to `ℚ̄_ℓ`-coefficients of `def-weil-pbc-qbar-category`): for a finite morphism
`p : T ⟶ Y` of `k₀`-schemes, the higher direct images `Rʳp₀*G` of a Weil sheaf vanish for
`r > 0`. -/
theorem WeilSheaf.isZero_higherLowerStar_of_isFinite {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (p : T ⟶ Y)
    [IsFinite p] [p.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l T) (r : ℕ) (hr : 0 < r) :
    IsZero ((WeilSheaf.higherLowerStar p r).obj G) := by
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : LocallyOfFinitePresentation p :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let q := Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀)))
  have : IsFinite q :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsFinite) p _ inferInstance
  have : LocallyOfFinitePresentation q :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
      (P := @LocallyOfFinitePresentation) p _ inferInstance
  have := preservesFiniteColimits_proEtaleLowerStar_of_isFinite q
    (ULift.{u + 1} (PadicAlgCl l))
  have : PreservesFiniteColimits (ProEtale.adicLowerStar l q ⋙ ProEtale.AdicSheaf.forget _) :=
    inferInstanceAs (PreservesFiniteColimits
      (ProEtale.AdicSheaf.forget _ ⋙ ProEtale.lowerStar (WeilCoefficients.{u} l) q))
  have : PreservesFiniteColimits (ProEtale.adicLowerStar l q) :=
    preservesFiniteColimits_of_reflects_of_preserves _ (ProEtale.AdicSheaf.forget _)
  have : PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l p) :=
    Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso _
  change IsZero ((WeilComplex.homologySheaf (r : ℤ)).obj
    ((WeilComplex.derivedLowerStar p).obj (WeilSheaf.toComplex.obj G)))
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  let e := (ProEtaleWeilSheaf.lowerStar k₀ l p).singleFunctorCompRightDerivedFunctorIso.app G.obj
  have h : IsZero ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l p).obj G.obj))) :=
    _root_.DerivedCategory.isZero_of_isLE _ 0 (r : ℤ) (by exact_mod_cast hr)
  exact h.of_iso ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).mapIso e)

section QuasiFinite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the higher direct images
with compact support `Rʳf₀!` vanish for `r > 0` (blueprint: `sk-l-dl-general-quasifinite`,
`lem-zl-quasi-finite`, part 1).

Zariski's main theorem factors `f` as a quasi-compact open immersion `j : X ⟶ T` followed by a
finite morphism `p : T ⟶ Y`, so that `Rf₀! ≅ Rp₀! ∘ Rj₀! ≅ Rp₀* ∘ j₀!`; the extension by zero
`j₀!` is exact and so is the finite direct image `p₀*`
(`AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`). -/
theorem isZero_higherLowerShriek_of_quasiFinite (r : ℕ) (hr : 0 < r) (F : WeilSheaf k₀ l X) :
    IsZero ((WeilSheaf.higherLowerShriek k₀ l f r).obj F) := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  obtain ⟨T, j, p, hj, hjc, hp, hjp⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  let : T.Over (Spec (CommRingCat.of k₀)) := ⟨p ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : p.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change j ≫ p ≫ Y ↘ Spec (CommRingCat.of k₀) = _
    rw [← Category.assoc, hjp, comp_over]⟩
  have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ _))
  have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := inferInstanceAs (QuasiCompact (p ≫ _))
  have : QuasiSeparated (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (p ≫ _))
  subst hjp
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j p
  obtain ⟨e'⟩ := WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion j F
  exact (WeilSheaf.isZero_higherLowerStar_of_isFinite p _ r hr).of_iso
    ((WeilComplex.homologySheaf r).mapIso (e.app (WeilSheaf.toComplex.obj F) ≪≫
      (WeilComplex.derivedLowerShriek k₀ l p).mapIso e' ≪≫
      WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar p _))

end QuasiFinite

end AlgebraicGeometry

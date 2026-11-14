/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection

/-! # Transitivity for the specified internal coefficient extension
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Transitivity of open-then-closed extension with the actual internal module coefficients.

Proof in words. Identify internal modules with sectionwise modules over their pulled
coefficient ring sheaves, using the canonical module equivalence. Its inverse-image
comparison gives the coefficient identifications along a, b, and their composite.
Apply normalized locally closed module-extension coherence to these coefficient
immersions. For each arrow, the open-then-closed factorization comparison identifies
that extension with open extension into its scheme-theoretic closure followed by closed
direct image. Transport the normalized composition isomorphism through these three
factorization comparisons and the module equivalences. The resulting component has
exactly the two displayed closure-extension objects. All source schemes are Noetherian,
so the opens in these factorizations are quasi-compact. Empty sources and zero modules
are included because the comparisons restrict to the identity on zero objects. -/
theorem locallyClosedCoefficientExtension_composition
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {T S X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian X]
    (a : S ⟶ X) [IsImmersion a] (b : T ⟶ S) [IsImmersion b]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj B T)) :
    Nonempty ((coefficientHeartLocallyClosedExtension B a inferInstance).obj
        ((coefficientHeartLocallyClosedExtension B b inferInstance).obj M) ≅
      (coefficientHeartLocallyClosedExtension B (b ≫ a) inferInstance).obj M) := by
  classical
  open CondensedRing in
  let closureFactorization {Y Z : Scheme.{u}} [IsNoetherian Z]
      (f : Y ⟶ Z) [IsImmersion f] : GeneratorFactorization f := by
    have : TopologicalSpace.NoetherianSpace Y := f.isEmbedding.isInducing.noetherianSpace
    exact .inr ⟨f.image, f.toImage, f.imageι, f.toImage_imageι,
      inferInstance, inferInstance⟩
  let A := closureFactorization a
  let D := closureFactorization b
  let C := closureFactorization (b ≫ a)
  have hA : CondensedRing.generatorExtension B A =
      coefficientHeartLocallyClosedExtension B a inferInstance := rfl
  have hD : CondensedRing.generatorExtension B D =
      coefficientHeartLocallyClosedExtension B b inferInstance := rfl
  have hC : CondensedRing.generatorExtension B C =
      coefficientHeartLocallyClosedExtension B (b ≫ a) inferInstance := rfl
  rw [← hA, ← hD, ← hC]
  let P := (CondensedRing.generatorExtension B D).obj M
  let N := (CondensedRing.generatorExtension B A).obj P
  have hrA := CondensedRing.generatorRestriction_isIso B A
  have hrD := CondensedRing.generatorRestriction_isIso B D
  let eA : (CondensedRing.upperStar B a).obj N ≅ P :=
    (asIso (CondensedRing.generatorRestriction B A)).app P
  let eD : (CondensedRing.upperStar B b).obj P ≅ M :=
    (asIso (CondensedRing.generatorRestriction B D)).app M
  have hs : CondensedRing.universallySupported B (b ≫ a) N := by
    intro Y _ _ g hg
    let d := pullback.fst g a
    let t := pullback.snd g a
    obtain ⟨hW, hWc⟩ := CondensedRing.immersion_noetherian d
    let := hW
    let := hWc
    apply CondensedRing.supported_zero B d
    · exact CondensedRing.supported_pullback B a g N
        (fun k hk ↦ CondensedRing.generatorExtension_support B A k hk P)
    · have ht : Disjoint (Set.range t) (Set.range b) := by
        rw [Set.disjoint_left]
        rintro x ⟨y, rfl⟩ ⟨z, hz⟩
        apply Set.disjoint_left.mp hg ⟨d y, rfl⟩
        refine ⟨z, ?_⟩
        have hw : d ≫ g = t ≫ a := pullback.condition
        exact (congrArg a hz).trans
          (congrArg (fun f : pullback g a ⟶ X ↦ f y) hw).symm
      have hz := CondensedRing.generatorExtension_support B D t ht M
      let e : (CondensedRing.upperStar B d).obj
          ((CondensedRing.upperStar B g).obj N) ≅
          (CondensedRing.upperStar B t).obj P :=
        ((CondensedRing.upperStarComp B d g).symm ≪≫
          CondensedRing.upperStarCongr B (pullback.condition (f := g) (g := a)) ≪≫
          CondensedRing.upperStarComp B t a).app N ≪≫
          (CondensedRing.upperStar B t).mapIso eA
      exact hz.of_iso e
  obtain ⟨e⟩ := CondensedRing.generatorExtension_reconstruct B C N hs
  exact ⟨e ≪≫ (CondensedRing.generatorExtension B C).mapIso
    ((CondensedRing.upperStarComp B b a).app N ≪≫
      (CondensedRing.upperStar B b).mapIso eA ≪≫ eD)⟩

end AlgebraicGeometry.ProEtale

module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Agreement with bounded derived global sections

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-rgamma-unbounded-bounded.md (blueprint: lem-kun-rgamma-unbounded-bounded).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Agreement of bounded-below and unbounded derived global sections, including the
augmentation-compatible comparison, its uniqueness up to homotopy and its naturality.
Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lem-kun-rgamma-unbounded-bounded; Stacks Project, Tags 079P and 070I
(blueprint: lem-kun-rgamma-unbounded-bounded).

Proof: choose the two K-injective resolutions using
`prop-weil-pbc-kinjective-resolutions-exist`. Their augmentations become invertible under
localization. Apply `lem-weil-pbc-kinjective-hom-derived` with target `J` to lift
`Q(b) ∘ Q(a)⁻¹` uniquely to a homotopy class `u`. The same argument with target `I`
lifts the inverse; injectivity implies the two inverse homotopy equations and `a ≫ u ~ b`.
Global sections is additive and preserves the homotopy equations termwise, so its image
of `u` is invertible in `D(Λ)`. The K-injective computation of derived global sections
identifies the source and target with the two recipes. A second compatible comparison
has the same image under localization, hence is homotopic and has the same image after
sections. For any derived morphism `f`, lift its conjugates by the augmentations into
`I'` and `J'`. The two composites into `J'` have equal localizations; injectivity makes
them homotopic, proving the displayed naturality square after sections and localization.
Identity and composition of the lifts follow by the same injectivity argument. -/
theorem rGamma_unbounded_bounded (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ DerivedCategory.Plus.ι.obj K)
    (a : C ⟶ I) (b : C ⟶ J)
    (ha : CochainComplex.IsKInjectiveResolution T Λ a)
    (hb : CochainComplex.IsKInjectiveResolution T Λ b) :
    ∃ u : I ⟶ J,
      Nonempty (Homotopy (a ≫ u) b) ∧
      (∀ u' : I ⟶ J, Nonempty (Homotopy (a ≫ u') b) → Nonempty (Homotopy u u')) ∧
      IsIso (DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u)) ∧
      (∃ eI :
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj
          (DerivedCategory.Plus.ι.obj K) ≅ DerivedCategory.Q.obj
          (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I),
        ∃ eJ :
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj
            (DerivedCategory.Plus.ι.obj K) ≅ DerivedCategory.Q.obj
          (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J),
          eI.hom ≫ DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u) = eJ.hom) ∧
      (∀ (C' I' J' : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
        (K' : DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (eC' : DerivedCategory.Q.obj C' ≅ DerivedCategory.Plus.ι.obj K')
        (a' : C' ⟶ I') (b' : C' ⟶ J'),
        CochainComplex.IsKInjectiveResolution T Λ a' →
        CochainComplex.IsKInjectiveResolution T Λ b' →
        ∀ (u' : I' ⟶ J'), Nonempty (Homotopy (a' ≫ u') b') →
        ∀ f : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj C',
          (∃ p : I ⟶ I',
            DerivedCategory.Q.map a ≫ DerivedCategory.Q.map p =
              f ≫ DerivedCategory.Q.map a') ∧
          (∃ q : J ⟶ J',
            DerivedCategory.Q.map b ≫ DerivedCategory.Q.map q =
              f ≫ DerivedCategory.Q.map b') ∧
          (∀ (p : I ⟶ I') (q : J ⟶ J'),
            DerivedCategory.Q.map a ≫ DerivedCategory.Q.map p =
              f ≫ DerivedCategory.Q.map a' →
            DerivedCategory.Q.map b ≫ DerivedCategory.Q.map q =
              f ≫ DerivedCategory.Q.map b' →
            DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u) ≫ DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map q) = DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map p) ≫ DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u'))) := by
  sorry

end AlgebraicGeometry.Etale

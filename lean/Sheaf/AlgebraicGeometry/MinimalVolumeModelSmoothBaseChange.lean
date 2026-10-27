module

public import Sheaf.AlgebraicGeometry.TraitVolumeModels
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Minimal volume models and smooth local base change

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 4.3 Proposition 2 and Lemma 3,
printed pp.105--106 (blueprint: lem-sfb-minimal-volume-model-smooth-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
open TraitVolume

/-- Minimal volume models have finitely many nonempty birational classes, and every
representative list, including any permitted shrinking, gives all minimal models after
smooth trait-local base change.

Source: BLR 4.3 Proposition 2 and Lemma 3, pp.105--106
(blueprint: lem-sfb-minimal-volume-model-smooth-base-change).

Proof: choose a finite nonempty weak Néron family, refined to irreducible special fibres.
Take the minimum of its differential orders. The weak rational mapping property extends
any model's generic identity into one member of this family. Volume order comparison
bounds that model's order below by the chosen minimum. Equality gives an open immersion
on a fibrewise dense domain, hence a birational identity and finitely many classes.
Over the local ring of a smooth special generic point the uniformizer is still π and
the weak family remains weak Néron. Each special component upstairs dominates the
special generic point downstairs, since projection after field extension is open.
Differential base change and its exterior power identify the normalized local generators,
so all component opens preserve their orders. Repeating the minimum and equal-order
arguments proves minimality and coverage over the new DVR. Base changing the original
birational identities carries this coverage to any chosen representative list. Finally,
removing a closed nowhere dense subset of the special fibre preserves its generic
local ring; after base change the remaining open is dense in every component, so neither
its order nor its birational class changes. -/
theorem minimalVolumeModel_smooth_baseChange
    (R E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field E] [Algebra R E] [IsFractionRing R E]
    (π : R) (hπ : Irreducible π)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R))
    (hs : (Scheme.SpecToEquivOfField Ω (Spec (.of R)) s).1 = IsLocalRing.closedPoint R)
    (F : Type u) [Field F] [Algebra (Scheme.strictHenselizationRing s) F]
    [IsFractionRing (Scheme.strictHenselizationRing s) F]
    (ι : E →+* F)
    (hι : ∀ a : R, ι (algebraMap R E a) =
      algebraMap (Scheme.strictHenselizationRing s) F (strictMap s a))
    (G : Over (Spec (.of E))) [GrpObj G]
    (d : ℕ) [SmoothOfRelativeDimension d G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsClosedImmersion (pullback.diagonal G.hom)]
    (ω : Γ(TopForms G.hom d, ⊤))
    (hω : ∀ x : G.left, Scheme.Modules.GeneratesAt ω x)
    (hleft : IsLeftInvariant G d ω)
    (hbounded : IsBounded ι (algebraMap (Scheme.strictHenselizationRing s) F)
      (strictMap s π) G) :
    ∃ n₀ : ℤ, IsMinimum π G d ω n₀ ∧
      (∃ (r : ℕ) (M : Fin r → Model
          (Spec.map (CommRingCat.ofHom (algebraMap R E))) G),
        Representatives π G d ω n₀ r M) ∧
      ∀ (r : ℕ) (M : Fin r → Model
          (Spec.map (CommRingCat.ofHom (algebraMap R E))) G),
        Representatives π G d ω n₀ r M → SmoothBaseChange π G d ω n₀ r M := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativePureIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.CoefficientPropertiesIso

/-!
# Transport of native mixed filtrations by exact functors

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5.
(blueprint: lem-zl-native-mixed-exact-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2

/-- An exact functor that preserves constructible carriers and pure weights sends
native mixed filtrations to mixed filtrations with the same weight bound.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-native-mixed-exact-transport).
Proof: apply the functor to every object and arrow of the given finite chain.
The constructibility assumption supplies constructible terms. Finite-limit
preservation preserves the zero initial term and monomorphisms; the image of the
endpoint isomorphism gives the last term. The canonical cokernel comparison of
finite-colimit preservation identifies every new quotient with the image of the
old quotient. The latter has the same pure weight, and purity is invariant under
this Weil isomorphism. The real inequalities on the weights are unchanged. This
argument includes length zero and repeated terms. -/
theorem mixed_map (D E : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (Y₀ : Over (Spec (.of E.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (F : WeilModule D l X₀ ⥤ WeilModule E l Y₀)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (iota : PadicAlgCl l →+* ℂ)
    (hconstructible : ∀ A, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left A.carrier →
        IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (E.geometricFiber Y₀).left (F.obj A).carrier)
    (hpure : ∀ A v, Pure D l X₀ A iota v → Pure E l Y₀ (F.obj A) iota v)
    (M : WeilModule D l X₀) (w : ℝ) (hM : Mixed D l X₀ M iota w) :
    Mixed E l Y₀ (F.obj M) iota w := by
  obtain ⟨n, G, φ, hc, hz, ⟨last⟩, hm, hp⟩ := hM
  have hmono (i : Fin n) : Mono (φ i) := hm i
  refine ⟨n, (fun i ↦ F.obj (G i)), (fun i ↦ F.map (φ i)),
    (fun i ↦ hconstructible _ (hc i)), F.map_isZero hz, ⟨F.mapIso last⟩,
    (fun i ↦ inferInstance), ?_⟩
  intro i
  obtain ⟨v, hv, hquot⟩ := hp i
  refine ⟨v, hv, ?_⟩
  exact (pure_iso_iff E l Y₀ (PreservesCokernel.iso F (φ i)) iota v).mp
    (hpure _ v hquot)

/-- The endpoint isomorphism in a native mixed filtration may be changed by a
Weil isomorphism.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-native-mixed-exact-transport).
Proof: keep every term, arrow and pure quotient, and compose the endpoint
isomorphism with the given isomorphism. Its inverse gives the converse. -/
theorem mixed_iso_iff (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {M N : WeilModule D l X₀} (e : M ≅ N) (iota : PadicAlgCl l →+* ℂ) (w : ℝ) :
    Mixed D l X₀ M iota w ↔ Mixed D l X₀ N iota w := by
  suffices h : ∀ {A B : WeilModule D l X₀}, (A ≅ B) →
      Mixed D l X₀ A iota w → Mixed D l X₀ B iota w from ⟨h e, h e.symm⟩
  intro A B e ⟨n, G, φ, hc, hz, ⟨last⟩, hm, hp⟩
  exact ⟨n, G, φ, hc, hz, ⟨last ≪≫ e⟩, hm, hp⟩

/-- An equivalence preserving and reflecting constructibility and punctual pure
weights preserves and reflects mixed filtrations. Only forward-object properties
are required; the counit supplies those for the inverse.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-native-mixed-exact-transport).
Proof: apply mixed_map for the forward direction. For an inverse-image object,
the counit identifies its forward image with the original object. Isomorphism
invariance of constructibility and purity therefore supplies both inverse-image
hypotheses of mixed_map. Map a mixed filtration back, then use the unit to identify
the resulting endpoint with the original Weil object. -/
theorem mixed_iff_of_equivalence (D E : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (Y₀ : Over (Spec (.of E.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (F : WeilModule D l X₀ ≌ WeilModule E l Y₀) (iota : PadicAlgCl l →+* ℂ)
    (hconstructible : ∀ A, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left A.carrier ↔
        IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (E.geometricFiber Y₀).left (F.functor.obj A).carrier)
    (hpure : ∀ A v, Pure D l X₀ A iota v ↔ Pure E l Y₀ (F.functor.obj A) iota v)
    (M : WeilModule D l X₀) (w : ℝ) :
    Mixed D l X₀ M iota w ↔ Mixed E l Y₀ (F.functor.obj M) iota w := by
  constructor
  · exact mixed_map D E l X₀ Y₀ F.functor iota
      (fun A ↦ (hconstructible A).mp) (fun A v ↦ (hpure A v).mp) M w
  · intro hM
    have hc (B : WeilModule E l Y₀)
        (hB : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (E.geometricFiber Y₀).left B.carrier) :
        IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (D.geometricFiber X₀).left (F.inverse.obj B).carrier := by
      apply (hconstructible _).mpr
      exact (constantModelConstructible_iso_iff (Profinite.padicAlgClRingObj l)
        ((CategoryTheory.Endofunctor.IsoAlgebra.forget _).mapIso
          (F.counitIso.app B))).mpr hB
    have hp (B : WeilModule E l Y₀) (v : ℝ) (hB : Pure E l Y₀ B iota v) :
        Pure D l X₀ (F.inverse.obj B) iota v := by
      exact (hpure _ v).mpr ((pure_iso_iff E l Y₀ (F.counitIso.app B) iota v).mpr hB)
    exact (mixed_iso_iff D l X₀ (F.unitIso.app M) iota w).mpr
      (mixed_map E D l Y₀ X₀ F.inverse iota hc hp (F.functor.obj M) w hM)

end WeilConjectures.NativeL2

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.AlgebraicGeometry.DualizingComplexCtf
import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
import WeilConjectures.SixFunctors.CondensedCompactSupportComposition
import Mathlib.Algebra.CharP.CharAndCard

/-! # Verdier duality preserves constructible finite-Tor complexes

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-pd-preservation/_section.md and sk-lem-pd-preservation.proof.md
(blueprint: sk-lem-pd-preservation).

The exceptional inverse image is presented by its adjunction to the actual
compactification lower shriek on the localizing closures. The conclusion gives a
restriction of the specified ambient relative internal-Hom functor, including its
morphism map. No completion is imposed on the ambient derived module category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For every admissible condensed coefficient ring, the Verdier dual relative to
`omega = a_X^! Lambda_s` restricts to the full bounded constructible finite-Tor
subcategory. The equality after the full inclusion specifies both its object and
morphism maps as those of the ambient relative internal Hom.

Here `c` is any compactification of the structure morphism, `h` certifies that its
actual lower shriek maps the localizing closures into one another, and `G` is any
right adjoint with the displayed adjunction. These are presentations of `a_X^!`,
not a preservation assumption about it. The existence of these presentations is
`sk-prop-sf-existence`. The coefficient unit is its degree-zero regular module;
its membership in the localizing closure is supplied in the conclusion, as in
`det-pd-dualizing-complex-ctf`.

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-pd-preservation/_section.md and sk-lem-pd-preservation.proof.md,
first two sentences (blueprint: sk-lem-pd-preservation).

Proof:
1. Specialize the bundled `det-pd-dualizing-complex-ctf` to the identity morphism of X:
   take `c` for both structure compactifications and the proper identity
   compactification of the identity. The canonical identity comparison of
   `sk-thm-sf-comp-composition` lifts to the localizing closure, which is closed under
   isomorphisms; it gives the identity right adjoint and the compositor by whiskering
   and the left unitor. The first assertion then supplies the membership witness `h0`
   of the coefficient unit and puts `G(Lambda_s)` in Dctf.
2. The finite base field has cardinality a power of p, so characteristic p, and its
   algebraic closure has the same characteristic. It is algebraically closed, so by
   `sk-lem-base-field-cd` (`BaseFieldFiniteCD.of_isAlgClosed`) its ell-cohomological
   dimension is finite. For every K in Dctf, the first assertion of
   `det-thm-sf-ctf-stability-internal-hom` applied to K and `G(Lambda_s)` gives
   `RHom_{Lambda_X}(K, G(Lambda_s))` in Dctf.
3. Fixing the second argument of the existing relative `derivedHom` gives the
   ambient contravariant functor. Since Dctf is full (`sk-def-sfb-constructible`),
   step 2 lifts this functor to Dctf by `ObjectProperty.lift`, with the same ambient
   morphisms; the displayed equality after inclusion holds definitionally.
-/
theorem verdierDual_restricts_ctf
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (h : ∀ K, localizingClosureProEtale Λ X.left K →
      localizingClosureProEtale Λ (Spec (.of D.k))
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
    (G : (localizingClosureProEtale Λ (Spec (.of D.k))).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (_adj : localizingLowerShriek Λ c h ⊣ G) :
    ∃ h0 : localizingClosureProEtale Λ (Spec (.of D.k))
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj Λ (Spec (.of D.k))))),
      ∃ F : (ConstantModelConstructibleFiniteTor Λ X.left)ᵒᵖ ⥤
          ConstantModelConstructibleFiniteTor Λ X.left,
        F ⋙ (constantModelBoundedConstructible Λ X.left ⊓
            DerivedCategory.finiteTorAmplitude _).ι =
          (constantModelBoundedConstructible Λ X.left ⊓
              DerivedCategory.finiteTorAmplitude _).ι.op ⋙
            (derivedHom Λ X.left).flip.obj
              (G.obj ⟨(DerivedCategory.singleFunctor _ 0).obj
                (Mod.regular (condensedRingObj Λ (Spec (.of D.k)))), h0⟩).obj := by
  classical
  let cId : Compactification (𝟙 X.left) := Compactification.ofIsProper (𝟙 X.left)
  let eId := CompactSupportComposition.identity Λ X.left
  have hId : ∀ K, localizingClosureProEtale Λ X.left K →
      localizingClosureProEtale Λ X.left
        ((rightDerivedLowerShriekOfCompactification Λ cId).obj K) := by
    intro K hK P hP hS
    let _ := hP.2.1
    exact P.prop_of_iso (eId.app K).symm (hK P hP hS)
  let e : localizingLowerShriek Λ cId hId ≅
      𝟭 (localizingClosureProEtale Λ X.left).FullSubcategory :=
    NatIso.ofComponents
      (fun K ↦ (localizingClosureProEtale Λ X.left).isoMk (eId.app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact eId.hom.naturality f.hom)
  let adjId : localizingLowerShriek Λ cId hId ⊣
      𝟭 (localizingClosureProEtale Λ X.left).FullSubcategory :=
    Adjunction.id.ofNatIsoLeft e.symm
  let α : localizingLowerShriek Λ cId hId ⋙ localizingLowerShriek Λ c h ≅
      localizingLowerShriek Λ c h :=
    Functor.isoWhiskerRight e _ ≪≫ Functor.leftUnitor _
  obtain ⟨h0, hω, _⟩ := dualizingComplex_mem_ctf_and_composition D ℓ _hℓ Λ _hΛ
    (𝟙 X) c c cId h h hId G G (𝟭 _) _adj _adj adjId α
  refine ⟨h0, ?_⟩
  let P := constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _
  let ω := (G.obj ⟨(DerivedCategory.singleFunctor _ 0).obj
    (Mod.regular (condensedRingObj Λ (Spec (.of D.k)))), h0⟩).obj
  let H := P.ι.op ⋙ (derivedHom Λ X.left).flip.obj ω
  have hchar0 : ringChar D.k₀ = D.p := by
    let _ : Fact D.p.Prime := ⟨D.prime⟩
    let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    exact ringChar.eq D.k₀ D.p
  have hchar : ringChar D.k = D.p :=
    (Algebra.ringChar_eq D.k₀ D.k).symm.trans hchar0
  let _ : Fact (ringChar D.k).Prime := ⟨hchar ▸ D.prime⟩
  let _ : Fact (ringChar D.k ≠ ℓ) := ⟨by rw [hchar]; exact _hℓ.symm⟩
  let _ : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let _ : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  let _ : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  let _ : IsSeparated (X.left ↘ Spec (.of D.k)) := ‹IsSeparated X.hom›
  let _ : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hH : ∀ K, P (H.obj K) := by
    intro K
    exact (internalHom_stability Λ ℓ D.k (BaseFieldFiniteCD.of_isAlgClosed ℓ D.k)
      _hΛ K.unop.obj ω K.unop.property hω).1
  exact ⟨P.lift H hH, rfl⟩

end AlgebraicGeometry.ProEtale.CondensedRing

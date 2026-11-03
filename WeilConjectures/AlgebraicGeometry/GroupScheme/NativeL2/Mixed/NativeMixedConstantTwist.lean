/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeConstantWeilTwistFunctor
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.Pure.NativePureSubobjects
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.Pure.ConstantTwistWeight
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

/-! # Mixedness under constant Weil twists

Source: latest blueprint, lem-wf-constant-twist-weight, finite-filtration clause.
(blueprint: lem-zl-native-mixed-constant-twist)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeEnvelope

/-- Tensor a mixed filtration with the constant line, shifting every weight by c.
Source: latest blueprint, lem-wf-constant-twist-weight, final sentence.
(blueprint: lem-zl-native-mixed-constant-twist)

Proof: constant tensoring is exact and its underlying functor is tensor with the unit.
Apply it to every term and arrow of the mixed filtration. The terms remain constructible,
zero remains zero, and monomorphisms remain monomorphisms. Exactness identifies every
new successive cokernel with the constant twist of the old cokernel. The pure twist
weight formula gives its weight v+c, bounded by w+c. Compose the endpoint isomorphism
with the functorial tensor comparison to obtain the specified normalizedTwist object.
-/
theorem Mixed.constantTwist
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (M : WeilModule D l X₀)
    (iota : PadicAlgCl l →+* ℂ) (w c : ℝ) (hM : Mixed D l X₀ M iota w)
    (b : (PadicAlgCl l)ˣ) (hb : 2 * Real.logb (Nat.card D.k₀) ‖iota b‖ = c) :
    Mixed D l X₀ (normalizedTwist D l X₀ hl M b) iota (w + c) := by
  let T₀ := (D.geometricFiber X₀).left
  have : CompactSpace T₀ := QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  have : IsLocallyNoetherian T₀ := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  have : IsNoetherian T₀ := {}
  let Λ := Profinite.padicAlgClRingObj.{u} l
  have cmp := (adicConstructibilityPredicateComparison l T₀ Λ .algebraicClosure).1
  have hcIso {A B : NativeCondensedModule.Modules l T₀} (e : A ≅ B)
      (hA : IsConstantModelConstructible Λ T₀ A) :
      IsConstantModelConstructible Λ T₀ B :=
    (cmp _).mp (((cmp _).mpr hA).of_iso e)
  obtain ⟨_, hck, _, _, _, _, _⟩ :=
    (coefficientHeart_closure l (Profinite.padicAlgClCondensedRing l) (Or.inr rfl)).2 T₀
  let := hck
  let T := constantTwistFunctor D l hl X₀ b
  obtain ⟨n, G, φ, hc, hz, ⟨last⟩, hm, hp⟩ := hM
  refine ⟨n, fun i ↦ T.obj (G i), fun i ↦ T.map (φ i), ?_, T.map_isZero hz,
    ⟨T.mapIso last ≪≫ constantTwistFunctorObjIso D l hl X₀ b M⟩, ?_, ?_⟩
  · intro i
    exact hcIso (ρ_ (G i).carrier).symm (hc i)
  · intro i
    let := hm i
    infer_instance
  · intro i
    obtain ⟨v, hv, hPure⟩ := hp i
    have hcQ : IsConstantModelConstructible Λ T₀ (cokernel (φ i)).carrier := by
      let V := Endofunctor.IsoAlgebra.forget
        (CondensedRing.upperStar Λ (D.geometricFrobenius X₀).hom)
      exact hcIso (PreservesCokernel.iso V (φ i)).symm
        (ObjectProperty.prop_cokernel _ (V.map (φ i)) (hc i.castSucc) (hc i.succ))
    let Q : condensedConstructibleWeilSheaves Λ (D.geometricFrobenius X₀).hom :=
      ⟨cokernel (φ i), (cmp _).mpr hcQ⟩
    have hTwist := Pure.constantTwist D l hl X₀ Q iota v c hPure b hb
    let e : cokernel (T.map (φ i)) ≅ normalizedTwist D l X₀ hl (cokernel (φ i)) b :=
      (PreservesCokernel.iso T (φ i)).symm ≪≫
        constantTwistFunctorObjIso D l hl X₀ b (cokernel (φ i))
    refine ⟨v + c, by simpa [add_comm] using add_le_add_right hv c, ?_⟩
    exact Pure.of_mono D l X₀ e.hom iota (v + c) hTwist

end WeilConjectures.NativeL2

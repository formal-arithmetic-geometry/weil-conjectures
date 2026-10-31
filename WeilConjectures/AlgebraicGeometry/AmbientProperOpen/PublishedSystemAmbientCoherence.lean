/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
public import WeilConjectures.SixFunctors.Published.PublishedSystemAmbientPresentation
import Mathlib.Algebra.CharP.CharAndCard

/-! # Ambient tensor-composition coherence in the published sequence categories
Source: Stacks 03EL, 07A4 and 07A7. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  WeilConjectures.CoefficientClosedStructure.tensor
  WeilConjectures.AmbientPullbackTensor.tensorData
  WeilConjectures.AmbientPullbackTensor.derivedComp
  WeilConjectures.AmbientPullbackTensor.pull
  WeilConjectures.pullbackTensorSystemComparison
  WeilConjectures.pullbackTensorSequenceDerived
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

/-- The sequence-site clause of ambient tensor-composition coherence, with the
published category types and actual system tensor models.
Source: Stacks 03EL, 07A4 and 07A7
(blueprint: lem-sf-published-system-ambient-coherence).
Proof: the cardinality of the finite base field is a power of the prime F.p, so its
characteristic is F.p. Its algebraic closure has the same characteristic; hence
hl gives the characteristic inequality required by ambientPullbackTensorCoherence.
Objects of Spaces F provide the finite-type and quasi-compact structure maps.
Apply that theorem with s = none and the systemClosed and systemTensorModel data
of pullbackTensorCalculus. Take its final conjunct. The recorded ambient package
contains precisely these functors, comparisons and compositor, so this is the
stated equation, for arbitrary unbounded sequence objects. -/
theorem publishedSystemAmbientCoherence (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∀ {X Y Z : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z)
      (M N : WeilConjectures.coefficientSequenceDerived l E Z.obj.left),
      ((WeilConjectures.publishedSystemAmbientData l E).pull f.hom.left).map
          (((WeilConjectures.publishedSystemAmbientData l E).tensor g.hom.left).hom.app (M, N)) ≫
        ((WeilConjectures.publishedSystemAmbientData l E).tensor f.hom.left).hom.app
          (((WeilConjectures.publishedSystemAmbientData l E).pull g.hom.left).obj M,
            ((WeilConjectures.publishedSystemAmbientData l E).pull g.hom.left).obj N) ≫
        (WeilConjectures.pullbackTensorCalculus l E X.obj.left).systemClosed.tensor.map
          (Prod.mkHom
            (((WeilConjectures.publishedSystemAmbientData l E).comp
              f.hom.left g.hom.left).hom.app M)
            (((WeilConjectures.publishedSystemAmbientData l E).comp
              f.hom.left g.hom.left).hom.app N)) =
      ((WeilConjectures.publishedSystemAmbientData l E).comp f.hom.left g.hom.left).hom.app
          ((WeilConjectures.pullbackTensorCalculus l E Z.obj.left).systemClosed.tensor.obj (M, N)) ≫
        ((WeilConjectures.publishedSystemAmbientData l E).tensor
          (f.hom.left ≫ g.hom.left)).hom.app (M, N) := by
  intro X Y Z f g M N
  let : Fact F.p.Prime := ⟨F.prime⟩
  let : Fintype F.k₀ := Fintype.ofFinite F.k₀
  have hcard : Fintype.card F.k₀ = F.p ^ F.a := by
    simpa only [Nat.card_eq_fintype_card] using F.card_base.trans F.cardinality_eq
  let : CharP F.k₀ F.p := charP_of_card_eq_prime_pow hcard
  have hchar : l ≠ ringChar F.k := by
    rw [← Algebra.ringChar_eq F.k₀ F.k, ringChar.eq F.k₀ F.p]
    exact hl
  have : LocallyOfFiniteType X.obj.hom := X.property.1
  have : QuasiCompact X.obj.hom := X.property.2
  have : LocallyOfFiniteType Y.obj.hom := Y.property.1
  have : QuasiCompact Y.obj.hom := Y.property.2
  have : LocallyOfFiniteType Z.obj.hom := Z.property.1
  have : QuasiCompact Z.obj.hom := Z.property.2
  let TZ :=
    (WeilConjectures.pullbackTensorCalculus l E Z.obj.left).systemClosed
  let TY :=
    (WeilConjectures.pullbackTensorCalculus l E Y.obj.left).systemClosed
  let TX :=
    (WeilConjectures.pullbackTensorCalculus l E X.obj.left).systemClosed
  let RZ :=
    (WeilConjectures.pullbackTensorCalculus l E Z.obj.left).systemTensorModel
  let RY :=
    (WeilConjectures.pullbackTensorCalculus l E Y.obj.left).systemTensorModel
  let RX :=
    (WeilConjectures.pullbackTensorCalculus l E X.obj.left).systemTensorModel
  have hc := (WeilConjectures.AmbientPullbackTensor.ambientPullbackTensorCoherence.{u, u} l E
    F.k₀ F.k hchar X.obj.hom Y.obj.hom Z.obj.hom f.hom.left g.hom.left
    f.hom.w g.hom.w none TZ TY TX RZ RY RX).2.2.2.2.2.2.2.2
  exact hc M N

end AlgebraicGeometry.ProEtale.AmbientProperOpen

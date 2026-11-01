/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Compact.ConstructibleCompactSupportTargetIso
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # NativeExceptionalStructuralTransport

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The two point pullbacks form an adjunction: the isomorphism transport
comparison supplies inverse functors on the actual common-stage categories. -/
private theorem point_pullback_adjunction
    [I : ∀ x : (geometric D (point D)).base.left,
      Invertible (l : (geometric D (point D)).base.left.residueField x)]
    [J : ∀ x : Spec (CommRingCat.of D.k),
      Invertible (l : (Spec (CommRingCat.of D.k)).residueField x)] :
    Nonempty (commonStageDerivedPullback l (PadicAlgCl l) (pointGeometricIso D).hom ⊣
      commonStageDerivedPullback l (PadicAlgCl l) (pointGeometricIso D).inv) := by
  obtain ⟨iX, iY, hc⟩ := isomorphismFieldTransport D l (Fact.out : l ≠ D.p)
    (PadicAlgCl l) (pointGeometricIso D).hom
  have hiX : iX = I := Subsingleton.elim _ _
  have hiY : iY = J := Subsingleton.elim _ _
  subst iX
  subst iY
  obtain ⟨hX, hY, _, _, A, B, _, ⟨a⟩, ⟨b⟩⟩ := hc
  let P := commonStageDerivedPullback l (PadicAlgCl l) (pointGeometricIso D).hom
  let Q := commonStageDerivedPullback l (PadicAlgCl l) (pointGeometricIso D).inv
  have e : P ⋙ Q ≅ 𝟭 _ := by
    simpa only [P, Q, IsIso.Iso.inv_hom] using a.epsilon
  have e' : Q ⋙ P ≅ 𝟭 _ := by
    simpa only [P, Q, IsIso.inv_inv, IsIso.Iso.inv_hom, IsIso.Iso.inv_inv] using b.epsilon
  exact ⟨(CategoryTheory.Equivalence.mk P Q e.symm e').toAdjunction⟩

/-- Ordinary exceptional images of the normalized point unit agree after identifying
the geometric fiber of the model point with literal Spec k.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, structural
specialization; native comparison proof Step 4 and pointGeometricIso.
(blueprint: lem-sf-native-exceptional-structural-transport).

Proof: a morphism a₀ to the model point is its structural morphism, by the Over
commutativity equation. Its geometric base change followed by pointGeometricIso.hom
is therefore the literal geometric structural map. The family isomorphism comparison
for pointGeometricIso preserves the normalized coefficient unit. Factor the ordinary
compact-support functor for this composite as compact support followed by exact
transport along the point isomorphism. Compactification coherence identifies this
factorization for c and c', retaining the proper/open normalization of both systems.
Transport the adjunctions through that isomorphism. Uniqueness of right adjoints,
with their specified units and counits, identifies the exceptional image of the unit.
Apply rho on X. This uses ordinary constructible operations only, and is independent
of a native adjunction. Identity point isomorphisms and empty X give the same formula. -/
theorem native_exceptional_structural_transport (R : Family l D)
    (X : Space D) (a₀ : X.base ⟶ (point D).base)
    [IsSeparated a₀.left] [LocallyOfFiniteType a₀.left] [QuasiCompact a₀.left]
    (S : CoefficientSystem D l a₀) (c : Compactification (geometricMap D a₀))
    (S' : StructuralSystem D l X) (c' : Compactification (geometric D X).base.hom) :
    Nonempty ((rho D l R X).obj
        ((S.ring.operation c .closed).G.obj (omega D l R (point D))) ≅
      (rho D l R X).obj
        ((S'.ring.operation c' .closed).G.obj (geometricPointOmega D l R))) := by
  let := (R.data (geometric D (point D))).units
  let : ∀ x : Spec (CommRingCat.of D.k),
      Invertible (l : (Spec (CommRingCat.of D.k)).residueField x) :=
    (R.data (geometricPoint D)).units
  obtain ⟨a⟩ := point_pullback_adjunction D l
  have hgeo : geometricMap D a₀ ≫ (pointGeometricIso D).hom =
      (geometric D X).base.hom :=
    Over.w ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map a₀)
  obtain ⟨e⟩ := ConstructibleExceptionalCoefficients.constructible_compact_support_target_iso
    l (PadicAlgCl l) D (Fact.out : l ≠ D.p)
    (X := (geometric D X).base.left) (Y := (geometric D (point D)).base.left)
    (Z := Spec (CommRingCat.of D.k))
    (geometricMap D a₀) (geometric D X).base.hom (pointGeometricIso D) hgeo S c S' c'
  let b := ((S'.ring.operation c' .closed).adjunction.comp a).ofNatIsoLeft e.symm
  let t := (S.ring.operation c .closed).adjunction.rightAdjointUniq b
  let v := (R.unit_spec (geometricPoint D) (geometric D (point D))
    (pointGeometricIso D).symm).exists.choose
  exact ⟨(rho D l R X).mapIso
    (t.app (omega D l R (point D)) ≪≫
      (S'.ring.operation c' .closed).G.mapIso v)⟩

end WeilConjectures.NativeExceptionalForgetful

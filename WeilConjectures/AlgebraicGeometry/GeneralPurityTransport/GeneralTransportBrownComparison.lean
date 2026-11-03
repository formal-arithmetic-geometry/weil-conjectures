/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransportData
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # The Brown comparison from an explicit smooth adjunction

Source: current blueprint sk-thm-purity-transport, proof Step 3.
(blueprint: lem-pur-general-transport-brown-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport

/-- The explicit smooth adjunction determines the unique counit-compatible comparison
with every localizing Brown adjunction, including its literal restricted counit.
Source: sk-thm-purity-transport.proof.md, Step 3
(blueprint: lem-pur-general-transport-brown-comparison).
Proof in words. Transpose the small counit under the large adjunction. The resulting
map induces the composite of the two Hom bijections on every shifted Dctf generator.
The localizing generator criterion makes it invertible, so the large right adjoint
preserves Dctf. Restrict the same adjunction along the full inclusions. The restriction
formula retains its ambient counit. Right-adjoint uniqueness supplies the comparison;
transposing its counit identity gives uniqueness of each component. -/
theorem brownComparison_of_adjunctionFamily
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (a : AdjunctionFamily ell k) : BrownComparison ell k a := by
  intro c s hL G b
  let P := property ell c s.X.left
  have hcons := constantModelConstructibleFiniteTor_wellDefined (c.obj ell) s.X.left
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstantModelConstructible (c.obj ell) s.X.left) :=
    hcons.1
  have : (constantModelBoundedConstructible (c.obj ell) s.X.left
      ).IsClosedUnderIsomorphisms := hcons.2.1
  have : (_root_.DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (ProEt.topology s.X.left) Ab.{u + 1})
        (condensedRingObj (c.obj ell) s.X.left))).IsTriangulated :=
    hcons.2.2.2.2.2.2.2.1
  have : P.IsClosedUnderIsomorphisms := inferInstance
  have : P.IsStableUnderShift ℤ := by
    change ((constantModelBoundedConstructible (c.obj ell) s.X.left) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).IsStableUnderShift ℤ
    unfold constantModelBoundedConstructible
    change ((_root_.DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty
        (IsConstantModelConstructible (c.obj ell) s.X.left)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).IsStableUnderShift ℤ
    infer_instance
  have hG : ∀ K : c.ctf ell s.Y.left,
      property ell c s.X.left (G.obj ((inclusion ell c s.Y.left).obj K)).obj :=
    fun K ↦ AdjunctionTransfer.rightAdjoint_preserves_generators
      (property ell c s.X.left) (property ell c s.Y.left)
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification) (a c s).support_closed hL
      (source ell c s.map s.dim (a c s).source_closed) (a c s).adjunction G b K
  let L := (localizing ell c s.Y.left).lift
    ((localizing ell c s.X.left).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification)
    (fun K ↦ hL K.obj K.property)
  let commL : inclusion ell c s.X.left ⋙ L ≅
      support ell c s.compactification (a c s).support_closed ⋙
        inclusion ell c s.Y.left := Iso.refl _
  let commR : inclusion ell c s.Y.left ⋙ G ≅
      exceptional ell c G hG ⋙ inclusion ell c s.X.left := Iso.refl _
  let bctf := b.restrictFullyFaithful (ObjectProperty.fullyFaithfulιOfLE _)
    (ObjectProperty.fullyFaithfulιOfLE _) commL commR
  refine ⟨hG, bctf, ?_, (a c s).adjunction.rightAdjointUniq bctf, ?_, ?_⟩
  · intro K
    have h := b.map_restrictFullyFaithful_counit_app
      (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
      commL commR K
    have h' := congrArg (fun f ↦ f.hom) h
    change (bctf.counit.app K).hom = 𝟙 _ ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification).map (𝟙 _) ≫
      (b.counit.app ((inclusion ell c s.Y.left).obj K)).hom at h'
    have hclean : 𝟙 _ ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).map
            (𝟙 ((localizing ell c s.X.left).ι.obj
              (G.obj ((inclusion ell c s.Y.left).obj K)))) ≫
        (b.counit.app ((inclusion ell c s.Y.left).obj K)).hom =
        (b.counit.app ((inclusion ell c s.Y.left).obj K)).hom := by
      exact (Category.id_comp _).trans
        ((congrArg
          (fun q ↦ q ≫ (b.counit.app ((inclusion ell c s.Y.left).obj K)).hom)
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s.compactification).map_id
            ((localizing ell c s.X.left).ι.obj
              (G.obj ((inclusion ell c s.Y.left).obj K))))).trans
          (Category.id_comp _))
    exact heq_of_eq (h'.trans hclean)
  · intro K
    exact (a c s).adjunction.rightAdjointUniq_hom_app_counit bctf K
  · intro gamma hgamma
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (bctf.homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using
      (hgamma K).trans ((a c s).adjunction.rightAdjointUniq_hom_app_counit bctf K).symm

end AlgebraicGeometry.ProEtale.GeneralPurityTransport

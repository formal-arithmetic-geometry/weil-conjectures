/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportRealization

/-! # Constructibility of the native proper module direct image

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-sf-adic-proper-ordinary-push-preservation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- The actual native module right-derived direct image preserves the full bounded
constructible subcategory for a proper map; no comparison of adjunctions is asserted.
Source: BS Lemma 6.7.2, Proposition 6.8.14 and Remark 6.8.15, pp. 61--62;
Step 5 of lem-sf-adic-proper-adjunction-realization
(blueprint: lem-sf-adic-proper-ordinary-push-preservation).

Proof: apply locally_finite_adic_compact_support_realization to the proper
compactification (id_Z,p). Extension by zero along id_Z is the identity, by its
section formula, so the actual native compact-support operation is Rp_*.
The coefficient precomposition equation in O identifies its ring map with the
native coefficient map in that realization. The section-module equivalence in
F.data transports the native right adjunction to the actual ordinary module
right adjunction: their inverse-image functors are the same scalar-extension
pullback. Uniqueness of right adjoints identifies their direct images with
ContinuousRational.DirectImage.derivedPush p.left O.coefficient. The native
constructible predicate transported by this equivalence is precisely
boundedConstructible. Apply the compact-support preservation clause and transport
along this isomorphism. Its image assertion applies to all bounded constructible
inputs: over a coefficient field bounded constructible complexes have finite Tor
amplitude, so there is no added hypothesis on K. Any choices of presentation
in the compact-support theorem give the same subcategory through this native
predicate; the fixed Family and Operations need not be those choices. Properness
is essential for (id_Z,p) to be a compactification. The empty scheme and zero
complex are included, since all functors and preservation clauses apply there. -/
theorem adic_proper_ordinary_push_preservation (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (F : Family l D)
    (Z T : GeometricSpace D) (p : Z.base ⟶ T.base)
    (hp : IsProper p.left)
    (O : Operations l p.left (F.data Z).realization (F.data T).realization) :
    ∀ K, boundedConstructible l Z.base.left (F.data Z).realization K →
      boundedConstructible l T.base.left (F.data T).realization
        ((ContinuousRational.DirectImage.derivedPush p.left O.coefficient).obj K) := by
  classical
  let : Z.base.left.Over (Spec (CommRingCat.of D.k)) := ⟨Z.base.hom⟩
  let : T.base.left.Over (Spec (CommRingCat.of D.k)) := ⟨T.base.hom⟩
  let : LocallyOfFiniteType (Z.base.left ↘ Spec (CommRingCat.of D.k)) := Z.finiteType
  let : QuasiCompact (Z.base.left ↘ Spec (CommRingCat.of D.k)) := Z.quasiCompact
  let : LocallyOfFiniteType (T.base.left ↘ Spec (CommRingCat.of D.k)) := T.finiteType
  let : QuasiCompact (T.base.left ↘ Spec (CommRingCat.of D.k)) := T.quasiCompact
  let : p.left.IsOver (Spec (CommRingCat.of D.k)) := ⟨p.w⟩
  let : IsProper p.left := hp
  obtain ⟨P⟩ := ConstructibleExceptionalCoefficients.exists_coefficient_construction
    l (ULift.{u} (PadicAlgCl l)) D hl p.left
  obtain ⟨G, ⟨C⟩⟩ :=
    LocallyFiniteAdicCompactSupport.locally_finite_adic_compact_support_realization
      l D hl P (Compactification.ofIsProper p.left)
  let := G
  have hc : O.coefficient = (G.pull p.left).hom := by
    apply ((proEtaleSheafAdjunction p.left CommRingCat.{u + 1}).homEquiv _ _).injective
    ext V s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact (O.functions V s x).trans (G.pull_normalized p.left V s x).symm
  have hpush : ContinuousRational.DirectImage.modulePush p.left O.coefficient =
      proEtaleRingModuleDirectImage p.left
        (LocallyFiniteAdicRealization.ringSheaf l T.base.left)
        (LocallyFiniteAdicRealization.ringSheaf l Z.base.left) (G.pull p.left) := by
    rw [hc]
    rfl
  let e : ProEtale.adicOpenImmersionLowerShriek l (𝟙 Z.base.left) ≅ 𝟭 _ :=
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l (𝟙 Z.base.left)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (ProEtale.adicUpperStarId l Z.base.left).symm)
  let de : (ProEtale.adicOpenImmersionLowerShriek l (𝟙 Z.base.left)).mapDerivedCategory ≅
      𝟭 _ := Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _
  let ae : LocallyFiniteAdicCompactSupport.actual l
      (Compactification.ofIsProper p.left) ≅
      (ProEtale.adicLowerStar l p.left).rightDerivedFunctor :=
    Functor.isoWhiskerRight de _ ≪≫ Functor.leftUnitor _
  let transport : (ProEtale.adicLowerStar l p.left).rightDerivedFunctor ⋙
        sectionDerived l T.base.left (F.data T).realization ≅
      sectionDerived l Z.base.left (F.data Z).realization ⋙
        ContinuousRational.DirectImage.derivedPush p.left O.coefficient := by
    exact LocallyFiniteAdicCompactSupport.properTransport l p.left ≪≫
      Functor.isoWhiskerLeft (sectionDerived l Z.base.left (F.data Z).realization)
        (Functor.rightDerivedFunctorNatIso (eqToIso hpush.symm))
  have : (ProEtale.DerivedCategory.boundedAdicConstructible l T.base.left
      ).IsClosedUnderIsomorphisms := by
    dsimp [ProEtale.DerivedCategory.boundedAdicConstructible]
    infer_instance
  intro K hK
  obtain ⟨L, hL, ⟨i⟩⟩ := hK
  refine ⟨(ProEtale.adicLowerStar l p.left).rightDerivedFunctor.obj L, ?_, ?_⟩
  · exact (ProEtale.DerivedCategory.boundedAdicConstructible l T.base.left).prop_of_iso
      (ae.app L) (C.preserves L hL)
  · exact ⟨transport.app L ≪≫
      (ContinuousRational.DirectImage.derivedPush p.left O.coefficient).mapIso i⟩

end WeilConjectures.AdicQbarRealization.Proper

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageComparisonIsomorphisms
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageComparisonCoherence
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteBridgeFoundations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomNaturality
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteEvaluation

/-! # Normalized coefficient calculus on the two small sites

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
  AlgebraicGeometry.ProEtale.pbcComparisonReduction
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.Etale.derivedTensor AlgebraicGeometry.Etale.derivedHom
  AlgebraicGeometry.ProEtale.derivedTensor AlgebraicGeometry.ProEtale.derivedHom
  AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂
  AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂
  _root_.DerivedCategory.instMonoidalCategory_weilConjectures
  _root_.DerivedCategory.commShift₂CurriedTensor

-- Keep the derived functors abstract while identifying their site presentations.
set_option maxHeartbeats 1000000 in
-- Keep the derived functors abstract while identifying their site presentations.
private theorem stage_direct_natural
    (pro : Bool) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {T X : Scheme.{u}} (f : T ⟶ X)
    {s t : Stage l E} (a : Arrow s t) {K L : Sites.D pro s.ring T} (g : K ⟶ L) :
    (Sites.scalar pro a.ringMap X).map ((Sites.push pro s.ring f).map g) ≫
        Sites.direct pro a.ringMap f L =
      Sites.direct pro a.ringMap f K ≫
        (Sites.push pro t.ring f).map ((Sites.scalar pro a.ringMap T).map g) := by
  cases pro <;> dsimp only [Sites.scalar, Sites.direct, Sites.push, id_eq]
  · exact Etale.finiteCoefficientDirectImageMap_naturality a.ringMap f g
  · exact ProEtale.finiteCoefficientDirectImageMap_naturality a.ringMap f g

-- Keep the derived functors abstract while identifying their site presentations.
set_option maxHeartbeats 1000000 in
-- Keep the derived functors abstract while identifying their site presentations.
private theorem coefficient_direct_comp
    (pro : Bool) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    {T X : Scheme.{u}} (f : T ⟶ X) (K : Sites.D pro A T) :
    (Sites.scalar pro ψ X).map (Sites.direct pro φ f K) ≫
        Sites.direct pro ψ f ((Sites.scalar pro φ T).obj K) ≫
          (Sites.push pro C f).map ((Sites.comp pro φ ψ χ h T).hom.app K) =
      (Sites.comp pro φ ψ χ h X).hom.app ((Sites.push pro A f).obj K) ≫
        Sites.direct pro χ f K := by
  subst χ
  cases pro <;> dsimp only [Sites.scalar, Sites.direct, Sites.push, Sites.comp, id_eq]
  · have he := Etale.finiteCoefficientDirectImageMap_coefficientChain φ ψ f K
    have hcomp := congrArg (fun g ↦
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫ g) he
    simpa only [CategoryTheory.Category.assoc, Iso.hom_inv_id_app_assoc] using hcomp.symm
  · have he := ProEtale.finiteCoefficientDirectImageMap_coefficientChain φ ψ f K
    have hcomp := congrArg (fun g ↦
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
        φ ψ (ψ.comp φ) rfl).hom.app
          ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫ g) he
    simpa only [CategoryTheory.Category.assoc, Iso.hom_inv_id_app_assoc] using hcomp.symm

universe g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄

set_option maxHeartbeats 2000000 in
-- Transposition compares the published site presentations.
private theorem stage_hom_natural
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison pro φ X)
    {K K' M M' : Sites.D pro A X} (g : K' ⟶ K) (h : M ⟶ M') :
    (Sites.scalar pro φ X).map
        ((Functor.uncurry.obj (Sites.hom pro A X)).map (Prod.mkHom g.op h)) ≫
          Sites.homMap pro φ X μ K' M' =
      Sites.homMap pro φ X μ K M ≫
        (Functor.uncurry.obj (Sites.hom pro B X)).map
          (Prod.mkHom ((Sites.scalar pro φ X).map g).op ((Sites.scalar pro φ X).map h)) := by
  exact scalar_tensor_hom_comparison_naturality
    (Sites.tensor pro A X) (Sites.hom pro A X) (Sites.tensor pro B X) (Sites.hom pro B X)
    (Sites.adj pro A X) (Sites.adj pro B X)
    (normalized_stage_site_evaluation_dinaturality pro A X)
    (normalized_stage_site_evaluation_dinaturality pro B X)
    (Sites.scalar pro φ X) μ K M K' M' g h

private theorem stage_dual_natural
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {aX : X ⟶ S} (c : Compactification aX)
    (μ : Sites.TensorComparison pro φ X)
    (w : (Sites.scalar pro φ X).obj (Sites.omega pro A c) ⟶ Sites.omega pro B c)
    {K L : Sites.D pro A X} (g : K ⟶ L) :
    (Sites.scalar pro φ X).map ((Sites.dual pro A c).map g.op) ≫
        Sites.dualMap pro φ c μ w K =
      Sites.dualMap pro φ c μ w L ≫
        (Sites.dual pro B c).map ((Sites.scalar pro φ X).map g).op := by
  have hn := stage_hom_natural pro φ X μ g (𝟙 (Sites.omega pro A c))
  simp only [_root_.CategoryTheory.Functor.map_id, Functor.uncurry_obj_map,
    Category.comp_id] at hn
  dsimp only [Sites.dualMap, Sites.dual, Functor.flip]
  rw [← Category.assoc, hn, Category.assoc]
  simpa only [CategoryTheory.Category.assoc] using congrArg
    (fun q ↦ Sites.homMap pro φ X μ L (Sites.omega pro A c) ≫ q)
    (((Sites.hom pro B X).map ((Sites.scalar pro φ X).map g).op).naturality w).symm

private theorem stage_dual_unit
    (pro : Bool) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (μ : ∀ {s t : Stage l E} (a : Arrow s t), Sites.TensorComparison pro a.ringMap X)
    (σ : ∀ s : Stage l E, Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip)
    (hi : Sites.StageComparisonIsomorphisms pro l E f i c μ)
    (hc : Sites.StageComparisonCoherence pro l E f i c μ σ)
    (s : Stage l E) (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field) (K : Sites.D pro s.ring X)
    (hK : Sites.Ctf pro s.ring X K) :
    Sites.dualMap pro a.ringMap c (μ a) (Sites.stageOmegaMap pro a c) K ≫
      (Sites.dual pro s.ring c).map
        ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).inv.app K).op =
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app
        ((Sites.dual pro s.ring c).obj (op K)) := by
  have hh := hc.hom_unit s a h K (Sites.omega pro s.ring c) hK (hi.omega_ctf s)
  have hn := ((Sites.hom pro s.ring X).map
    ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).inv.app K).op).naturality
      ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app (Sites.omega pro s.ring c))
  simp only [Functor.id_obj] at hn hh
  dsimp only [Sites.dualMap, Sites.dual, Functor.flip]
  rw [hc.omega_unit s a h, Category.assoc, hn]
  simpa only [Functor.uncurry_obj_map, Category.assoc] using hh

private theorem stage_dual_comp
    (pro : Bool) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (μ : ∀ {s t : Stage l E} (a : Arrow s t), Sites.TensorComparison pro a.ringMap X)
    (σ : ∀ s : Stage l E, Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip)
    (hi : Sites.StageComparisonIsomorphisms pro l E f i c μ)
    (hc : Sites.StageComparisonCoherence pro l E f i c μ σ)
    {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
    (h : ab.embedding = b.embedding.comp a.embedding) (K : Sites.D pro s.ring X)
    (hK : Sites.Ctf pro s.ring X K) :
    (Sites.scalar pro b.ringMap X).map
        (Sites.dualMap pro a.ringMap c (μ a) (Sites.stageOmegaMap pro a c) K) ≫
      Sites.dualMap pro b.ringMap c (μ b) (Sites.stageOmegaMap pro b c)
        ((Sites.scalar pro a.ringMap X).obj K) ≫
        (Sites.dual pro v.ring c).map
          ((Sites.comp pro a.ringMap b.ringMap ab.ringMap
            (Arrow.ringMap_comp a b ab h) X).inv.app K).op =
      (Sites.comp pro a.ringMap b.ringMap ab.ringMap
        (Arrow.ringMap_comp a b ab h) X).hom.app ((Sites.dual pro s.ring c).obj (op K)) ≫
          Sites.dualMap pro ab.ringMap c (μ ab) (Sites.stageOmegaMap pro ab c) K := by
  let F := Sites.scalar pro a.ringMap X
  let G := Sites.scalar pro b.ringMap X
  let J := Sites.scalar pro ab.ringMap X
  let H := Sites.hom pro v.ring X
  let α := Sites.comp pro a.ringMap b.ringMap ab.ringMap
    (Arrow.ringMap_comp a b ab h) X
  have hh := hc.hom_comp a b ab h K (Sites.omega pro s.ring c) hK (hi.omega_ctf s)
  have hn := stage_hom_natural pro b.ringMap X (μ b) (𝟙 (F.obj K))
    (Sites.stageOmegaMap pro a c)
  simp only [Functor.uncurry_obj_map, op_id, _root_.CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp] at hn
  have hw := hc.omega_comp a b ab h
  have ht := (H.map (α.inv.app K).op).naturality
    (α.hom.app (Sites.omega pro s.ring c) ≫ Sites.stageOmegaMap pro ab c)
  dsimp only [F, G, J, H, α, Functor.comp_obj] at ht
  dsimp only [Sites.dualMap, Sites.dual, Functor.flip]
  simp only [_root_.CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← reassoc_of% (H.obj (op (G.obj (F.obj K)))).map_comp
    (G.map (Sites.stageOmegaMap pro a c)) (Sites.stageOmegaMap pro b c)]
  rw [hw]
  erw [ht]
  rw [(H.obj (op (J.obj K))).map_comp]
  simpa only [Functor.uncurry_obj_map, Category.assoc, F, G, J, H, α,
    Functor.comp_obj] using congrArg
      (fun q ↦ q ≫ (H.obj (op (J.obj K))).map (Sites.stageOmegaMap pro ab c)) hh.symm

private theorem adjunct_counit
    {C : Type g₁} {D : Type g₂}
    [CategoryTheory.Category.{h₁} C] [CategoryTheory.Category.{h₂} D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {K : C} {M : D} (q : F.obj K ⟶ M) :
    F.map (a.homEquiv K M q) ≫ a.counit.app M = q := by
  exact (a.homEquiv K M).symm_apply_apply q

private theorem inverse_component_naturality
    {C : Type g₁} {D : Type g₂}
    [CategoryTheory.Category.{h₁} C] [CategoryTheory.Category.{h₂} D] {F G : C ⥤ D} (α : F ⟶ G)
    {K L : C} (g : K ⟶ L) [IsIso (α.app K)] [IsIso (α.app L)] :
    G.map g ≫ inv (α.app L) = inv (α.app K) ≫ F.map g := by
  apply (cancel_mono (α.app L)).1
  simp only [CategoryTheory.Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [α.naturality g, IsIso.inv_hom_id_assoc]

private theorem right_mate_naturality
    {C : Type g₁} {D : Type g₂} {C' : Type g₃} {D' : Type g₄}
    [CategoryTheory.Category.{h₁} C] [CategoryTheory.Category.{h₂} D]
    [CategoryTheory.Category.{h₃} C'] [CategoryTheory.Category.{h₄} D']
    {FA : C ⥤ D} {GA : D ⥤ C} {FB : C' ⥤ D'} {GB : D' ⥤ C'}
    (adA : FA ⊣ GA) (adB : FB ⊣ GB) (SC : C ⥤ C') (SD : D ⥤ D')
    (α : FA ⋙ SD ⟶ SC ⋙ FB) {K L : D} (g : K ⟶ L)
    [IsIso (α.app (GA.obj K))] [IsIso (α.app (GA.obj L))] :
    SC.map (GA.map g) ≫ adB.homEquiv _ _
        (inv (α.app (GA.obj L)) ≫ SD.map (adA.counit.app L)) =
      adB.homEquiv _ _ (inv (α.app (GA.obj K)) ≫ SD.map (adA.counit.app K)) ≫
        GB.map (SD.map g) := by
  apply (adB.homEquiv _ _).symm.injective
  rw [adB.homEquiv_naturality_left_symm, adB.homEquiv_naturality_right_symm]
  simp only [Equiv.symm_apply_apply]
  have hn := inverse_component_naturality α (GA.map g)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  simp only [CategoryTheory.Category.assoc, ← SD.map_comp]
  exact congrArg (fun q ↦ inv (α.app (GA.obj K)) ≫ SD.map q)
    (adA.counit.naturality g)

private theorem etale_closed_natural
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K L : Cat A X} (g : K ⟶ L)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj K))]
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj L))] :
    (Etale.scalarExtension φ Z).map ((closedUpper A i).map g) ≫ closedMap φ i L =
      closedMap φ i K ≫ (closedUpper B i).map ((Etale.scalarExtension φ X).map g) := by
  classical
  let α : R(Etale.lowerStar (ModuleCat.{u + 1} A) i) ⋙ Etale.scalarExtension φ X ⟶
      Etale.scalarExtension φ Z ⋙ R(Etale.lowerStar (ModuleCat.{u + 1} B) i) := {
    app := Etale.finiteCoefficientDirectImageMap φ i
    naturality := fun _ _ g ↦ Etale.finiteCoefficientDirectImageMap_naturality φ i g }
  simpa only [closedUpper, closedMap, α, Functor.id_obj, dif_pos (inferInstance : IsIso
      (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj K))),
    dif_pos (inferInstance : IsIso
      (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj L)))] using
    right_mate_naturality
      (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
      (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)))
      (Etale.scalarExtension φ Z) (Etale.scalarExtension φ X) α g

private theorem stage_closed_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Cat A X)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M))] :
    Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).map (closedMap φ i M) ≫
        (Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).counit.app
            ((Etale.scalarExtension φ X).obj M) =
    (Etale.scalarExtension φ X).map
      ((Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M) := by
  classical
  simp only [closedMap, dif_pos (inferInstance : IsIso
    (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M))),
    adjunct_counit, IsIso.hom_inv_id_assoc]

private theorem stage_omega_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {aX : X ⟶ S} (c : Compactification aX)
    [HasCompactification aX] :
    (support B c).map (omegaMap φ c) ≫ (adj B c).counit.app (𝟙_ _) =
      Etale.ExceptionalCoefficients.comparisonInverse φ
          (HasCompactification.compactification aX) (omega A c) ≫
        (Etale.scalarExtension φ S).map ((adj A c).counit.app (𝟙_ _)) ≫
        (Etale.ExceptionalCoefficients.unitIso φ S).hom := by
  dsimp only [support, omegaMap, adj, upper, omega,
    Etale.ExceptionalCoefficients.mateMap]
  have hn := (Etale.rightDerivedUpperShriekAdjunction B aX).counit.naturality
    (Etale.ExceptionalCoefficients.unitIso φ S).hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, adjunct_counit]
  erw [Category.assoc]
  rfl

set_option maxHeartbeats 2000000 in
-- Assemble the two site records and their normalization fields.
/-- The normalized two-site coefficient calculus, without geometric transport or
ramification assertions.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3;
the finite quotient comparisons are lem-coef-finite-direct-image,
lem-coef-finite-closed-shriek, lem-coef-finite-dualizing, thm-coef-finite-hom and
cor-coef-finite-verdier (blueprint: lem-route-normalized-stage-coefficient-calculus).

Proof: use a flat constructible model to prove finite-ring scalar preservation on
the etale site. Reflect the Tor interval of a pro-etale input to its etale origin,
apply that result and transport it by the scalar/site comparison. The general finite
coefficient direct-image theorem now applies on the etale site without presenting
stage fields in a smaller universe. Its etale-origin comparison square, followed by
naturality along the origin isomorphism, proves the pro-etale direct assertion.
Use the separately stated pointwise geometric theorem for the normalized tensorators,
symmetries, remaining closed/dualizing/Hom isomorphisms and their geometric domains.
Use its separate coherence theorem for the pairing, residual units/composites and
four site equations. Construct the two Calculus records explicitly with the actual
closed and dualizing maps. Direct naturality and composition are the published
coefficient cocycle. Hom naturality is tensor-Hom transposition of tensorator
naturality and evaluation dinaturality. Its specialization, followed by Hom
functoriality, gives Verdier naturality, identity and composition. Hom at the
dualizing object followed by the dualizing isomorphism gives Verdier invertibility.
For the etale closed map, transpose the inverse direct comparison followed by the
extended exceptional counit; naturality and the counit equation follow by adjunction
injectivity and inverse-component naturality. The dualizing counit equation is
homEquiv naturality in the target. The closed site bridge is the image of the
comparison unit at a bounded-below input. The dualizing bridge is the image of the
base-unit comparison. Their invertibility and the remaining Hom bridge give the
Verdier bridge by composition. Supply the four site equations from coherence.
The final pro-etale identifications are reflexivity, since the constructed maps are
literally proClosedMap and proOmegaMap. -/
theorem normalized_stage_coefficient_calculus
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) :
    ∃ (et : Sites.Calculus false l E f i c) (pro : Sites.Calculus true l E f i c),
      Sites.Normalized l E f i c et pro ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (M : Sites.D true s.ring X),
        Sites.Ctf true s.ring X M → pro.closedMap a M = Sites.proClosedMap a.ringMap i M) ∧
      (∀ {s t : Stage l E} (a : Arrow s t),
        pro.omegaMap a = Sites.proOmegaMap a.ringMap c) := by
  have := c.hasCompactification
  obtain ⟨μ, σ, hμ, hσ, hi, hsi⟩ := normalized_stage_comparison_isomorphisms
    D l hl E T X Z f i c
  obtain ⟨hc, hse⟩ := normalized_stage_comparison_coherence
    D l hl E T X Z f i c μ hμ σ hσ hi hsi
  have hring {s t : Stage l E} (a : Arrow s t) :=
    finite_ring_scalar_direct_foundations D a.ringMap T X f
  have hbridges (s : Stage l E) := finite_ring_site_bridge_foundations s.ring i c
  let calculus (pro : Bool) : Sites.Calculus pro l E f i c := {
    symmetry := σ pro
    symmetry_normalized := hσ pro
    tensorIso := μ pro
    tensor_normalized := hμ pro
    closedMap := fun a M ↦ Sites.stageClosedMap pro a i M
    omegaMap := fun a ↦ Sites.stageOmegaMap pro a c
    scalar_ctf_X := fun a K hK ↦ (hring a).2.1 pro K hK
    scalar_ctf_T := fun a K hK ↦ (hring a).1 pro K hK
    direct_iso := fun a K hK ↦ (hring a).2.2 pro K hK
    closed_iso := (hi pro).closed_iso
    omega_iso := (hi pro).omega_iso
    hom_iso := (hi pro).hom_iso
    dual_iso := by
      intro s t a K hK
      have hH : IsIso
          (Sites.homMap pro a.ringMap X (μ pro a) K (Sites.omega pro s.ring c)) :=
        (hi pro).hom_iso a K (Sites.omega pro s.ring c) hK ((hi pro).omega_ctf s)
      have : IsIso (Sites.stageOmegaMap pro a c) := (hi pro).omega_iso a
      have hω := Functor.map_isIso
        ((Sites.hom pro t.ring X).obj (op ((Sites.scalar pro a.ringMap X).obj K)))
        (Sites.stageOmegaMap pro a c)
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hH hω
    evaluation_eq := (hc pro).evaluation_eq
    bidual_eq := (hc pro).bidual_eq
    direct_natural := by
      intro s t a K L g _ _
      exact stage_direct_natural pro l E f a g
    closed_natural := by
      cases pro
      · intro s t a K L g hK hL
        have := hsi.closed_direct_iso a K hK
        have := hsi.closed_direct_iso a L hL
        exact etale_closed_natural a.ringMap i g
      · exact (hc true).closed_natural rfl
    hom_natural := by
      intro s t a K K' M M' g h _ _ _ _
      exact stage_hom_natural pro a.ringMap X (μ pro a) g h
    dual_natural := by
      intro s t a K L g _ _
      exact stage_dual_natural pro a.ringMap c (μ pro a) _ g
    direct_unit := (hc pro).direct_unit
    closed_unit := (hc pro).closed_unit
    omega_unit := (hc pro).omega_unit
    hom_unit := (hc pro).hom_unit
    dual_unit := stage_dual_unit pro l E f i c (μ pro) (σ pro) (hi pro) (hc pro)
    direct_comp := fun a b ab h K _ ↦ coefficient_direct_comp pro
      a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) f K
    closed_comp := (hc pro).closed_comp
    omega_comp := (hc pro).omega_comp
    hom_comp := (hc pro).hom_comp
    dual_comp := stage_dual_comp pro l E f i c (μ pro) (σ pro) (hi pro) (hc pro) }
  refine ⟨calculus false, calculus true, ?_, ?_, ?_⟩
  · have := c.hasCompactification
    change Sites.NormalizedAux l E f i c (calculus false) (calculus true)
    exact {
      etale_closed := fun _ _ _ ↦ rfl
      etale_omega := fun _ ↦ rfl
      compact_support_iso := hsi.compact_support_iso
      closed_direct_iso := hsi.closed_direct_iso
      closed_counit := by
        intro s t a M hM
        have := hsi.closed_direct_iso a M hM
        exact stage_closed_counit a.ringMap i M
      omega_counit := fun a ↦ stage_omega_counit a.ringMap c
      closed_site_iso := fun s M hM ↦ (hbridges s).1 M hM
      omega_site_iso := fun s ↦ (hbridges s).2
      hom_site_iso := hsi.hom_site_iso
      dual_site_iso := by
        intro s K hK
        have hH : IsIso (Sites.siteHom s.ring X K (omega s.ring c)) :=
          hsi.hom_site_iso s K (omega s.ring c) hK ((hi false).omega_ctf s)
        have : IsIso (Sites.omegaBridge s.ring c) := (hbridges s).2
        have hω := Functor.map_isIso
          ((Sites.hom true s.ring X).obj (op ((Sites.nu s.ring X).obj K)))
          (Sites.omegaBridge s.ring c)
        exact @IsIso.comp_isIso _ _ _ _ _ _ _ hH hω
      closed_site := hse.closed_site
      omega_site := hse.omega_site
      hom_site := hse.hom_site
      dual_site := hse.dual_site }
  · intro s t a M _
    rfl
  · intro s t a
    rfl

end WeilConjectures.FiniteFreeCoefficients

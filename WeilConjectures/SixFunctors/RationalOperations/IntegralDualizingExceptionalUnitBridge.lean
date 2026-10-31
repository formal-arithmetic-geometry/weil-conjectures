/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
public import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import all WeilConjectures.SixFunctors.Integral.IntegralConstructibleReductionHom
import all WeilConjectures.SixFunctors.Compact.CompactSupportTermHomFinite
import Mathlib.CategoryTheory.CofilteredSystem

/-! Bridge theorem for the integral dualizing exceptional value.

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, first paragraph.
(blueprint: lem-sf-rational-dualizing-identification-integral-bridge).

The integral exceptional coefficient comparisons identify every finite reduction
with the corresponding dualizing term. Finite constructible Hom sets and Kőnig's
lemma supply a compatible family of isomorphisms. The intrinsic Roos/Milnor
reconstruction then lifts the family and its inverse to the integral category.
The conclusion concerns existence of an isomorphism of objects; no claim of
canonical compatibility of the initially constructed finite isomorphisms is needed.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Reduction from the smaller quotient represents the same Hom functor as
reduction to the larger quotient followed by scalar restriction. -/
private def reductionHomEquiv
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    (K : C) (P : B) : (Ln.obj K ⟶ P) ≃ (Lm.obj K ⟶ S.obj P) :=
  (an.homEquiv K P).trans
    ((Iso.homCongr (Iso.refl K) (e.app P).symm).trans (am.homEquiv K _).symm)

private theorem reductionHomEquiv_apply
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    (K : C) (P : B) (f : Ln.obj K ⟶ P) :
    reductionHomEquiv am an S e K P f =
      (am.homEquiv K _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K)) ≫ S.map f := by
  have h : (an.homEquiv K P f) ≫ e.inv.app P =
      (an.unit.app K ≫ e.inv.app (Ln.obj K)) ≫ Rm.map (S.map f) := by
    rw [an.homEquiv_unit, Category.assoc]
    simpa only [Category.assoc, Functor.comp_map] using
      congrArg (fun q ↦ an.unit.app K ≫ q) (e.inv.naturality f)
  change (am.homEquiv K (S.obj P)).symm
    (𝟙 K ≫ (an.homEquiv K P f) ≫ e.inv.app P) = _
  rw [Category.id_comp, h]
  exact am.homEquiv_naturality_right_symm _ _

private theorem reductionHomEquiv_comp
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    (K : C) {P Q : B} (f : Ln.obj K ⟶ P) (g : P ⟶ Q) :
    reductionHomEquiv am an S e K Q (f ≫ g) =
      reductionHomEquiv am an S e K P f ≫ S.map g := by
  simp only [reductionHomEquiv_apply, Functor.map_comp, Category.assoc]

/-- Descend an isomorphism by the universal property of derived reduction.
No choice of a finite exceptional counit enters this construction. -/
private noncomputable def descendIso
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    (K M : C) (f : Lm.obj K ≅ Lm.obj M) : Ln.obj K ≅ Ln.obj M := by
  let EK := reductionHomEquiv am an S e K
  let EM := reductionHomEquiv am an S e M
  let g := (EK (Ln.obj M)).symm (f.hom ≫ EM (Ln.obj M) (𝟙 _))
  let h := (EM (Ln.obj K)).symm (f.inv ≫ EK (Ln.obj K) (𝟙 _))
  have hg : EK (Ln.obj M) g = f.hom ≫ EM (Ln.obj M) (𝟙 _) :=
    (EK (Ln.obj M)).apply_symm_apply _
  have hh : EM (Ln.obj K) h = f.inv ≫ EK (Ln.obj K) (𝟙 _) :=
    (EM (Ln.obj K)).apply_symm_apply _
  refine ⟨g, h, ?_, ?_⟩
  · apply (EK (Ln.obj K)).injective
    rw [reductionHomEquiv_comp, hg, Category.assoc]
    rw [← reductionHomEquiv_comp, Category.id_comp, hh]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · apply (EM (Ln.obj M)).injective
    rw [reductionHomEquiv_comp, hh, Category.assoc]
    rw [← reductionHomEquiv_comp, Category.id_comp, hg]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem descendIso_fac
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    (K M : C) (f : Lm.obj K ≅ Lm.obj M) :
    (am.homEquiv K _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K)) ≫
        S.map (descendIso am an S e K M f).hom =
      f.hom ≫
        (am.homEquiv M _).symm (an.unit.app M ≫ e.inv.app (Ln.obj M)) := by
  rw [← reductionHomEquiv_apply]
  change reductionHomEquiv am an S e K (Ln.obj M)
    ((reductionHomEquiv am an S e K (Ln.obj M)).symm
      (f.hom ≫ reductionHomEquiv am an S e M (Ln.obj M) (𝟙 _))) = _
  rw [(reductionHomEquiv am an S e K (Ln.obj M)).apply_symm_apply,
    reductionHomEquiv_apply]
  rw [S.map_id, Category.comp_id]

/-- The proved Roos/Milnor argument of `integralConstructibleReductionHom`, with
only the successor compatibility that its proof actually uses. All auxiliary
facts come from that module through a private proof import. -/
private theorem successorReductionHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (K M : sfIntegralConstructibleCategory l E X)
    (f : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj K.obj ⟶
      (scalarReductionDerivedExtension l E X n).obj M.obj)
    (hf : ∀ n : ℕ,
      f (n + 1) ≫ normalizedDVRReductionTransition l E X D hl n.le_succ M.obj =
        normalizedDVRReductionTransition l E X D hl n.le_succ K.obj ≫
          (normalizedDVRRes l E X n.le_succ).map (f n)) :
    ∃! g : K.obj ⟶ M.obj,
      ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).map g = f n := by
  obtain ⟨hp, δ, hδ⟩ := M.property.1
  let := hp
  have hc : IsHomotopyLimit (sfIntegralReductionCone l E X M.obj) := by
    apply roos_isHomotopyLimit (δ := δ)
    change IsDerivedLimitTriangle
      (K := fun n ↦ (sfDerivedReductionRestricted l E X n).obj M.obj)
      (fun n ↦ (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op)
      M.obj (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app M.obj)) δ
    simpa only [sfIntegralReductionTower,
      Functor.ofOpSequence_map_homOfLE_succ] using hδ
  have (n : ℕ) : Finite
      (K.obj⟦(1 : ℤ)⟧ ⟶ (sfIntegralReductionTower l E X M.obj).obj (op n)) :=
    reduction_hom_finite D l hl E X K M n
  have hb := hc.bijective_milnorMap K.obj
  let a (n : ℕ) := (normalizedDVRIntegralAdjunction l E X n).homEquiv K.obj _ (f n)
  have ha (n : ℕ) : a (n + 1) ≫
      (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op = a n := by
    have ht : (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op =
        (sfDerivedReductionTransition l E X n).app M.obj :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [ht, intrinsic_transition_eq D l hl E X M.obj n]
    exact adjoint_compatible
      (normalizedDVRIntegralAdjunction l E X (n + 1))
      (normalizedDVRIntegralAdjunction l E X n)
      (normalizedDVRRes l E X n.le_succ)
      (normalizedDVRResCompletedComp.{u, u, u} l E X D hl n.le_succ)
      (f (n + 1)) (f n) (hf n)
  obtain ⟨g, hg⟩ := hb.surjective ⟨a, ha⟩
  change K.obj ⟶ M.obj at g
  have hgn (n : ℕ) : (scalarReductionDerivedExtension.{u, u} l E X n).map g = f n := by
    apply ((normalizedDVRIntegralAdjunction l E X n).homEquiv _ _).injective
    have hn := congrArg (fun z ↦ z.val n) hg
    change g ≫ (sfDerivedReductionUnit l E X n).app M.obj = a n at hn
    rw [Adjunction.homEquiv_unit]
    have hu := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g
    exact hu.symm.trans hn
  refine ⟨g, hgn, ?_⟩
  intro g' hg'
  apply hb.injective
  apply Subtype.ext
  funext n
  change g' ≫ (sfDerivedReductionUnit l E X n).app M.obj =
    g ≫ (sfDerivedReductionUnit l E X n).app M.obj
  change g' ≫ (normalizedDVRIntegralAdjunction l E X n).unit.app M.obj =
    g ≫ (normalizedDVRIntegralAdjunction l E X n).unit.app M.obj
  have hu := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g
  have hu' := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g'
  dsimp only [Functor.id_map, Functor.comp_map] at hu hu'
  rw [hu', hu, hg' n, hgn n]

omit [IsSeparated (X ↘ Spec (.of D.k))] in
include D hl in
private theorem reductionIsoFinite (F : FieldStage.{u} l)
    (K M : sfIntegralConstructibleCategory l F.carrier X) (n : ℕ) :
    Finite ((scalarReductionDerivedExtension l F.carrier X n).obj K.obj ≅
      (scalarReductionDerivedExtension l F.carrier X n).obj M.obj) := by
  let := RationalVerdier.units D l hl X
  obtain ⟨a, b, hab, hK⟩ := K.property.2
  obtain ⟨c, d, hcd, hM⟩ := M.property.2
  have hKt := (integral_residue_tor D l hl F.carrier X).1
    K.obj K.property a b hab (hK 0).2 n
  have hMt := (integral_residue_tor D l hl F.carrier X).1
    M.obj M.property c d hcd (hM 0).2 n
  have : Finite ((scalarReductionDerivedExtension l F.carrier X n).obj K.obj ⟶
      (scalarReductionDerivedExtension l F.carrier X n).obj M.obj) :=
    intrinsic_hom_finite D l hl F.carrier (n + 1) (Nat.succ_pos n) X _ _
      (hK n).1 (hM n).1 a b c d hKt hMt
  exact Finite.of_injective (fun e ↦ e.hom) (fun _ _ h ↦ Iso.ext h)

include D hl in
/-- Finite Hom sets allow independently existing finite isomorphisms to be made
compatible. Lift the resulting family and its inverse through the Roos triangle. -/
private theorem isoOfReductionIsos (F : FieldStage.{u} l)
    (K M : sfIntegralConstructibleCategory l F.carrier X)
    (hne : ∀ n : ℕ, Nonempty
      ((scalarReductionDerivedExtension l F.carrier X n).obj K.obj ≅
        (scalarReductionDerivedExtension l F.carrier X n).obj M.obj)) :
    Nonempty (K.obj ≅ M.obj) := by
  let I (n : ℕ) := (scalarReductionDerivedExtension l F.carrier X n).obj K.obj ≅
    (scalarReductionDerivedExtension l F.carrier X n).obj M.obj
  let π (n : ℕ) : I (n + 1) → I n :=
    descendIso (normalizedDVRIntegralAdjunction l F.carrier X (n + 1))
      (normalizedDVRIntegralAdjunction l F.carrier X n)
      (normalizedDVRRes l F.carrier X n.le_succ)
      (normalizedDVRResCompletedComp l F.carrier X D hl n.le_succ) K.obj M.obj
  let T : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (fun n ↦ ↾(π n))
  have (j : ℕᵒᵖ) : Finite (T.obj j) := reductionIsoFinite D l hl X F K M j.unop
  have (j : ℕᵒᵖ) : Nonempty (T.obj j) := hne j.unop
  obtain ⟨e, he⟩ := nonempty_sections_of_finite_cofiltered_system T
  have hseq (n : ℕ) : π n (e (op (n + 1))) = e (op n) := by
    have h := he (homOfLE n.le_succ).op
    dsimp only [T] at h
    rw [Functor.ofOpSequence_map_homOfLE_succ] at h
    exact h
  have hhom (n : ℕ) :
      (e (op (n + 1))).hom ≫
          normalizedDVRReductionTransition l F.carrier X D hl n.le_succ M.obj =
        normalizedDVRReductionTransition l F.carrier X D hl n.le_succ K.obj ≫
          (normalizedDVRRes l F.carrier X n.le_succ).map (e (op n)).hom := by
    rw [← hseq n]
    exact (descendIso_fac (normalizedDVRIntegralAdjunction l F.carrier X (n + 1))
      (normalizedDVRIntegralAdjunction l F.carrier X n)
      (normalizedDVRRes l F.carrier X n.le_succ)
      (normalizedDVRResCompletedComp l F.carrier X D hl n.le_succ)
      K.obj M.obj (e (op (n + 1)))).symm
  have hinv (n : ℕ) :
      (e (op (n + 1))).inv ≫
          normalizedDVRReductionTransition l F.carrier X D hl n.le_succ K.obj =
        normalizedDVRReductionTransition l F.carrier X D hl n.le_succ M.obj ≫
          (normalizedDVRRes l F.carrier X n.le_succ).map (e (op n)).inv := by
    apply (cancel_mono
      ((normalizedDVRRes l F.carrier X n.le_succ).map (e (op n)).hom)).1
    rw [Category.assoc, ← hhom n, Iso.inv_hom_id_assoc]
    rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [(normalizedDVRRes l F.carrier X n.le_succ).map_id, Category.comp_id]
  obtain ⟨f, hf, _⟩ := successorReductionHom D l hl F.carrier X K M
    (fun n ↦ (e (op n)).hom) hhom
  obtain ⟨g, hg, _⟩ := successorReductionHom D l hl F.carrier X M K
    (fun n ↦ (e (op n)).inv) hinv
  have idcoh (L : sfIntegralConstructibleCategory l F.carrier X) (n : ℕ) :
      𝟙 ((scalarReductionDerivedExtension l F.carrier X (n + 1)).obj L.obj) ≫
          normalizedDVRReductionTransition l F.carrier X D hl n.le_succ L.obj =
        normalizedDVRReductionTransition l F.carrier X D hl n.le_succ L.obj ≫
          (normalizedDVRRes l F.carrier X n.le_succ).map
            (𝟙 ((scalarReductionDerivedExtension l F.carrier X n).obj L.obj)) := by
    simp
  obtain ⟨_, _, hK⟩ := successorReductionHom D l hl F.carrier X K K (fun _ ↦ 𝟙 _) (idcoh K)
  obtain ⟨_, _, hM⟩ := successorReductionHom D l hl F.carrier X M M (fun _ ↦ 𝟙 _) (idcoh M)
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · apply (hK (f ≫ g) (fun n ↦ ?_)).trans (hK (𝟙 _) (by intro n; simp)).symm
    rw [Functor.map_comp, hf n, hg n, Iso.hom_inv_id]
  · apply (hM (g ≫ f) (fun n ↦ ?_)).trans (hM (𝟙 _) (by intro n; simp)).symm
    rw [Functor.map_comp, hg n, hf n, Iso.inv_hom_id]

/-- The object comparison at one positive coefficient level. Coherence of these
particular isomorphisms is unnecessary for the object-existence assertion. -/
private noncomputable def unitReduction
    (S : structureSystem l X D hl Ω) (F : FieldStage.{u} l)
    (U : C l Ω (Spec (.of D.k)) (.integral F))
    (eU : U.obj ≅ integralConstantCoefficientObject l F.carrier (Spec (.of D.k)))
    (n : ℕ) :
    (scalarReductionDerivedExtension l F.carrier X n).obj
      ((S.ring.operation (integralDualizingCompactification D X)
        (.integral F)).G.obj U).obj ≅ integralDualizingFiniteTerm l F.carrier D X n := by
  let N : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  let a := PurCompactSupport.reduction l F.carrier N N.pos
  let h : Allowed l (s := .integral F) (t := .finite F N) a := Allowed.reduction F N
  let c := integralDualizingCompactification D X
  let SX := S.ring.scalar (s := .integral F) (t := .finite F N) a h true
  let SY := S.ring.scalar (s := .integral F) (t := .finite F N) a h false
  letI := SX.commShift
  letI := SY.commShift
  let b := S.ring.comparison c (s := .integral F) (t := .finite F N) a h
  let V := (S.ring.operation c (.integral F)).G.obj U
  let r : (SY.functor.obj U).obj ≅ finiteConstantCoefficientObject l F.carrier
      (Spec (.of D.k)) n :=
    SY.realization.app U ≪≫
      (PurCompactSupport.finiteReductionIso l F.carrier (Spec (.of D.k)) n).app U.obj ≪≫
      (scalarReductionDerivedExtension l F.carrier (Spec (.of D.k)) n).mapIso eU ≪≫
      @asIso _ _ _ _ (constantCoefficientReductionMap l F.carrier (Spec (.of D.k)) n)
        ((integralConstantCoefficient_constructible l F.carrier (Spec (.of D.k)) D hl).2.2.2
          n).1
  exact (PurCompactSupport.finiteReductionIso l F.carrier X n).symm.app V.obj ≪≫
    (SX.realization.app V).symm ≪≫
    (RingStage.inclusion l Ω X (.finite F N)).mapIso (b.b.app U) ≪≫
    (S.ring.finiteRight c F N).app (SY.functor.obj U) ≪≫
    (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l F.carrier (n + 1))
      c).mapIso r

/-- Integral exceptional value of the canonical coefficient unit.
Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 1
(blueprint: lem-sf-rational-dualizing-identification-integral-bridge).

Proof: reduce the integral exceptional value using the coefficient comparison of S.
Its finite right realization and the reduction of hU identify it with the same
finite dualizing terms as w.omega. Descend isomorphisms between successive
reductions by the reduction/restriction adjunctions. Each isomorphism set is finite
by constructible Hom finiteness and nonempty by the preceding comparisons. Kőnig's
lemma gives a compatible family. Roos/Milnor reconstruction lifts its maps and
inverses; uniqueness proves the two inverse identities. The argument includes the
empty scheme and the first quotient (index zero means exponent one).
-/
theorem integralDualizing_exceptional_unit_bridge
    (S : structureSystem l X D hl Ω) (F : FieldStage.{u} l)
    (w : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
    (U : C l Ω (Spec (.of D.k)) (.integral F))
    (hU : Nonempty ((RingStage.inclusion l Ω (Spec (.of D.k)) (.integral F)).obj U ≅
      integralConstantCoefficientObject l F.carrier (Spec (.of D.k)))) :
    Nonempty ((RingStage.inclusion l Ω X (.integral F)).obj
      ((S.ring.operation (integralDualizingCompactification D X)
        (.integral F)).G.obj U) ≅ w.omega.obj) := by
  let := RationalVerdier.units D l hl X
  obtain ⟨eU⟩ := hU
  let V := (S.ring.operation (integralDualizingCompactification D X) (.integral F)).G.obj U
  have hV : sfIntegralConstructible l F.carrier X V.obj := by
    rw [(integral_residue_tor D l hl F.carrier X).2]
    exact V.property
  exact isoOfReductionIsos D l hl X F ⟨V.obj, hV⟩ w.omega
    (fun n ↦ ⟨unitReduction D l hl X Ω S F U eU n ≪≫ (w.reduction n).symm⟩)

end RationalOperations
end WeilConjectures

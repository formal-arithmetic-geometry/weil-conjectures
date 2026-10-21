/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Sheaf.CategoryTheory.PresheafTensorInternalHom

/-! # Sectionwise localization and sheafification of an internal ring

Source: Stacks Project, Modules on Sites, Tag 0EMC, lemma-simple-invert;
ordinary localization: Algebra, Tags 00CO and 00CP.
(blueprint: lem-sfb-ring-localization-sheafification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonoidalClosed TensorProduct
namespace CategoryTheory

attribute [instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable {C : Type u} [Category.{v} C]

/-- Fractions in the actual localization, including power torsion.
Source: Stacks Tags 00CO and 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationFraction {A : Type w} [CommRing A] (t r : A) (n : ℕ) :
    Localization.Away t :=
  Localization.mk r ⟨t ^ n, ⟨n, rfl⟩⟩

/-- The actual sectionwise localization presheaf; restrictions are localization maps.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationPresheaf (A : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := CommRingCat.of (Localization.Away (M := A.obj U) (t.val U))
  map {U V} f := CommRingCat.ofHom (IsLocalization.map (Localization.Away (M := A.obj V) (t.val V))
    (P := A.obj V) (R := A.obj U) (S := Localization.Away (M := A.obj U) (t.val U))
    (M := Submonoid.powers (t.val U : A.obj U))
    (T := Submonoid.powers (t.val V : A.obj V)) (A.map f).hom (by
    rintro x ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change (t.val V : A.obj V) ^ n = (A.map f).hom ((t.val U : A.obj U) ^ n)
    rw [map_pow]
    exact congrArg (fun a : A.obj V => a ^ n) (t.property f).symm))
  map_id U := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (R := A.obj U)
      (Submonoid.powers (t.val U : A.obj U))
    ext r
    simp
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (R := A.obj U)
      (Submonoid.powers (t.val U : A.obj U))
    ext r
    simp

/-- The canonical sectionwise map r ↦ r/1.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationPresheafUnit (A : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) : A ⟶ sfbLocalizationPresheaf A t where
  app U := CommRingCat.ofHom (algebraMap (A.obj U) (Localization.Away (M := A.obj U) (t.val U)))
  naturality U V f := by
    ext r
    simp [sfbLocalizationPresheaf]

/-- The presheaf consists of fractions with the stated power-torsion relation,
ring operations and restriction formula; no cancellation is used.
Source: Stacks Tags 00CO, 00CP and 0EMC
(blueprint: lem-sfb-ring-localization-sheafification).

Proof: apply the fraction description of def-weil-ring-localization-away at each
object. Every denominator is a power of t. Cross multiplication in localization
says that two fractions agree precisely after multiplication by another power of t.
The localization addition and multiplication formulas give the displayed operations.
For a restriction, lem-weil-pbc-localization-away-universal-property characterizes
its lift by the restriction on r/1 and sends the denominator to the same power of
the restricted section. It therefore gives the displayed fraction formula.
Identity and composition follow by the uniqueness clause of that same node. -/
theorem sfbLocalizationPresheaf_spec (A : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) :
    (∀ (U : Cᵒᵖ) (x : Localization.Away (M := A.obj U) (t.val U)),
      ∃ (r : A.obj U) (n : ℕ), x = sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n) ∧
    (∀ (U : Cᵒᵖ) (r r' : A.obj U) (n m : ℕ),
      sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n = sfbLocalizationFraction (@id (A.obj
          U) (t.val U)) r' m ↔
        ∃ k : ℕ, (@id (A.obj U) (t.val U)) ^ k * ((@id (A.obj U) (t.val U)) ^ m * r - (@id (A.obj
          U) (t.val U)) ^ n * r') = 0) ∧
    (∀ (U : Cᵒᵖ) (r r' : A.obj U) (n m : ℕ),
      sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n + sfbLocalizationFraction (@id (A.obj
          U) (t.val U)) r' m =
        sfbLocalizationFraction (@id (A.obj U) (t.val U)) ((@id (A.obj U) (t.val U)) ^ m * r +
          (@id (A.obj U) (t.val U)) ^ n * r') (n + m) ∧
      sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n * sfbLocalizationFraction (@id (A.obj
          U) (t.val U)) r' m =
        sfbLocalizationFraction (@id (A.obj U) (t.val U)) (r * r') (n + m)) ∧
    (∀ {U V : Cᵒᵖ} (f : U ⟶ V) (r : A.obj U) (n : ℕ),
      (sfbLocalizationPresheaf A t).map f (sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n) =
        sfbLocalizationFraction (t.val V) (A.map f r) n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U x
    induction x using Localization.induction_on with
    | H x =>
      obtain ⟨r, s, ⟨n, hn⟩⟩ := x
      exact ⟨r, n, congrArg (Localization.mk r) (Subtype.ext hn.symm)⟩
  · intro U r r' n m
    simp only [sfbLocalizationFraction, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists, Subtype.exists, Submonoid.mem_powers_iff]
    constructor
    · rintro ⟨c, ⟨k, rfl⟩, h⟩
      exact ⟨k, by rw [mul_sub, sub_eq_zero]; exact h⟩
    · rintro ⟨k, h⟩
      exact ⟨_, ⟨k, rfl⟩, by simpa only [mul_sub, sub_eq_zero] using h⟩
  · intro U r r' n m
    constructor
    · simp only [sfbLocalizationFraction, Localization.add_mk]
      congr 1
      · exact add_comm _ _
      · exact Subtype.ext (pow_add _ _ _).symm
    · simp only [sfbLocalizationFraction, Localization.mk_mul]
      congr 1
      exact Subtype.ext (pow_add _ _ _).symm
  · intro U V f r n
    change IsLocalization.map (R := A.obj U) (P := A.obj V)
      (S := Localization.Away (M := A.obj U) (t.val U))
      (Localization.Away (M := A.obj V) (t.val V))
      (M := Submonoid.powers (t.val U : A.obj U))
      (T := Submonoid.powers (t.val V : A.obj V))
      (A.map f).hom (by
        rintro x ⟨k, rfl⟩
        refine ⟨k, ?_⟩
        change (t.val V : A.obj V) ^ k = (A.map f).hom ((t.val U : A.obj U) ^ k)
        rw [map_pow]
        exact congrArg (fun a : A.obj V ↦ a ^ k) (t.property f).symm)
      (Localization.mk (S := Submonoid.powers (t.val U : A.obj U)) r
        ⟨(t.val U : A.obj U) ^ n, ⟨n, rfl⟩⟩) =
        Localization.mk (S := Submonoid.powers (t.val V : A.obj V)) (A.map f r)
          ⟨(t.val V : A.obj V) ^ n, ⟨n, rfl⟩⟩
    erw [Localization.mk_eq_mk', IsLocalization.map_mk', ← Localization.mk_eq_mk']
    congr 1
    apply Subtype.ext
    exact (map_pow _ _ _).trans (congrArg (fun a ↦ a ^ n) (t.property f))

variable (J : GrothendieckTopology C)

/-- The size assumption in the node supplies left exact abelian sheafification.
Source: Stacks, Sites, Tag 00W1; the sheafification used in Tag 0EMC
(blueprint: lem-sfb-ring-localization-sheafification).

Proof: use UnivLE to replace the site by a small equivalent category in universe w.
Apply GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian to abelian groups on
that small model and transport the left exact reflector along the equivalence,
as in hasSheafifyEssentiallySmallSite. Thus this is supplied by the size convention,
rather than an additional hypothesis of the localization theorem. -/
@[instance 20000] theorem sfbLocalization_hasSheafify [UnivLE.{max u v, w}] :
    HasSheafify J AddCommGrpCat.{w} := by
  have : UnivLE.{u, w} := UnivLE.trans.{u, max u v, w}
  have : UnivLE.{v, w} := UnivLE.trans.{v, max u v, w}
  have : Small.{w} C := UnivLE.small.{u, w} C
  have : LocallySmall.{w} C := ⟨fun X Y ↦ UnivLE.small.{v, w} (X ⟶ Y)⟩
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} := GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite J _

/-- Sheafification equivalences are stable under the tensor product of abelian presheaves.
Source: blueprint sk-def-sfb-sheaf-tensor, strong monoidality, applied in Stacks Tag 0EMC
(blueprint: lem-sfb-ring-localization-sheafification).

Proof: use the small-model end constructions in sk-def-sfb-sheaf-tensor. Its strong
symmetric monoidal comparison identifies sheafification of q tensor H with the tensor
of the sheafifications. If sheafification inverts q it therefore inverts q tensor H;
symmetry gives the other variable. This is exactly the two fields of IsMonoidal. -/
@[instance 20000] theorem sfbLocalization_monoidalLocalEquivalences [UnivLE.{max u v, w}] :
    (J.W (A := AddCommGrpCat.{w})).IsMonoidal := by
  have : UnivLE.{u, w} := UnivLE.trans.{u, max u v, w}
  have : UnivLE.{v, w} := UnivLE.trans.{v, max u v, w}
  have : Small.{w} C := UnivLE.small.{u, w} C
  have : LocallySmall.{w} C := ⟨fun X Y ↦ UnivLE.small.{v, w} (X ⟶ Y)⟩
  let h := presheaf_enrichedHoms_exist (C := C) (A := AddCommGrpCat.{w})
  let : ∀ F G : Cᵒᵖ ⥤ AddCommGrpCat.{w},
      Enriched.FunctorCategory.HasEnrichedHom AddCommGrpCat.{w} F G := h.1
  let : ∀ F G : Cᵒᵖ ⥤ AddCommGrpCat.{w},
      Enriched.FunctorCategory.HasFunctorEnrichedHom AddCommGrpCat.{w} F G := h.2
  infer_instance

/-- Sheafify the sectionwise localization as a commutative internal ring, using the
strong symmetric monoidal abelian sheafification functor.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationRingObject (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    CommMon (Sheaf J AddCommGrpCat.{max u v w}) := by
  let P := sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t
  let Q := P ⋙ forget₂ CommRingCat RingCat
  letI : IsCommMonObj (Q ⋙ forget₂ RingCat AddCommGrpCat.{max u v w}) :=
    Q.isCommMonObj_compForget₂ (fun U a b => @mul_comm (P.obj U) _ a b)
  exact (presheafToSheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj
    (CommMon.mk (Q ⋙ forget₂ RingCat AddCommGrpCat.{max u v w}))

/-- A morphism of internal commutative rings acts by ring homomorphisms on sections.
Source: Stacks Tag 00YV, and the section-ring reconstruction used in Tag 0EMC
(blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbRingSectionMap {R D : CommMon (Sheaf J AddCommGrpCat.{max u v w})}
    (f : R ⟶ D) : InternalAbelianSheafModule.sectionRings J R.X ⟶
      InternalAbelianSheafModule.sectionRings J D.X :=
  Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{max u v w}).functor.map
      ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.map f))
    InternalAbelianSheafModule.commMonToRing.{max u v w}

/-- The underlying abelian sheaf map into the sheafified localization.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationUnderlyingUnit (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    R.X ⟶ (sfbLocalizationRingObject.{u, v, w} J R t).X :=
  (asIso ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit.app R.X)).inv ≫
    (presheafToSheaf J AddCommGrpCat.{max u v w}).map
      (Functor.whiskerRight
        (sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{max u v w}))

private def ringPresheafAb (P : Cᵒᵖ ⥤ CommRingCat.{w}) :
    CommMon (Cᵒᵖ ⥤ AddCommGrpCat.{w}) := by
  let Q := P ⋙ forget₂ CommRingCat RingCat
  let : IsCommMonObj (Q ⋙ forget₂ RingCat AddCommGrpCat.{w}) :=
    Q.isCommMonObj_compForget₂ (fun U a b ↦ @mul_comm (P.obj U) _ a b)
  exact CommMon.mk (Q ⋙ forget₂ RingCat AddCommGrpCat.{w})

private def sectionToAb
    (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (P : Cᵒᵖ ⥤ CommRingCat.{max u v w})
    (f : InternalAbelianSheafModule.sectionRings J R.X ⟶ P) :
    (sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj R ⟶
      ringPresheafAb P := by
  let : MonObj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj R.X) :=
    ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj R).mon
  let : MonObj (ringPresheafAb P).X := (ringPresheafAb P).mon
  let h : ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj R).X ⟶
      (ringPresheafAb P).X := Functor.whiskerRight f
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{max u v w})
  have : IsMonHom h := by
    constructor
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      ext z
      obtain ⟨z⟩ := z
      change (f.app U).hom
        ((MonObj.one (X := (sheafToPresheaf J AddCommGrpCat.{max u v w}).obj R.X)).app U
          (ULift.up z)) = (z : P.obj U)
      rw [show (MonObj.one (X := (sheafToPresheaf J AddCommGrpCat.{max u v w}).obj R.X)).app U
          (ULift.up z) = z • (1 : (InternalAbelianSheafModule.sectionRings J R.X).obj U)
        from InternalAbelianSheafModule.sectionOne_zsmul _ U z]
      simp
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.toIntLinearMap_injective
      apply TensorProduct.ext'
      intro a b
      exact (f.app U).hom.map_mul a b
  exact CommMon.homMk (Mon.Hom.mk h)

private def abToSection
    (P : Cᵒᵖ ⥤ CommRingCat.{max u v w})
    (D : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (f : P ⟶ InternalAbelianSheafModule.sectionRings J D.X) :
    ringPresheafAb P ⟶
      (sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj D := by
  let : MonObj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj D.X) :=
    ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj D).mon
  let : MonObj (ringPresheafAb P).X := (ringPresheafAb P).mon
  let h : (ringPresheafAb P).X ⟶
      ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj D).X :=
    Functor.whiskerRight f
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{max u v w})
  have : IsMonHom h := by
    constructor
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      ext z
      obtain ⟨z⟩ := z
      change (f.app U).hom (z : P.obj U) =
        (MonObj.one (X := (sheafToPresheaf J AddCommGrpCat.{max u v w}).obj D.X)).app U
          (ULift.up z)
      rw [InternalAbelianSheafModule.sectionOne_zsmul]
      change (f.app U).hom (z : P.obj U) =
        z • (1 : (InternalAbelianSheafModule.sectionRings J D.X).obj U)
      simp
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.toIntLinearMap_injective
      apply TensorProduct.ext'
      intro a b
      exact (f.app U).hom.map_mul a b
  exact CommMon.homMk (Mon.Hom.mk h)

private def ringSheafificationLift
    (P : Cᵒᵖ ⥤ CommRingCat.{max u v w})
    (D : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (f : P ⟶ InternalAbelianSheafModule.sectionRings J D.X) :
    (presheafToSheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj
      (ringPresheafAb P) ⟶ D :=
  ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).mapCommMon.homEquiv _ _).symm
    (abToSection J P D f)

private def mapToSections
    (P : Cᵒᵖ ⥤ CommRingCat.{max u v w})
    (D : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (f : ringPresheafAb P ⟶
      (sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj D) :
    P ⟶ InternalAbelianSheafModule.sectionRings J D.X where
  app U := by
    let B := ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ
      AddCommGrpCat.{max u v w}).functor.obj
        ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj D)).obj U
    let : MonObj B.X := B.mon
    let : IsCommMonObj B.X := B.comm
    let : CommRing B.X := InternalAbelianSheafModule.commRing B.X
    let h : P.obj U →+ B.X := (f.hom.hom.app U).hom
    refine CommRingCat.ofHom (show P.obj U →+* B.X from
      { h with map_one' := ?_, map_mul' := ?_ })
    · have hh := ConcreteCategory.congr_hom
        (congr_app (IsMonHom.one_hom f.hom.hom) U) (ULift.up 1)
      change h ((1 : ℤ) : P.obj U) = (1 : B.X) at hh
      rw [Int.cast_one] at hh
      exact hh
    · intro a b
      exact ConcreteCategory.congr_hom
        (congr_app (IsMonHom.mul_hom f.hom.hom) U) (a ⊗ₜ[ℤ] b)
  naturality U V g := by
    apply CommRingCat.hom_ext
    ext x
    exact ConcreteCategory.congr_hom (f.hom.hom.naturality g) x

private def ringSheafificationSigma (P : Cᵒᵖ ⥤ CommRingCat.{max u v w}) :
    P ⟶ InternalAbelianSheafModule.sectionRings J
      ((presheafToSheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj
        (ringPresheafAb P)).X :=
  mapToSections J P _
    ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).mapCommMon.unit.app
      (ringPresheafAb P))

private theorem ringSheafificationSigma_apply
    (P : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (U : Cᵒᵖ) (x : P.obj U) :
    (ringSheafificationSigma J P).app U x =
      (toSheafify J (ringPresheafAb P).X).app U x := by
  change (((sheafificationAdjunction J AddCommGrpCat.{max u v w}).mapCommMon.unit.app
    (ringPresheafAb P)).hom.hom.app U) x = _
  simp [Adjunction.mapCommMon]

private theorem ringSheafificationLift_spec
    (P : Cᵒᵖ ⥤ CommRingCat.{max u v w})
    (D : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (f : P ⟶ InternalAbelianSheafModule.sectionRings J D.X) (U : Cᵒᵖ) (x : P.obj U) :
    (sfbRingSectionMap J (ringSheafificationLift J P D f)).app U
      ((toSheafify J (P ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat.{max u v w})).app U x) = f.app U x := by
  have h := congrArg (fun k ↦ k.hom.hom)
    (((sheafificationAdjunction J AddCommGrpCat.{max u v w}).mapCommMon.homEquiv
      (ringPresheafAb P) D).apply_symm_apply (abToSection J P D f))
  change toSheafify J _ ≫ (ringSheafificationLift J P D f).hom.hom.hom =
    Functor.whiskerRight f
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{max u v w}) at h
  exact ConcreteCategory.congr_hom (congr_app h U) x

private theorem ringSheafification_hom_ext
    (P : Cᵒᵖ ⥤ CommRingCat.{max u v w})
    (D : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (g g' : (presheafToSheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj
      (ringPresheafAb P) ⟶ D)
    (h : ∀ (U : Cᵒᵖ) (x : P.obj U),
      (sfbRingSectionMap J g).app U ((toSheafify J (ringPresheafAb P).X).app U x) =
        (sfbRingSectionMap J g').app U
          ((toSheafify J (ringPresheafAb P).X).app U x)) : g = g' := by
  apply CommMon.hom_ext
  apply ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _).injective
  ext U x
  exact h U x

/-- The canonical localization unit preserves the internal multiplication and unit.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification).

Proof: reconstruct the section rings of R by evaluating its multiplication on pure
 tensors and its unit on 1, as in def-weil-pbc-internal-abelian-sheaf-module-equivalence.
 The sectionwise algebra maps commute with restriction by the uniqueness in
 lem-weil-pbc-localization-away-universal-property and preserve multiplication and one.
 Strong monoidal sheafification from sk-def-sfb-sheaf-tensor sends this presheaf ring
 map to an internal ring map. The inverse sheafification counit is an internal ring
 isomorphism by the lifted monoidal sheafification adjunction. The forgetful functors
 reflect its invertibility. Their composite is the displayed map. -/
theorem sfbLocalizationUnderlyingUnit_isMonHom
    (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    IsMonHom (sfbLocalizationUnderlyingUnit.{u, v, w} J R t) := by
  let f := sectionToAb J R _
    (sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t)
  let c := (sheafificationAdjunction J AddCommGrpCat.{max u v w}).mapCommMon.counit.app R
  have hc : c.hom.hom =
      (sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit.app R.X := by
    simp [c, Adjunction.mapCommMon]
  have : IsIso c.hom := by
    have : IsIso ((Mon.forget _).map c.hom) := by
      change IsIso c.hom.hom
      rw [hc]
      infer_instance
    exact isIso_of_reflects_iso c.hom (Mon.forget _)
  have : IsIso c := by
    have : IsIso ((CommMon.forget₂Mon _).map c) := ‹IsIso c.hom›
    exact isIso_of_reflects_iso c (CommMon.forget₂Mon _)
  let g := inv c ≫ (presheafToSheaf J AddCommGrpCat.{max u v w}).mapCommMon.map f
  have hg : g.hom.hom = sfbLocalizationUnderlyingUnit J R t := by
    change (inv c).hom.hom ≫ _ = _
    have hi : (inv c).hom.hom = inv c.hom.hom :=
      (Functor.map_inv (CommMon.forget _) c)
    rw [hi]
    simp only [hc, sfbLocalizationUnderlyingUnit, asIso_inv]
    rfl
  rw [← hg]
  exact g.hom.isMonHom_hom

/-- The canonical internal ring map R → aP, with no chosen undetermined data.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationUnit (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    R ⟶ sfbLocalizationRingObject.{u, v, w} J R t := by
  letI := sfbLocalizationUnderlyingUnit_isMonHom.{u, v, w} J R t
  exact CommMon.homMk (Mon.Hom.mk (sfbLocalizationUnderlyingUnit.{u, v, w} J R t))

private theorem sectionMap_comp
    {R D E : CommMon (Sheaf J AddCommGrpCat.{max u v w})} (f : R ⟶ D) (g : D ⟶ E) :
    sfbRingSectionMap J (f ≫ g) = sfbRingSectionMap J f ≫ sfbRingSectionMap J g := by
  ext U x
  rfl

private theorem sectionMap_injective
    {R D : CommMon (Sheaf J AddCommGrpCat.{max u v w})} {f g : R ⟶ D}
    (h : sfbRingSectionMap J f = sfbRingSectionMap J g) : f = g := by
  apply CommMon.hom_ext
  apply Sheaf.hom_ext
  ext U x
  exact ConcreteCategory.congr_hom (congr_app h U) x

private theorem localizationUnit_sections
    (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    sfbRingSectionMap J (sfbLocalizationUnit J R t) =
      sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t ≫
        ringSheafificationSigma J
          (sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext r
  let i := Functor.whiskerRight
    (sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{max u v w})
  have hc : (asIso
      ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit.app R.X)).inv.hom =
      toSheafify J R.X.obj := by
    apply (cancel_mono
      ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit.app R.X).hom).1
    have he := congrArg (fun k ↦ k.hom)
      (asIso ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit.app R.X)).inv_hom_id
    exact he.trans
      ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).right_triangle_components R.X).symm
  change ((asIso
      ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit.app R.X)).inv.hom ≫
        sheafifyMap J i).app U r = _
  rw [hc]
  have h := ConcreteCategory.congr_hom (congr_app (toSheafify_naturality J i).symm U) r
  have hs := ringSheafificationSigma_apply J
    (sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) U
    ((sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t).app U r)
  exact h.trans hs.symm

private def localizationLift (A B : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) (f : A ⟶ B)
    (ht : ∀ U : Cᵒᵖ, IsUnit (f.app U (t.val U))) : sfbLocalizationPresheaf A t ⟶ B where
  app U := by
    let : IsLocalization.Away (R := A.obj U) (@id (A.obj U) (t.val U))
        (Localization.Away (M := A.obj U) (t.val U)) := Localization.isLocalization
    exact CommRingCat.ofHom
      (IsLocalization.Away.lift (R := A.obj U) (P := B.obj U)
        (S := Localization.Away (M := A.obj U) (t.val U))
        (g := (f.app U).hom) (@id (A.obj U) (t.val U)) (ht U))
  naturality U V g := by
    apply CommRingCat.hom_ext
    symm
    change (B.map g).hom.comp
      (IsLocalization.Away.lift (R := A.obj U)
        (S := Localization.Away (M := A.obj U) (t.val U)) (t.val U) (ht U)) =
      (IsLocalization.Away.lift (R := A.obj V)
        (S := Localization.Away (M := A.obj V) (t.val V)) (t.val V) (ht V)).comp
          ((sfbLocalizationPresheaf A t).map g).hom
    apply IsLocalization.ringHom_ext (S := Localization.Away (M := A.obj U) (t.val U))
      (R := A.obj U) (Submonoid.powers (t.val U : A.obj U))
    ext r
    change B.map g (IsLocalization.Away.lift (R := A.obj U)
      (S := Localization.Away (M := A.obj U) (t.val U)) (t.val U) (ht U)
      (algebraMap (A.obj U) (Localization.Away (M := A.obj U) (t.val U)) r)) =
        IsLocalization.Away.lift (R := A.obj V)
          (S := Localization.Away (M := A.obj V) (t.val V)) (t.val V) (ht V)
          ((sfbLocalizationPresheaf A t).map g
            (algebraMap (A.obj U) (Localization.Away (M := A.obj U) (t.val U)) r))
    simp only [IsLocalization.Away.lift_eq]
    have hg := ConcreteCategory.congr_hom
      ((sfbLocalizationPresheafUnit A t).naturality g) r
    symm at hg
    change (sfbLocalizationPresheaf A t).map g
      (algebraMap (A.obj U) (Localization.Away (M := A.obj U) (t.val U)) r) =
        algebraMap (A.obj V) (Localization.Away (M := A.obj V) (t.val V)) (A.map g r) at hg
    rw [hg, IsLocalization.Away.lift_eq]
    exact (ConcreteCategory.congr_hom (f.naturality g) r).symm

private theorem localizationLift_unit (A B : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) (f : A ⟶ B)
    (ht : ∀ U : Cᵒᵖ, IsUnit (f.app U (t.val U))) :
    sfbLocalizationPresheafUnit A t ≫ localizationLift A B t f ht = f := by
  ext U r
  let : IsLocalization.Away (R := A.obj U) (@id (A.obj U) (t.val U))
      (Localization.Away (M := A.obj U) (t.val U)) := Localization.isLocalization
  exact IsLocalization.Away.lift_eq
    (g := (f.app U).hom) (R := A.obj U)
    (S := Localization.Away (M := A.obj U) (t.val U))
    (@id (A.obj U) (t.val U)) (ht U) r

private theorem localization_hom_ext (A B : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) (f g : sfbLocalizationPresheaf A t ⟶ B)
    (h : sfbLocalizationPresheafUnit A t ≫ f = sfbLocalizationPresheafUnit A t ≫ g) :
    f = g := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  let f' : Localization.Away (M := A.obj U) (t.val U) →+* B.obj U := (f.app U).hom
  let g' : Localization.Away (M := A.obj U) (t.val U) →+* B.obj U := (g.app U).hom
  change f' = g'
  apply IsLocalization.ringHom_ext (R := A.obj U) (Submonoid.powers (t.val U : A.obj U))
  ext r
  exact ConcreteCategory.congr_hom (congr_app h U) r

/-- Sheafification of the sectionwise localization is the universal internal
commutative ring in which the given global section is invertible. Its underlying
section-ring sheaf is ring sheafification, normalized by the abelian sheafification
unit. The comparison with any other localization is the unique compatible isomorphism.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification).

Proof, following the node's six steps:
1. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence to recover section
rings by multiplication on pure tensors and evaluation of the unit at 1.
The monoidal-local-equivalence condition follows from the small-model enriched ends
of det-def-sfb-sheaf-tensor-presheaf and Mathlib's tensor--internal-hom adjunction.
Conversion of sectionwise ring maps to internal maps follows by testing on pure tensors
and on integer multiples of the unit; the reverse conversion uses the same equations.
2. Form the actual objectwise localization and its restrictions, using
lem-weil-pbc-localization-away-universal-property. The same uniqueness proves the
presheaf laws and naturality of r ↦ r/1; sfbLocalizationPresheaf_spec records the
fractions, relation and operations of def-weil-ring-localization-away.
3. Sheafify its internal commutative ring structure by the strong symmetric
monoidal abelian sheafification. The canonical unit is the sheafified r ↦ r/1
composed with the inverse counit. The compatible fractions 1/t give a global
inverse of its image of t. The first displayed equality is counit normalization.
4. For f:R→D inverting t, extend each f_U uniquely to the section localization
by lem-weil-pbc-localization-away-universal-property. Its value on r/t^n is
f_U(r)f_U(t)^(-n). Uniqueness on r/1 makes these extensions natural.
5. Apply Mathlib's Adjunction.mapCommMon to the monoidal sheafification adjunction
of def-weil-pbc-sheafification. Its Hom equivalence extends the presheaf ring map
uniquely, and its lifted unit has underlying map toSheafify. This
also proves the displayed ring-sheafification universal property for arbitrary
presheaf ring maps h. If two maps out of aP agree after the localization unit,
localization uniqueness makes their presheaf restrictions agree, and
sheafification uniqueness makes the maps equal.
6. Apply both localization universal properties to get maps aP→L and L→aP.
Their composites are identities by uniqueness, and the map aP→L is unique even
among all maps, hence among isomorphisms. No cancellation of t and no stalks or
enough-points assumption enter the argument. -/
theorem sfbRingLocalizationSheafification
    (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    (∀ (U : Cᵒᵖ) (r : (InternalAbelianSheafModule.sectionRings J R.X).obj U),
      (sfbRingSectionMap.{u, v, w} J (sfbLocalizationUnit.{u, v, w} J R t)).app U r =
        (toSheafify J
          ((sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) ⋙ forget₂
          CommRingCat RingCat ⋙
            forget₂ RingCat AddCommGrpCat.{max u v w})).app U
          ((sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t).app U
          r)) ∧
    (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J (sfbLocalizationUnit.{u, v, w} J R t)).app
          U (t.val U))) ∧
    (∀ (D : CommMon (Sheaf J AddCommGrpCat.{max u v w})) (f : R ⟶ D),
      (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J f).app U (t.val U))) →
        ∃! g : (sfbLocalizationRingObject.{u, v, w} J R t) ⟶ D, (sfbLocalizationUnit.{u, v, w} J R
          t) ≫ g = f) ∧
    (∀ (L : CommMon (Sheaf J AddCommGrpCat.{max u v w})) (j : R ⟶ L),
      (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J j).app U (t.val U))) →
      (∀ (D : CommMon (Sheaf J AddCommGrpCat.{max u v w})) (f : R ⟶ D),
        (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J f).app U (t.val U))) →
          ∃! g : L ⟶ D, j ≫ g = f) →
      ∃! γ : (sfbLocalizationRingObject.{u, v, w} J R t) ≅ L, (sfbLocalizationUnit.{u, v, w} J R
          t) ≫ γ.hom = j) ∧
    (∀ (D : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
      (h : (sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) ⟶
          InternalAbelianSheafModule.sectionRings J D.X),
      ∃! g : (sfbLocalizationRingObject.{u, v, w} J R t) ⟶ D,
        ∀ (U : Cᵒᵖ) (x : (sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X)
          t).obj U),
          (sfbRingSectionMap.{u, v, w} J g).app U
            ((toSheafify J
              ((sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) ⋙
          forget₂ CommRingCat RingCat ⋙
                forget₂ RingCat AddCommGrpCat.{max u v w})).app U x) = h.app U x) := by
  let A := InternalAbelianSheafModule.sectionRings J R.X
  let P := sfbLocalizationPresheaf A t
  let L := sfbLocalizationRingObject J R t
  let η := sfbLocalizationUnit J R t
  let σ := ringSheafificationSigma J P
  have hη : sfbRingSectionMap J η = sfbLocalizationPresheafUnit A t ≫ σ :=
    localizationUnit_sections J R t
  have hinv : ∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap J η).app U (t.val U)) := by
    intro U
    rw [hη]
    exact (IsLocalization.Away.algebraMap_isUnit (R := A.obj U)
      (S := Localization.Away (M := A.obj U) (t.val U)) (t.val U)).map (σ.app U).hom
  have hup : ∀ (D : CommMon (Sheaf J AddCommGrpCat.{max u v w})) (f : R ⟶ D),
      (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap J f).app U (t.val U))) →
        ∃! g : L ⟶ D, η ≫ g = f := by
    intro D f hf
    let h := localizationLift A (InternalAbelianSheafModule.sectionRings J D.X) t
      (sfbRingSectionMap J f) hf
    let g : L ⟶ D := ringSheafificationLift J P D h
    have hg : η ≫ g = f := by
      apply sectionMap_injective J
      rw [sectionMap_comp, hη]
      ext U r
      have hs := ringSheafificationSigma_apply J P U
        ((sfbLocalizationPresheafUnit A t).app U r)
      have hl := ringSheafificationLift_spec J P D h U
        ((sfbLocalizationPresheafUnit A t).app U r)
      have hu := ConcreteCategory.congr_hom
        (congr_app (localizationLift_unit A (InternalAbelianSheafModule.sectionRings J D.X)
          t (sfbRingSectionMap J f) hf) U) r
      exact (congrArg ((sfbRingSectionMap J g).app U) hs).trans (hl.trans hu)
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    apply ringSheafification_hom_ext J P D g' g
    have hh : σ ≫ sfbRingSectionMap J g' = σ ≫ sfbRingSectionMap J g := by
      apply localization_hom_ext A _ t
      rw [← Category.assoc, ← Category.assoc, ← hη,
        ← sectionMap_comp, ← sectionMap_comp, hg', hg]
    intro U x
    have hx := ConcreteCategory.congr_hom (congr_app hh U) x
    have hs := ringSheafificationSigma_apply J P U x
    exact ((congrArg ((sfbRingSectionMap J g').app U) hs).symm.trans hx).trans
      (congrArg ((sfbRingSectionMap J g).app U) hs)
  refine ⟨?_, hinv, hup, ?_, ?_⟩
  · intro U r
    rw [hη]
    exact ringSheafificationSigma_apply J P U _
  · intro M j hj hu
    obtain ⟨g, hg, huniq⟩ := hup M j hj
    obtain ⟨d, hd, _⟩ := hu L η hinv
    have hgd : g ≫ d = 𝟙 L := (hup L η hinv).unique
      (by rw [← Category.assoc, hg, hd]) (Category.comp_id η)
    have hdg : d ≫ g = 𝟙 M := (hu M j hj).unique
      (by rw [← Category.assoc, hd, hg]) (Category.comp_id j)
    refine ⟨⟨g, d, hgd, hdg⟩, hg, ?_⟩
    intro e he
    apply Iso.ext
    exact huniq e.hom he
  · intro D h
    refine ⟨ringSheafificationLift J P D h, ?_, ?_⟩
    · exact ringSheafificationLift_spec J P D h
    · intro g hg
      apply ringSheafification_hom_ext J P D
      intro U x
      exact (hg U x).trans (ringSheafificationLift_spec J P D h U x).symm

end CategoryTheory

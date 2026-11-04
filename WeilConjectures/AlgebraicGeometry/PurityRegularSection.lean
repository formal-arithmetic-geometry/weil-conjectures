/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.DualRank
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Regular sections and transverse direct sums

Source: Stacks Project, Tags 067M, 01WY, 01M2, 01LW and 01LX; purity blueprint,
localized top Chern class, statement and (L3) (blueprint: def-pur-regular-section).

The module starts with an actual global section of F. Its evaluation on the ordinary sheaf
dual defines the map to Spec Sym(F dual). The affine characterization determines this map
uniquely, so choosing it does not choose arbitrary geometric data. Regularity uses the actual
components in a frame, and transversality uses the concatenation of two such component lists.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry

/-- Evaluation at a global section, using the ordinary sheaf-Hom bidual map.
Source: Stacks Tag 01M2; purity section convention (blueprint: def-pur-regular-section). -/
def regularSectionEvaluation {T : Scheme.{u}} (F : T.Modules) (s : F.sections) :
    Scheme.Modules.dual F ⟶ SheafOfModules.unit T.ringCatSheaf :=
  SheafOfModules.homObjSectionsEquiv (Scheme.Modules.dual F)
    (SheafOfModules.unit T.ringCatSheaf)
    (SheafOfModules.sectionsMap (SheafOfModules.bidual (R := T.sheaf) F) s)

/-- Two sections of `p` agree after precomposition with `h` iff their affine-chart
components agree over every affine open (the charts being monomorphisms). -/
theorem comp_eq_comp_iff_of_affineCharts {S E W : Scheme.{u}} (p : E ⟶ S)
    {Y : S.affineOpens → Scheme.{u}}
    (chart : ∀ U : S.affineOpens, (p ⁻¹ᵁ U.1).toScheme ⟶ Y U)
    [∀ U, Mono (chart U)] (a b : S ⟶ E) (c c' : ∀ U : S.affineOpens, U.1.toScheme ⟶ Y U)
    (ha : ∀ U, ∃ aU : U.1.toScheme ⟶ (p ⁻¹ᵁ U.1).toScheme,
      aU ≫ (p ⁻¹ᵁ U.1).ι = U.1.ι ≫ a ∧ aU ≫ chart U = c U)
    (hb : ∀ U, ∃ bU : U.1.toScheme ⟶ (p ⁻¹ᵁ U.1).toScheme,
      bU ≫ (p ⁻¹ᵁ U.1).ι = U.1.ι ≫ b ∧ bU ≫ chart U = c' U) (h : W ⟶ S) :
    h ≫ a = h ≫ b ↔ ∀ U, h ∣_ U.1 ≫ c U = h ∣_ U.1 ≫ c' U := by
  constructor
  · intro e U
    obtain ⟨aU, ha₁, ha₂⟩ := ha U
    obtain ⟨bU, hb₁, hb₂⟩ := hb U
    have : h ∣_ U.1 ≫ aU = h ∣_ U.1 ≫ bU := by
      rw [← cancel_mono (p ⁻¹ᵁ U.1).ι, Category.assoc, Category.assoc, ha₁, hb₁,
        morphismRestrict_ι_assoc, morphismRestrict_ι_assoc, e]
    rw [← ha₂, ← hb₂, reassoc_of% this]
  · intro e
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨U, hU, hx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (h x))
    obtain ⟨aU, ha₁, ha₂⟩ := ha ⟨U, hU⟩
    obtain ⟨bU, hb₁, hb₂⟩ := hb ⟨U, hU⟩
    have : h ∣_ U ≫ aU = h ∣_ U ≫ bU := by
      rw [← cancel_mono (chart ⟨U, hU⟩), Category.assoc, Category.assoc, ha₂, hb₂]
      exact e ⟨U, hU⟩
    refine ⟨h ⁻¹ᵁ U, hx, ?_⟩
    rw [← morphismRestrict_ι_assoc, ← morphismRestrict_ι_assoc, ← ha₁, ← hb₁,
      reassoc_of% this]

namespace VectorBundleZeroSection

variable {S : Scheme.{u}} (M : S.Modules)

/-- Lift a linear form to the base. -/
def liftToBase (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) :
    SymmetricAlgebraSheaf.algebra M ⟶
      ((antiEquivalence S).functor.obj (op (baseObject S))).obj :=
  (exists_quasiCoherentSymmetricAlgebra_core S M
    ((antiEquivalence S).functor.obj (op (baseObject S))).obj φ).exists.choose

theorem liftToBase_sectionMap (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) (U : S.Opens)
    (a : SymmetricAlgebraSheaf.sections M (op U)) :
    (liftToBase M φ).right.hom.app (op U) (SymmetricAlgebraSheaf.sectionMap M (op U) a) =
      SymmetricAlgebra.lift (A := S.presheaf.obj (op U)) (φ.val.app (op U)).hom a := by
  have h := (exists_quasiCoherentSymmetricAlgebra_core S M
    ((antiEquivalence S).functor.obj (op (baseObject S))).obj φ).exists.choose_spec
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes]
      exact congrArg (fun q ↦ q.hom.app (op U) r) (Under.w (liftToBase M φ))
  | ι x =>
      rw [SymmetricAlgebra.lift_ι_apply]
      exact h U x
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]
variable [IsNoetherian S] (d : ℕ) [M.IsFiniteLocallyFreeOfRank d]

/-- Lift a linear form to the base. -/
def sectionOver (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) : baseObject S ⟶ over S d M :=
  ((antiEquivalence S).functor.preimage
    (((antiEquivalence S).counitIso.app (algebraObject S d M)).hom ≫
      ObjectProperty.homMk (liftToBase M φ))).unop

/-- Lift a linear form to the base. -/
def sectionOfForm (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) : S ⟶ scheme S d M :=
  (sectionOver M d φ).hom.left

theorem sectionOfForm_π (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) :
    sectionOfForm M d φ ≫ π S d M = 𝟙 S :=
  Over.w (sectionOver M d φ).hom

theorem sectionOver_map (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) :
    (antiEquivalence S).functor.map (sectionOver M d φ).op =
      ((antiEquivalence S).counitIso.app (algebraObject S d M)).hom ≫
        ObjectProperty.homMk (liftToBase M φ) :=
  (antiEquivalence S).functor.map_preimage _

set_option maxHeartbeats 1000000 in -- unfolding the anti-equivalence is slow
theorem sectionOfForm_appLE (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) (U : S.Opens) :
    (algebraIso S d M).hom.right.hom.app (op U) ≫
      (sectionOfForm M d φ).appLE ((π S d M) ⁻¹ᵁ U) U
        (by rw [← Scheme.Hom.comp_preimage, sectionOfForm_π]; simp) =
      (liftToBase M φ).right.hom.app (op U) := by
  have hn := congrArg (fun t ↦ t.hom.right.hom.app (op U)) (sectionOver_map M d φ)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Under.comp_right,
    TopCat.Sheaf.comp_app] at hn
  change (sectionOfForm M d φ).appLE ((π S d M) ⁻¹ᵁ U) U _ =
    ((antiEquivalence S).counitIso.app (algebraObject S d M)).hom.hom.right.hom.app (op U) ≫
      (liftToBase M φ).right.hom.app (op U) at hn
  have hc := congrArg (fun t ↦ t.hom.right.hom.app (op U))
    ((antiEquivalence S).counitIso.app (algebraObject S d M)).inv_hom_id
  simp only [ObjectProperty.FullSubcategory.comp_hom, Under.comp_right,
    TopCat.Sheaf.comp_app, ObjectProperty.FullSubcategory.id_hom, Under.id_right,
    TopCat.Sheaf.id_app] at hc
  change ((antiEquivalence S).counitIso.app (algebraObject S d M)).inv.hom.right.hom.app
    (op U) ≫ _ = _
  rw [hn, ← Category.assoc, hc, Category.id_comp]

set_option maxHeartbeats 1000000 in -- unfolding the anti-equivalence is slow
theorem sectionOfForm_affineChart (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf)
    (U : S.affineOpens) :
    (sectionOfForm M d φ).resLE ((π S d M) ⁻¹ᵁ U.1) U.1
        (by rw [← Scheme.Hom.comp_preimage, sectionOfForm_π]; simp) ≫ affineChart S d M U =
      U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (SymmetricAlgebra.lift (φ.val.app (op U.1)).hom).toRingHom) := by
  have hφ : CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap M (op U.1)) ≫
      (algebraIso S d M).hom.right.hom.app (op U.1) ≫
      (sectionOfForm M d φ).appLE ((π S d M) ⁻¹ᵁ U.1) U.1
        (by rw [← Scheme.Hom.comp_preimage, sectionOfForm_π]; simp) =
      CommRingCat.ofHom (SymmetricAlgebra.lift (φ.val.app (op U.1)).hom).toRingHom := by
    rw [sectionOfForm_appLE]
    apply CommRingCat.hom_ext
    exact RingHom.ext (liftToBase_sectionMap M φ U.1)
  change (sectionOfForm M d φ).resLE ((π S d M) ⁻¹ᵁ U.1) U.1 _ ≫
      ((π S d M) ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap M (op U.1)) ≫
          (algebraIso S d M).hom.right.hom.app (op U.1)) = _
  rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  simp only [← Spec.map_comp, Category.assoc] at hφ ⊢
  rw [hφ]
  rfl


set_option maxHeartbeats 1000000 in -- unfolding the anti-equivalence is slow
/-- The section of the vector bundle attached to a linear form `φ : M → O_S`, characterized
on affine charts by `SymmetricAlgebra.lift φ`. -/
theorem sectionOfForm_existsUnique (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) :
    ∃! f : {f : S ⟶ scheme S d M // f ≫ π S d M = 𝟙 S},
      ∀ U : S.affineOpens,
        ∃ fU : U.1.toScheme ⟶ ((π S d M) ⁻¹ᵁ U.1).toScheme,
          fU ≫ ((π S d M) ⁻¹ᵁ U.1).ι = U.1.ι ≫ f.val ∧
          fU ≫ affineChart S d M U =
            U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              (SymmetricAlgebra.lift (φ.val.app (op U.1)).hom).toRingHom) := by
  have hex (U : S.affineOpens) : ∃ fU : U.1.toScheme ⟶ ((π S d M) ⁻¹ᵁ U.1).toScheme,
      fU ≫ ((π S d M) ⁻¹ᵁ U.1).ι = U.1.ι ≫ sectionOfForm M d φ ∧
      fU ≫ affineChart S d M U =
        U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
          (SymmetricAlgebra.lift (φ.val.app (op U.1)).hom).toRingHom) :=
    ⟨_, Scheme.Hom.resLE_comp_ι _ _, sectionOfForm_affineChart M d φ U⟩
  refine ⟨⟨sectionOfForm M d φ, sectionOfForm_π M d φ⟩, hex, fun f hf ↦ Subtype.ext ?_⟩
  have hiso (U : S.affineOpens) : IsIso (affineChart S d M U) := (affineChart_spec S d M U).1
  have hmono (U : S.affineOpens) : Mono (affineChart S d M U) := inferInstance
  have key := comp_eq_comp_iff_of_affineCharts (π S d M)
    (Y := fun U ↦ Spec (.of (SymmetricAlgebraSheaf.sections M (op U.1))))
    (fun U ↦ affineChart S d M U) f.val (sectionOfForm M d φ) _ _ hf hex (𝟙 S)
  simpa using key.2 fun U ↦ rfl

end VectorBundleZeroSection

variable (P : WeilConjectures.PurityFiniteSetting.{u})
  (T : Scheme.{u}) (hT : T ⟶ Spec (CommRingCat.of P.field.k))
  [IsSeparated hT] [LocallyOfFiniteType hT] [QuasiCompact hT]

/-- E(F) is the canonical relative spectrum of Sym(F dual), with its canonical zero section.
Source: Stacks Tag 01M2 (blueprint: def-pur-regular-section). -/
def regularSectionBundle (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r] :
    PurityVectorBundle P T hT r where
  E := @VectorBundleZeroSection.scheme T (isNoetherian_of_locallyOfFiniteType hT) r
    (Scheme.Modules.dual F) (Scheme.Modules.isFiniteLocallyFreeOfRank_dual F r)
  p := @VectorBundleZeroSection.π T (isNoetherian_of_locallyOfFiniteType hT) r
    (Scheme.Modules.dual F) (Scheme.Modules.isFiniteLocallyFreeOfRank_dual F r)
  𝓔 := Scheme.Modules.dual F
  locallyFree := Scheme.Modules.isFiniteLocallyFreeOfRank_dual F r
  phi := Iso.refl _
  over_commutes := Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map into E(F) exists uniquely and has the evaluation ring map on every
relative-Spec affine chart. Source: Stacks Tags 01LW and 01LX
(blueprint: def-pur-regular-section).
Proof: extend evaluation by the symmetric-algebra universal property. The relative-Spec
anti-equivalence sends this algebra morphism to a morphism over T. Its affine-chart clause
identifies the restriction with Spec of SymmetricAlgebra.lift of evaluation, using the affine
symmetric-algebra comparison. Conversely these affine maps determine the morphism on a cover,
so uniqueness follows. -/
theorem regularSectionGeometric_existsUnique (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections) :
    ∃! f : {f : T ⟶ (regularSectionBundle P T hT F r).E //
        f ≫ (regularSectionBundle P T hT F r).p = 𝟙 T},
      ∀ U : T.affineOpens,
        ∃ fU : U.1.toScheme ⟶
            (((regularSectionBundle P T hT F r).p) ⁻¹ᵁ U.1).toScheme,
          fU ≫ (((regularSectionBundle P T hT F r).p) ⁻¹ᵁ U.1).ι = U.1.ι ≫ f.val ∧
          fU ≫ @VectorBundleZeroSection.affineChart T
            (isNoetherian_of_locallyOfFiniteType hT) r (Scheme.Modules.dual F)
              (Scheme.Modules.isFiniteLocallyFreeOfRank_dual F r) U =
            U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              ((SymmetricAlgebra.lift
                (((regularSectionEvaluation F s).val.app (op U.1)).hom)).toRingHom)) := by
  exact @VectorBundleZeroSection.sectionOfForm_existsUnique T
    (Scheme.Modules.dual F) (isNoetherian_of_locallyOfFiniteType hT) r
    (Scheme.Modules.isFiniteLocallyFreeOfRank_dual F r) (regularSectionEvaluation F s)

/-- The geometric section determined by dual evaluation, chosen from its unique affine
characterization, not from an unconstrained existence statement.
Source: Stacks Tags 01M2 and 01LX (blueprint: def-pur-regular-section). -/
def regularSectionGeometric (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : {f : T ⟶ (regularSectionBundle P T hT F r).E //
      f ≫ (regularSectionBundle P T hT F r).p = 𝟙 T} :=
  (regularSectionGeometric_existsUnique P T hT F r s).exists.choose

/-- The zero scheme is the fibre product of the evaluation section with the zero section.
Source: Stacks Tag 067M (blueprint: def-pur-regular-section). -/
def regularSectionZeroScheme (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : Scheme.{u} :=
  pullback (regularSectionGeometric P T hT F r s).val
    (regularSectionBundle P T hT F r).zeroSection

/-- The zero-scheme projection to the base.
Source: Stacks Tag 067M (blueprint: def-pur-regular-section). -/
def regularSectionZeroProjection (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : regularSectionZeroScheme P T hT F r s ⟶ T :=
  pullback.fst _ _

set_option backward.isDefEq.respectTransparency false in
/-- Regularity is regularity of the component germs in an actual local frame of F.
Source: Stacks Tags 067M and 01WY (blueprint: def-pur-regular-section). -/
def IsRegularSection (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : Prop :=
  ∀ x : regularSectionZeroScheme P T hT F r s,
    ∃ (U : T.affineOpens)
      (hx : regularSectionZeroProjection P T hT F r s x ∈ U.1)
      (b : Module.Basis (Fin r) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1))),
      RingTheory.Sequence.IsRegular
        (T.presheaf.stalk (regularSectionZeroProjection P T hT F r s x))
        (List.ofFn (fun i : Fin r ↦
          T.presheaf.germ U.1 (regularSectionZeroProjection P T hT F r s x) hx
            (b.repr (s.val (op U.1)) i)))

/-- The scheme-theoretic intersection is the pullback of the zero-scheme inclusions.
Source: Stacks Tag 067M; purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionIntersectionScheme (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : Scheme.{u} :=
  pullback (regularSectionZeroProjection P T hT F r s)
    (regularSectionZeroProjection P T hT G e t)

/-- The intersection projection.
Source: Stacks Tag 067M; purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionIntersectionProjection (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) :
    regularSectionIntersectionScheme P T hT F G r e s t ⟶ T :=
  pullback.fst _ _ ≫ regularSectionZeroProjection P T hT F r s

set_option backward.isDefEq.respectTransparency false in
/-- Transversality requires both sections regular and the concatenated actual components
regular in simultaneous frames at every intersection point.
Source: Stacks Tag 067M; purity (L3) (blueprint: def-pur-regular-section). -/
def IsTransverseDirectSum (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : Prop :=
  IsRegularSection P T hT F r s ∧ IsRegularSection P T hT G e t ∧
  ∀ x : regularSectionIntersectionScheme P T hT F G r e s t,
    ∃ (U : T.affineOpens)
      (hx : regularSectionIntersectionProjection P T hT F G r e s t x ∈ U.1)
      (b : Module.Basis (Fin r) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1)))
      (c : Module.Basis (Fin e) (T.presheaf.obj (op U.1)) (G.val.obj (op U.1))),
      RingTheory.Sequence.IsRegular
        (T.presheaf.stalk (regularSectionIntersectionProjection P T hT F G r e s t x))
        ((List.ofFn (fun i : Fin r ↦
          T.presheaf.germ U.1 (regularSectionIntersectionProjection P T hT F G r e s t x)
            hx (b.repr (s.val (op U.1)) i))) ++
          List.ofFn (fun j : Fin e ↦
            T.presheaf.germ U.1 (regularSectionIntersectionProjection P T hT F G r e s t x)
              hx (c.repr (t.val (op U.1)) j)))

set_option backward.isDefEq.respectTransparency false in
/-- The finite direct sum is the product module sheaf, whose section is the pair (s,t).
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSum {X : Scheme.{u}} (F G : X.Modules)
    (s : F.sections) (t : G.sections) : (F ⨯ G).sections :=
  (F ⨯ G).unitHomEquiv (prod.lift (F.unitHomEquiv.symm s) (G.unitHomEquiv.symm t))

/-- The direct sum of ranks r and e has rank r+e.
Source: purity (L3) (blueprint: def-pur-regular-section).
Proof: take simultaneous local frames and concatenate their bases. Their inverses are the
two coordinate projections. These simultaneous frame opens cover the base. -/
theorem regularSectionSum_rank {X : Scheme.{u}} (F G : X.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e] :
    (F ⨯ G).IsFiniteLocallyFreeOfRank (r + e) := by
  obtain ⟨I, U, hU, eU⟩ := SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u,
    u, u}.1 ‹F.IsFiniteLocallyFreeOfRank r›
  obtain ⟨J, V, hV, eV⟩ := SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u,
    u, u}.1 ‹G.IsFiniteLocallyFreeOfRank e›
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free (F ⨯ G)
    (fun p : I × J ↦ Scheme.Opens.ι (U p.1 ⊓ V p.2)) ?_ fun p ↦ ⟨?_⟩
  · simp only [Scheme.Opens.opensRange_ι]
    rw [← iSup_inf_iSup, (Opens.coversTop_iff _ _).1 hU, (Opens.coversTop_iff _ _).1 hV,
      inf_top_eq]
  · let W : X.Opens := U p.1 ⊓ V p.2
    have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.restrictFunctor W.ι) :=
      preservesColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback W.ι).symm
    exact (Scheme.Modules.restrictFunctor W.ι).mapIso
        ((biprod.isoProd F G).symm ≪≫ biprod.isoCoprod F G) ≪≫
      (PreservesColimitPair.iso (Scheme.Modules.restrictFunctor W.ι) F G).symm ≪≫
      coprod.mapIso (Scheme.Modules.nonempty_restrict_iso_free_of_le inf_le_left
          (eU p.1).some).some
        (Scheme.Modules.nonempty_restrict_iso_free_of_le inf_le_right (eV p.2).some).some ≪≫
      SheafOfModules.freeSumIso _ _ ≪≫
      SheafOfModules.freeFunctor.mapIso
        ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
          (finSumFinEquiv.trans Equiv.ulift.symm)).toIso

/-- The zero scheme of the actual paired section of the direct sum module.
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSumZeroScheme (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : Scheme.{u} :=
  @regularSectionZeroScheme P T hT _ _ _ (F ⨯ G) (r + e)
    (regularSectionSum_rank F G r e) (regularSectionSum F G s t)

/-- The paired zero-scheme projection.
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSumZeroProjection (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : regularSectionSumZeroScheme P T hT F G r e s t ⟶ T :=
  @regularSectionZeroProjection P T hT _ _ _ (F ⨯ G) (r + e)
    (regularSectionSum_rank F G r e) (regularSectionSum F G s t)

/-- The paired zero scheme is canonically the scheme-theoretic intersection, over the base.
Source: purity (L3), affine fibre products (blueprint: def-pur-regular-section).
Proof: in simultaneous frames both closed subschemes have quotient ring A/(a_i,b_j).
The intersection tensor product A/(a_i) tensor_A A/(b_j) maps to this quotient by
multiplication; a-bar maps inversely to a-bar tensor 1. These maps commute with projections.
Consequently the affine comparisons agree on overlaps and glue. As closed subschemes of T,
the comparison over T is unique. -/
theorem regularSectionSumZeroComparison_existsUnique (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) :
    ∃! i : regularSectionSumZeroScheme P T hT F G r e s t ≅
        regularSectionIntersectionScheme P T hT F G r e s t,
      i.hom ≫ regularSectionIntersectionProjection P T hT F G r e s t =
        regularSectionSumZeroProjection P T hT F G r e s t := by
  sorry

/-- The canonical comparison, determined by its commutation with the zero-scheme projections.
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSumZeroComparison (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) :
    regularSectionSumZeroScheme P T hT F G r e s t ≅
      regularSectionIntersectionScheme P T hT F G r e s t :=
  (regularSectionSumZeroComparison_existsUnique P T hT F G r e s t).exists.choose

end AlgebraicGeometry

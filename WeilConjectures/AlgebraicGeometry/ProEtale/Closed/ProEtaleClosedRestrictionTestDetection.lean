/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleSpecializationUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedLocalizationSequence
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Detecting closed restriction on affine boundary tests

Source: the closed-localization and sheaf-locality steps of
`lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A closed restriction is detected by affine weakly contractible tests all of whose
points specialize into the closed part. This statement concerns an arbitrary module
sheaf, with no proper morphism, derived functor, or injective object.

Source: parent boundary-restriction proof, Steps 1 and 3; Stacks Tags 098H,
09AG and 09AH, using the closed-localization cover of Tag 09C9.
(blueprint: lem-sp-proetale-closed-restriction-test-detection).

Proof: Let z be the closed complement, L its module inverse image, and P the
sectionwise direct image, with the adjunction supplied by ringed open-closed
localization. Prove N = P(L(M)) is zero. The existing localization cover refines
every site object into objects mapping to the open and affine weakly contractible
objects all of whose points specialize into the closed fibre. On an open object,
base change to the closed complement is empty, so the sheaf axiom makes N's
sections zero. On a boundary object, the specialization-unit theorem makes
M(W) to N(W) bijective, and the hypothesis makes its source zero. Sheaf
separatedness now makes every section of N zero. Apply L and the invertible
closed counit to deduce L(M) = 0. Finally tensor extension along the constant-ring
coefficient isomorphism is the inverse of scalar transport, hence preserves this
zero object. The existing cover and empty-site arguments include empty opens,
empty closed complements, and the zero coefficient ring. -/
theorem isZero_closedRestriction_of_boundary_tests
    (A : Type u) [CommRing A]
    {D E : Scheme.{u}} (i : E ⟶ D) [IsOpenImmersion i] [QuasiCompact i]
    (M : proEtaleRingModules D (proEtaleConstantRing D A))
    (htest : ∀ (W : D.ProEt), IsAffine W.left →
      (∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
        Epi e → Function.Surjective (e.hom.app (op W))) →
      (∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
        Specializes x ((pullback.fst W.hom i.closedComplement) z)) →
      IsZero (((SheafOfModules.evaluation
        ((sheafCompose (ProEt.topology D)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing D A)) (op W)) ⋙
              forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).obj M)) :
    IsZero ((proEtaleConstantRingPullback A i.closedComplement).obj M) := by
  let z := i.closedComplement
  let R := proEtaleConstantRing D A
  let U := ProEt.mk i
  let : IsOpenImmersion U.hom := ‹IsOpenImmersion i›
  let : QuasiCompact U.hom := ‹QuasiCompact i›
  have hU : Set.range U.hom = (Set.range z)ᶜ := by
    dsimp [U, z]
    rw [i.range_closedComplement, compl_compl]
    rfl
  obtain ⟨_, _, ai, _, hc, _, _, _, _, _, _, _, _, _⟩ :=
    proEtale_ringed_open_closed z U hU R
  let L := proEtaleModuleInverseImage z R
  let P := proEtaleRingedDirectImage z R
  let N := P.obj (L.obj M)
  have hN : IsZero N := by
    apply (IsZero.iff_id_eq_zero _).2
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = 0
    obtain ⟨I, V, f, hf, hV⟩ := localization_cover z U hU T.unop
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mp N.isSheaf)
    apply (hsh.isSheafFor_of_mem_precoverage hf).isSeparatedFor.ext
    rintro W g ⟨j⟩
    change N.val.map (f j).op x = N.val.map (f j).op 0
    have hzero : Subsingleton (N.val.obj (op (V j))) := by
      rcases hV j with hopen | ⟨hA, hw, hs⟩
      · obtain ⟨φ⟩ := hopen
        have hempty : IsEmpty ↥(pullback (V j).hom z) := by
          apply Scheme.isEmpty_pullback
          apply Set.disjoint_left.mpr
          rintro y ⟨v, rfl⟩ hy
          have hm : (V j).hom v ∈ Set.range U.hom :=
            ⟨φ.left v, congrArg (fun g : (V j).left ⟶ D ↦ g v)
              (MorphismProperty.Over.w φ)⟩
          rw [hU] at hm
          exact hm hy
        let : IsEmpty ((proEtaleBaseChange z).obj (V j)).left := hempty
        exact module_empty_sections _ (L.obj M) ((proEtaleBaseChange z).obj (V j))
      · let : IsAffine (V j).left := hA
        have hb := proEtale_module_unit_bijective_of_specialization
          z (V j) hw hs R ai M
        have hM : Subsingleton (M.val.obj (op (V j))) :=
          AddCommGrpCat.subsingleton_of_isZero (htest (V j) hA hw hs)
        refine ⟨fun a b ↦ ?_⟩
        obtain ⟨a, rfl⟩ := hb.2 a
        obtain ⟨b, rfl⟩ := hb.2 b
        exact congrArg ((ai.unit.app M).val.app (op (V j)))
          (@Subsingleton.elim _ hM a b)
    exact @Subsingleton.elim _ hzero _ _
  let : L.IsLeftAdjoint := ai.isLeftAdjoint
  let : IsIso (ai.counit.app (L.obj M)) := hc _
  have hL : IsZero (L.obj M) :=
    (L.map_isZero hN).of_iso (asIso (ai.counit.app (L.obj M))).symm
  let c := proEtaleConstantRingComparison z A
  let rc := (sheafCompose (ProEt.topology _)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence _ rc
  let adj := proEtaleRingExtensionAdjunction z R (proEtaleConstantRing _ A) c
  let t := adj.leftAdjointUniq e.symm.toAdjunction
  exact (e.inverse.map_isZero hL).of_iso (t.app _)

end AlgebraicGeometry.Scheme

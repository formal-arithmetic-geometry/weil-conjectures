/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective

/-! # A scalar-extension window independent of the target ring

Source: latest blueprint sk-lem-finite, integral Complement, common Tor interval
(blueprint: lem-sf-perfect-scalar-extension-window).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A bounded finite-projective representative gives one ordered Tor window for every
ordinary derived extension of scalars. No flatness or surjectivity of the ring map is
required.

Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
integral Complement, final sentence (blueprint: lem-sf-perfect-scalar-extension-window).

Proof: write P as Q(C), with C a bounded complex of finite projectives in [l,h].
Projective terms are flat and bounded flat complexes are K-flat, so the canonical
K-flat counit computes every derived extension on C. Extension of scalars preserves
finite projectivity, using the tensor-product base-change instances. It preserves
zero terms, so the extended complex is bounded in the very same interval [l,h].
Tensoring its flat terms with a degree-zero module gives that Tor interval. Enlarge
its lower endpoint to min l h to order the endpoints, including when C is zero and
l > h. Transport both properties through the counit and the given model isomorphism.
-/
theorem perfect_scalar_extension_window {R : Type u} [CommRing R]
    (P : DerivedCategory (ModuleCat.{u} R)) (hP : IsPerfectRingComplex P) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ (S : Type u) [CommRing S] (f : R →+* S),
      IsPerfectRingComplex ((ModuleCat.ordinaryDerivedExtendScalars f).obj P) ∧
      torAmplitudeIn _ a b ((ModuleCat.ordinaryDerivedExtendScalars f).obj P) := by
  obtain ⟨C, l, h, hl, hh, hC, ⟨e⟩⟩ := hP
  have := hl
  have := hh
  have hflat (i : ℤ) : ObjectProperty.flat (C.X i) := by
    have := (hC i).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  have hk := CochainComplex.kFlat_of_bounded_of_flat C l h hflat
  refine ⟨min l h, h, min_le_right _ _, ?_⟩
  intro S _ f
  let F := ModuleCat.extendScalars f
  let CS : CochainComplex (ModuleCat.{u} S) ℤ := (F.mapHomologicalComplex (.up ℤ)).obj C
  have hS (i : ℤ) : Module.Projective S (CS.X i) ∧ Module.Finite S (CS.X i) := by
    have := (hC i).1
    have := (hC i).2
    let := f.toAlgebra
    change Module.Projective S (TensorProduct R S (C.X i)) ∧
      Module.Finite S (TensorProduct R S (C.X i))
    exact ⟨inferInstance, inferInstance⟩
  have hsflat (i : ℤ) : ObjectProperty.flat (CS.X i) := by
    have := (hS i).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  have hSl : CS.IsStrictlyGE l := by dsimp [CS]; infer_instance
  have hSh : CS.IsStrictlyLE h := by dsimp [CS]; infer_instance
  have := hSl
  have := hSh
  have : IsIso ((ModuleCat.ordinaryDerivedChangeOfRings f).counit.app C) :=
    (ModuleCat.ordinaryDerivedChangeOfRings f).computes C hk
  let es : (ModuleCat.ordinaryDerivedExtendScalars f).obj P ≅ Q.obj CS :=
    (ModuleCat.ordinaryDerivedExtendScalars f).mapIso e ≪≫
      asIso ((ModuleCat.ordinaryDerivedChangeOfRings f).counit.app C)
  refine ⟨⟨CS, l, h, hSl, hSh, hS, ⟨es⟩⟩, ?_⟩
  apply (torAmplitudeIn (ModuleCat.{u} S) (min l h) h).prop_of_iso es.symm
  exact (torAmplitudeIn_Q_obj_of_flat CS l h hsflat).mono (min_le_left _ _) le_rfl

end DerivedCategory

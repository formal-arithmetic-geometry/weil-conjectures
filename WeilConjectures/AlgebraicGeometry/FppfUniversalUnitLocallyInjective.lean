/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.FppfSmallLocalRepresentatives

/-! Local injectivity from the small-valued universal property. -/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- Compare an individually specified small-valued sheafification with the
-- usual large-valued one. Smallness above makes the comparison reversible.
/-- A small-valued universal fppf sheafification map is locally injective.
Source: Stacks, Sites, Tags 00WB and 00WK, with the smallness bridge proved in
`fppf_small_of_local_representatives`. Shrink the standard large-valued
sheafification to a small-valued sheaf and factor its unit through the specified
universal map. Local injectivity of the standard unit passes to that map.
(blueprint: lem-trf-fppf-universal-unit-locally-injective). -/
theorem fppf_universal_unit_locally_injective {S : Scheme.{u}}
    (P : (Over S)ᵒᵖ ⥤ Type u) (F : Sheaf (fppfTopology.over S) (Type u))
    (η : P ⟶ F.obj)
    (hη : ∀ G : Sheaf (fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    Presheaf.IsLocallyInjective (fppfTopology.over S) η := by
  classical
  let J := fppfTopology.over S
  let P' := P ⋙ uliftFunctor.{u + 1}
  let Q : Sheaf J (Type (u + 1)) := (presheafToSheaf J _).obj P'
  let θ : P' ⟶ Q.obj := toSheafify J P'
  have : Presheaf.IsLocallySurjective J θ := inferInstance
  have hsmall : FunctorToTypes.Small.{u} Q.obj := fun T ↦
    fppf_small_of_local_representatives P Q θ T.unop
  let Q' : (Over S)ᵒᵖ ⥤ Type u := FunctorToTypes.shrink.{u} Q.obj
  let e (T : Over S) : Q.obj.obj (op T) ≃ Q'.obj (op T) := equivShrink _
  have he (T V : Over S) (f : T ⟶ V) (x : Q.obj.obj (op V)) :
      e T (Q.obj.map f.op x) = Q'.map f.op (e V x) := by
    simp [e, Q']
  have hQ' : Presheaf.IsSheaf J Q' :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (Presieve.isSheaf_of_nat_equiv e he
        ((isSheaf_iff_isSheaf_of_type _ _).mp Q.property))
  let θ' : P ⟶ Q' :=
    { app := fun T ↦ ↾fun p ↦ (equivShrink _) (θ.app T ⟨p⟩)
      naturality := by
        intro T V f
        ext p
        dsimp [Q', FunctorToTypes.shrink]
        rw [Equiv.symm_apply_apply]
        exact congrArg (equivShrink _) (NatTrans.naturality_apply θ f ⟨p⟩) }
  obtain ⟨l, hl⟩ := (hη ⟨Q', hQ'⟩).surjective θ'
  have hθ : Presheaf.IsLocallyInjective J θ := inferInstance
  have hθ' : Presheaf.IsLocallyInjective J θ' := by
    constructor
    intro T p q hpq
    have hpq' : θ.app T ⟨p⟩ = θ.app T ⟨q⟩ :=
      (equivShrink _).injective hpq
    have hc := Presheaf.equalizerSieve_mem J θ (X := T)
      (show P'.obj T from ULift.up p) (show P'.obj T from ULift.up q) hpq'
    apply J.superset_covering _ hc
    intro V f hf
    exact ULift.up_injective hf
  exact Presheaf.isLocallyInjective_of_isLocallyInjective_fac J hl

end AlgebraicGeometry.Scheme

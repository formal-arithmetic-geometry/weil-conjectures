/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorFlat
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.FlatPermanence

/-! # Pointwise flatness under base change

Source: Stacks Project, More on Morphisms, Tag 047C, clauses (1) and (2), specialized
to the structure sheaf (blueprint: lem-sfb-pointwise-flatness-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flatness at a point ascends under arbitrary base change and is reflected by base
change flat at the image point. There are no finiteness or Noetherian hypotheses.
Source: Stacks Project, More on Morphisms, Tag 047C, clauses (1) and (2), for the
structure sheaf (blueprint: lem-sfb-pointwise-flatness-base-change).

Proof:
1. Put x = a(x'), y' = f'(x'), y = f(x) = g(y'), and let R, A, B, C be the stalks
   of Y, X, Y', X' at these points. The actual stalk maps form a commutative square
   of local homomorphisms (def-pc-fibre-product, def-weil-flat-morphism). Set
   D = A tensor_R B. The canonical map D to C, restricting to the projection stalk
   maps, is flat by lem-pc-pullback-stalk-tensor-flat. We need no equality C = D.
2. For ascent, A is R-flat. By lem-weil-pbc-flat-module-base-change, B tensor_R A
   is B-flat. The tensor flip identifies it with D as a B-module. Its inverse is
   the reverse flip; balancing gives well-definedness, and the composites fix pure
   tensors. Since C is D-flat, lem-pc-module-flat-transitive makes C B-flat.
3. For reflection, B is R-flat, so lem-weil-pbc-flat-module-base-change makes D
   A-flat. By lem-pc-module-flat-transitive, C is A-flat. The map A to C is the
   actual local projection stalk map. Hence lem-weil-pbc-flat-local-hom-faithfully-flat
   makes C faithfully flat over A.
4. Also C is B-flat by hypothesis, so lem-pc-module-flat-transitive makes C R-flat.
   The R-actions through A and B agree by the stalk square. Apply
   lem-weil-pbc-flat-permanence to R to A and the A-module C: flatness over R and
   faithful flatness over A imply flatness of A over R, as required.
-/
theorem pointwise_flatness_base_change
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (x' : ↥(pullback f g)) :
    ((f.stalkMap ((pullback.fst f g) x')).hom.Flat →
      ((pullback.snd f g).stalkMap x').hom.Flat) ∧
    ((g.stalkMap ((pullback.snd f g) x')).hom.Flat →
      ((pullback.snd f g).stalkMap x').hom.Flat →
      (f.stalkMap ((pullback.fst f g) x')).hom.Flat) := by
  let R := Y.presheaf.stalk (f ((pullback.fst f g) x'))
  let A := X.presheaf.stalk ((pullback.fst f g) x')
  let B := Y'.presheaf.stalk ((pullback.snd f g) x')
  let C := (pullback f g).presheaf.stalk x'
  let ra : R →+* A := (f.stalkMap ((pullback.fst f g) x')).hom
  let e := Y.presheaf.stalkCongr (Inseparable.of_eq
    (congrArg (fun φ : pullback f g ⟶ Y ↦ φ x') pullback.condition))
  let rb : R →+* B := (g.stalkMap ((pullback.snd f g) x')).hom.comp e.hom.hom
  let ac : A →+* C := ((pullback.fst f g).stalkMap x').hom
  let bc : B →+* C := ((pullback.snd f g).stalkMap x').hom
  have hsquare : ac.comp ra = bc.comp rb := by
    have h := Scheme.Hom.stalkMap_congr_hom _ _
      (pullback.condition (f := f) (g := g)) x'
    simp only [Scheme.Hom.stalkMap_comp] at h
    exact congrArg CommRingCat.Hom.hom h
  let : Algebra R A := ra.toAlgebra
  let : Algebra R B := rb.toAlgebra
  let : Algebra A C := ac.toAlgebra
  let : Algebra B C := bc.toAlgebra
  let : Algebra R C := (ac.comp ra).toAlgebra
  have : IsScalarTower R A C := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R B C := .of_algebraMap_eq fun r ↦ RingHom.congr_fun hsquare r
  let bC : B →ₐ[R] C := ⟨bc, fun r ↦ (RingHom.congr_fun hsquare r).symm⟩
  let dc : TensorProduct R A B →ₐ[A] C := Algebra.TensorProduct.lift
    (Algebra.ofId A C) bC (fun _ _ ↦ Commute.all _ _)
  let : Algebra (TensorProduct R A B) C := dc.toRingHom.toAlgebra
  have hAC : dc.toRingHom.comp (algebraMap A (TensorProduct R A B)) = ac := by
    ext a
    change dc (TensorProduct.tmul R a 1) = ac a
    simp only [dc, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hBC : dc.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = bc := by
    ext b
    simp [dc, bC, Algebra.TensorProduct.lift_tmul]
  have hflat : Module.Flat (TensorProduct R A B) C :=
    pullback_stalk_tensor_flat g f x' rfl rfl hAC hBC
  have hd : dc.toRingHom.Flat := (RingHom.flat_algebraMap_iff).mpr hflat
  constructor
  · intro ha
    have : Module.Flat R A := ha
    have hi : (algebraMap B (TensorProduct R B A)).Flat :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    let ir : B →ₐ[R] TensorProduct R A B := Algebra.TensorProduct.includeRight
    have hi' : ir.toRingHom.Flat := by
      have heq : ir.toRingHom =
          (Algebra.TensorProduct.comm R B A).toRingHom.comp
            (algebraMap B (TensorProduct R B A)) := rfl
      rw [heq]
      exact hi.comp (.of_bijective (Algebra.TensorProduct.comm R B A).bijective)
    change bc.Flat
    rw [← hBC]
    exact hi'.comp hd
  · intro hb hc
    have hb' : rb.Flat :=
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e.hom)).comp hb
    have : Module.Flat R B := hb'
    have hi : (algebraMap A (TensorProduct R A B)).Flat :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    have hac : ac.Flat := by
      rw [← hAC]
      exact hi.comp hd
    have : Module.Flat A C := hac
    have : IsLocalHom (algebraMap A C) :=
      inferInstanceAs (IsLocalHom ((pullback.fst f g).stalkMap x').hom)
    have : Module.FaithfullyFlat A C := Module.FaithfullyFlat.of_flat_of_isLocalHom
    apply RingHom.flat_of_flat_module_of_faithfullyFlat_module (M := C) ra
    change (ac.comp ra).Flat
    rw [hsquare]
    exact hb'.comp hc

end AlgebraicGeometry

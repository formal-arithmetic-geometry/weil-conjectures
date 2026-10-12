/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Compatibility of the Cech model with the canonical flat cohomology comparison

Source: Stacks Project, Tags 02KH, 01XD and 02KE.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

/-- Identify categorical scalar extension with tensor using the given algebra action.
Source: Mathlib's definition of extendScalars and the algebra smul identity.
(blueprint: lem-pc-flat-cech-cohomology-square) -/
noncomputable def extendScalarsTensorIso (A : Type u) [AddCommGroup A] [Module R A] :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R A) ≅
      ModuleCat.of S (TensorProduct R S A) := by
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r s ↦ (@Algebra.smul_def R S _ _ _ r s).symm }
  let t := TensorProduct.congr e (LinearEquiv.refl R A)
  let eS : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R A) ≃ₗ[S]
      TensorProduct R S A :=
    { toEquiv := t.toEquiv
      map_add' := t.map_add
      map_smul' := by
        intro b x
        change t (b • x) = b • t x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul s a => rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  exact eS.toModuleIso

/-- The tensor identification is the identity on pure tensors.
Source: the defining tensor maps in Mathlib.
(blueprint: lem-pc-flat-cech-cohomology-square) -/
lemma extendScalarsTensorIso_hom_tmul (A : Type u) [AddCommGroup A] [Module R A]
    (b : S) (a : A) :
    (extendScalarsTensorIso (R := R) (S := S) A).hom
      (TensorProduct.tmul R b a) = TensorProduct.tmul R b a := by
  rfl

/-- Exact scalar extension commutes with the homology of the ordered Cech complex.
This uses only the three terms at the selected degree; boundedness is unnecessary.
Source: Mathlib `ShortComplex.mapHomologyIso`, as in Stacks Tag 02KH.
(blueprint: lem-pc-flat-tensor-complex-cohom) -/
noncomputable def flatCechHomologyIso [Module.Flat R S] (f : X ⟶ Spec (.of R))
    (U : ι → X.Opens) (M : X.Modules) (q : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).obj ((cechOver f U M).homology q) ≅
      (tensorCech (S := S) f U M).homology q := by
  have : (ModuleCat.extendScalars (algebraMap R S)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).left_adjoint_additive
  have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap R S)).leftAdjoint_preservesColimits
  have : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R S)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ((cechOver f U M).sc q).mapHomologyIso (ModuleCat.extendScalars (algebraMap R S)) |>.symm

/-- Leray identifications can be chosen so that any chain map with the canonical
pure-tensor formula induces the specified sheaf cohomology comparison. This is a
compatibility statement; it does not assert that the chain map is invertible.

Source: Stacks Project, Lemma 30.5.2 (Tag 02KH), separated-case paragraph;
Lemma 30.2.6 (Tag 01XD), and the canonical comparison of Tag 02KE.
(blueprint: lem-pc-flat-cech-cohomology-square)

Proof: Separatedness over an affine base makes the tuple intersections of U affine;
base change gives an affine-intersection cover on X_S. The pulled-back module is
quasi-coherent. Apply the Cech-to-sheaf comparison to these two covers. Affine
acyclicity makes the comparison maps isomorphisms. The Cech-to-sheaf edge maps
are natural for the inverse-image coefficient map induced by the module adjunction
unit: construct them from the augmented Cech double complexes of injective
resolutions, and use a resolution comparison for this coefficient map. On each
tuple intersection the map of augmentations is exactly the map specified by
IsCechBaseChange. Thus the resulting square commutes on cocycles and boundaries.
The scalar action on each comparison is induced by multiplication on the module,
so the first edge map is R-linear and the second S-linear. Restricting scalars from
global functions gives e and e'. Finally extend the original edge map to S tensor,
and use the canonical exact-tensor homology comparison flatCechHomologyIso.
On pure tensors b tensor x the composite is b times the inverse-image cohomology
map of the unit. This is the defining formula for H.baseChange; tensor induction
then gives the displayed equality. No invertibility of c is used in this argument.
The comparison is valid in degree zero, on the empty scheme, and for any flat
algebra including the zero ring. -/
theorem exists_cechBaseChange_cohomology_square [Module.Flat R S]
    (f : X ⟶ Spec (.of R)) [IsSeparated f] [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    (c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)) (hc : IsCechBaseChange f U M c) :
    ∃ e : (cechOver f U M).homology q ≅ ModuleCat.of R (HOver f M q),
    ∃ e' : (cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)).homology q ≅
          ModuleCat.of S (HOver (baseChangeSnd (S := S) f)
            (baseChangedModule (S := S) f M) q),
      (extendScalarsTensorIso (S := S) (HOver f M q)).inv ≫
        (ModuleCat.extendScalars (algebraMap R S)).map e.inv ≫
        (flatCechHomologyIso (S := S) f U M q).hom ≫
        HomologicalComplex.homologyMap c q ≫ e'.hom =
          ModuleCat.ofHom (H.baseChange (S := S) f M q) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

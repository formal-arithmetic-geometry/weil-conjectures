/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeApproximation

/-!
# Extension of finite-type quasi-coherent submodules

Source: Stacks Project, Properties, Lemma 01PF.
(blueprint: lem-weil-pbc-module-finite-type-submodule-extension).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

set_option maxHeartbeats 800000 in
-- Transporting generators and the image factorization need extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
/-- A finite-type quasi-coherent submodule on a quasi-compact open extends to the scheme.

Source: Stacks Project, Properties, Lemma 01PF.
(blueprint: lem-weil-pbc-module-finite-type-submodule-extension).

Proof:
1. Extend the prescribed inclusion using the quasi-coherent extension theorem 01PE(3),
   obtaining H, a map to F, and an isomorphism H restricted to U with G. The open
   immersion is quasi-compact because U is compact and X is quasi-separated.
2. Transport the finite local generators of G along the inverse isomorphism. Apply
   exists_finiteType_global_approximation to H: its finite-affine-cover induction
   uses exists_finiteType_affine_enlargement to obtain a quasi-coherent finite-type
   E with a monomorphism to H which restricts to an isomorphism on U.
3. Take the abelian image of the composite E to H to F. The image is quasi-coherent
   and finite type by quasiCoherent_cokernel_image and finiteType_image_extension.
   Over U the composite is the prescribed monomorphism preceded by an isomorphism.
   Its restricted factorization through the image is therefore monic, and it is
   epic because restriction preserves epimorphisms; hence it is an isomorphism.
4. Compose its inverse with the restriction E to H and the isomorphism to G.
   Cancel the restricted factorization through the image to prove that this
   isomorphism commutes with the inclusions into F restricted to U. -/
theorem exists_quasicoherent_finiteType_submodule_extension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    [G.IsQuasicoherent] [G.IsFiniteType]
    (ι : G ⟶ F.over U) [Mono ι] :
    ∃ (G' : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      G'.IsQuasicoherent ∧ G'.IsFiniteType ∧
        ∃ (ι' : G' ⟶ F), Mono ι' ∧ ∃ (e : G'.over U ≅ G),
          (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map ι' = e.hom ≫ ι := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨H, hH, ψ, α, hψ⟩ :=
    exists_quasiCoherent_extension_of_quasiCompact_open X U inferInstance F G ι
  have : H.IsQuasicoherent := hH
  have : (H.over U).IsFiniteType := by
    obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData G
    let q' : (H.over U).LocalGeneratorsData :=
      { I := q.I
        X := q.X
        coversTop := q.coversTop
        generators i := (q.generators i).ofEpi (α.inv.over (q.X i)) }
    have : q'.IsFiniteType :=
      { isFiniteType := fun i ↦ by
          have := hq.isFiniteType i
          exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType }
    exact { exists_localGeneratorsData := ⟨q', inferInstance⟩ }
  obtain ⟨E, hE, hEft, j, hj, hjU⟩ := exists_finiteType_global_approximation X U hU H
  have : E.IsQuasicoherent := hE
  have : E.IsFiniteType := hEft
  let r := j ≫ ψ
  let R := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U
  have : IsIso (R.map j) := hjU
  have hr : R.map r = (asIso (R.map j) ≪≫ α).hom ≫ ι := by
    change R.map (j ≫ ψ) = _
    rw [Functor.map_comp]
    change R.map j ≫ (SheafOfModules.overFunctor _ U).map ψ = _
    rw [hψ]
    rfl
  have : Mono (R.map r) := by rw [hr]; infer_instance
  have : Mono (R.map (Abelian.factorThruImage r)) :=
    mono_of_mono_fac (by rw [← Functor.map_comp, Abelian.image.fac])
  have : Epi (R.map (Abelian.factorThruImage r)) :=
    inferInstanceAs (Epi ((SheafOfModules.pushforward
      (F := Over.forget U) (𝟙 ((moduleRings X.toRingedSpace).over U))).map
        (Abelian.factorThruImage r)))
  have : IsIso (R.map (Abelian.factorThruImage r)) := isIso_of_mono_of_epi _
  have himg := quasiCoherent_cokernel_image r
  refine ⟨Abelian.image r, himg.2.2.2.2.2.2.2.1,
    (RingedSpace.finiteType_image_extension X.toRingedSpace).2.1 r,
    Abelian.image.ι r, inferInstance,
    (asIso (R.map (Abelian.factorThruImage r))).symm ≪≫ asIso (R.map j) ≪≫ α, ?_⟩
  apply (cancel_epi (R.map (Abelian.factorThruImage r))).1
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← Functor.map_comp, Abelian.image.fac, hr]
  simp

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of sections of modules on a scheme

The tensor product `M ⊗ N` of two `𝒪_X`-modules is the sheafification of the tensor product of
the underlying presheaves of modules (`SheafOfModules.tensorObjIsoSheafification`). Sections
`s ∈ Γ(M, U)` and `t ∈ Γ(N, U)` therefore have a tensor product `s ⊗ t ∈ Γ(M ⊗ N, U)`, the image
of `s ⊗ₜ t` under the sheafification map. It is bilinear and compatible with restriction, and the
tensor product of free generators is a free generator: on the presheaf level this is
`TensorProduct.bijective_smul_tmul`, and sheafification is locally injective and locally
surjective.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.tmulSection`: the tensor product `s ⊗ t` of sections.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.tmulSection`: the tensor product of free
  generators is a free generator.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

variable (M N) in
/-- The unit `M ⊗ₚ N ⟶ a(M ⊗ₚ N)` of the sheafification of the tensor product of the
underlying presheaves of modules. -/
noncomputable abbrev toSheafifyTensor :=
  (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app
    (M.val ⊗ N.val)

variable (M N) in
/-- The sheafification of the tensor product of the underlying presheaves of modules. -/
noncomputable abbrev sheafifyTensor : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)).obj (M.val ⊗ N.val)

/-- The tensor product `s ⊗ t ∈ Γ(M ⊗ N, U)` of sections `s ∈ Γ(M, U)` and `t ∈ Γ(N, U)`. -/
noncomputable def tmulSection {U : X.Opens} (s : Γ(M, U)) (t : Γ(N, U)) : Γ(M ⊗ N, U) :=
  Hom.app (SheafOfModules.tensorObjIsoSheafification M N).inv U
    ((toSheafifyTensor M N).app (op U) (s ⊗ₜ[Γ(X, U)] t))

lemma toSheafifyTensor_map {U V : X.Opens} (i : V ⟶ U) (x : (M.val ⊗ N.val).obj (op U)) :
    (sheafifyTensor M N).presheaf.map i.op ((toSheafifyTensor M N).app (op U) x) =
      (toSheafifyTensor M N).app (op V) ((M.val ⊗ N.val).map i.op x) :=
  (PresheafOfModules.naturality_apply (toSheafifyTensor M N) i.op x).symm

lemma toSheafifyTensor_smul {U : X.Opens} (r : Γ(X, U)) (x : (M.val ⊗ N.val).obj (op U)) :
    (toSheafifyTensor M N).app (op U) (r • x) = r • (toSheafifyTensor M N).app (op U) x :=
  ((toSheafifyTensor M N).app (op U)).hom.map_smul r x

lemma isFreeGenerator_toSheafifyTensor {U : X.Opens} {s : Γ(M, U)} {t : Γ(N, U)}
    (hs : IsFreeGenerator s) (ht : IsFreeGenerator t) :
    IsFreeGenerator (M := sheafifyTensor M N)
      ((toSheafifyTensor M N).app (op U) (s ⊗ₜ[Γ(X, U)] t)) := by
  have hP (W : X.Opens) (hW : W ≤ U) : Function.Bijective fun r : Γ(X, W) ↦
      r • (M.val ⊗ N.val).map (homOfLE hW).op (s ⊗ₜ[Γ(X, U)] t) :=
    TensorProduct.bijective_smul_tmul (hs W hW) (ht W hW)
  have hPmap {V W : X.Opens} (hV : V ≤ U) (i : W ⟶ V) :
      (M.val ⊗ N.val).map i.op ((M.val ⊗ N.val).map (homOfLE hV).op (s ⊗ₜ[Γ(X, U)] t)) =
        (M.val ⊗ N.val).map (homOfLE ((leOfHom i).trans hV)).op (s ⊗ₜ[Γ(X, U)] t) := by
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallyInjective
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  have hinj (V : X.Opens) (h : V ≤ U) : Function.Injective fun r : Γ(X, V) ↦
      r • (sheafifyTensor M N).presheaf.map (homOfLE h).op
        ((toSheafifyTensor M N).app (op U) (s ⊗ₜ[Γ(X, U)] t)) := by
    intro r r' hrr'
    dsimp only at hrr'
    rw [toSheafifyTensor_map, ← toSheafifyTensor_smul, ← toSheafifyTensor_smul] at hrr'
    have hS := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) (X := op V) _ _ hrr'
    refine Scheme.ext_of_mem hS fun Z l hl ↦ (hP Z ((leOfHom l).trans h)).1 ?_
    have : (M.val ⊗ N.val).map l.op (r • (M.val ⊗ N.val).map (homOfLE h).op
        (s ⊗ₜ[Γ(X, U)] t)) = (M.val ⊗ N.val).map l.op (r' • (M.val ⊗ N.val).map (homOfLE h).op
        (s ⊗ₜ[Γ(X, U)] t)) := hl
    rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul, hPmap] at this
    exact this
  refine isFreeGenerator_of_locally _ hinj fun V h q ↦ ?_
  refine ⟨_, Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) (U := op V) q,
    fun W i hi ↦ ?_⟩
  obtain ⟨x, hx⟩ := hi
  obtain ⟨a, rfl⟩ := (hP W ((leOfHom i).trans h)).2 x
  refine ⟨a, ?_⟩
  refine hx.symm.trans ?_
  change (toSheafifyTensor M N).app (op W) (a • _) = _
  rw [toSheafifyTensor_smul, toSheafifyTensor_map]

/-- **The tensor product of free generators is a free generator.** -/
lemma IsFreeGenerator.tmulSection {U : X.Opens} {s : Γ(M, U)} {t : Γ(N, U)}
    (hs : IsFreeGenerator s) (ht : IsFreeGenerator t) : IsFreeGenerator (tmulSection s t) :=
  (isFreeGenerator_toSheafifyTensor hs ht).app_hom
    (SheafOfModules.tensorObjIsoSheafification M N).symm

lemma tmulSection_map {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    (M ⊗ N).presheaf.map (homOfLE h).op (tmulSection s t) =
      tmulSection (M.presheaf.map (homOfLE h).op s) (N.presheaf.map (homOfLE h).op t) := by
  rw [tmulSection]
  refine (Hom.app_presheaf_map (SheafOfModules.tensorObjIsoSheafification M N).inv
    (homOfLE h) _).symm.trans ?_
  rw [toSheafifyTensor_map]
  rfl

lemma smul_tmulSection {U : X.Opens} (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmulSection (r • s) t = r • tmulSection s t := by
  rw [tmulSection, tmulSection, ← Hom.app_smul, ← toSheafifyTensor_smul]
  rfl

lemma tmulSection_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmulSection s (r • t) = r • tmulSection s t := by
  rw [tmulSection, tmulSection, ← Hom.app_smul, ← toSheafifyTensor_smul]
  congr 2
  exact TensorProduct.tmul_smul r s t

end AlgebraicGeometry.Scheme.Modules

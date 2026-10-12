/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.Algebra.Homology.KFlat

/-! # Total tensor complexes through the canonical affine chart

Source: Stacks Project, Tag 08DX(2), the underived total-complex comparison.
(blueprint: lem-pc-affine-chart-total-tensor).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance chartTotalTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Associated sheaf followed by canonical chart restriction commutes with total tensor.
Source: Stacks Project, Tag 08DX, lemma-quasi-coherence-tensor-product, proof of (2),
and Tag 01I8 for the underived associated-sheaf tensor identification.
(blueprint: lem-pc-affine-chart-total-tensor).

Proof: let C be tilde followed by restriction along X.toSpecΓ. The affine associated-
sheaf tensor comparison identifies C(U tensor V) with C(U) tensor C(V). Its defining
formula on pure tensors proves naturality in U and V; restriction has the same
naturality by its defining formula on restricted sections. The affine tilde functor
is a left adjoint, and open restriction preserves colimits, so C preserves the
coproduct indexed by all pairs (p,q) with p+q=n in each integer degree n. Combine the
tensor comparisons on these summands with the coproduct comparison. Naturality
identifies the first differentials and the signed second differentials. This gives
mutually inverse chain maps between C(Tot(P tensor N)) and Tot(C(P) tensor C(N)).
Take the inverse comparison to obtain the displayed orientation. This construction
uses no K-flatness, no localization, and no finiteness assumption; it also applies
to zero rings, zero complexes and an empty affine scheme. -/
theorem affineChart_totalTensor_iso (X : Scheme.{u}) [IsAffine X]
    (P N : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ) :
    letI : Functor.PreservesZeroMorphisms
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    letI : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
        ((curriedTensor _).obj F).PreservesZeroMorphisms :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
        SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
        (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
    let R := (Scheme.Modules.restrictFunctor X.toSpecΓ).mapHomologicalComplex (.up ℤ)
    Nonempty
      (CochainComplex.mapBifunctor (R.obj (T.obj P)) (R.obj (T.obj N))
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) ≅
      R.obj (T.obj (CochainComplex.mapBifunctor P N
        (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))))) := by
  sorry

end AlgebraicGeometry

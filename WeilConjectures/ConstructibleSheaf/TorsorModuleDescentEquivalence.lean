/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModuleComparisons
import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModuleFull
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModuleEssentialImage

/-!
# Descent equivalence for a connected finite torsor

For a connected finite Galois cover `c.P → V`, representations of the group over `𝔽_ℓ` are
equivalent to étale sheaves of modules on `V` whose pullback to `c.P` is constant.

## Implementation details

The functor sends a representation `N` to its associated sheaf of equivariant locally constant
`N`-valued functions on the pulled-back torsor (see `associatedModuleFunctor`). Diagonal
evaluation identifies its pullback with the constant sheaf, and the trivial rank-one
representation goes to the constant coefficient sheaf. Fullness and faithfulness use that, by
connectedness of `c.P`, a map of constant sheaves is a single linear map of values, which is
equivariant by compatibility with the descent data. Essential surjectivity recovers a
representation from a trivialization and its descent isomorphism; no finite-dimensionality is
needed.

## References

* [Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Representations are equivalent to all module sheaves trivialized by a connected
finite torsor. The underlying functor is additive, its pullback is naturally constant,
and the trivial rank-one representation descends to the coefficient sheaf. -/
theorem Scheme.GaloisCover.exists_module_descent_equivalence
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P] :
    let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
    let D : ObjectProperty (Sheaf V.smallEtaleTopology C) := fun F ↦
      ∃ A : C, Nonempty ((c.π)^*[C].obj F ≅
        (constantSheaf c.P.smallEtaleTopology C).obj A)
    ∃ E : Rep.{u + 1} (ZMod ℓ) P ≌ D.FullSubcategory,
      let T := E.functor ⋙ D.ι
      T.Additive ∧
      Nonempty (T ⋙ (c.π)^*[C] ≅
        forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
          ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ⋙
          constantSheaf c.P.smallEtaleTopology C) ∧
      Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
        (constantSheaf V.smallEtaleTopology C).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  classical
  dsimp only
  let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let D : ObjectProperty (Sheaf V.smallEtaleTopology C) := fun F ↦
    ∃ A : C, Nonempty ((c.π)^*[C].obj F ≅
      (constantSheaf c.P.smallEtaleTopology C).obj A)
  let T := c.associatedModuleFunctor ℓ
  obtain ⟨⟨eπ⟩, hunit⟩ := c.associatedModuleFunctor_comparisons ℓ P
  let _ : T.Full := c.associatedModuleFunctor_full ℓ P
  obtain ⟨x⟩ := ‹ConnectedSpace c.P›.toNonempty
  let Φ := c.P.uliftPointSmallEtale x
  let _ : (constantSheaf c.P.smallEtaleTopology C).Faithful :=
    Functor.Faithful.of_comp_iso (Φ.constantSheafCompSheafFiberIso _ C)
  let _ : (T ⋙ (c.π)^*[C]).Faithful := Functor.Faithful.of_iso eπ.symm
  let _ : T.Faithful := Functor.Faithful.of_comp T (c.π)^*[C]
  have hT : ∀ N, D (T.obj N) := fun N ↦
    ⟨_, ⟨eπ.app N⟩⟩
  let L := D.lift T hT
  have hess : L.EssSurj := by
    constructor
    intro F
    obtain ⟨A, hA⟩ := F.property
    obtain ⟨N, ⟨e⟩⟩ := c.associatedModuleFunctor_essentialImage ℓ P F.obj A hA
    exact ⟨N, ⟨D.isoMk e⟩⟩
  let _ : L.EssSurj := hess
  let _ : L.IsEquivalence := {}
  let E := L.asEquivalence
  refine ⟨E, ?_, ?_, ?_⟩
  · change (L ⋙ D.ι).Additive
    exact Functor.additive_of_iso (D.liftCompιIso T hT).symm
  · exact ⟨eπ⟩
  · exact hunit

end AlgebraicGeometry

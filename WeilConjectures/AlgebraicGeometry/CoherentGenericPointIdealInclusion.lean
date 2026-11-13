/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.CoherentGenericPointClosedDescent
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericIdealMap
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentLocalIsomorphism
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A coherent ideal inclusion near a generic point

Stacks Project, Tag 01YE.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry
namespace Scheme
namespace Modules
noncomputable section

/-- Closed pushforward preserves invertibility of a stalk map at a source point. -/
private theorem pushforward_stalk_isIso {X Z : Scheme.{w}} (i : Z ⟶ X)
    [IsClosedImmersion i] {A B : Z.Modules} (χ : A ⟶ B) (z : Z)
    [IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).map χ)] :
    IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base z)).map
      ((pushforward i).map χ)) := by
  have hA := closedImmersion_pushforward_stalks i i.isClosedEmbedding A
  have hB := closedImmersion_pushforward_stalks i i.isClosedEmbedding B
  let cA := ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base A.presheaf z)
  let cB := ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base B.presheaf z)
  let f := (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base z)).map
    ((pushforward i).map χ)
  let g := (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).map χ
  have hca : Function.Bijective cA := (hA.2.1 z).1
  have hcb : Function.Bijective cB := (hB.2.1 z).1
  have hg : Function.Bijective g := ConcreteCategory.bijective_of_isIso g
  have comm (a) : cB (f a) = g (cA a) := by
    exact congr($(hA.2.2 B χ z) a)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hca.1
      apply hg.1
      rw [← comm, ← comm, hab]
    · intro b
      obtain ⟨a, ha⟩ := hg.2 (cB b)
      obtain ⟨a', ha'⟩ := hca.2 a
      refine ⟨a', hcb.1 ?_⟩
      rw [comm, ha', ha]
  exact (ConcreteCategory.isIso_iff_bijective f).mpr hf

/-- A coherent module whose generic stalk is killed by the ambient maximal ideal contains
an injective pushforward of a finite direct sum of a coherent ideal on the integral closed
subscheme, and this inclusion is an isomorphism on an ambient neighbourhood of that point.
(Stacks, Tag 01YE). -/
theorem coherent_generic_point_ideal_inclusion {X Z : Scheme.{w}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules)
    (hF : AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace F)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ x : (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint Z))).obj F,
        a • x = 0) :
    ∃ (r : ℕ) (I : Z.IdealSheafData),
      AlgebraicGeometry.RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      ∃ (α : (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⟶ F),
        Mono α ∧
        ∃ (W : X.Opens), i.base (genericPoint Z) ∈ W ∧
          IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W).map α)
    := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  obtain ⟨G, hG, β, hβ, hβstalk⟩ := coherent_generic_point_closed_descent i F hF hkill
  obtain ⟨r, I, hI, hsum, χ, hχ, hχstalk⟩ := coherent_integral_generic_ideal_map Z G hG
  have : Mono β := hβ
  have : Mono χ := hχ
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
    (i.base (genericPoint Z))).map β) := hβstalk
  have : IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace
    (genericPoint Z)).map χ) := hχstalk
  let α := (pushforward i).map χ ≫ β
  have : Mono α := inferInstance
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map ((pushforward i).map χ)) :=
    pushforward_stalk_isIso i χ (genericPoint Z)
  have hαstalk : Function.Bijective ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map α) := by
    dsimp only [α]
    rw [Functor.map_comp]
    exact ConcreteCategory.bijective_of_isIso _
  have hsource := (isCoherent_pushforward_of_isFinite i _ hsum).1
  obtain ⟨W, hW, hαW⟩ :=
    (coherent_local_isomorphism X F _ hF hsource α (i.base (genericPoint Z))).2.2.2 hαstalk
  exact ⟨r, I, hI, α, inferInstance, W, hW, hαW⟩

end
end Modules
end Scheme
end AlgebraicGeometry

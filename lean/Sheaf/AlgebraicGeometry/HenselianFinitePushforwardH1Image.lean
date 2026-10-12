/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift
import Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1

/-!
# Images of finite constant pushforwards in restricted injectives

Source: Stacks Project, proof of Lemma 0A5H, finite-pushforward lifting argument; Lemma 0A48.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A class from a finite pushforward of a finite constant module sheaf has zero image
in the restriction of an injective module sheaf on a proper henselian scheme.

Source: Stacks Project, proof of Lemma 0A5H, finite-pushforward lifting argument;
Lemmas 0A48 and 03FD.
(blueprint: lem-weil-pbc-henselian-finite-pushforward-h1-image)

Proof: Form V₀ = V ×[Y] Y₀. Its map h₀ to Y₀ is finite, and V is proper over A,
since h is finite and Y is proper. Finite underived base change identifies i⁻¹h_*M
with h₀_*i_V⁻¹M. Inverse image preserves constant sheaves. The edge maps for h and
h₀ identify their pushforward cohomology with cohomology on V and V₀. Finite étale
lifting over the proper henselian scheme V identifies finite M-torsors on V and V₀;
thus H¹(V,M) → H¹(V₀,M) is bijective. Compatibility of the edge maps with base
change now shows that every class x on Y₀ lifts to a class z on Y in H¹(h_*M).
Naturality for ψ identifies its restricted image with the restriction of H¹(ψ)(z).
The underlying abelian sheaf of an injective module sheaf is cohomologically acyclic
(03FD), so H¹(ψ)(z) = 0. Additivity of restriction gives the desired zero image.
All forgetful identifications are natural: direct image is computed sectionwise,
while inverse image commutes with forgetting modules by exact sheafification.
The argument also covers the empty V and the zero module M. -/
theorem finite_pushforward_H_one_image_eq_zero_of_henselianLocalRing
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (i : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (sq : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    {V : Scheme.{u}} (h : V ⟶ Y) [IsFinite h] [LocallyOfFinitePresentation h]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (ψ : (h)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf V.smallEtaleTopology _).obj M) ⟶ J)
    (x : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj
        ((h)_*[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf V.smallEtaleTopology _).obj M)))) 1) :
    Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map ψ)) 1 x = 0 := by
  obtain ⟨z, hz⟩ := finite_pushforward_H_one_lift_of_henselianLocalRing f i f₀ sq Λ J h M ψ x
  have hzero : Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).map ψ) 1 z = 0 :=
    @Subsingleton.elim _ (subsingleton_H_one_of_injective_module_sheaf Y Λ J) _ _
  rw [hz, hzero, map_zero]
  simp

end AlgebraicGeometry.Etale

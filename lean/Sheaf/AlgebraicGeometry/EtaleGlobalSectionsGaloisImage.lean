/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
import Sheaf.FieldTheory.GaloisAutomorphismExtension

/-!
# Global sections under the abelian Galois stalk equivalence

Source: Stacks Project, Etale Cohomology, Tag 04JM, lemma-global-sections-point.
(blueprint: lem-sc-etale-global-sections-galois-invariants).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The image of the canonical terminal germ map is precisely the invariant subgroup.

Source: Stacks Project, Tags 04JM and 04JQ.
(blueprint: aux-etale-global-sections-image).

Proof: A terminal section has the same germ after any change of lift, because
there is only one lift to a terminal object. Extend each Galois automorphism to
Omega and apply the action compatibility hypothesis to obtain invariance.
Conversely, represent an invariant germ on a finite separable extension inside
Ks: shrink an etale neighbourhood to the finite connected component containing
the geometric point. Enlarge to a finite Galois extension L/K. Restriction on
connected pointed neighbourhoods is injective by sheaf separatedness, since a
further nonempty etale neighbourhood covers the connected field spectrum.
Thus invariance of the germ implies that its representative over L is fixed
by Gal(L/K). The sheaf equalizer for the finite Galois cover Spec L of Spec K
then descends that representative to a terminal section. Its germ is the given
one. This argument only uses finite separable subextensions, so it also applies
when Omega contains transcendental elements. -/
theorem etaleGlobalSections_galoisInvariants_image
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (T : (Spec (.of K)).Etale) (hT : Limits.IsTerminal T)
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber)
    (hi : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
      (i.hom.app F) ((E.functor.obj F).obj.ρ g
        ((i.inv.app F) ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z)
    (x : (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj T)
    : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (v : (E.functor.obj F).obj.V),
      v ∈ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
        (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ) ↔
      ∃ z : F.obj.obj (op T),
      (i.inv.app F) ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber T x F.obj z) = v := by
  sorry

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.FieldTheory.Galois.Profinite
import Sheaf.AlgebraicGeometry.GaloisStalkFiniteActionRealization
import Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct

/-!
# Essential surjectivity of the canonical Galois stalk functor

Source: Stacks Project, Tags 03QT and 03QR.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 03QT, theorem-equivalence-sheaves-point, proof;
Tag 03QR, the etale-scheme/Galois-set equivalence used there.
(blueprint: lem-exc-galois-stalk-action-essentially-surjective).

Any lift of the stalk functor with the canonical formula realizes every discrete G-set.

Proof: Fix a discrete continuous G-set M in Type w, where w = max (u + 1) v.
Its orbits are finite: an open stabilizer has finite index in the compact absolute
Galois group. Each orbit can therefore be represented by a finite set in Type u,
with its continuous G-action transported along a bijection. Apply etaleFieldGsets
to realize this small G-set by an etale K-scheme X. The representable presheaf h_X
is a sheaf, by smallEtaleRepresentablePresheaf_isSheaf. Lift its values to Type w.
The representable-stalk isomorphism identifies its stalk with the Omega-points
of X. Finite separable residue fields identify these points with the Ks-points
of X, naturally. The change-of-lift formula for T and j identifies the actions,
so T(h_X) is the chosen orbit, equivariantly. Form in sheaves with values in Type w
the coproduct of these sheaves, indexed by the orbit set of M, which is in Type w.
The stalk preserves this coproduct because it is left adjoint to the skyscraper
functor. Through the natural isomorphism j, its injections are the underlying
maps of the T-images of the sheaf coproduct injections, hence equivariant.
Their induced bijection from the disjoint union of orbits to T of the coproduct
is therefore an equivariant isomorphism. The disjoint union of orbits is M,
giving the required object in the essential image. For M empty use the empty
coproduct. This construction does not require a coproduct scheme in Type u,
even when the orbit set lies in the larger universe w. -/
theorem galoisStalkActionFunctor_essSurj
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∀ (T : Sheaf J (Type (max (u + 1) v)) ⥤
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) →
      T.EssSurj := by
  classical
  dsimp only
  intro T j hj
  let U := ObjectProperty.ι
      (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := Gal(Ks/K)))
    ⋙ ObjectProperty.ι
      (Action.IsContinuous (V := Type (max (u + 1) v)) (G := Gal(Ks/K)))
    ⋙ Action.forget (Type (max (u + 1) v)) (Gal(Ks/K))
  refine ⟨fun M ↦ ?_⟩
  obtain ⟨I, A, f, hfinite, ⟨hc⟩, ⟨hu⟩⟩ :=
    discreteContAction_finite_orbit_coproduct (Gal(Ks/K)) M
  have hreal (i : I) :=
    galoisStalkActionFunctor_finite_mem_essImage K Ks Ω T j hj (A i) (hfinite i)
  choose F he using hreal
  let e (i : I) : T.obj (F i) ≅ A i := (he i).some
  have : HasSheafify (Spec (.of K)).smallEtaleTopology
      (Type (max (u + 1) v)) := inferInstance
  have : Limits.HasColimitsOfShape (Discrete I) (Type (max (u + 1) v)) := inferInstance
  have : Limits.HasColimitsOfShape (Discrete I)
      (Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))) :=
    Sheaf.instHasColimitsOfShape
  let D := Discrete.functor F
  let c := Limits.colimit.cocone D
  let a : Discrete.functor A ≅ D ⋙ T :=
    Discrete.natIso (fun i ↦ (e i.as).symm)
  let d := (Limits.Cocone.precompose a.hom).obj (T.mapCocone c)
  let k : M ⟶ T.obj c.pt := hc.desc d
  have hp : Limits.PreservesColimit D (T ⋙ U) :=
    Limits.preservesColimit_of_natIso D j.symm
  let q := Limits.isColimitOfPreserves (T ⋙ U) (Limits.colimit.isColimit D)
  let b := Functor.isoWhiskerRight a U
  let z := hu.coconePointsIsoOfNatIso q b
  have hk : U.map k = z.hom := by
    apply hu.hom_ext
    intro i
    change U.map ((Limits.Cofan.mk M f).ι.app i) ≫ U.map k = _
    rw [← U.map_comp, hc.fac]
    dsimp [z, Limits.IsColimit.coconePointsIsoOfNatIso, Limits.IsColimit.map]
    exact (hu.fac ((Limits.Cocone.precompose b.hom).obj
      ((T ⋙ U).mapCocone (Limits.colimit.cocone D))) i).symm
  have : IsIso (U.map k) := hk ▸ z.isIso_hom
  have : IsIso k.hom.hom.hom := ‹IsIso (U.map k)›
  have : IsIso k.hom.hom := inferInstance
  have : IsIso k.hom := ObjectProperty.isIso_hom_iff _ |>.mp inferInstance
  have : IsIso k := ObjectProperty.isIso_hom_iff _ |>.mp inferInstance
  exact ⟨c.pt, ⟨(asIso k).symm⟩⟩

end AlgebraicGeometry.Scheme

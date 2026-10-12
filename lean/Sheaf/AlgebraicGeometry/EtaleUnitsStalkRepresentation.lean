/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsCohomology

/-!
# The geometric units stalk with its Galois representation

Source: Stacks Project, Tag 03QV, Example sheaves-point (2), and Tag 04JQ.
(blueprint: lem-sc-etale-units-stalk-representation).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The geometric stalk of the units sheaf, transported by a canonical stalk equivalence,
is equivariantly linearly equivalent to separable-closure units. No cohomology occurs here.

Source: Stacks Project, Example sheaves-point (2), Tag 03QV, and Tag 04JQ.
(blueprint: lem-sc-etale-units-stalk-representation).

Proof: Evaluate the germ of a unit in the residue field Ω at the chosen geometric lift.
An etale neighbourhood of a point over a field has a cofinal connected affine
neighbourhood Spec L with L/K finite separable. Its evaluation therefore belongs to
Ks inside Ω. Since the embedding Ks -> Ω is injective, evaluation and its inverse on
this image give a well-defined map from the colimit to Ks units. Conversely a unit
and its inverse belong to a finite separable extension inside Ks, hence define a unit
section on Spec L and its germ. These constructions are inverse: two representatives
with the same value agree after passing to a common finite separable extension.
They preserve multiplication, which is addition in the additive coefficient group,
and hence are Z-linear. Compose with i on the units sheaf to obtain e. For each g,
extend g to an automorphism τ of Ω. Changing the geometric lift by τ sends a value a
to g(a), by the given action formula and the equality restricting τ to g on Ks.
Thus e intertwines the action. The canonical ULift.up/down in gmPresheaf is removed
in evaluation. In particular the stalk is Ks units, not all Ω units when K is
imperfect, and the result holds equally in positive characteristic. -/
theorem exists_etaleUnits_stalk_linearEquiv
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra (SeparableClosure K) Ω] [Algebra K Ω]
    [IsScalarTower K (SeparableClosure K) Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    let G := Gal(SeparableClosure K/K)
    let D := Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ G
    let U : D ⥤ Rep.{u + 1} ℤ G := ObjectProperty.ι _
    ∀ (E : Sheaf J AddCommGrpCat.{u + 1} ≌ D)
      (i : E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
        Action.forget (ModuleCat.{u + 1} ℤ) G ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅ p.sheafFiber),
      (∀ (F : Sheaf J AddCommGrpCat.{u + 1}) (g : G) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap (SeparableClosure K) Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap (SeparableClosure K) Ω))
        (X : S.Etale) (x x' : p.fiber.obj X)
        (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
        (z : F.obj.obj (op X)),
        (i.hom.app F) ((E.functor.obj F).obj.ρ g
          ((i.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) →
      ∃ e : (E.functor.obj S.gmSheaf).obj.V ≃ₗ[ℤ] (Field.galoisUnitsTopRep K).V,
        ∀ (g : G) (x : (E.functor.obj S.gmSheaf).obj.V),
          e ((E.functor.obj S.gmSheaf).obj.ρ g x) =
            (Field.galoisUnitsTopRep K).ρ g (e x) := by
  sorry

end AlgebraicGeometry.Scheme

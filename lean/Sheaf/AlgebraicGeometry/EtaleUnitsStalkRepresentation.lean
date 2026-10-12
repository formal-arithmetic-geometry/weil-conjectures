/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsCohomology
import Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationOverfield
import Sheaf.FieldTheory.GaloisAutomorphismExtension
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# The geometric units stalk with its Galois representation

Source: Stacks Project, Tag 03QV, Example sheaves-point (2), and Tag 04JQ.
(blueprint: lem-sc-etale-units-stalk-representation).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

-- The categorical fibre and integer-module coercions require additional elaboration work.
set_option maxHeartbeats 800000 in
-- Keep the existing names of the two proof binders in the action hypothesis.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
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
  classical
  dsimp only
  intro E i hi
  let S := Spec (.of K)
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  obtain ⟨a, ha⟩ := exists_etaleUnits_stalk_evaluation_overfield K Ω
  let b := (i.app S.gmSheaf).addCommGroupIsoToAddEquiv
  let e : (E.functor.obj S.gmSheaf).obj.V ≃ₗ[ℤ] (Field.galoisUnitsTopRep K).V :=
    (b.trans a).toIntLinearEquiv
  refine ⟨e, ?_⟩
  intro g v
  let : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨X, x, z, hz⟩ := p.toPresheafFiber_jointly_surjective
    (P := S.gmSheaf.obj) ((i.hom.app S.gmSheaf) v)
  have hv : (i.inv.app S.gmSheaf) (p.toPresheafFiber X x S.gmSheaf.obj z) = v := by
    rw [hz, i.hom_inv_id_app_apply]
  obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K (SeparableClosure K) Ω g
  let x' : p.fiber.obj X :=
    Over.homMk (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left) (by
      rw [Category.assoc, x.w]
      change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) = _
      rw [← Spec.map_comp]
      congr 1
      ext k
      exact τ.commutes k)
  have haction := (congrArg
    (fun t ↦ (i.hom.app S.gmSheaf) ((E.functor.obj S.gmSheaf).obj.ρ g t)) hv).symm.trans
      (hi S.gmSheaf g τ hτ X x x' rfl z)
  change a ((i.hom.app S.gmSheaf) ((E.functor.obj S.gmSheaf).obj.ρ g v)) =
    (Field.galoisUnitsTopRep K).ρ g (a ((i.hom.app S.gmSheaf) v))
  rw [haction, ← hz]
  apply Additive.toMul.injective
  apply Units.ext
  apply (algebraMap (SeparableClosure K) Ω).injective
  rw [ha]
  change (ΓSpecIso (.of Ω)).hom
    (x'.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) =
    algebraMap (SeparableClosure K) Ω
      (g (↑(Additive.toMul (a (p.toPresheafFiber X x S.gmSheaf.obj z)))))
  have hτ' (t : SeparableClosure K) :
      algebraMap (SeparableClosure K) Ω (g t) = τ (algebraMap (SeparableClosure K) Ω t) :=
    DFunLike.congr_fun hτ t
  rw [hτ', ha]
  change (ΓSpecIso (.of Ω)).hom
    ((Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left).appTop
      ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) = _
  rw [Scheme.Hom.comp_appTop]
  exact ConcreteCategory.congr_hom (ΓSpecIso_naturality (CommRingCat.ofHom τ.toRingHom))
    (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))

end AlgebraicGeometry.Scheme

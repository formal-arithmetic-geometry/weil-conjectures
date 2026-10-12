module

public import Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationFixedFieldComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.FieldTheory.GaloisAutomorphismExtension

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

/-- The stalk comparison and the supplied action formula identify the pullback along the
fixed-field inclusion with the sheaf transported by the fixed-field equivalence.  This is the
first (before transport along `e`) part of the inverse-image comparison; its proof is the
represented-germ construction from Stacks, Tags 03QT, 03QW and 04JQ.
(blueprint: lem-sc-primary-fixed-field-pullback-iso)

Proof: identify stalks by the pullback stalk theorem, use the supplied germ-action formula and
extensions of Galois automorphisms to obtain equivariance, then apply the full faithful
fixed-field equivalence and its unit/counit. -/
theorem primary_fixedField_pullback_iso
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : AddCommGrpCat.of R.obj.V ≅
      ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (_hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (_hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : M.obj.obj (op X)),
      i.hom (R.obj.ρ g (i.inv ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x M.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' M.obj z)
    (H : OpenSubgroup (Gal(Ks/K)))
    [FiniteDimensional K (IntermediateField.fixedField H.toSubgroup)]
    (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    : Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1}
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (IntermediateField.fixedField H.toSubgroup))))).obj M ≅
      C.inverse.obj (primaryRestrictedModule K Ks H R)) := by
  sorry

end AlgebraicGeometry.Scheme

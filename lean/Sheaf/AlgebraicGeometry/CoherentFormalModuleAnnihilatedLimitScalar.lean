module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace LinearMap

/-- Products of scalar quasi-inverses annihilate kernel and cokernel.
Source: Stacks Project, Remark 0888, final scalar-composite argument.
(blueprint: lem-weil-pbc-formal-annihilation-affine-limit-criterion)
-/
theorem annihilated_of_scalar_composites
    {A : Type u} [CommRing A] (K : Ideal A) (t : ℕ)
    {P : Type v} {R : Type w} [AddCommGroup P] [Module A P]
    [AddCommGroup R] [Module A R] (v : P →ₗ[A] R)
    (hv : ∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      ∃ k : R →ₗ[A] P,
        k.comp v = (f * g) • LinearMap.id ∧
        v.comp k = (f * g) • LinearMap.id) :
    K ^ (2 * t) ≤ Module.annihilator A (LinearMap.ker v) ∧
      K ^ (2 * t) ≤ Module.annihilator A (R ⧸ LinearMap.range v) := by
  rw [two_mul, pow_add]
  constructor
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, hk, _⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    have h := congrArg (fun l : P →ₗ[A] P ↦ l x) hk
    simpa [LinearMap.mem_ker.mp x.property] using h.symm
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, _, hk⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change (LinearMap.range v).mkQ ((f * g) • y) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨k y, ?_⟩
      exact congrArg (fun l : R →ₗ[A] R ↦ l y) hk

end LinearMap

/-- The scalar reverse maps on the affine inverse limit.
Source: Stacks Project, Remark 0888, final paragraph, implication (1) to (2).
The componentwise annihilation hypotheses give the canonical lift maps at every
level. Their compatibility with transition maps makes them a map on inverse
limits; the two scalar composite identities are then checked by the limit
projections. This is the intermediate scalar-composite assertion used by the
annihilation criterion.
(blueprint: lem-weil-pbc-formal-annihilation-affine-limit-scalar)
-/
abbrev affineLimitModule (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentFormalModule X I)
    (U : X.affineOpens) := ↥(limit (F.obj ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op U.1)) : ModuleCat Γ(X, U.1))

/-- For scalars in the affine ideal power, construct compatible reverse maps on all
levels and pass them to the inverse limit. At each level, annihilation of the
kernel makes the map independent of the chosen lift, while annihilation of the
cokernel provides a lift. Naturality of the transition maps gives compatibility.
The two composite identities follow by checking every limit projection.
Source: Stacks Project, Remark 0888, final paragraph.
(blueprint: lem-weil-pbc-formal-annihilation-affine-limit-scalar)
-/
theorem coherentFormalModule_affine_limit_scalar_composites
    (X : Scheme.{u}) [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G) (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) (U : X.affineOpens) :
    ∀ (f g : Γ(X, U.1)), f ∈ K.ideal U ^ t → g ∈ K.ideal U ^ t →
      ∃ k : affineLimitModule X I G U →ₗ[Γ(X, U.1)] affineLimitModule X I F U,
        k.comp (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom =
          (f * g) • (LinearMap.id : affineLimitModule X I F U →ₗ[Γ(X, U.1)]
            affineLimitModule X I F U) ∧
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom.comp k =
          (f * g) • (LinearMap.id : affineLimitModule X I G U →ₗ[Γ(X, U.1)]
            affineLimitModule X I G U) := by
  sorry

end AlgebraicGeometry

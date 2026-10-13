module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Paper.ShiftedKoszulAugmentation

@[expose] public section

universe a b
open CategoryTheory
namespace AlgebraicGeometry

/-- The shifted Koszul complex on powers of a finite sequence gives a perfect affine object.
Source: Stacks Project, Tag 08CX and Definition 08CM.
(blueprint: lem-sc-affine-perfect-koszul-principal-unit-perfect).

Proof: In degree `-n` the complex is the exterior power of degree `n + 1` of `A^r`.
The exterior powers have the wedge bases indexed by subsets of the standard basis,
so they are finite free and vanish when `n + 1 > r`. Extension gives zero in positive
cochain degrees, and negating the differential does not change any term. Applying
associated sheaves termwise therefore gives a bounded complex of finite free structure
sheaf modules. Restrict this complex to the whole scheme, or any neighbourhood of a
point. Restriction preserves finite free modules and zero terms, and its derived
comparison identifies this strictly perfect model with the restricted derived object.
This is the definition of perfectness. For `r = 0` all terms are zero; if `A` is the
zero ring, the spectrum is empty and the pointwise conclusion is vacuous. -/
theorem affine_perfect_koszul_principal_unit_perfect
    (A : Type a) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (he : 1 ≤ e)
    [HasDerivedCategory.{b}
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{b}
        (SheafOfModules.{a} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    Scheme.IsPerfect (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
          (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))) := by
  sorry

end AlgebraicGeometry

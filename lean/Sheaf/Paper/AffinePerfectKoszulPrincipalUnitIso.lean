module

public import Sheaf.Paper.ShiftedKoszulAugmentation

@[expose] public section

universe a b
open CategoryTheory
namespace AlgebraicGeometry

/-- The canonical shifted Koszul augmentation is invertible on the principal-open union.
Source: Stacks Project, Tag 08CX; More on Algebra, Tags 0626 and 0663.
(blueprint: lem-sc-affine-perfect-koszul-principal-unit-iso).

Proof: On `D(f i)`, localization makes `f i` and therefore `(f i)^e` units. In the
localized exterior algebra let `h` be left exterior multiplication by the standard
basis vector `e_i` divided by `(f i)^e`. The contraction formula
`d(e_i ∧ x) = (f i)^e x - e_i ∧ d(x)` gives `dh + hd = id`, including degree zero.
Thus the full localized Koszul complex is contractible. The cone of the augmentation
from the deleted, shifted complex to the ring in degree zero is this full Koszul
complex, with the corresponding signs. The augmentation is consequently a
quasi-isomorphism on each `D(f i)`. Termwise associated sheaves commute with these
localizations, so the same holds on the scheme. These principal opens cover their
union; cohomology sheaves, hence quasi-isomorphisms, are detected on an open cover.
Exact restriction and derived localization therefore make the displayed restricted
augmentation an isomorphism. For `r = 0` the union is empty and all module sheaves on
it are zero. For `r = 1` this is the inverse to multiplication by a unit. -/
theorem affine_perfect_koszul_principal_unit_iso
    (A : Type a) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (he : 1 ≤ e)
    [HasDerivedCategory.{b}
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{b}
        (SheafOfModules.{a} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    IsIso (((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace)
        (⨆ i : Fin r, (Spec (.of A)).basicOpen
          ((Scheme.ΓSpecIso (.of A)).inv (f i)))).mapDerivedCategory).map
            (affineKoszulAugmentation A r (fun i ↦ f i ^ e))) := by
  sorry

end AlgebraicGeometry

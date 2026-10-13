/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact

/-! # Homology of a finite-free zero-differential internal Hom complex

Source: Stacks Project, Tags 0BQY and 0A8X.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The coordinate homology maps exhibit Hom-complex homology as a product.

Source: Stacks Project, Tag 0BQY, finite-free Hom calculation in Lemma 48.15.4,
expanded using Tag 0A8X, the product terms and differential of the Hom complex.
(blueprint: new-h3-finite-free-zero-homology-product).

Proof: Write P = Hom(E,K). For each p, put F_p = Hom(E.X p,-). The fixed product
projections and the zero differential of E give P the coordinatewise differential
F_p(K.d). Choose an interval containing the support of E. Outside it F_p is the
zero functor, so these product diagrams reduce to finite products. A chosen basis
of each E.X p identifies F_p naturally with a finite product of the identity;
finiteFreeInternalHomExact gives exactness of F_p. Apply it to the sequences
of cycles, boundaries, and homology of K. Thus F_p preserves the cycle kernel
and the quotient of cycles by boundaries, giving the coordinate map g in each
degree. Finite products in the abelian category preserve these kernels and
quotients. Consequently the g maps form a limiting fan on homology. A cycle lift
d is unique because F_p(K.iCycles q) is monic. Its composite with F_p(K.homologyπ q)
is the coordinate quotient map, which gives the last equation by the universal
property of the homology cokernel. Transport along p+n=q gives the indexed form
below. This argument does not assume concentration of K. Empty support and
rank-zero terms give zero products and the same universal properties.
-/
theorem finiteFreeZero_homologyProduct
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (E K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ) (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (ULift.{u} (Fin r)))) :
    let P := homComplex (R := R) E K
    ∃ g : ∀ (p q : ℤ), p + n = q →
        (P.homology n ⟶ SheafOfModules.homObj (R := R) (E.X p) (K.homology q)),
      Nonempty (IsLimit (Fan.mk (P.homology n)
        (fun p : ℤ ↦ g p (p + n) rfl))) ∧
      ∀ (p q : ℤ) (hpq : p + n = q)
        (d : P.cycles n ⟶ SheafOfModules.homObj (R := R) (E.X p) (K.cycles q)),
        d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles q) =
          P.iCycles n ≫ (Classical.choose (homComplex_projections_exists (R := R)))
            E K n p q hpq →
        d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ q) =
          P.homologyπ n ≫ g p q hpq := by sorry

end CategoryTheory

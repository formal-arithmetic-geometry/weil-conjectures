/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Sheaf.AlgebraicGeometry.HomComplexSingle
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Deriving internal Hom from a module in degree zero

Source: Stacks Project, Cohomology on Sites, Section 08J7, Lemma 0A95;
Duality for Schemes, Tag 0BV1.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory

/-- A right derived functor of termwise internal Hom from a fixed module agrees with
internal RHom from that module placed in degree zero. This comparison concerns only
O-modules, and requires neither an algebra structure nor an adjunction.

Source: Stacks Project, Cohomology on Sites, Section 08J7, Lemma 0A95;
Duality for Schemes, Tag 0BV1, lemma-sheafhom-affine-ext
(blueprint: lem-sc-derived-internal-hom-single-comparison).

Proof:
1. Let I be the functorial K-injective resolution of the Grothendieck abelian category
   of R-modules. The right derivability structure of K-injectives computes the given
   right derived functor S on I, with its comparison invertible on K-injective objects.
   Indeed, quasi-isomorphisms between K-injectives are homotopy equivalences;
   additive termwise Hom preserves homotopies, and Q inverts homotopy equivalences.
2. For M concentrated in degree zero, the degree n term of Hom-complex(M[0], I) is
   Hom(M, I.X n): only the degree-zero source factor survives in the product defining
   Hom-complex. Its differential is postcomposition with d_I, since d_M is zero.
   The existing homComplex_single_iso gives this identification objectwise. Its
   projection construction and the Hom-complex map formula show naturality. Thus
   projection onto that factor and insertion with zero in all other factors give a
   natural chain isomorphism with the termwise internal Hom complex.
3. Apply derivedInternalHom_comparison to this same I and fix the first variable at
   M[0]. Compose its comparison with the natural chain isomorphism from step 2.
4. The resulting comparisons identify both functors on K-injective representatives,
   naturally in all morphisms. The K-injective localization equivalence descends this
   natural isomorphism to the derived category. Equivalently, uniqueness of the right
   derived functor transports the comparison to the given S. This includes zero M,
   arbitrary unbounded complexes, and every choice of the derived-category universe. -/
theorem derivedInternalHom_single_comparison
    (X : AlgebraicGeometry.Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (AlgebraicGeometry.moduleRings X.toRingedSpace))]
    (M : SheafOfModules.{u} (AlgebraicGeometry.moduleRings X.toRingedSpace))
    [((SheafOfModules.homFunctor X.sheaf).obj (op M)).Additive]
    (S : DerivedCategory (SheafOfModules.{u}
      (AlgebraicGeometry.moduleRings X.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (AlgebraicGeometry.moduleRings X.toRingedSpace)))
    (δ : ((SheafOfModules.homFunctor X.sheaf).obj (op M)).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ S)
    (hδ : S.IsRightDerivedFunctor δ (HomologicalComplex.quasiIso _ (.up ℤ))) :
    Nonempty (S ≅ (Functor.curry.obj
      (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  sorry

end CategoryTheory

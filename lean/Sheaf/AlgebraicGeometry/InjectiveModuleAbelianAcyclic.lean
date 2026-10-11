/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Abelian cohomology of injective etale module sheaves

Source: Stacks Project, Cohomology on Sites, Lemma 03FD, second paragraph of the proof
(blueprint: lem-weil-pbc-injective-module-abelian-acyclic).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An injective sheaf of modules over the constant commutative ring sheaf has vanishing
positive-degree cohomology on every object of the small etale site, computed in abelian
sheaves. No injectivity of the underlying abelian sheaf is assumed. `ULift` only places
coefficients in the universe of the sheaf values.

Source: Stacks Project, Lemma 03FD, second paragraph of the proof
(blueprint: lem-weil-pbc-injective-module-abelian-acyclic).

Proof (the node's five steps). Fix an object U and any covering of U. Write O for the
constant ring sheaf and K for the chain complex of free presheaves of O-modules of this
covering. Yoneda identifies Hom(O_V, G) with G(V), by evaluation at the generator indexed
by the identity of V. Thus Hom(K, G) is naturally the Cech cochain complex of G, including
its alternating restriction differential (def-weil-presheaf-modules-sheafification,
def-weil-pbc-cech-complex, lem-weil-pbc-free-cech-complex-exact; Step 1).
The free complex K has zero positive homology, objectwise, by
lem-weil-pbc-free-cech-complex-exact (Step 2). An injective module sheaf I is injective as
a presheaf of modules by lem-weil-pbc-injective-module-injective-presheaf. Exactness of
Hom(-, I) then shows that Hom(K, I), hence the Cech complex of I, has zero positive
cohomology (Step 3). Forgetting the module action leaves the section groups and
restriction maps unchanged, so the underlying abelian sheaf has the identical Cech
complex (def-weil-pbc-abelian-etale-sheaves and def-weil-pbc-cech-complex; Step 4).
Apply lem-weil-pbc-cech-vanishing-criterion with all objects and all coverings. Fibre
products exist by def-weil-pbc-etale-site, and every cover refines itself. The preceding
Cech vanishing supplies the third hypothesis, giving zero higher right derived
functors of abelian-sheaf evaluation at every U (Step 5). -/
theorem isZero_rightDerived_etale_toSheaf_of_injective
    (X : Scheme.{u}) (R : Type u) [CommRing R]
    (I : SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R)))) [Injective I]
    (U : X.Etale) (q : ℕ) (hq : 0 < q) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op U)).rightDerived q).obj ((SheafOfModules.toSheaf _).obj I)) := by
  sorry

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Strict-local exchange compared with derived global sections

Source: Stacks Project, Tags 03QO and 095T.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- Strict-local stalk exchange is the derived-unit map on total-space hypercohomology.
This statement is on all bounded below complexes and all integer degrees; it contains
no comparison with Ext-valued sheaf cohomology.

Source: Stacks Project, etale-cohomology.tex, Tag 03QO and the final map-on-stalks
paragraph of Tag 095T, before closed-fibre comparison.
(blueprint: lem-weil-pbc-strict-local-derived-global-exchange)

Proof: Choose a bounded below injective representative I of K, and a bounded below
injective replacement g'^*I → J of its exact inverse image. Direct image preserves
K-injectives because it is right adjoint to exact inverse image. Thus Rf_*K is
represented by f_*I and Rf'_*g'^*K by f'_*J. The closed-point stalk is exact, and
Tag 03QO identifies it naturally with global sections over each strict-local base.
Locality of φ puts the image of the closed B-point at the closed A-point. Inverse-image
stalk comparison identifies the stalk after g^* with the original stalk at that image;
changing the separably closed residue field does not change this stalk. Apply these
natural identifications degree by degree to the two complexes, and use exactness to
commute stalks with homology. Leray identifies Γ(Spec A,f_*I) with Γ(X,I), and similarly
for B and J. Their homologies give c₁ and c₂. The termwise derived exchange formula
represents the exchange by g^*f_*I → f'_*g'^*I → f'_*J. Under the germ identifications
its map on sections is Γ(X,I) → Γ(X',g'^*I) → Γ(X',J), the underived unit followed by
the replacement. The derived adjunction unit and Leray compatibility identify its
class with the morphism defining p. Taking homology proves the equation. Comparisons
of K-injective representatives are unique up to homotopy and induce isomorphisms,
so the calculation applies to the chosen derived functors in the statement. -/
theorem Etale.exists_addEquiv_strictLocal_derivedGlobal_exchange
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (φ : A →+* B) [IsLocalHom φ]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of B))
    (g' : X' ⟶ X) (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) :
    let g := Spec.map (CommRingCat.ofHom φ)
    let S := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let T := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    let t := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    let P := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let P' := (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let U := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj (P.obj K)
    let V := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (P'.obj (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K))
    let p := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      (P.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').derivedPlus.unit.app K) ≫
        (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (lowerStar AddCommGrpCat.{u + 1} g')
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _ _ _
          (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
            (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g'))
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g')).hom.app
            (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K))
    ∃ (c₁ : ((t.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S) ≃+ U)
      (c₂ : ((t.sheafFiber (A := AddCommGrpCat.{u + 1})).obj T) ≃+ V),
      ∀ x, c₂ (((t.sheafFiber (A := AddCommGrpCat.{u + 1})).map e).hom x) = p.hom (c₁ x) := by
  sorry

end AlgebraicGeometry

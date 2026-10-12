/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # Strict-local exchange with abelian coefficients

Source: Stacks Project, Tags 03QO and 095T.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- The geometric calculation of exchange for abelian sheaves, before any comparison
with cohomology computed in a category of modules.

Source: Stacks Project, Tag 03QO and the map-on-stalks paragraph of Tag 095T.
(blueprint: lem-weil-pbc-strict-local-abelian-total-exchange)

Proof: by Tag 03QO, the closed-point germ on each strict local base identifies
sections with the stalk and is exact. Locality of φ makes the image of the
closed B-point the closed A-point. Inverse-image stalk comparison, including
invariance under separably closed residue field extensions, therefore identifies
the source stalk with sections of the derived direct image on Spec A. Choose a
bounded below injective abelian resolution G → I and a K-injective replacement
of g'^* I. Exactness of the stalk functors identifies the two stalk homologies
with the homologies of the section complexes on X and X'. These compute Ext
from the constant integer sheaf, hence Sheaf.H. The termwise exchange formula
identifies the stalk map with pullback of sections followed by the replacement.
The degree-zero unit is pullback of sections; its derived map is the Ext map
cohomologyMap, by the derived adjunction and the constant-sheaf comparison.
Uniqueness of comparisons into K-injectives ensures the identification in every
degree. This uses no properness or torsion assumption. -/
theorem Etale.exists_addEquiv_strictLocal_abelian_total_exchange
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (φ : A →+* B) [IsLocalHom φ]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of B))
    (g' : X' ⟶ X) (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let g := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let S := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let T := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    let t := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    ∃ (a₁ : ((t.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S) ≃+ Sheaf.H G q)
      (a₂ : ((t.sheafFiber (A := AddCommGrpCat.{u + 1})).obj T) ≃+
        Sheaf.H ((g')^*[AddCommGrpCat.{u + 1}].obj G) q),
      ∀ x, a₂ (((t.sheafFiber (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        Etale.cohomologyMap g' G q (a₁ x) := by
  sorry

end AlgebraicGeometry

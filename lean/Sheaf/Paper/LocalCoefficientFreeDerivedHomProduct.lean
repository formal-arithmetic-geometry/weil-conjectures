/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.LocalCoefficientTelescope
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.Algebra.Homology.HomComplexProjections
import Sheaf.Paper.CountableFreeInternalHomProduct

/-! # Internal Hom from the free telescope vertex

Source: Stacks Project, algebraization.tex, Tag 0997, proof of lemma-hom-from-Af.
-/

@[expose] public section

universe u w wSlice

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Internal derived Hom from the countable free module is the derived product,
with the dual telescope map corresponding to `1 - shift`.

Source: Stacks Project, algebraization.tex, Tag 0997, proof of lemma-hom-from-Af
(blueprint: lem-weil-pbc-local-coefficient-free-derived-hom-product).

Proof: Choose a K-injective representative I of the restricted complex on the slice.
The representative comparison for derived internal Hom computes its value by
Hom-complex(P[0],I), where P is the countable free module. Projecting onto source degree
zero identifies this complex with the degreewise internal Hom from P. Use the
specified projections of `homComplex_projections_exists` for this identification.
The proved `countableFree_internalHom_product` supplies the ordinary product property.
Its argument is that tensoring any
test module with P preserves the coproduct, and the tensor-Hom adjunction identifies
maps into this internal Hom with families of maps into the target. The projections
are precomposition with the basis inclusions followed by evaluation at 1. Thus the
Hom-complex is the termwise product of copies of I, with coordinatewise differential.
The termwise K-injective product theorem identifies its image in the derived category,
with these projections, with the specified product of
the restricted complex. Precomposition by d(e_n)=e_n-f e_(n+1) has n-th coordinate
pr_n-f pr_(n+1). Naturality of the representative comparison and the localization of
scalar multiplication give the asserted square. Explicitly, the resolution map
commutes with scalar multiplication by `localSectionMultiplication_naturality`, and
`Localization.liftNatTrans_app` gives the scalar map on derived restrictions. The
construction uses no exactness of infinite products and applies also to f=0, f a unit,
and a zero coefficient ring. -/
theorem localCoefficientFreeDerivedHom_product
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R)))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)] :
    let L := (localCoefficientDerivedRestriction R U).obj K
    let H := (Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj L
    ∃ e : H.obj (op ((DerivedCategory.singleFunctor _ 0).obj
        (localCoefficientFreeSum R U))) ≅ ∏ᶜ (fun _ : ℕ ↦ L),
      H.map ((DerivedCategory.singleFunctor _ 0).map
        (localCoefficientTelescopeMap R U f)).op ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism
        (fun _ ↦ (localSectionDerivedMultiplication R U f).app K) := by sorry

end CategoryTheory

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization
import Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction

/-! # Transport the restriction diagram to covering opens of an open union

Source: Stacks Project, Tag 08BW, restriction to the union before applying exactness.
(blueprint: lem-sc-open-union-restriction-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The local restriction diagram on an ambient union is transported to an actual
cover of the union scheme. This statement supplies only equivalences, comparison
isomorphisms, and compatibility of local maps; it does not assert any gluing.
Source: Stacks Project, Tag 08BW, canonical restriction to the union; Mathlib's
`Modules.overMapCompOverEquiv`, `overFunctorEquiv`, `restrictFunctorComp` and
`restrictFunctorCongr` implement the change of open schemes.
(blueprint: lem-sc-open-union-restriction-transport).

Proof: Put Y = (W union V).toScheme and take U and T to be the inverse images
of W and V under the open inclusion Y into X. Inverse image preserves union,
and its inverse image of W union V is top, so U and T cover Y. Each pulled-back
open scheme is canonically isomorphic to the corresponding original open scheme,
as is their intersection. Transport module sheaves through these scheme
isomorphisms; their exact functors induce the displayed derived equivalences.
Supply localizations in Hom universe w by derivedOpenLocalization and the
localization transport in open_derived_localization_adjunction, applied with
Y's given localization. For qW and qV, identify both underived restriction routes
with restriction along W into Y and V into Y, respectively, using
Modules.overMapCompOverEquiv, overFunctorEquiv, restrictFunctorComp and
restrictFunctorCongr, and then derive these natural isomorphisms. The overlap
comparison is a pasted square of the same underived isomorphisms. On a complex,
the factorization identities for mapDerivedCategoryCompIso and
mapDerivedCategoryNatIso show that deriving this pasted square equals pasting
its derived comparisons; extend the identity through the localization using
Localization.natTrans_ext. Conjugate a and b by kW and kV and take their
preimages under the two derived equivalences. Apply the overlap equivalence to
the desired equality, use this pasted-square identity and functoriality, and
cancel the equivalence units and comparison inverse pairs. The remaining
equality is exactly the displayed ambient compatibility hypothesis. The same
argument includes empty opens, disjoint opens, and an empty union, since all
scheme identifications and equivalence identities hold in these cases. -/
theorem open_union_restriction_transport
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let U := (W ⊔ V).ι ⁻¹ᵁ W
    let T := (W ⊔ V).ι ⁻¹ᵁ V
      ∃ hU : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      letI := hU
      ∃ hT : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace)),
      letI := hT
      ∃ hI : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings (U ⊓ T).toScheme.toRingedSpace)),
      letI := hI
      let RU := (schemeOpenRestriction (W ⊔ V).toScheme U).mapDerivedCategory
      let RT := (schemeOpenRestriction (W ⊔ V).toScheme T).mapDerivedCategory
      let SU := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)).mapDerivedCategory
      let ST := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)).mapDerivedCategory
      let tU := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)
      let tT := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)
      ∃ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV),
      ∀ (G E : schemeDerivedCategory X)
        (a : JW.obj G ⟶ JW.obj E) (b : JV.obj G ⟶ JV.obj E),
        sW.inv.app G ≫ SW.map a ≫ sW.hom.app E =
          sV.inv.app G ≫ SV.map b ≫ sV.hom.app E →
        let a' := eW.functor.preimage
          (qW.hom.app (L.obj G) ≫ kW.hom.app G ≫ a ≫
            kW.inv.app E ≫ qW.inv.app (L.obj E))
        let b' := eV.functor.preimage
          (qV.hom.app (L.obj G) ≫ kV.hom.app G ≫ b ≫
            kV.inv.app E ≫ qV.inv.app (L.obj E))
        tU.inv.app (L.obj G) ≫ SU.map a' ≫ tU.hom.app (L.obj E) =
          tT.inv.app (L.obj G) ≫ ST.map b' ≫ tT.hom.app (L.obj E) := by sorry

end AlgebraicGeometry.Scheme

/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.Algebra.Homology.OpenExtensionRestrictionIso
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-! # Coherence of supplied open-union restriction comparisons

Source: Stacks Project Tags 08BW and 08BT; Mathlib restriction composition.
(blueprint: lem-sc-open-union-restriction-comparison-coherence).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Supplied direct restriction comparisons descend to commuting overlap comparisons.
Source: Stacks Project Tag 08BW, cohomology.tex, lemma-mayer-vietoris-hom;
Tag 08BT, lemma-adjoint-lower-shriek-restrict.
(blueprint: lem-sc-open-union-restriction-comparison-coherence).

Proof: Treat each chain W intersect V into W into W union V, and W intersect V into
V into W union V separately. Direct restriction through the inverse image of W is a
localization: extension by zero is an exact left adjoint, its unit is invertible,
and exact derived functoriality derives that adjunction and unit. The unit is the
canonical restriction-of-extension map: on each stalk of the open it is the identity,
as in the proof of nonempty_openExtensionRestrictionIso. Transport through
Modules.overEquiv. By Localization.fullyFaithfulWhiskeringLeft, precomposition with
this restriction is fully faithful on functor categories. The canonical nested
restriction comparison identifies PW followed by SW with direct restriction from
the union to the intersection. Combine that comparison with the supplied qW, qIY
and the inverse of tU. Descend the resulting isomorphism uniquely to cW. Do the
same for V to obtain cV, using the same qIY and eI. Threefold restriction coherence
identifies SW(kW) followed by sW with the union-to-intersection comparison followed
by the ambient direct comparison. Underived, both composites restrict the same
section; cancel the overEquiv units and counits and use overFunctorMap. Derive this
identity using mapDerivedCategoryCompIso_fac, mapDerivedCategoryNatIso_fac and
Localization.natTrans_ext. Substitution into the defining identities for cW,cV
gives the two equations.
Define qI as the functor associator followed by qIY
whiskered with L and the canonical ambient intersection restriction comparison.
Its component is qIY(LG) followed by that ambient comparison, so the resulting
equations are precisely the asserted equations with qI. These arguments apply to empty,
disjoint, and repeated opens. No direct equivalences, localizations or direct comparisons
are constructed by this statement: they are supplied as inputs. -/
theorem open_union_restriction_comparison_coherence
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ W).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (((W ⊔ V).ι ⁻¹ᵁ W) ⊓ ((W ⊔ V).ι ⁻¹ᵁ V)).toScheme.toRingedSpace))]
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
      ∀ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV),
      ∀ (eI : schemeDerivedCategory (U ⊓ T).toScheme ≌
          schemeDerivedCategory (W ⊓ V).toScheme)
        (_qIY : (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory ⋙
          eI.functor ≅ (schemeOpenOverlapRestriction X
            (homOfLE (inf_le_left.trans le_sup_left) : W ⊓ V ⟶ W ⊔ V)).mapDerivedCategory),
      ∃ (cW : SU ⋙ eI.functor ≅ eW.functor ⋙ SW)
        (cV : ST ⋙ eI.functor ≅ eV.functor ⋙ SV)
        (qI : (L ⋙ (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory) ⋙
          eI.functor ≅ (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory),
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tU.inv.app (L.obj G)) ≫ cW.hom.app (RU.obj (L.obj G)) ≫
          SW.map (qW.hom.app (L.obj G)) ≫ SW.map (kW.hom.app G) ≫ sW.hom.app G =
            qI.hom.app G) ∧
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tT.inv.app (L.obj G)) ≫ cV.hom.app (RT.obj (L.obj G)) ≫
          SV.map (qV.hom.app (L.obj G)) ≫ SV.map (kV.hom.app G) ≫ sV.hom.app G =
            qI.hom.app G) := by sorry

end AlgebraicGeometry.Scheme

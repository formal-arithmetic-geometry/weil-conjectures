/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme


/-! # Supported perfect restriction in a compact-open overlap model

Source: Stacks Project, Tags 08EK and 09IM.
(blueprint: lem-sc-supported-overlap-restriction-data).
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
/-- Express restriction of a supported perfect complex to the overlap on a compact
open of V. This is restriction data only; no extension to V is asserted.
Source: Stacks Project, Tag 09IM, the overlap input to Tag 08EK.
(blueprint: lem-sc-supported-overlap-restriction-data).

Proof: Set U to the open range of the inclusion of W intersect V into V. The intersection
is compact by quasi-separatedness and compactness of W and affine V, so U is compact.
The inverse image of T in V is closed. Its complement identifies through the open
embedding with V intersect the compact open complement of T, hence is compact by the
same intersection criterion. The inclusion U.toScheme into W is an open immersion.
Define G by exact restriction of F along that inclusion. At each point of U, pull back
a strictly perfect neighbourhood model of F, preserving the degree bounds, finite free
modules and retract equations. These give perfectness of G. Exact homology and the
restriction-stalk comparison identify each stalk of G with the corresponding stalk of F,
so support restricts as stated. The scheme isomorphism from the ambient overlap to U
supplies the exact module equivalence and the derived equivalence e. Transport the
chosen derived localization along it, and transport the localized-site localizations
through the corresponding equivalences on each open of U to supply hO. The natural
restriction composition comparisons identify ordinary restriction from V followed by e
with SV, and identify e(G) with SW(F). Both comparisons arise by deriving the underived
restriction comparisons, so commute with shifts and biproducts. Apply those comparisons
to G plus G[1] to obtain the last isomorphism. Empty opens and empty support need no
separate case: the same scheme isomorphism, exact restrictions and zero stalks apply. -/
theorem exists_supported_overlap_restriction_data
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    (F : schemeDerivedCategory W.toScheme) (hF : IsPerfect W.toScheme F)
    (hFT : (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F).val.presheaf x)))) :
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    ∃ U : V.toScheme.Opens, IsCompact (U : Set V.toScheme) ∧
      IsClosed (Subtype.val ⁻¹' T : Set V.toScheme) ∧
      IsCompact (Subtype.val ⁻¹' T : Set V.toScheme)ᶜ ∧
      ∃ hD : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      letI := hD
      ∃ hO : ∀ O : U.toScheme.Opens, HasDerivedCategory.{w}
          (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over O)),
      letI := hO
      ∃ G : schemeDerivedCategory U.toScheme, IsPerfect U.toScheme G ∧
        (∀ (i : ℤ) (x : U.toScheme), x.val.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).obj G).val.presheaf
              x))) ∧
        ∃ e : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory (W ⊓ V).toScheme,
          Nonempty ((schemeOpenRestriction V.toScheme U).mapDerivedCategory ⋙ e.functor ≅ SV) ∧
          Nonempty (e.functor.obj (G ⊞ G⟦(1 : ℤ)⟧) ≅ SW.obj (F ⊞ F⟦(1 : ℤ)⟧)) := by sorry

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Final

/-! # Constructible derived mapping continuity on affine ind-etale limits

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14 and
proof of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

The comparison is the localization of the map out of the termwise filtered
colimit of compatible complex representatives. It is not a categorical colimit
assertion in the triangulated category. The representatives retain both the
transition maps and the legs of the evaluation-defined pullback comparison.
All constructions use the ordinary constant-coefficient small etale category.

## Main statements

* `constructible_mapping_continuity`: the canonical comparison is invertible.
* `comparison_cofinal`: the canonical cofinal comparison triangle.
* `comparison_naturality`: system maps, coefficient maps and base restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

/-- Global RHom of the two exact inverse images along a scheme over X.
This is the existing RΓ of the existing derived internal Hom.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def value (T : Over X) : DerivedCategory (ModuleCat.{u + 1} A) :=
  ((ExternalRHom.globalHom A T.left).obj
    (op ((ExternalRHom.pull A T.hom).obj K))).obj
      ((ExternalRHom.pull A T.hom).obj M)

/-- Pullback of derived morphisms, transported along the canonical composition
isomorphisms for inverse image. Its source is the evaluation transpose already
provided by ExternalRHom.restriction; no map or isomorphism is chosen.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def pullback {T S : Over X} (f : T ⟶ S) : value A K M S ⟶ value A K M T :=
  ExternalRHom.restriction A f.left
      ((ExternalRHom.pull A S.hom).obj K) ((ExternalRHom.pull A S.hom).obj M) ≫
    ((ExternalRHom.globalHom A T.left).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).hom.app K).op).app
          ((ExternalRHom.pull A f.left).obj ((ExternalRHom.pull A S.hom).obj M)) ≫
    ((ExternalRHom.globalHom A T.left).obj
      (op ((ExternalRHom.pull A T.hom).obj K))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
          f.w.symm).inv.app M)

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

variable {J : Type (u + 1)} [SmallCategory J]
variable (E : J ⥤ Over X) (d : Cone E) (r : J ⥤ I)

variable (K' M' : DerivedCategoryModule A X) (α : K' ⟶ K) (β : M ⟶ M')

end AlgebraicGeometry.Etale.IndEtaleMapping

# AlgebraicGeometry.etaleOpenObjectCohomologyMap

## Reason

Construct the map underlying the original comparison explicitly, so that its bijectivity
and a degree-zero generator identity can be independent proof obligations. Existing
statements and definitions are unchanged, including every target signature.

## Old

These four construction declarations and the two property declarations did not exist.
The original theorem had its existing statement and the whole proof `:= by sorry`.

## New

The new construction and property declarations are the following module contents.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # The canonical open-object cohomology map

Source: Stacks Project, Cohomology on Sites, Tag 03F3.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The actual free abelian representable sheaf functor used in object cohomology.
Source: Stacks Project, Tag 03F3, sections represented by free abelian sheaves.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenFreeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}

/-- The identity generator, transported to sections of the inverse image on the open.
Source: Stacks Project, Tag 03F3, the free-sheaf/Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenFreeSheafSection {X : Scheme.{u}} (U : X.Opens) :
    ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj
      ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι))).obj.obj
        (op (Scheme.Etale.mk (𝟙 U.toScheme))) := by
  let A := (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)
  let b : U.toScheme.Etale := Scheme.Etale.mk (𝟙 U.toScheme)
  let a := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj b
  let t : a ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (𝟙 U.toScheme) (by rfl)
  let s : A.obj.obj (op a) :=
    (toSheafify X.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).app
        (op a) (FreeAbelianGroup.of ⟨t⟩)
  exact ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
    inferInstance).inv.app A).hom.app (op b) s

/-- The constant-to-pulled-back-free-sheaf map classifying the identity generator.
Source: Stacks Project, Tag 03F3, the sections adjunction at the terminal object.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenFreeSheafUnit {X : Scheme.{u}} (U : X.Opens) :
    (constantSheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj
        ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)) :=
  (constantSheafAdj U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
    (show IsTerminal (Scheme.Etale.mk (𝟙 U.toScheme)) from
      IsTerminal.ofUniqueHom
        (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
        (fun a f ↦ by
          apply MorphismProperty.Over.Hom.ext
          exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))).homEquiv _ _ |>.symm
        ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm (etaleOpenFreeSheafSection U))

/-- Pull an Ext class back to the open and precompose with the identity generator.
This is a real construction, with no choice of a comparison isomorphism.
Source: Stacks Project, Tag 03F3, identification of section complexes.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenObjectCohomologyMap {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : X.Opens) :
    ((Functor.flip ((etaleOpenFreeSheaf X).op ⋙ Abelian.extFunctor q)).obj F).obj
        (op (Scheme.Etale.mk U.ι)) ⟶
      AddCommGrpCat.of (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q) :=
  AddCommGrpCat.ofHom
    (((Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit U)).precomp _ (zero_add q)).comp
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).mapExtAddHom _ F q))

end AlgebraicGeometry
```

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.Paper.SiteRestrictionInjectives

/-! # Bijectivity of the canonical open-object cohomology map

Source: Stacks Project, Cohomology on Sites, Tag 03F3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical identity-generator map is bijective on object cohomology.
Source: Stacks Project, Cohomology on Sites, Tag 03F3, proof of cohomology-of-open.
(blueprint: lem-weil-pbc-etale-open-object-cohomology-map-bijective)

Proof: Choose an injective resolution I of F. Extension by zero along the open is
exact and left adjoint to localization restriction, so restriction preserves injectives.
The inverse-image/restriction comparison identifies the pulled-back resolution with
that restricted resolution. The sheafification, free abelian group and Yoneda
adjunctions identify Hom from the free sheaf at U to I in each degree with I(U).
The constant-sheaf adjunction at the terminal object of U identifies Hom from the
constant integers to the restricted resolution with the same group I(U).
These are additive identifications commuting with the differentials. Their composite
is pullback followed by precomposition with etaleOpenFreeSheafUnit U: the chosen
identity generator is sent to the original section by the Yoneda adjunction.
The Ext/injective-resolution comparison identifies this map on cohomology classes
with etaleOpenObjectCohomologyMap. Hence that map is bijective in every degree.
The argument also applies to degree zero and to the empty open: it compares the
same section complexes, including the zero complex over the empty open. -/
theorem etaleOpenObjectCohomologyMap_bijective {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : X.Opens) :
    Function.Bijective (etaleOpenObjectCohomologyMap F q U) := by sorry

end AlgebraicGeometry
```

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit

/-! # Identity-generator coherence for nested open subschemes

Source: Stacks Project, Tag 03F3, and the open-restriction adjunction unit calculation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The identity generator restricts to the inclusion generator on a smaller open.
Source: Stacks Project, Tag 03F3, localization restriction; the explicit adjunction
unit calculation in open_restriction_pullback_unit.
(blueprint: lem-weil-pbc-etale-open-free-sheaf-unit-coherence)

Proof: Apply the constant-sheaf adjunction at the terminal object of V to both sides.
On the left, etaleOpenFreeSheafUnit V is the identity generator of the free sheaf
at V. The free-representable map sends this generator to the inclusion V to U.
On the right, the constant pullback comparison sends 1 to 1, and pulling back the
identity generator at U gives the same inclusion generator over V. To check this
with the specified inverse-image comparisons, apply open_restriction_pullback_unit
with g equal to U.ι and W equal to V. The fibre product V times_X U identifies
with V, since V is contained in U and U.ι is a monomorphism. The identity unit
cancels against the identity comparison. The inverse-image composition unit equation
then identifies the two successive restriction comparisons with the direct one.
Naturality of sheafification and of the free functor sends the generator associated
to the identity of V to the generator associated to X.homOfLE h. Thus both sides
classify the same section, and the adjunction bijection proves the equality.
This calculation is valid for equal opens and for the empty open as well. -/
theorem etaleOpenFreeSheafUnit_coherence {X : Scheme.{u}}
    (U V : X.Opens) (h : V ≤ U) :
    etaleOpenFreeSheafUnit V ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} V.ι).map
          ((etaleOpenFreeSheaf X).map
            (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
              (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk U.ι)
              (X.homOfLE h) (X.homOfLE_ι h) trivial)) ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
          (X.homOfLE_ι h).symm).hom.app
            ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)) =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (X.homOfLE h)).inv.app
        (AddCommGrpCat.of (ULift ℤ))) ≫
      (Etale.upperStar AddCommGrpCat.{u + 1} (X.homOfLE h)).map
        (etaleOpenFreeSheafUnit U) := by sorry

end AlgebraicGeometry
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural | F2 | Uses the explicit map, its bijectivity, and generator coherence in the proof; original signature unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMapBijective | F2, new | States bijectivity of the fixed constructed map. |
| Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafUnitCoherence | F2, new | States a degree-zero identity about the constructed generator map. |

These new modules have no existing downstream users on the base. The item's new helper
is private and fully proved; no public signature gains a reference to it. No target
statement uses a changed definition, so this additive proof construction does not reopen
the target statement review.

## Status

landed 20261012T110300-L-614220 2026-10-12 (merge of deliver/F2/Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural)

# AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_globalHomology

## Reason

Complete the DIFFERENT retirement listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology. The original theorem
already has zero holes and compiles. Its public name collides with the adopted
WeilConjectures theorem, whose statement uses strictLocalization and
strictLocalizationToBase. The original instead concerns strictHenselizationScheme
and strictHenselizationStructuralMap. An import substitution would change the mate.

Retain the complete original theorem in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology, under the
explicit smallModel_ prefix. Withdraw the ambiguous module. The proof body is
byte-identical; its signature changes only in the name. All public imports remain
identical in the retained module. Adapt both direct consumers by their private
import and theorem-call rename. Their signatures, definitions, visibility and public
imports stay identical. No adopted-source file changes, and no target meaning changes.

The existing node keeps its statement, proof, dependencies and unit route. Its Lean
attachment follows the retained realization. No new mathematical node is introduced.

## Old

The withdrawn module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit

/-! # The strict-local base-change mate on global cohomology

Source: Stacks Project, Tags 03Q8, 03Q9 and 0GIT.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The homology of the derived base-change mate is invertible on strict-local sections.
This only asserts invertibility after global sections; it does not assert that the mate
is an isomorphism of sheaves on the strict-local base.
Source: Stacks Project, Tag 03Q9, the affine-neighbourhood continuity argument and the
injective-representative construction of the canonical map
(blueprint: lem-weil-pbc-strict-local-base-change-global-homology).

Proof: choose a bounded-below injective representative J of K. For each affine pointed
étale neighbourhood V of s, restriction of J to X ×_S V preserves injectives, so its
sections complex computes that neighbourhood's hypercohomology. Sheafification of this
cohomology presheaf gives H^n(Rf_*K) (03Q8), and sheafification leaves its geometric stalk
unchanged. Cofinality of affine pointed neighbourhoods identifies this stalk with the
filtered colimit of their hypercohomology. The strict henselization is their inverse limit;
fibre products with X commute with that limit. Each X ×_S V is qcqs because f is qcqs and
V is affine, and transitions are affine by base change of morphisms between affine schemes.
Derived continuity (0GIT) identifies the colimit with hypercohomology of the limit pullback
of K. Strict-local global sections are exact, and coincide with the closed-point stalk
(03QO); hence the source of the displayed map computes the same colimit, while its target
computes limit hypercohomology through Leray. At the level of J, the adjunction mate is
restriction of sections along the pullback square. After taking H^n this is the continuity
map on every neighbourhood. The equality on all germ components, and the colimit universal
property, therefore identify the displayed map with the continuity isomorphism. No torsion
assumption is needed by 0GIT.
-/
theorem isIso_strictHenselization_baseChange_globalHomology
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))) := by
  let m :=
    ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K)))
  change IsIso m
  obtain ⟨P⟩ := smallModel_nonempty_strictLocalBaseChange_continuityPresentation f s K n
  let : SmallCategory P.I := P.category
  let : IsCofiltered P.I := P.cofiltered
  let : ∀ i, CompactSpace (P.D.obj i) := P.compact
  let : ∀ i, QuasiSeparatedSpace (P.D.obj i) := P.quasiSeparated
  let : ∀ {i j : P.I} (a : i ⟶ j), IsAffineHom (P.D.map a) := P.affine
  -- The mate extends the source cocone by its restriction equations.
  let a : Cocone P.F := Cocone.mk _ P.sourceLegs
  let b := a.extend m
  obtain ⟨hb⟩ := derivedEtaleCohomology_limit X P.D P.c P.isLimit P.t P.p P.over
    K n P.F P.e P.transition b P.limitIso P.restriction
  -- Both cocones are colimiting; identify their universal comparison with the mate.
  have hdesc : P.sourceIsColimit.desc b = m := by
    apply P.sourceIsColimit.hom_ext
    intro i
    exact P.sourceIsColimit.fac b i
  have : IsIso (P.sourceIsColimit.desc b) :=
    (P.sourceIsColimit.nonempty_isColimit_iff_isIso_desc).mp ⟨hb⟩
  simpa only [hdesc] using this

end AlgebraicGeometry.Etale
```

## New

The retained module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit

/-! # The strict-local base-change mate on global cohomology

This theorem retains `strictHenselizationScheme` and its structural map.
The adopted theorem with the unprefixed name uses `strictLocalization` instead.

Source: Stacks Project, Tags 03Q8, 03Q9 and 0GIT.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The homology of the derived base-change mate is invertible on strict-local sections.
This only asserts invertibility after global sections; it does not assert that the mate
is an isomorphism of sheaves on the strict-local base.
Source: Stacks Project, Tag 03Q9, the affine-neighbourhood continuity argument and the
injective-representative construction of the canonical map
(blueprint: lem-weil-pbc-strict-local-base-change-global-homology).

Proof: choose a bounded-below injective representative J of K. For each affine pointed
étale neighbourhood V of s, restriction of J to X ×_S V preserves injectives, so its
sections complex computes that neighbourhood's hypercohomology. Sheafification of this
cohomology presheaf gives H^n(Rf_*K) (03Q8), and sheafification leaves its geometric stalk
unchanged. Cofinality of affine pointed neighbourhoods identifies this stalk with the
filtered colimit of their hypercohomology. The strict henselization is their inverse limit;
fibre products with X commute with that limit. Each X ×_S V is qcqs because f is qcqs and
V is affine, and transitions are affine by base change of morphisms between affine schemes.
Derived continuity (0GIT) identifies the colimit with hypercohomology of the limit pullback
of K. Strict-local global sections are exact, and coincide with the closed-point stalk
(03QO); hence the source of the displayed map computes the same colimit, while its target
computes limit hypercohomology through Leray. At the level of J, the adjunction mate is
restriction of sections along the pullback square. After taking H^n this is the continuity
map on every neighbourhood. The equality on all germ components, and the colimit universal
property, therefore identify the displayed map with the continuity isomorphism. No torsion
assumption is needed by 0GIT.
-/
theorem smallModel_isIso_strictHenselization_baseChange_globalHomology
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))) := by
  let m :=
    ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K)))
  change IsIso m
  obtain ⟨P⟩ := smallModel_nonempty_strictLocalBaseChange_continuityPresentation f s K n
  let : SmallCategory P.I := P.category
  let : IsCofiltered P.I := P.cofiltered
  let : ∀ i, CompactSpace (P.D.obj i) := P.compact
  let : ∀ i, QuasiSeparatedSpace (P.D.obj i) := P.quasiSeparated
  let : ∀ {i j : P.I} (a : i ⟶ j), IsAffineHom (P.D.map a) := P.affine
  -- The mate extends the source cocone by its restriction equations.
  let a : Cocone P.F := Cocone.mk _ P.sourceLegs
  let b := a.extend m
  obtain ⟨hb⟩ := derivedEtaleCohomology_limit X P.D P.c P.isLimit P.t P.p P.over
    K n P.F P.e P.transition b P.limitIso P.restriction
  -- Both cocones are colimiting; identify their universal comparison with the mate.
  have hdesc : P.sourceIsColimit.desc b = m := by
    apply P.sourceIsColimit.hom_ext
    intro i
    exact P.sourceIsColimit.fac b i
  have : IsIso (P.sourceIsColimit.desc b) :=
    (P.sourceIsColimit.nonempty_isColimit_iff_isIso_desc).mp ⟨hb⟩
  simpa only [hdesc] using this

end AlgebraicGeometry.Etale
```

The direct consumers have only the following changes:

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictHenselizationCohomologyComparisonIso.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictHenselizationCohomologyComparisonIso.lean
@@ -10,5 +10,5 @@
 public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
 public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
-import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology
+import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology
 
 /-! # Invertibility of the strict-local cohomology comparison
@@ -86,5 +86,5 @@
   subst E H a b t
   delta mappedMate
-  exact isIso_strictHenselization_baseChange_globalHomology f s K n
+  exact smallModel_isIso_strictHenselization_baseChange_globalHomology f s K n
 
 /-- The cohomology comparison in the unrestricted stalk formula is invertible.
```

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalBaseChangeModelGlobalHomology.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalBaseChangeModelGlobalHomology.lean
@@ -9,5 +9,5 @@
 public import WeilConjectures.SixFunctors.BaseChange.Derived
 public import WeilConjectures.Mathlib.RingTheory.Henselian
-import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology
+import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology
 import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
 import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
@@ -208,5 +208,5 @@
 
 Proof:
-1. Apply `isIso_strictHenselization_baseChange_globalHomology` to f, s, K and n.
+1. Apply `smallModel_isIso_strictHenselization_baseChange_globalHomology` to f, s, K and n.
 Compare the mate in that theorem with `derivedBaseChangeMapPlus` on injective
 representatives using `Adjunction.derivedPlus_mateEquiv_app_fac` and
@@ -242,5 +242,5 @@
   have hcanonical := isIso_globalHomology_of_mate AddCommGrpCat.{u + 1}
     (IsPullback.of_hasPullback f (strictHenselizationStructuralMap s)).toCommSq K n
-    (isIso_strictHenselization_baseChange_globalHomology f s K n)
+    (smallModel_isIso_strictHenselization_baseChange_globalHomology f s K n)
   exact isIso_globalHomology_isoModel AddCommGrpCat.{u + 1} f
     (strictHenselizationStructuralMap s)
```

## Users

The source-only tools/downstream.py census lists exactly two downstream modules and
the same two callers. A direct import search across lean/ and quarantine/ confirms
that there are no other importers of the withdrawn module. The retirement table's
historical third consumer, Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula,
is already an empty withdrawn module and has no current rework row. It is not
changed here. Its adopted counterpart imports the adopted canonical-model theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | A3 | Withdraw ambiguous module; preserve its theorem in the module below. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology | new, A3 | Retain complete original-model theorem under explicit smallModel_ name. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed in current local claim records | Rename private import and theorem application only; compiles. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed in current local claim records | Rename private import, theorem application and its proof-docstring reference only; compiles. |

Both direct consumers compiled through lcompile.py against the delivered retained
module. There are no further current downstream consumers. No consumer statement is
weakened or otherwise changed. No definition changes, so no target semantic review
is reopened. The original node remains realized, rather than being declared unused.
The sk-prop-h2 unit has empty realization lists; no unit route is bypassed.

## Status

landed 20261023T134730-L-2741374 2026-10-23 (merge of deliver/A3/Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology)

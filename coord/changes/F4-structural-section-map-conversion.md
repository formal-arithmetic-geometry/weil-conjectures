# qcoherentPullbackSection

## Reason

The structural map has the same signature and is proved equal to its existing construction.
Kernel conversion at the required lifted component formula repeatedly unfolded the entire
composition, exceeding the file limit. A copy chosen from a proved unique equality prevents that
unfolding; sectionMapCopy_eq exposes the original formula for mathematical proofs. Its existence
and uniqueness theorem is proved. No witness is taken from an unproved existence assertion.
No source-library file or target statement is changed.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # The structural tensor-section pullback formula

Source: Stacks Project, Tags 03P2, 03DR and 01FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- Structural pullback of a tensor section across a square, followed by the module map.
Source: Stacks Project, Tags 03P2, 03DR and 01FD.
(blueprint: lem-weil-pbc-qcoherent-pullback-sections-map). -/
def qcoherentPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj G, ⊤) :=
  tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ ≫
    ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
    ((tensorPullback V.hom).map ψ).app ⊤

end
end AlgebraicGeometry.Scheme.Modules
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # The structural tensor-section pullback formula

Source: Stacks Project, Tags 03P2, 03DR and 01FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- A copy of a section morphism is uniquely determined by equality to that morphism.
Source: equality reflexivity and uniqueness.
(blueprint: lem-weil-pbc-qcoherent-pullback-sections-map)

Proof: Use the given map itself. Any map equal to it is that same map. -/
theorem existsUniqueSectionMapCopy {A B : Ab.{u}} (f : A ⟶ B) :
    ∃! k : A ⟶ B, k = f := by
  exact ⟨f, rfl, fun k hk ↦ hk⟩

/-- A uniquely specified copy keeps section maps stable under kernel conversion. -/
def sectionMapCopy {A B : Ab.{u}} (f : A ⟶ B) : A ⟶ B :=
  Classical.choose (existsUniqueSectionMapCopy f)

/-- Copying preserves the section morphism exactly.
Source: the defining unique equality.
(blueprint: lem-weil-pbc-qcoherent-pullback-sections-map)

Proof: The chosen map satisfies its defining equality to the original map. -/
theorem sectionMapCopy_eq {A B : Ab.{u}} (f : A ⟶ B) : sectionMapCopy f = f :=
  (Classical.choose_spec (existsUniqueSectionMapCopy f)).1

/-- Structural pullback of a tensor section across a square, followed by the module map.
Source: Stacks Project, Tags 03P2, 03DR and 01FD.
(blueprint: lem-weil-pbc-qcoherent-pullback-sections-map). -/
def qcoherentPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj G, ⊤) :=
  sectionMapCopy (
  tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ ≫
    ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
    ((tensorPullback V.hom).map ψ).app ⊤)

end
end AlgebraicGeometry.Scheme.Modules
```

## Users

QcoherentPullbackSectionsNaturality is new in this packet. Its explicit formula proof now rewrites
sectionMapCopy_eq after unfolding qcoherentPullbackSection. Other new consumers use its proved
API. The existing and quarantined consumers QcoherentNormalizedPullbackSquare and
QcoherentCohomologyComparisonPullback keep the same statement; the map has exactly the same
value and signature. The former is proved in this delivery, and the latter compiles unchanged against the new map (23.9 seconds).
The definition module was unclaimed when checked. Neither quarantined consumer requires a
signature or definition change.


The downstream query lists the first three modules below; the three new users are
also included. No existing consumer changes its signature or mathematical statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QcoherentPullbackSections | unclaimed | Same signature and map; uniquely determined copy construction. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | F4 | Same statement; the component formula uses the same map. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | Same statement and map; no adaptation needed. |
| Sheaf.AlgebraicGeometry.QcoherentPullbackSectionsNaturality | F4, new | Proves the original formula through sectionMapCopy_eq. |
| Sheaf.AlgebraicGeometry.QcoherentTensorPullbackSheafMap | F4, new | Uses the structural section map and its naturality theorem. |
| Sheaf.AlgebraicGeometry.QcoherentPullbackCohomologyMaps | F4, new | Uses the proved global-unit formula; no unfolding of the copied map. |

## Status

landed 20261021T012358-L-2182839 2026-10-21 (merge of deliver/F4/Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare)

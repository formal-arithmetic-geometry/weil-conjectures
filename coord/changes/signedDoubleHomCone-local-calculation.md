# CategoryTheory.SignedDoubleHomCone projection API and local proof commands

## Reason

The seven-step signed component calculation is proved through a private abstract
Hom/projection interface. Keeping `homComplexFunctor` abstract prevents repeated
unfolding of the chosen bifunctor during elaboration. The delivery checker
conservatively classifies the added namespace, variable and local attribute
commands as an interface change. In addition, repeated elaboration of the raw
choice specifications made the complete file reach the 60-second limit. The
existing component API supplies exactly those choices and their laws. Reusing
it reduces the full compile to 27 seconds without changing the chosen objects.

## Old

The original file has no local irreducibility attribute or `Calculation`
namespace. Its public context is:

```lean
universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SignedDoubleHomCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}
```

The original projection bodies are:

```lean
noncomputable def proj (K I : Complex.{u, v, w, r} R) (n a b : ℤ) (h : a + n = b) :
    (homComplex K I).X n ⟶ SheafOfModules.homObj (K.X a) (I.X b) :=
  Classical.choose (homComplex_projections_exists (R := R)) K I n a b h

noncomputable def productLimit (K I : Complex.{u, v, w, r} R) (n : ℤ) :
    IsLimit (Fan.mk ((homComplex K I).X n) (fun a : ℤ ↦ proj K I n a (a + n) rfl)) :=
  Classical.choice
    ((Classical.choose_spec (homComplex_projections_exists (R := R))).1 K I n)
```

## New

Before the unchanged public context, the proof uses:

```lean
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.homComplexFunctor
```

The private `Calculation` namespace adds an abstract category and projection
specification, proves the signed shift and cone calculations, and closes before
the existing public context. All declarations in it are private and proved.
Before the original public definitions, the two transparency options are set to
`true`. These are elaboration settings for this file; the irreducibility
attribute is explicitly local. No persistent attribute is changed.

The two projection definitions now reuse the existing component API:

```lean
noncomputable def proj (K I : Complex.{u, v, w, r} R) (n a b : ℤ) (h : a + n = b) :
    (homComplex K I).X n ⟶ SheafOfModules.homObj (K.X a) (I.X b) :=
  homComplexπ K I n a b h

noncomputable def productLimit (K I : Complex.{u, v, w, r} R) (n : ℤ) :
    IsLimit (Fan.mk ((homComplex K I).X n) (fun a : ℤ ↦ proj K I n a (a + n) rfl)) :=
  homComplexIsLimit K I n
```

Both new bodies are definitionally equal to their old bodies.
`WeilConjectures.Algebra.Homology.HomComplexComponents` is publicly imported in
place of its projection-existence dependency because these definitions use its
API. The proof uses `homComplex_d_π` and `homComplexFunctor_map_f_π`.
The unused public imports `Sheaf.CategoryTheory.SiteCoveringAxioms` and
`Mathlib.Algebra.Homology.DerivedCategory.Basic` are removed. None of the four
downstream modules uses `Precoverage.IsSiteForCoverings`, and their existing
imports already provide their derived-category declarations.
The other nine original public definitions and all public signatures, including
the complete nine-clause signature of `comparison`, are unchanged. No target
meaning changes.

## Users

`tools/downstream.py` lists these four downstream modules. None mentions
`homComplexFunctor`. The local commands do not alter their elaboration
environments, and the two definition bodies are definitionally equal to the
old bodies. No consumer adaptation is required.
The holder column records the current `coord/claims` entries. All four original
consumer files compile unchanged against the revised item after import pruning;
the import-ordered set check also compiles the item in 21.0 seconds. Separate
`rfl` checks confirm both replacement bodies equal their old expressions.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CoefficientBidualTriangles | G3 | Uses the unchanged comparison and dual definitions; no adaptation. |
| Sheaf.CategoryTheory.RelativeBidualTriangles | unclaimed | Uses the unchanged comparison and dual definitions; no adaptation. |
| Sheaf.Paper.DeltaRestriction | X9 | Receives the same public declarations through imports; no adaptation. |
| Sheaf.Paper.DualityPairing | D3 | Imports the same public API; no adaptation. |

## Status

landed 20261020T135428-L-1822569 2026-10-20 (merge of deliver/U1/Sheaf.Algebra.Homology.SignedDoubleHomCone)

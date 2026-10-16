# SheafOfModules.exists_moduleSheaf_of_cover_with_maps

## Reason

The auxiliary was split from `exists_moduleSheaf_of_cover` with an independent section
universe `v`. The parent, correctly, already used `max uC vC w v`. An arbitrary universe
is not closed under products indexed by a larger family or by all objects and arrows of
a larger site. For example, on the open-set site of a sufficiently large discrete set,
the covering by singletons and one-dimensional F₂-module sheaves on the singletons
force a global module with all functions from the discrete set to F₂ as sections.
There need not be a representative of that section set in the smaller universe.

Use the parent's existing universe for both input and output modules in the auxiliary.
This corrects the auxiliary's size convention; no `Challenge.lean` target changes.
The intended mathematical module-sheaf gluing assertion and every term hypothesis and
conclusion clause are retained. Source: Stacks Project, Sites, Tag 04TR,
https://stacks.math.columbia.edu/tag/04TR.

The original parent source fails against the corrected auxiliary at its call with
`stuck at solving universe constraint max (max (max uC vC) w) ?u =?=
max (max (max uC v) vC) w`. Give that call its five universe arguments explicitly.
This is the only adapted line; the parent's statement and visibility are untouched.
The parent is currently unclaimed.

The new `SiteModuleCompatibleTuples` module contains real constructions and fully
proved lemmas: compatible families indexed by all test spans, restriction, module
operations, graph evaluation, transition extension, their inverse equations and local
isomorphisms, and the coordinatewise sheaf condition. It adds no axiom or unfinished
proof. Choosing a local amalgamation uses a proved unique-existence sheaf axiom.

Remove the unused proof import `Sheaf.CategoryTheory.SiteCoveringAxioms` from the
auxiliary, and the redundant direct public import `Mathlib.Algebra.Module.Equiv.Defs`.
The latter remains available through the existing public Mathlib dependency chain;
no declaration used by a statement loses visibility.

## Old

```lean
theorem exists_moduleSheaf_of_cover_with_maps
    {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (U : C) (I : Type w) (Uᵢ : I → Over U)
    (hcover : Presieve.ofArrows (fun i ↦ (Uᵢ i).left) (fun i ↦ (Uᵢ i).hom) ∈ J U)
    (A : Sheaf (J.toGrothendieck.over U) RingCat.{uR})
    (hcomm : ∀ (W : (Over U)ᵒᵖ) (r s : A.obj.obj W), r * s = s * r)
    (Fᵢ : ∀ i : I, ringedSiteModules.{v, uR, vC, max uC vC}
      (A.over (Uᵢ i)))
    (φ : ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j),
      (Fᵢ i).val.obj (op (Over.mk (T := Over U) a)) ≃ₗ[A.obj.obj (op W)]
        (Fᵢ j).val.obj (op (Over.mk (T := Over U) b)))
    (hnatural : ∀ (i j : I) (W V : Over U) (k : V ⟶ W)
      (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i j V (k ≫ a) (k ≫ b) ((Fᵢ i).val.map
        (Over.homMk (U := Over.mk (T := Over U) (k ≫ a))
          (V := Over.mk (T := Over U) a) k rfl).op x) =
        (Fᵢ j).val.map
          (Over.homMk (U := Over.mk (T := Over U) (k ≫ b)) (V := Over.mk (T := Over U) b) k rfl).op
            (φ i j W a b x))
    (hcocycle : ∀ (i j k : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (c : W ⟶ Uᵢ k)
      (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i k W a c x = φ j k W b c (φ i j W a b x)) :
    ∃ F : ringedSiteModules.{v, uR, vC, max uC vC} A,
      ∃ e : ∀ i : I, F.over (Uᵢ i) ⟶ Fᵢ i,
      ∃ e_inv : ∀ i : I, Fᵢ i ⟶ F.over (Uᵢ i),
        (∀ i, e_inv i ≫ e i = 𝟙 _) ∧
        (∀ i, e i ≫ e_inv i = 𝟙 _) ∧
        ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j)
          (x : F.val.obj (op W)),
          φ i j W a b ((e i).val.app (op (Over.mk (T := Over U) a)) x) =
            (e j).val.app (op (Over.mk (T := Over U) b)) x
```

Parent call:
```lean
    exists_moduleSheaf_of_cover_with_maps J U I Uᵢ hcover A hcomm Fᵢ φ hnatural hcocycle
```

## New

```lean
theorem exists_moduleSheaf_of_cover_with_maps
    {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (U : C) (I : Type w) (Uᵢ : I → Over U)
    (hcover : Presieve.ofArrows (fun i ↦ (Uᵢ i).left) (fun i ↦ (Uᵢ i).hom) ∈ J U)
    (A : Sheaf (J.toGrothendieck.over U) RingCat.{uR})
    (hcomm : ∀ (W : (Over U)ᵒᵖ) (r s : A.obj.obj W), r * s = s * r)
    (Fᵢ : ∀ i : I, ringedSiteModules.{max uC vC w v, uR, vC, max uC vC}
      (A.over (Uᵢ i)))
    (φ : ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j),
      (Fᵢ i).val.obj (op (Over.mk (T := Over U) a)) ≃ₗ[A.obj.obj (op W)]
        (Fᵢ j).val.obj (op (Over.mk (T := Over U) b)))
    (hnatural : ∀ (i j : I) (W V : Over U) (k : V ⟶ W)
      (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i j V (k ≫ a) (k ≫ b) ((Fᵢ i).val.map
        (Over.homMk (U := Over.mk (T := Over U) (k ≫ a))
          (V := Over.mk (T := Over U) a) k rfl).op x) =
        (Fᵢ j).val.map
          (Over.homMk (U := Over.mk (T := Over U) (k ≫ b)) (V := Over.mk (T := Over U) b) k rfl).op
            (φ i j W a b x))
    (hcocycle : ∀ (i j k : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (c : W ⟶ Uᵢ k)
      (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i k W a c x = φ j k W b c (φ i j W a b x)) :
    ∃ F : ringedSiteModules.{max uC vC w v, uR, vC, max uC vC} A,
      ∃ e : ∀ i : I, F.over (Uᵢ i) ⟶ Fᵢ i,
      ∃ e_inv : ∀ i : I, Fᵢ i ⟶ F.over (Uᵢ i),
        (∀ i, e_inv i ≫ e i = 𝟙 _) ∧
        (∀ i, e i ≫ e_inv i = 𝟙 _) ∧
        ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j)
          (x : F.val.obj (op W)),
          φ i j W a b ((e i).val.app (op (Over.mk (T := Over U) a)) x) =
            (e j).val.app (op (Over.mk (T := Over U) b)) x
```

Parent call:
```lean
    exists_moduleSheaf_of_cover_with_maps.{uC, vC, uR, w, v}
      J U I Uᵢ hcover A hcomm Fᵢ φ hnatural hcocycle
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.SiteModuleSheafGluingAux --uses
SheafOfModules.exists_moduleSheaf_of_cover_with_maps` lists fifteen downstream modules
and only the parent as a direct external user. The table includes both lists.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SiteModuleSheafGluingAux | D4 | Own auxiliary: corrected section universe, complete proof; all term hypotheses and conclusion clauses retained. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.CategoryTheory.SiteModuleSheafGluing | unclaimed | Only direct caller: already has the enlarged universe. One call now supplies explicit universe arguments; its signature and visibility are identical. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.Paper.CondensedLfpCoefficientModel | A4 | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| TargetsCheck | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Transitive user only: no use of the auxiliary declaration; statements and definitions unchanged. The public parent statement is identical. |

## Status

landed 20261016T054833-L-155587 2026-10-16 (merge of deliver/D4/Sheaf.CategoryTheory.SiteModuleSheafGluingAux)

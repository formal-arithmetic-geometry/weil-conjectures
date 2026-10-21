# StrictTower projected-comparison and equality-transport API

## Reason

Concrete component rewrites of alpha repeatedly expanded the large derived
functor data in the kernel. A generic component constructor and cancellation
calculation let the proof instantiate explicit functors without those rewrites.
The original alpha body is kept verbatim, so its existing rfl normalization
consumer remains valid. The arrows module is unclaimed.

## Old

There were no gCongr, projectedComparison, alphaNaturality,
projectedComparison_app, whiskeredComparison_split_cancel,
projectedComparison_cancel_of_factor or alpha_def declarations.
Every existing declaration signature, attribute, public import and data body
is retained verbatim.

## New

projectedComparison is a real natural transformation with the five specified
component factors. Its naturality is the proved alphaNaturality equation.
The proved alpha_def theorem identifies the unchanged original alpha with that
constructor. gCongr wraps the actual equality-transport isomorphism for G and
has a proved reflexivity equation. No witness of mere existence is used.

A generic split-cancellation theorem cancels the beta isomorphism, the clopen
counit/projection splitting and the surrounding compositors. Its factorization
version, used by the item, has signature:

```lean
theorem projectedComparison_cancel_of_factor
    {C D E P V : Type*} [Category C] [Category D] [Category E] [Category P] [Category V]
    (Ji : C ⥤ D) (Gp : D ⥤ E) (Gq : C ⥤ P) (Gs : P ⥤ V) (Js : V ⥤ P)
    (Jb : P ⥤ E) (Jsb Jk : V ⥤ E) (Gr₀ Gr : C ⥤ V)
    (t : Ji ⋙ Gp ≅ Gq ⋙ Jb) (ε : Gs ⋙ Js ⟶ 𝟭 P) (π : 𝟭 P ⟶ Gs ⋙ Js)
    (c₁ : Js ⋙ Jb ≅ Jsb) (c₂ : Jsb ≅ Jk)
    (d₁ : Gq ⋙ Gs ≅ Gr₀) (d₂ : Gr₀ ≅ Gr)
    (hε : ∀ M, ε.app M ≫ π.app M = 𝟙 _)
    (a : Ji ⋙ Gp ⟶ Gr ⋙ Jk)
    (ha : a = projectedComparison Ji Gp Gq Gs Js Jb Jsb Jk Gr
      t.hom π c₁.hom c₂.hom (d₁.hom ≫ d₂.hom))
    (u : Gq ⋙ Jb ⟶ Ji ⋙ Gp) (hu : u = t.inv) (N : C)
    (A : Jk.obj (Gr.obj N) ⟶ Gp.obj (Ji.obj N))
    (hA : A = Jk.map (d₂.inv.app N ≫ d₁.inv.app N) ≫
      c₂.inv.app (Gs.obj (Gq.obj N)) ≫ c₁.inv.app (Gs.obj (Gq.obj N)) ≫
      Jb.map (ε.app (Gq.obj N)) ≫ u.app N) :
    A ≫ a.app N = 𝟙 _
```

All new theorem proofs are complete. A private component formula and private
comparison-with-whiskering theorem support the API. The AlphaComponents section
locally protects the concrete functors and adjunctions while checking the API;
these settings end before gamma. Only the new component constructor and gCongr
receive irreducibility attributes; existing declaration attributes are unchanged.

## Users

These APIs are new, so only the following packet modules consume them.
Existing alpha users require no adaptation. In particular the original private
alpha_app_definition of ProperOpenTowerComparison remains an rfl proof because
the alpha body is unchanged. No target statement or definition changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows | unclaimed | Adds proved APIs; keeps existing data verbatim. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | U3 | Uses explicit cancellation API. |
| Sheaf.AlgebraicGeometry.SingleProperOpenArrows | U3, new | Uses the real generic component constructor. |

## Status

landed 20261021T024203-L-3042570 2026-10-21 (merge of deliver/U3/Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus)

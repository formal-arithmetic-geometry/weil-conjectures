# tensorBicomplex and tensorBicomplexMap

## Reason

The two declarations duplicated Mathlib's bifunctorial homological-complex
construction.  The upstream review requests using the existing construction
directly, so the bespoke `ofGradedObject` data and `homMk` proof are removed.
This also makes the public definitions definitionally equal to the canonical
Mathlib objects.

## Old

```lean
def tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) :=
  ofGradedObject (.down ℕ) (.down ℕ)
    (fun pq => P.X pq.1 ⊗ Q.X pq.2)
    (fun p p' q => P.d p p' ⊗ₘ 𝟙 (Q.X q))
    (fun p q q' => 𝟙 (P.X p) ⊗ₘ Q.d q q')
    (by intro p p' h q; simp [P.shape p p' h])
    (by intro p q q' h; simp [Q.shape q q' h])
    (by
      intro p p' p'' q
      simp only [tensorHom_comp_tensorHom, HomologicalComplex.d_comp_d, Category.comp_id]
      simp)
    (by
      intro p q q' q''
      simp only [tensorHom_comp_tensorHom, HomologicalComplex.d_comp_d, Category.comp_id]
      simp)
    (by
      intro p p' q q'
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp])

/-- A pair of chain maps acts termwise on the tensor bicomplex.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
def tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') : tensorBicomplex P Q ⟶ tensorBicomplex P' Q' :=
  homMk (fun pq => a.f pq.1 ⊗ₘ b.f pq.2)
    (by intro p p' q h; simp only [tensorBicomplex, ofGradedObject_d_f, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, a.comm p p'])
    (by intro p q q' h; simp only [tensorBicomplex, ofGradedObject_X_d, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, b.comm q q'])
```

## New

```lean
abbrev tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) :=
  ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).obj P).obj Q

/-- A pair of chain maps acts termwise on the tensor bicomplex.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') : tensorBicomplex P Q ⟶ tensorBicomplex P' Q' :=
  ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).map a).app Q ≫
    ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).obj P').map b
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.TorSymmetry | unclaimed | Compiles unchanged against the canonical abbrev and map. |
| Sheaf.Algebra.Homology.FlatResolutionTorComparison | unclaimed | Forced proof adaptation: canonical differential simp lemmas and explicit d_comp_d. |
| Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso | unclaimed | Forced proof adaptation: canonical differential/map simp lemmas; signatures unchanged. |
| Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso | unclaimed | Forced proof adaptation: canonical differential/map simp lemmas; signatures unchanged. |

The downstream scan found 1340 transitive importers, with exactly the four direct
users above mentioning the changed declarations. No term, differential or component
map changes mathematically: scratch checks establish the tensor formulas in all
degrees (including zero and nonadjacent degrees). Thus definitions used by targets
retain their meaning; the second reading verifies this definition change for the
target statement review. No target statement is changed. The three adapted modules
are unclaimed in the inspected claims directory; TorSymmetry needs no adaptation.

The forced changed lines replace ofGradedObject_d_f/ofGradedObject_X_d and homMk_f_f
with the corresponding mapBifunctorHomologicalComplex simp lemmas, then rewrite
whiskerings as tensorHom. The row naturality proof needs these rewrites before
change, since the canonical map is a composition. FlatResolutionTorComparison
uses the named d_comp_d identity for the local short-complex zero proof.

The redundant direct public import of HomologicalBicomplex is removed: Bifunctor
exports it through TotalComplex. Additive remains public because chainTensorMap
uses mapHomologicalComplex in its type and body.

## Status

landed 20261013T201804-L-3975120 2026-10-13 (merge of deliver/N2/Sheaf.Algebra.Homology.TensorBicomplex)

# Proof-checking commands in Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence

## Reason

The first server preflight requires a change record because its interface scanner
classifies new module-level checking options and `omit ... in` commands as interface
changes. This record documents those commands. No existing declaration signature,
universe, instance, attribute, definition body, notation or public import changes.
The three existing public definitions remain verbatim. There is no mathematical
statement or definition repair and no consumer adaptation.

`autoImplicit false` makes the existing project convention explicit.
`backward.isDefEq.respectTransparency false` permits the proof's dependent functor
and page comparison expressions to elaborate. The new `omit` commands apply only
to private helper theorems. The scoped `maxHeartbeats` option applies only to checking
the completed theorem proof; it does not change Lean's server time limit.

## Old

The archived item opens its public section directly with its universe declaration:

```lean
@[expose] public section

universe u w
```

Its theorem signature is:

```lean
theorem bounded_tensor_tor_spectral_sequence :
    ∃ (S : Bounded (ModuleCat.{u} R) ⥤ Bounded (ModuleCat.{u} R) ⥤
        E₂CohomologicalSpectralSequence (ModuleCat.{u} R))
      (F : ∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        DecreasingFiltration
          ((homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj)))
      (N : Bounded (ModuleCat.{u} R) → Bounded (ModuleCat.{u} R) → ℤ → ℤ → ℤ)
      (hN : ∀ (C D : Bounded (ModuleCat.{u} R)) (n p : ℤ), 2 ≤ N C D n p)
      (e₂ : ∀ (C D : Bounded (ModuleCat.{u} R)) (p q : ℤ),
        (((S.obj C).obj D).page 2).X (p, q) ≅ kunnethTorPage R p q C D)
      (eInf : ∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ)
          (hr : 2 ≤ r) (hs : N C D n p ≤ r),
        (F C D n).gr p ≅ (((S.obj C).obj D).page r hr).X (p, n - p)),
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        ∃ a b : ℤ, (F C D n).F a = ⊤ ∧ (F C D n).F b = ⊥) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D')
          (p q : ℤ),
        (((S.map f).app D ≫ (S.obj C').map g).hom 2).f (p, q) ≫
            (e₂ C' D' p q).hom =
          (e₂ C D p q).hom ≫ kunnethTorPageMap R p q f g) ∧
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ) (hr : 2 ≤ r),
        N C D n p ≤ r →
          (((S.obj C).obj D).page r hr).dFrom (p, n - p) = 0 ∧
          (((S.obj C).obj D).page r hr).dTo (p, n - p) = 0) ∧
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ)
          (hr : 2 ≤ r) (hs : N C D n p ≤ r),
        (((S.obj C).obj D).page r hr).iCycles (p, n - p) ≫
            (eInf C D n p r hr hs).inv =
          (((S.obj C).obj D).page r hr).homologyπ (p, n - p) ≫
            (((S.obj C).obj D).iso r (r + 1) (p, n - p) rfl hr).hom ≫
              (eInf C D n p (r + 1) (by omega) (by omega)).inv) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D'),
        ∃ (a : ∀ (n p : ℤ), ((F C D n).F p : ModuleCat.{u} R) ⟶
              ((F C' D' n).F p : ModuleCat.{u} R))
          (b : ∀ n p : ℤ, (F C D n).gr p ⟶ (F C' D' n).gr p),
          (∀ n p : ℤ,
            a n p ≫ ((F C' D' n).F p).arrow =
              ((F C D n).F p).arrow ≫
                (homologyFunctor (ModuleCat.{u} R) n).map (f.hom ⊗ₘ g.hom)) ∧
          (∀ n p : ℤ,
            cokernel.π (Subobject.ofLE _ _ ((F C D n).F_succ_le p)) ≫ b n p =
              a n p ≫ cokernel.π (Subobject.ofLE _ _ ((F C' D' n).F_succ_le p))) ∧
          (∀ (n p r : ℤ) (hr : 2 ≤ r)
              (hs : N C D n p ≤ r) (ht : N C' D' n p ≤ r),
            b n p ≫ (eInf C' D' n p r hr ht).hom =
              (eInf C D n p r hr hs).hom ≫
                (((S.map f).app D ≫ (S.obj C').map g).hom r hr).f (p, n - p)))
```

## New

The restored item makes its proof-checking options explicit:

```lean
@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w
```

The private helper theorems `shiftGrIso_projection`, `stationary_transport`,
`stationary_at`, `graded_inverse_naturality`, and `page_index_naturality` each have
the local prefix:

```lean
omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
```

The main theorem has the scoped proof-checking prefix. Its original existential
binders `hN` and `hs` are used implicitly; their names are preserved verbatim.

```lean
set_option linter.unusedVariables false in
-- Preserve the original names of existential binders used only implicitly.
set_option maxHeartbeats 1000000 in
-- Associativity and naturality involve dependent page and filtered-graded indices.
```

Its signature remains verbatim:

```lean
theorem bounded_tensor_tor_spectral_sequence :
    ∃ (S : Bounded (ModuleCat.{u} R) ⥤ Bounded (ModuleCat.{u} R) ⥤
        E₂CohomologicalSpectralSequence (ModuleCat.{u} R))
      (F : ∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        DecreasingFiltration
          ((homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj)))
      (N : Bounded (ModuleCat.{u} R) → Bounded (ModuleCat.{u} R) → ℤ → ℤ → ℤ)
      (hN : ∀ (C D : Bounded (ModuleCat.{u} R)) (n p : ℤ), 2 ≤ N C D n p)
      (e₂ : ∀ (C D : Bounded (ModuleCat.{u} R)) (p q : ℤ),
        (((S.obj C).obj D).page 2).X (p, q) ≅ kunnethTorPage R p q C D)
      (eInf : ∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ)
          (hr : 2 ≤ r) (hs : N C D n p ≤ r),
        (F C D n).gr p ≅ (((S.obj C).obj D).page r hr).X (p, n - p)),
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        ∃ a b : ℤ, (F C D n).F a = ⊤ ∧ (F C D n).F b = ⊥) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D')
          (p q : ℤ),
        (((S.map f).app D ≫ (S.obj C').map g).hom 2).f (p, q) ≫
            (e₂ C' D' p q).hom =
          (e₂ C D p q).hom ≫ kunnethTorPageMap R p q f g) ∧
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ) (hr : 2 ≤ r),
        N C D n p ≤ r →
          (((S.obj C).obj D).page r hr).dFrom (p, n - p) = 0 ∧
          (((S.obj C).obj D).page r hr).dTo (p, n - p) = 0) ∧
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ)
          (hr : 2 ≤ r) (hs : N C D n p ≤ r),
        (((S.obj C).obj D).page r hr).iCycles (p, n - p) ≫
            (eInf C D n p r hr hs).inv =
          (((S.obj C).obj D).page r hr).homologyπ (p, n - p) ≫
            (((S.obj C).obj D).iso r (r + 1) (p, n - p) rfl hr).hom ≫
              (eInf C D n p (r + 1) (by omega) (by omega)).inv) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D'),
        ∃ (a : ∀ (n p : ℤ), ((F C D n).F p : ModuleCat.{u} R) ⟶
              ((F C' D' n).F p : ModuleCat.{u} R))
          (b : ∀ n p : ℤ, (F C D n).gr p ⟶ (F C' D' n).gr p),
          (∀ n p : ℤ,
            a n p ≫ ((F C' D' n).F p).arrow =
              ((F C D n).F p).arrow ≫
                (homologyFunctor (ModuleCat.{u} R) n).map (f.hom ⊗ₘ g.hom)) ∧
          (∀ n p : ℤ,
            cokernel.π (Subobject.ofLE _ _ ((F C D n).F_succ_le p)) ≫ b n p =
              a n p ≫ cokernel.π (Subobject.ofLE _ _ ((F C' D' n).F_succ_le p))) ∧
          (∀ (n p r : ℤ) (hr : 2 ≤ r)
              (hs : N C D n p ≤ r) (ht : N C' D' n p ≤ r),
            b n p ≫ (eInf C' D' n p r hr ht).hom =
              (eInf C D n p r hr hs).hom ≫
                (((S.map f).app D ≫ (S.obj C').map g).hom r hr).f (p, n - p)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence | F2 | Original public definitions and theorem signature unchanged; original hole proved. |
| Sheaf.Algebra.Homology.IntegralBoundedKunnethExact | unclaimed, quarantined | Archived direct importer; no adaptation because the public mathematical interface is unchanged. |

`tools/downstream.py --allow-missing --uses` reports zero live downstream modules
and zero live uses of all four original public declarations, because this item is
quarantined. Searching both live and quarantined Lean sources finds the archived
`IntegralBoundedKunnethExact` import. Its source is untouched. The item's DAG attachment,
its parent dependency, and the unit route are preserved; no withdrawal is requested.

## Status

landed 20261021T061041-L-1689610 2026-10-21 (merge of deliver/F2/Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence)

# AlgebraicGeometry.IsCanonicalDerivedTensorHom

## Reason

The original representative clause repeats a large elaborated sheaf tensor-Hom component
inside a quantified proposition. The unchanged file took about 54 seconds locally; adding
the uniqueness proof exceeded the 60-second limit. Name the actual uncurried component
in `schemeTensorHomUncurryComponent` and refer to it in the predicate. This is a real
construction, with no choice of additional data and no postponed proof. Unfolding the
helper gives the original expression by reflexivity; an isolated equality check
compiled with `:= rfl` against the delivered helper. All existing signatures remain
identical. The predicate has the same definitional meaning, so no target meaning changes.
The resulting full module compiled in 45.9 seconds; no file or proof was split to evade
the limit. The original definition bodies and global options otherwise stay unchanged.

## Old

```lean
def IsCanonicalDerivedTensorHom (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M)) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := schemeDerivedTensorMonoidal X
  letI := SheafOfModules.symmetricCategory X.sheaf
  (∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
    e K' L' M' (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map (b.op, c)) =
      (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
  (∀ (P L M : CochainComplex
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ),
    P.IsKFlat →
    ∀ φ : P ⟶ homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M),
      ∃ ψ : pullbackTensorTotal X P L ⟶
          (schemeHomKInjectiveResolution X).obj M,
        (∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
            ψ.f n =
          (β_ (P.X p) (L.X q)).hom ≫
            (SheafOfModules.tensorHomEquiv (L.X q) (P.X p)
              (((schemeHomKInjectiveResolution X).obj M).X n)).symm
              (φ.f p ≫ (Classical.choose (Classical.choose_spec
                (homComplex_exists (R := X.sheaf)))) L
                  ((schemeHomKInjectiveResolution X).obj M)
                  p q n h')) ∧
        e (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
            (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) =
          pullbackTensorModelMap X P L ≫ DerivedCategory.Q.map ψ ≫
            schemeHomResolutionInverse X M)
```

## New

```lean
def schemeTensorHomUncurryComponent (X : Scheme.{uCD})
    (P L M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h' : q + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    P.X p ⊗ L.X q ⟶ ((schemeHomKInjectiveResolution X).obj M).X n :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  (β_ (P.X p) (L.X q)).hom ≫
    (SheafOfModules.tensorHomEquiv (L.X q) (P.X p)
      (((schemeHomKInjectiveResolution X).obj M).X n)).symm
      (φ.f p ≫ (Classical.choose (Classical.choose_spec
        (homComplex_exists (R := X.sheaf)))) L
          ((schemeHomKInjectiveResolution X).obj M) p q n h')

/-- Naturality and the actual representative evaluation equation characterize the family.
The chain map ψ is fixed on every total-tensor summand by currying the degree-p
component of φ, projected to Hom(L^q,I(M)^(q+p)). The symmetry restores the order
P^p tensor L^q. The localization factorization and resolution map fix both targets.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def IsCanonicalDerivedTensorHom (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M)) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := schemeDerivedTensorMonoidal X
  letI := SheafOfModules.symmetricCategory X.sheaf
  (∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
    e K' L' M' (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map (b.op, c)) =
      (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
  (∀ (P L M : CochainComplex
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ),
    P.IsKFlat →
    ∀ φ : P ⟶ homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M),
      ∃ ψ : pullbackTensorTotal X P L ⟶
          (schemeHomKInjectiveResolution X).obj M,
        (∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
            ψ.f n =
          schemeTensorHomUncurryComponent X P L M φ p q n h') ∧
        e (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
            (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) =
          pullbackTensorModelMap X P L ≫ DerivedCategory.Q.map ψ ≫
            schemeHomResolutionInverse X M)
```

## Users

The transitive downstream census has 371 modules. Every such module retains the same
public declarations and definitional predicate. The following table lists all direct
textual users of the changed declaration (the `tools/downstream.py --uses` census).

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom | F3 | Predicate refactored; uniqueness proved. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | G1 | Same predicate and projections; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms | unclaimed | Same predicate and projections; no adaptation. |

No other module is changed in this delivery. No forced adaptations.

## Status

landed 20261012T194110-L-454887 2026-10-12 (merge of deliver/F3/Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom)

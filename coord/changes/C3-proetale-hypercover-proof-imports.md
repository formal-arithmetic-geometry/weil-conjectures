# hypercover_computes_boundedBelow_complex

## Reason

Prune the unused K-injective API import from the assigned module. Retain the public
affine-hypercover existence import for ProEtaleModuleCohomologyCoproducts. The hypercover,
matching limits, resolution maps and comparison homotopy are inputs, so none of their
existence theorems is used by this proof. The retained affine-hypercover import supplies
the matching-diagram definitions; derived-category Basic supplies the unchanged signature
without the K-injective API. Proof-only imports for the new comparison lemmas remain
non-public.

The existing theorem signature, universes, binders and conclusion are byte-for-byte
unchanged. No mathematical definition or target meaning changes. Proof-local options
increase the heartbeat allowance and permit the elaborator to compare the explicit
composed functors; their scopes end with the theorem, so they do not affect importers.

## Old

Public imports, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
public import Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
```

Existing theorem signature, verbatim:

```lean
theorem hypercover_computes_boundedBelow_complex (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W))
    [HasDerivedCategory.{w} (ModuleCat.{u + 1}
      (((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W)))]
    (hweak : ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left)))
    (hzero : Epi ((topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) :
    (∃ c : ∀ (E J : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))),
      (∀ n : ℤ, Injective (J.obj.X n)) →
      (i : E.obj ⟶ J.obj) → QuasiIso i →
      (DerivedCategory.Q.obj ((hypercoverTotal X R W U).obj E.obj) ≅
        DerivedCategory.Q.obj (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J.obj)),
      ∀ (E F J L : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
        (hJ : ∀ n : ℤ, Injective (J.obj.X n))
        (hL : ∀ n : ℤ, Injective (L.obj.X n))
        (i : E.obj ⟶ J.obj) (j : F.obj ⟶ L.obj)
        (hi : QuasiIso i) (hj : QuasiIso j) (f : E ⟶ F) (a : J ⟶ L),
        Nonempty (Homotopy (i ≫ a.hom) (f.hom ≫ j)) →
        DerivedCategory.Q.map ((hypercoverTotal X R W U).map f.hom) ≫
            (c F L hL j hj).hom =
          (c E J hJ i hi).hom ≫ DerivedCategory.Q.map
            (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map a.hom)) ∧
    (∀ (E F : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) (f : E ⟶ F),
      QuasiIso f.hom → QuasiIso ((hypercoverTotal X R W U).map f.hom))
```

## New

Public imports, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
public import Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
```

The theorem signature remains exactly the `Old` signature above. Its proof is now the
complete derived comparison assembled from the new lower statements and actual
augmentation maps. No existing definition was edited. No downstream module was adapted.

## Users

The current read-only downstream scan reports five downstream modules, below. The only
external use of the theorem is in `ProEtaleModuleCohomologyCoproducts`, which also uses the
publicly exported affine-hypercover existence theorem. This import is therefore retained.
Both direct callers are compiled unchanged against the sandbox overlay. No existing
signature or definition changes, and the K-injective API is unused by the signature.
The new exact-evaluation module publicly imports PreservesHomology and imports the
general abelian Exact API only for its proof; it has no pre-existing clients. Its
public sheaf-module Abelian import supplies required signature instance dependencies.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | unclaimed | Indirect user; no signature or definition changes. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts | unclaimed | Direct user; affine-hypercover re-export retained; compiles unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Indirect user; no signature or definition changes. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Direct user; compiles unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Indirect user; no signature or definition changes. |

## Status

landed 20261015T171715-L-504217 2026-10-15 (merge of deliver/C3/Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex)

# AlgebraicGeometry.Etale.closedSupportHom

## Reason

Implement the original theorem without changing its signature. The implementation adds
private cone and derived-comparison helpers, extra universe names, an `open
HomologicalComplex` command, scoped variables, and a local irreducibility attribute for
a private comparison definition. The stage-3 surface checker classifies these proof-context
commands as a possible interface change, so this record makes them independently reviewable.
The proof imports the new fully proved ordinary Hom sequence. No existing public definition,
notation, instance, target statement, or declaration signature is changed or removed.

Repair of returned head `9cef3f555`: the duplicate private `prev_rel` and `next_rel`
helpers are removed. Their uses now apply the existing public `ComplexShape.up_mk`
with the required index equation. The matching helpers in the source library are private.
This proof-only repair adds no interface change and requires no consumer adaptation.

Repair of returned head `0f7d9008b`: removed the private duplicate
`AlgebraicGeometry.Etale.ofNatIsoRight_unit_app` from the sequence module. The three
cited source copies are private. Its call site now uses Mathlib's public
`Adjunction.ofNatIsoRight_unit` with component and whiskering formulas, without
introducing another declaration or import. Both public signatures remain unchanged.

The source library already supplies the kernel-to-cone and concrete K-injective derived
computation. The ordinary sequence is constructed using the existing constant-sheaf and
extension-by-zero adjunctions, with the actual global-section restriction map.

## Old

The original theorem signature, verbatim:

```lean
theorem closedSupportHom (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ) :
    ∃ q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ),
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (n : ℤ), (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n)) ∧
      ∃ e : ∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (f : K ⟶ L),
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).map (DerivedCategory.Q.map f) ≫
          (e L).hom =
        (e K).hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (-1 : ℤ)).map
          (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
            (((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (((upperStar (ModuleCat.{u + 1} A) v ⋙
              Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (q.naturality ((CochainComplex.kInjectiveResolutionFunctor _).map f)).symm))
```

`AlgebraicGeometry.Etale.closedSupportHomSequence` did not exist.

## New

The theorem retains exactly the same signature:

```lean
theorem closedSupportHom (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ) :
    ∃ q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ),
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (n : ℤ), (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n)) ∧
      ∃ e : ∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (f : K ⟶ L),
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).map (DerivedCategory.Q.map f) ≫
          (e L).hom =
        (e K).hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (-1 : ℤ)).map
          (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
            (((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (((upperStar (ModuleCat.{u + 1} A) v ⋙
              Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (q.naturality ((CochainComplex.kInjectiveResolutionFunctor _).map f)).symm))
```

The added public helper has the following signature:

```lean
theorem closedSupportHomSequence (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∃ (α : (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
        (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)))) ⟶ Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
      (hzero : ∀ J, α.app J ≫ τ.app J = 0),
      ∀ J, Injective J → (ShortComplex.mk (α.app J) (τ.app J) (hzero J)).ShortExact
```

All other new declarations are private and proved. The public theorem signature was
compared with its existing node record and is identical. Extra context commands support
these proofs; they introduce no public instance or notation. The new node records the
helper's source, complete argument, and searches.

## Users

The prescribed command
`tools/downstream.py Sheaf.AlgebraicGeometry.ClosedSupportHom --uses
AlgebraicGeometry.Etale.closedSupportHom` reports zero downstream modules and only the
item itself as a textual user. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedSupportHom | K4 | Same public signature; complete proof and private helpers. |
| Sheaf.AlgebraicGeometry.ClosedSupportHomSequence | K4 (new module) | New proved underived sequence, with its new DAG node. |

The combined server compile passed: 33.6 seconds for the sequence and 28.1 seconds for the
main module. Both modules contain zero `sorry` tokens. No statement or definition used by
a target changes its meaning.

## Status

landed 20261018T092207-L-3361999 2026-10-18 (merge of deliver/K4/Sheaf.AlgebraicGeometry.ClosedSupportHom)

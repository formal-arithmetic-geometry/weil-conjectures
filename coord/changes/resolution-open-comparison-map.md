# AlgebraicGeometry.Scheme.Modules.resolutionOpenComparison

## Reason
Expose a constructed comparison so that restriction and scalar compatibility refer to the same map.
The comparison is a composition of genuine isomorphisms on the given restricted resolution.
No target or existing public signature changes; no data is selected from an unproved existence.

## Old
None: these are new declarations in new modules.

## New

```lean
def resolutionOpenComparison {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    (sectionCohomologyPresheaf
      (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) q).obj (op W) ≃+
      (RingedSpace.openModuleCohomology (f ⁻¹ᵁ W).toScheme.toRingedSpace q ⊤).obj
        ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F)
```

```lean
theorem restrictedResolutionSections_exists {X : Scheme.{uBC}} {F : X.Modules}
    (I : InjectiveResolution F) (U : X.Opens) :
    Nonempty (RestrictedResolutionSections I U)
```

```lean
theorem resolution_open_restriction_natural {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ W))
    (V : T.Opens) (hVW : V ≤ W) (U : (f ⁻¹ᵁ W).toScheme.Opens)
    (hU : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ V) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let c := resolutionOpenComparison f F I q W R
    ∃ d : P.obj (op V) ≃+
      (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G,
      ∀ x : P.obj (op W),
        (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
          (homOfLE (le_top : U ≤ ⊤))).app G (c x) =
            d ((P.map (homOfLE hVW).op).hom x)
```

```lean
theorem resolution_open_restriction_core {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let s : Γ(𝟙_ Y.Modules, ⊤) := unitSectionsEquiv ⊤ b
    let c := resolutionOpenComparison f F I q W R
    ∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus (𝟙_ Y.Modules) s →
      ∃ d : P.obj (op (T.basicOpen a)) ≃+
        (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G,
        ∀ x : P.obj (op W),
          (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
            (homOfLE (le_top : U ≤ ⊤))).app G (c x) =
              d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x)
```

```lean
theorem resolution_open_scalar_core {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let : CommRing (Y.ringCatSheaf.obj.obj (op ⊤)) :=
    inferInstanceAs (CommRing Γ(Y, ⊤))
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let c := resolutionOpenComparison f F I q W R
    ∀ (n : ℕ) (x : P.obj (op W)),
      (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
        (G.smulHom (b ^ n)) (c x) = c (a ^ n • x)
```

The private lemmas `unit_nonvanishing_basicOpen` and `homology_restriction_transport`
are proved local helpers and introduce no public interface or holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison | E4 | Its unchanged theorem combines the fixed comparison's two proved properties. |
| Sheaf.AlgebraicGeometry.ResolutionOpenComparisonMap | new in E4 | Constructs the comparison from genuine isomorphisms. |
| Sheaf.AlgebraicGeometry.RestrictedResolutionSectionsExist | new in E4 | Constructs an actual restricted resolution inside a theorem proof. |
| Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionNatural | new in E4 | Proves naturality of the fixed comparison for inverse-image opens. |
| Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionCore | new in E4 | Reduces the scalar nonvanishing open to restriction naturality. |
| Sheaf.AlgebraicGeometry.ResolutionOpenScalarCore | new in E4 | Proves scalar compatibility of the fixed comparison. |

## Status
landed 20261013T135101-L-155370 2026-10-13 (merge of deliver/E4/Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison)

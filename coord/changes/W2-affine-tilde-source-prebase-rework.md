# AlgebraicGeometry.affineTildeTensorOrdinarySourceIso

## Reason

Repair the quarantined prebase module by consolidating the duplicate Sheaf
implementations with the complete adopted source implementations. This is the
shorter existing-library route, with no new proof obligation. The old module
failed at a retired derived-pullback import; rebuilding its duplicated data and
proofs also exceeded the single-file limit after an initial successful compile.
The adopted source already supplies the same concrete constructions and theorems.

Three Sheaf modules become compatibility interfaces:
`AffineTildeTensorSourceComparisonCorePreBase`,
`AffineTildeTensorSourceComparisonHelpers`, and
`AffineTildePushforwardCohomologyNormalization`. The latter two were unclaimed.
All existing public declarations remain available at their previous import paths.
The legacy `affineTildeFunctor` is an abbreviation for the canonical
`affinePushforwardTilde`; both reduce to `tilde.functor (.of A)`. Its zero-map
instance reuses `affinePushforwardTilde_preservesZero`.

No file or declaration in `lean/WeilConjectures/` is modified. No definition in
a target statement changes its meaning. No unit route is bypassed.

## Old

The original modules defined their own copies of the normalization, generic
comparison helpers and prebase declarations. The two data constructions in the
archived item were:

```lean
def affineTildeTensorOrdinarySourceIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ≅
    ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let : (Scheme.Modules.tensorPullback g).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
    (.up ℤ)).obj M
  let : (affineTildeFunctor R).Additive :=
    instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : (affineTildeFunctor B).Additive :=
    instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap R B)).Additive :=
    ModuleCat.extendScalars_additive_sheaf _
  let θ : affineTildeFunctor R ⋙ Scheme.Modules.tensorPullback g ≅
      ModuleCat.extendScalars (algebraMap R B) ⋙ affineTildeFunctor B :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom (algebraMap R B)))
  let δ := (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app N
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  let : (affineTildeFunctor A).Additive :=
    instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : P.Additive := inferInstance
  let : (affineTildeFunctor A ⋙ P).Additive := inferInstance
  let : (affineTildeFunctor A ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affineTildeFunctor A).map_zero]
      exact P.map_zero _ _⟩
  let s : ((affineTildeFunctor R).mapHomologicalComplex (.up ℤ)).obj N ≅
      (P.mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) :=
    (Functor.mapHomologicalComplexCompIso
      (affineTildePushforwardComparison A R (algebraMap R A)) (.up ℤ)).app M
  exact δ.symm ≪≫
    ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).mapIso s

/-- The first two factors of the raw tensor map, before any coefficient map.
Source: Stacks Project, Tags 06Y6 and 06Z0.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison). -/
def affineTildeTensorDerivedCounit
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (F₀ : DerivedCategory.{wM} (ModuleCat.{u} B) ⥤
      schemeDerivedCategory.{u, w} (Spec (.of B)))
    (hF₀ : F₀ = Functor.mapDerivedCategory.{wM, w} (affineTildeFunctor B)) :
    F₀.obj
      (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)))) ⟶
    DerivedCategory.Q.obj
      (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).obj M))) := by
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj M
  let N' := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj N
  exact eqToHom (congrArg (fun G ↦ G.obj
      (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj N)))) hF₀) ≫
    (affineTildeFunctor B).mapDerivedCategory.map
      (m.counit.app ((HomotopyCategory.quotient _ _).obj N)) ≫
    ((affineTildeFunctor B).mapDerivedCategoryFactors.app N').hom
```

The legacy tilde definition was:

```lean
abbrev affineTildeFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
```

## New

The item preserves its three original public imports and adds:

```lean
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase
```

The helper likewise preserves its three public imports and adds:

```lean
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers
```

The normalization module preserves its four public imports and adds:

```lean
public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
```

Its only locally defined API consists of the two legacy names:

```lean
abbrev affineTildeFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) := affinePushforwardTilde A

@[instance] theorem affineTildeFunctor_preservesZero (A : Type u) [CommRing A] :
    (affineTildeFunctor A).PreservesZeroMorphisms :=
  affinePushforwardTilde_preservesZero A
```

The source prebase data are the old data above after expanding the two tilde
abbreviations and replacing the obsolete additivity proof by
`ModuleCat.baseDerivedTensor_extendScalars_additive`; proof irrelevance removes
that difference. The normalized old and source normalization implementations
are textually identical after this abbreviation substitution and removal of
blank lines. The two generic helper implementations differ additionally only
in line breaks of a local attribute command. The source prebase theorem proofs
are the same K-flat comparison and K-injective-resolution argument as the archive.
These are exact replacements of existing constructions and proofs, not choices
of arbitrary new witnesses.

The three normalization nodes are attached to the source declarations. Their
statements, proof plans, dependencies and unit realization are retained. The two
legacy alias names are retained in the Sheaf module rather than listed as
declarations of the source module;
they remain declared in the Sheaf compatibility module.

## Users

The source-only downstream check reports exactly the first three active users
below. Searches of the quarantine archive add the other direct importers. The assigned item and the two compatibility modules are the only changed
modules in this table. The two additional changed compatibility modules are
unclaimed. All effects are definitionally
identical API consolidation; there are no forced adaptations of another group's
module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization | unclaimed | Compatibility re-export; retains the legacy abbreviation and its instance. |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers | unclaimed | Compatibility re-export of the same generic comparison helpers. |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative | unclaimed | Same legacy tilde and normalization API. |
| Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates | unclaimed | Same cohomology map and comparison. |
| Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization | unclaimed | Same cohomology map and comparison. |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase | W2 | Restored as a compatibility import of its complete source implementation. |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre | unclaimed | Quarantined; same four prebase declarations and generic helpers. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization | unclaimed | Quarantined; same normalization construction and legacy abbreviation. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain | unclaimed | Quarantined; same source comparison construction. |

The report records the concrete compile and API checks. The maintainer's
independent reader should verify the exported source declarations and the
three updated Lean attachments. All quarantine archives remain untouched.

## Status

landed 20261020T230841-L-620461 2026-10-20 (merge of deliver/W2/Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase)

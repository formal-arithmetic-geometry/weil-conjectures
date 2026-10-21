# AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_derived_hom_descent

## Reason

The assigned Sheaf module contains zero holes and is explicitly listed for retirement
in coord/retire-items.tsv (DIFFERENT, one direct consumer). Its source counterpart
already proves a stronger theorem: no affineness hypothesis on U or strict-perfectness
hypothesis on Q, and the stalk comparison isomorphisms are canonical rather than
existential. Withdraw the duplicate and use the existing source theorem.

## Old

The withdrawn Sheaf declaration has signature:

```lean
theorem exists_affine_perfect_open_stalk_derived_hom_descent
    (X : Scheme.{u})
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    :
    let SU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
        ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X U ⟨x, hxU⟩
    letI : SU.PreservesZeroMorphisms :=
      AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X U ⟨x, hxU⟩
    ∀ t : DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj Q),
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      letI : S.Additive :=
        AlgebraicGeometry.openModuleStalkFunctor_additive X V ⟨x, hxV⟩
      letI : PreservesFiniteLimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteLimits X V ⟨x, hxV⟩
      letI : PreservesFiniteColimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteColimits X V ⟨x, hxV⟩
      ∃ (cP : DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj (T.obj P)) ≅
          DerivedCategory.Q.obj
            ((SU.mapHomologicalComplex (.up ℤ)).obj P))
        (cQ : DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj (T.obj Q)) ≅
          DerivedCategory.Q.obj
            ((SU.mapHomologicalComplex (.up ℤ)).obj Q))
        (g : DerivedCategory.Q.obj (T.obj P) ⟶ DerivedCategory.Q.obj (T.obj Q)),
        (S.mapDerivedCategoryFactors.app (T.obj P)).inv ≫
          S.mapDerivedCategory.map g ≫ (S.mapDerivedCategoryFactors.app (T.obj Q)).hom =
            cP.hom ≫ t ≫ cQ.inv
```

## New

Reuse this existing proved source declaration, unchanged:

```lean
theorem exists_affine_perfect_open_stalk_derived_hom_descent
    (X : Scheme.{u})
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (U : X.Opens) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) :
    let SU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
        ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X U ⟨x, hxU⟩
    letI : SU.PreservesZeroMorphisms :=
      AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X U ⟨x, hxU⟩
    ∀ t : DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj Q),
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      letI : S.Additive :=
        AlgebraicGeometry.openModuleStalkFunctor_additive X V ⟨x, hxV⟩
      letI : PreservesFiniteLimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteLimits X V ⟨x, hxV⟩
      letI : PreservesFiniteColimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteColimits X V ⟨x, hxV⟩
      let c : T ⋙ S.mapHomologicalComplex (.up ℤ) ≅ SU.mapHomologicalComplex (.up ℤ) :=
        Functor.mapHomologicalComplexCompIso
          (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      let cP := DerivedCategory.Q.mapIso (c.app P)
      let cQ := DerivedCategory.Q.mapIso (c.app Q)
      ∃ g : DerivedCategory.Q.obj (T.obj P) ⟶ DerivedCategory.Q.obj (T.obj Q),
        (S.mapDerivedCategoryFactors.app (T.obj P)).inv ≫
          S.mapDerivedCategory.map g ≫ (S.mapDerivedCategoryFactors.app (T.obj Q)).hom =
            cP.hom ≫ t ≫ cQ.inv
```

To obtain the original assertion, ignore its extra hypotheses hU and hQ and choose
the source theorem's canonical cP and cQ as the existential isomorphism witnesses.
The underlying opens, complexes, stalk rings, derived universes and equality are
identical. Zero complexes and zero free ranks are included; x in U excludes empty U.
The unit route is preserved, and all existing dependency nodes and edges remain.
The source proof uses exactly the retained bounded-projective and chain-map-lift
argument, followed by functoriality of Q and the derived factorization isomorphism.

The sole consumer's private import changes to the source module. It omits hU and hQ
at the theorem call, unpacks only g and hg, and explicitly defines the canonical
comparison c and its images cP and cQ. An explicit type for c fixes the stalk-ring
and derived-category inference. After the original associativity simplification,
rfl unfolds these comparison lets. Its public theorem signature, visibility,
attributes, universes, hypotheses, conclusion, docstring and public imports are
unchanged. The now unused original hU binder is retained, with the unused-variable
linter disabled only for this theorem. No file under lean/WeilConjectures is modified.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent | B5 | Withdrawn duplicate; node attached to the proved source declaration. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | unclaimed | Sole direct consumer: source private import and explicit canonical comparison witnesses; public signature unchanged. |

The downstream.py --uses check lists exactly these two declaration references and
one downstream module. Searches in lean/Sheaf, lean/WeilConjectures and quarantine
find no other importer of the withdrawn module. The only DAG parent is
lem-sc-perfect-stalk-derived-hom-lift; it continues to cite the same node, whose
Lean attachment now names the source theorem. Its proof description explains
how the canonical comparisons replace the old existential witnesses. No node is
deleted and no source declaration, signature, attribute, public import, definition
or instance is altered.

## Status

landed 20261021T001104-L-1369547 2026-10-21 (merge of deliver/B5/Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent)

# AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_chainMap_lift

## Reason

The assigned module has zero holes and is listed for retirement in coord/retire-items.tsv.
The source library proves a stronger result with the canonical restriction comparison.
Withdraw the duplicate and migrate its two direct consumers. No source file is changed.

## Old

The withdrawn Sheaf declaration has signature:

```lean
theorem exists_affine_perfect_open_stalk_chainMap_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (t : ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      ∃ (e : R ⋙ S ≅ T) (g : R.obj P ⟶ R.obj Q),
        S.map g = (e.app P).hom ≫ t ≫ (e.app Q).inv
```

## New

Reuse the existing proved source declaration, unchanged:

```lean
theorem exists_affine_perfect_open_stalk_chainMap_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (t : ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      let e : R ⋙ S ≅ T := Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      ∃ g : R.obj P ⟶ R.obj Q,
        S.map g = (e.app P).hom ≫ t ≫ (e.app Q).inv
```

The source theorem omits the unnecessary hU and hQ assumptions and fixes e to
Functor.mapHomologicalComplexCompIso of openModuleStalkRestrictionComparison. Taking
that explicit e proves the unchanged DAG statement, with the same affine neighbourhood
and the same chain map. This also covers equal opens, empty support, and zero ranks;
the hypothesis x in U rules out empty U. No target statement or definition changes.

The full source proof uses degreewise lifting, the conjugated chain-map equations,
degreewise shrinking, CochainComplex.ofHom, and cancellation of comparison inverses.
Both original dependency nodes remain needed and attached to their source results.
The unit route is preserved. The node is reattached to the source declaration; both
parent proof descriptions identify the canonical comparison used in the new proof.

Each direct consumer privately imports the source module, unpacks g and hg instead of
an existential comparison, and defines that comparison explicitly. Its existing
public signature, universes, hypotheses, attributes, docstrings and public imports
are unchanged. The original hU and hQ binders are retained even when unused.
A declaration-local set_option linter.unusedVariables false in suppresses only the
now unused original assumptions in each adapted theorem. All remaining proof lines
are unchanged. The initial delivery attempt compiled but refused the new unused-
variable warnings; these two scoped linter lines repair that refusal.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift | F6 | Withdrawn duplicate; node attaches to proved source theorem. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent | unclaimed | Source private import; canonical e; unchanged public signature. |
| Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection | unclaimed | Source private import; canonical c; unchanged public signature. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | unclaimed | Indirect user; unchanged derived-Hom-descent interface. |

The downstream.py --uses check finds exactly the two direct callers above and the
indirect derived-Hom lift. A search of both source roots finds no further importers
of the withdrawn module; the quarantine search finds no additional callers.
Both source counterparts already use the source theorem.
The DAG parents continue to cite the same retained node. No node is deleted, and no
source declaration, signature, attribute, public import or non-theorem body changes.

## Status

landed 20261020T233140-L-899237 2026-10-20 (merge of deliver/F6/Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift)

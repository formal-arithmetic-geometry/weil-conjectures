# AlgebraicGeometry.relativeMV_direct_image_homotopy_comparison

## Reason

Restore the module assigned by `coord/rework.tsv` from
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVDirectImageHomotopyComparison.lean`.
Its live source is absent following a reverted cluster restoration. The archived
proof has zero holes and compiles against the current published dependencies.
The direct consumer `RelativeMVCoverChainSquare` remains quarantined and its DAG
node still requires this comparison. Restoration, rather than withdrawal, repairs
this missing link without changing any mathematical statement or definition.

## Old

The live path `lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageHomotopyComparison.lean`
is absent. The archived module has the following public signature, which exactly
matches the existing node's `lean.statement`:

```lean
theorem relativeMV_direct_image_homotopy_comparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (A B : CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B')
      (α : A ⟶ F.obj A') (β : B ⟶ F.obj B')
      (H : Homotopy (t ≫ β) (α ≫ F.map t'))
      (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj A) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj B) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj
        (DerivedCategory.Q.obj (CochainComplex.mappingCone t)) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (b (U ⊓ V)).right),
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app A') ≫ e₁'.hom =
        e₁.hom ≫ a.hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map β ≫ η.app B') ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso t' G).inv) ≫
              η.app (CochainComplex.mappingCone t')) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom
```

Its public imports are:

```lean
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
```

Its private proof dependency is:

```lean
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRows
```

## New

Restore the complete archived module byte-for-byte to the assigned live path.
The signature and imports above, both proved private helpers, theorem proof,
docstrings, universe parameters and visibility are unchanged. No new declaration,
instance, attribute, definition or axiom is introduced. The existing DAG attachment,
proof plan, dependencies and unit route already match this proof and remain intact.

The proof uses the resolved row theorem for both short exact rows and their
three mate equations. The cone-to-quotient quasi-isomorphisms supply the two cone
vertex comparisons. The private helper `cone_quotient_naturality` proves
compatibility of the specified cone map with the quotient maps using Mathlib's
additive cone comparison. The private helper `cone_mate_quotient` combines this
with localization naturality and adjunction naturality. Its equation identifies
the overlap component; the global and biproduct components are supplied directly
by the row theorem. This argument does not require direct image to preserve
quasi-isomorphisms.

The restored file compiles cleanly on the published server build in 20.2
seconds. A separate validation set, with `#print axioms` appended, compiled
the restored module in 26.2 seconds and its unchanged archived direct consumer
in 24.7 seconds. Both public declarations list only `propext`, `Classical.choice`
and `Quot.sound`. Source checks confirm byte equality with the archive, exact
signature equality with the existing node, zero holes and the Lean line limit.

## Users

`tools/downstream.py` reports an unknown module because the live source is
absent. A source search of both `lean/` and `quarantine/` finds the single direct
consumer below. Its node cites this item in `proof_deps` and in a proof step's
`uses`. The consumer is checked unchanged against the restored source in a
separate validation directory; it is not included in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageHomotopyComparison | C4 | Restore archived complete module with the identical interface and proof. |
| Sheaf.AlgebraicGeometry.RelativeMVCoverChainSquare | unclaimed, quarantined | Original proof retains the same witnesses and all three comparison equations; no adaptation. |

## Status

landed 20261021T023305-L-2945083 2026-10-21 (merge of deliver/C4/Sheaf.AlgebraicGeometry.RelativeMVDirectImageHomotopyComparison)

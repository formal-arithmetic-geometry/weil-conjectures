# AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_degreewise_lift

## Reason

The assigned item is a zero-hole retirement in coord/retire-items.tsv. Its duplicate
Sheaf theorem existentially packages a comparison that the proved source theorem
supplies canonically. Withdraw the Sheaf duplicate and migrate its sole direct consumer.
No file under lean/WeilConjectures is changed. No target meaning changes.

## Old

The withdrawn Sheaf theorem has signature:

```lean
theorem exists_affine_perfect_open_stalk_degreewise_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (t : ∀ n : ℤ,
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q).X n) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      ∃ (e : R ⋙ S ≅ T) (g : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n),
        ∀ n : ℤ, (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) =
          (e.app P).hom.f n ≫ t n ≫ (e.app Q).inv.f n
```

PerfectOpenStalkChainMapLift privately imports the Sheaf module and unpacks eW, g and hg.

## New

Reuse the existing declaration from
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift, verbatim:

```lean
theorem exists_affine_perfect_open_stalk_degreewise_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (t : ∀ n : ℤ,
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q).X n) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      let e : R ⋙ S ≅ T := Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) (.up ℤ)
      ∃ g : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n,
        ∀ n : ℤ, (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) =
          (e.app P).hom.f n ≫ t n ≫ (e.app Q).inv.f n
```

The source signature has exactly the same universes, X, U, x, hxU, P, Q, hP and t.
The same affine W and maps g satisfy the same stalk equation; the comparison e is
fixed to Functor.mapHomologicalComplexCompIso of openModuleStalkRestrictionComparison.
Choosing this explicit e proves the old existential statement and the unchanged DAG
statement. No differential equation is added, and Q need not be perfect. Empty support
intervals and zero ranks still use zero maps. The assumption x in U excludes empty U;
equal opens and non-affine U are allowed.

The existing source proof was read in full. It extracts bounded support and free
retractions; lifts pi_n followed by t_n using the canonical finite-free local lifting
theorem; intersects the finite support neighbourhoods and shrinks to an affine W;
uses iota_n followed by the free lift inside the interval and zero outside; then proves
the formula by naturality, iota_n followed by pi_n = identity, and preservation of zero.
It leaves no hole and takes the same route as the original node. The node is retained
and attached to this stronger source declaration; its statement and dependencies stay.
No unit statement or proof step is bypassed. The parent node still cites this same node.

In the sole direct consumer, change the private import to the source module, unpack
only W, hxW, affineness, hWU, g and hg, and define eW to be the canonical comparison.
Restate hg with change using the local abbreviation eW, so the existing syntactic simp
cancellations still apply. This is definitional equality; no theorem or hypothesis is
added. All existing consumer signatures, attributes, docstrings and public imports stay.
All later proof lines are unchanged from the current shared consumer, including the
source degreewise-shrink call without an eW argument, its canonical cW/cV comparison
transport, and its final simplification and rfl. The source degreewise-shrink private
import introduced by a68ffff8db is preserved; neither the retired Sheaf shrink import nor
the old StalkInternalHomFinitePresentation import is restored.

An import-only migration failed in the previous attempt at line 62 with
`Tactic rcases failed ... is not an inductive datatype`: it tried to unpack the
comparison from the source theorem's g/hg pair. Defining eW fixes this mismatch.
Restating hg with the local eW abbreviation makes the component chain-map calculation
use the same expression. Both changes are by definitional equality.

Repair of returned head 3eb7bb5dd2: the earlier packet had been reviewed successfully,
but its landing overlapped a68ffff8db's degreewise-shrink consumer migration. Rebuilt
this consumer from the current shared version and applied only the lift migration above.
The shrinking migration and its remaining proof are preserved verbatim. The repaired
consumer compiled on the server in 3.3 seconds without warnings.

## Users

The source-only tools/downstream.py --uses query lists four transitive importers and
only the withdrawn module and ChainMapLift as declaration uses. The full library and
quarantine search finds no other importer of the withdrawn Sheaf module. The same-name
source declaration and its source ChainMapLift caller are preserved verbatim.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift | E4 (assigned retirement) | Duplicate withdrawn; node points to the proved stronger source theorem. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift | unclaimed | Private import migrated and canonical eW supplied; unchanged public interface. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent | unclaimed | Indirect importer; no interface or proof change needed. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | unclaimed | Indirect importer; no interface or proof change needed. |
| Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection | unclaimed | Indirect importer; no interface or proof change needed. |

The retire inventory's PROOFDIFF_UNSAFE warning referred to the pre-retirement dependency
snapshot. The current consumer already uses the source PerfectComplex and open module
stalk functor, and its sibling shrinking theorem uses source restriction comparisons.
The actual adapted consumer compiles against the current source theorem without any
duplicate declaration error. No supporting module is imported or retired speculatively.
The three indirect consumers see exactly the same public interface.

## Status

landed 20261020T221132-L-4147945 2026-10-20 (merge of deliver/E4/Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift)

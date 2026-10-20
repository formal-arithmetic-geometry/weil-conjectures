# AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_inverse_homotopies_spread

## Reason

Retire the copy assigned in coord/retire-items.tsv in favour of its already proved
upstream twin, as authorized in retire-sheaf-twins-20261020.md. The item contains
zero holes. Upstream drops three redundant hypotheses and otherwise has the same
statement. Its proof was read in full: it spreads the two given homotopies successively,
restricts the first to the common affine neighbourhood, and conjugates the inverse
through the natural comparison between iterated and direct restriction.

## Old

```lean
theorem exists_affine_perfect_open_stalk_inverse_homotopies_spread
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (f : P ⟶ Q) (V : X.Opens) (hxV : x ∈ V) (hV : IsAffineOpen V) (hVU : V ≤ U)
    (g : ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)
    (hfg : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        ((((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f) ≫ g)) (𝟙 _)))
    (hgf : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (g ≫ (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f))) (𝟙 _))) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      ∃ (gW : R.obj Q ⟶ R.obj P),
        Nonempty (Homotopy (R.map f ≫ gW) (𝟙 _)) ∧
        Nonempty (Homotopy (gW ≫ R.map f) (𝟙 _))
```

## New

The existing theorem in WeilConjectures.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread:

```lean
theorem exists_affine_perfect_open_stalk_inverse_homotopies_spread
    (X : Scheme.{u}) (U : X.Opens) (x : X)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (f : P ⟶ Q) (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
    (g : ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)
    (hfg : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        ((((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f) ≫ g)) (𝟙 _)))
    (hgf : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (g ≫ (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f))) (𝟙 _))) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      ∃ (gW : R.obj Q ⟶ R.obj P),
        Nonempty (Homotopy (R.map f ≫ gW) (𝟙 _)) ∧
        Nonempty (Homotopy (gW ≫ R.map f) (𝟙 _))
```

This is an existing stronger realization of the unchanged mathematical node: the
arguments hxU, hU and hV are not needed by the upstream theorem. Its schemes, complexes,
finite-free retraction hypotheses, fixed forward map, candidate inverse, two stalk
homotopies and conclusion are identical. Specialization proves the old assertion.
In particular, the forward map remains f, both inverse homotopies use the same gW,
and the final W is affine and contains x. The zero-complex, disjoint-support and
non-Noetherian cases are still covered. No target statement or definition changes.

The node keeps both proof steps and its sole proof dependency on single-homotopy
spreading. Only its lean attachment and proof provenance are refreshed. Its Lean
signature is copied verbatim from upstream; lean.note explains specialization. DAG
parents retain this node, so their mathematical dependency and the unit route remain.
The unit sk-prop-av-cube has no realized node at this local assembly step.

The only direct importer and declaration caller is
Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection. Change its private import to
the twin, omit hxU, hU and hV at this call, and rename its now unused local witness hV
to _hV. Its signature, public imports, attributes, visibility and remaining proof stay
identical. Its updated proof is checked again through lcompile.py in this repair.

Withdraw only lean/Sheaf/AlgebraicGeometry/PerfectOpenStalkInverseHomotopiesSpread.lean
via deleted.txt. No adopted-source file is changed or removed. The withdrawn module's
unused Sheaf internal-Hom import and derived-Hom Mayer-Vietoris re-export are not
added to the consumer: its signature and proof compile without them. This is deliberate
pruning, not a claim that the corresponding mathematical nodes are globally unused.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread | M2 | Retire duplicate; attach node to existing stronger upstream theorem. |
| Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection | unclaimed | Sole direct and transitive importer of the item; private import and obsolete proof arguments adapted. Public statement unchanged. |

The item and quasi-isomorphism consumer are the full downstream.py --uses result.
The only other caller with the same declaration name is upstream
PerfectStalkQuasiIsoDetection, which already imports the source twin and needs
no change. Current rework records contain no quarantined importer or pending
restoration for the item. No module held by another group is changed.

Repair of returned head 550c309ef3: the earlier packet removed an unused private
StalkInternalHomFinitePresentation import from PerfectOpenStalkChainMapLift.
Current sheaf-dag already lacks that import and also contains M1's landed
upstream degreewise-shrink API adaptation (a68ffff8db). The sandbox chain-map
file was refreshed verbatim from current source and compiled (3.7 seconds),
then omitted from the packet. Its current imports, public signature and complete
proof are preserved. No chain-map module edit remains in this delivery;
its other consumers consequently need no adaptation.

The unadapted original quasi-isomorphism consumer was compiled against the empty
retirement stub: original line 109 reports Unknown identifier
exists_affine_perfect_open_stalk_inverse_homotopies_spread, with a dependent rcases
error at line 108. The adapted version uses the upstream import and omits exactly
the three dropped arguments; its unused hV local witness becomes _hV. Thus the
consumer edit is required by the retirement and does not alter its assertion.

The adapted consumer compiled without warnings or errors in 6.8 seconds through
lcompile.py. A fresh downstream.py --uses scan confirms it is the sole consumer;
a source-only import-closure scan finds no newly overlapping twin modules and
no remaining reference to the withdrawn module in that consumer's closure.

## Status

landed 20261020T221244-L-4164528 2026-10-20 (merge of deliver/M2/Sheaf.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread)

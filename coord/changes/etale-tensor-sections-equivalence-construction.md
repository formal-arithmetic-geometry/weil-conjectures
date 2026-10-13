# AlgebraicGeometry.Scheme.Modules.sectionsEquiv (private proof construction)

## Reason

Repair of reviewer X-4538c's return D. The returned attempt constructed the
section equivalence after substituting concrete iterated tensor pullbacks. Comparing
its scalar equation with the definition of the restriction expanded concrete module
data and exceeded the unchanged file limit. The construction is now defined once
for arbitrary module objects: its forward and inverse maps are evaluation of a given
module isomorphism and its inverse. Its inverse and scalar laws are completely
proved before specialization. The generic transport calculation then specializes
through the proved map equality `restriction_eq`, rather than relying on expensive
conversion of the full concrete scalar equation.

This is a repair of the proof-local data construction, with no change to a public
library definition, existing signature, or target-used notion. The new definition
is private and contains no sorry. No object is chosen from an existence statement.
The exported transport theorem retains its exact original signature. Both factoring
modules are retained as mathematical results with complete proofs, not unfinished
steps introduced to evade a timeout. `scratchpad/UnsplitRepair.lean` assembles their
proofs and the main argument in one file and compiled at the unchanged 60-second
limit; lcompile reported 15.8 seconds including any slot wait.

## Old

The concrete proof-local section equivalence attempted before the return was:

```lean
  let k := (tensorSectionsComp a.left U.hom).app F ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj F) a.w)
  let e := (((CategoryTheory.evaluation _ AddCommGrpCat).obj (op ⊤)).mapIso
    ((toPresheaf V.left).mapIso k)).addCommGroupIsoToAddEquiv
```

This term was only in the failed scratch attempt. The delivered transport theorem
was left as `:= by sorry`; there is no old public definition to replace.

## New

```lean
private noncomputable def sectionsEquiv {Y : Scheme.{u}} {M N : Y.Modules} (k : M ≅ N) :
    Γ(M, ⊤) ≃+ Γ(N, ⊤) where
  toFun := k.hom.app ⊤
  invFun := k.inv.app ⊤
  map_add' := (k.hom.app ⊤).hom.map_add
  left_inv s := by
    change (k.hom ≫ k.inv).app ⊤ s = s
    rw [k.hom_inv_id]
    rfl
  right_inv s := by
    change (k.inv ≫ k.hom).app ⊤ s = s
    rw [k.inv_hom_id]
    rfl
```

`sectionsEquiv_apply` and `sectionsEquiv_smul` prove evaluation and linearity.
`transportForFamily` constructs the comparison component followed by `eqToIso`
along the etale triangle and proves its scalar-unit equation. `restriction_eq`
is a proved definitional equality of additive maps. Rewriting this equality in
the specialized generic result proves the exported transport theorem in full.
The definition has a local irreducibility attribute after its basic laws; all
elaboration controls remain local. The wrapper stores only additive equivalence
data; scalar compatibility is a theorem, avoiding construction of redundant scalar
structure on concrete tensor-pullback sections.

## Users

The private definition has only the following proof users. No downstream importer
sees this name or receives a changed existing definition. The two public theorems
have the same signatures and meaning as before; no forced adaptation is required,
and no target statement review is reopened by a changed definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleTensorSectionsTransport | Q4, new helper in this delivery | complete transport proof and private construction; public signature unchanged |
| Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv | Q4 | unchanged combination proof now uses a proved transport theorem |

## Status

landed 20261013T143550-L-562444 2026-10-13 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv)

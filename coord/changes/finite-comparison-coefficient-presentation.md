# finiteComparison coefficient presentation and module layout

## Reason

The generator correspondence was the sole remaining hole in the assigned module.
Its existing node already cited `lem-ctf-finite-comparison-presentation`, but no
Lean declaration or node file for that bridge existed in the current repository.
An independent presentation lemma needs the coefficient data without importing
the theorem that uses it. Move those constructions verbatim to a separate public
module, construct the model realizations and their comparison square, and prove
the generator correspondence by transporting the existing finite-Tor equivalence.

No target statement or mathematical definition changes. The moved declaration
block is byte-identical to the old block apart from blueprint links. The original
module publicly imports its new owner, preserving all original names and visibility.

## Old

In `Sheaf.Paper.FiniteComparisonLocalizing`, the exactness interface was:

```lean
theorem finiteComparisonRealization_exact (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    (finiteComparisonRealization B X eR).IsEquivalence ∧
    (finiteComparisonRealization B X eR).Additive ∧
    PreservesFiniteLimits (finiteComparisonRealization B X eR) ∧
    PreservesFiniteColimits (finiteComparisonRealization B X eR)
```

The same file owned `finiteComparisonPresheaf`,
`finiteComparisonConstantRealization`, `finiteComparisonRealization`, its three
additive/limit/colimit instances, both generator predicates, and both closures.
The theorem `finiteComparisonGenerators_identification` had its existing signature
and a `sorry` proof.

## New

The exactness interface in `Sheaf.Paper.FiniteComparisonCoefficients` is verbatim:

```lean
theorem finiteComparisonRealization_exact (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    (finiteComparisonRealization B X eR).IsEquivalence ∧
    (finiteComparisonRealization B X eR).Additive ∧
    PreservesFiniteLimits (finiteComparisonRealization B X eR) ∧
    PreservesFiniteColimits (finiteComparisonRealization B X eR)
```

The other coefficient declarations listed above move with it, with unchanged names,
signatures and bodies. `FiniteComparisonLocalizing` publicly imports that module
and retains its existing public imports. The generator theorem has its original
signature and a complete proof using the finite-Tor equivalence, both explicit
model realizations and the proved derived square.

`FiniteComparisonModelRealization` adds actual coefficient model functors, proved
additive equivalence instances, and proved pullback and derived-square theorems.
`FiniteComparisonPresentation` adds the independent predicate-identification lemma;
its two replete-image equalities are the single remaining named proof obligation.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.FiniteComparisonLocalizing` | C2 | Publicly reexports the identical coefficient declarations; completes the generator proof |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin` | unclaimed | Unchanged; uses the realization and exactness theorem through the original public import; compiles against the identical declarations |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization` | unclaimed | Unchanged; compiles against the new module layout and identical declarations |
| `Sheaf.Paper.FiniteComparisonCoefficients` | new in this delivery | Owns the unchanged coefficient constructions and instances |
| `Sheaf.Paper.FiniteComparisonModelRealization` | new in this delivery | Constructs the model realizations and proves their comparison square |
| `Sheaf.Paper.FiniteComparisonPresentation` | new in this delivery | States the remaining coefficient-predicate bridge |

`tools/downstream.py Sheaf.Paper.FiniteComparisonLocalizing --uses` and the current
symbol-use search identify exactly two existing external consumers of the moved
declarations: `FiniteDiscreteCtfOrigin` and `FiniteDiscreteCtfRealization`. Both use
`finiteComparisonRealization` and `finiteComparisonRealization_exact`. Both are
copied unchanged into the sandbox for the all-files compile, then omitted from the
packet. Their statements, proof bodies, and public imports are unchanged.
There are no forced adaptations. Since the definitions and statements are identical,
no target changes its meaning or needs a new statement review on mathematical grounds.

## Status

landed 20261021T024147-L-3039041 2026-10-21 (merge of deliver/C2/Sheaf.Paper.FiniteComparisonLocalizing)

# AlgebraicGeometry.exterior_dual_pairing_exists

## Reason

Retire `Sheaf.AlgebraicGeometry.DeterminantDualPairing`, row 715 of
`coord/retire-items.tsv`, in favor of its adopted upstream twin. Both declarations
already have complete proofs and zero holes. They express the same intrinsic pairing,
but the twin uses `exteriorPower` and `wedge` while the copy uses `exteriorSheaf`
and `exteriorSheafSection`. The canonical comparison is already proved, so the
three direct consumers can use the twin without changing their statements.

## Old

The retired declaration is:

```lean
theorem exterior_dual_pairing_exists (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ∃ f :
    (Scheme.Modules.exteriorSheaf (Scheme.Modules.dual M) n) ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n),
    ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (Scheme.Modules.exteriorSheafSection
        (Scheme.Modules.dual M) n U φ)).app (op (Over.mk (𝟙 U)))
        (Scheme.Modules.exteriorSheafSection M n U a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det
```

## New

The existing upstream declaration, unchanged, is:

```lean
theorem exterior_dual_pairing_exists (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ∃ f :
    (Scheme.Modules.exteriorPower (Scheme.Modules.dual M) n) ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M n),
    ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (wedge (M := Scheme.Modules.dual M) (r := n) (U := U) φ)).app
          (op (Over.mk (𝟙 U)))
        (wedge (M := M) (r := n) (U := U) a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det
```

The node's Lean attachment now records this upstream signature verbatim. No
natural-language statement changes: both exterior constructions sheafify the
same sectionwise exterior-power presheaf. No source-library file changes.

In each direct consumer, replace the private pairing import with the upstream
import and add the private `ExteriorSheafComparison` import. For the upstream
pairing `p₀`, apply the official local-bijectivity theorem directly, with its
unchanged determinant formula. This repair is based on the current consumers,
including B8's retirement of the local pairing and K4's retirement of exterior
restriction. It preserves their upstream imports and restriction comparisons.

For `DeterminantExteriorDualIso`, the local-to-global sheaf argument proves
`IsIso p₀`. Compose that isomorphism with
`exteriorSheafPowerIso (dual M) d` on the source and
`dualFunctor.mapIso (exteriorSheafPowerIso M d).op` on the target. The result
has exactly the existing public statement on `exteriorSheaf`.

For both Koszul consumers, use the same current comparison to define

```lean
let eSource := Scheme.Modules.exteriorSheafPowerIso (Scheme.Modules.dual C) n
let eTarget := (Scheme.Modules.dualFunctor Z).mapIso
  (Scheme.Modules.exteriorSheafPowerIso C n).op
let p := eSource.hom ≫ p₀ ≫ eTarget.hom
```

The local theorem proves bijectivity of `p₀` on each subopen. The comparison
section maps are bijective because they come from isomorphisms.
`Function.Bijective.comp` therefore proves bijectivity of `p`, which supplies
the original stalk-surjectivity argument. The former inverse-wedge conjugation
and cancellation are unnecessary: construction and local perfection now use
the same upstream exterior-power API.

The Yoneda consumer's final composition is expressed by two explicit
`Functor.map_comp` rewrites and composition of the three surjections. This
avoids an elaboration failure in the former final `simpa`, without changing
the map or its property. Existing signatures, attributes, public imports,
options and docstrings are retained. The two Koszul consumers preserve the
current upstream restriction theorem and `exteriorSheaf_eq_exteriorPower`
rewrites introduced by K4 while this repair was running.

All four node copies start from the current repository records. Their proof,
proof dependencies and origins describe the actual construction; the pairing
node is attached to the existing upstream theorem. Review metadata and all
other fields are preserved. No new node or helper declaration is introduced.

The transport is valid in every degree, including zero, over zero section rings
and on empty opens, and adds no freeness assumptions. The consumers retain their
own hypotheses. No target type, public definition, chapter or unit route changes.
No target statement review is reopened. All parent DAG dependencies on the
construction node stay: they now reach the unchanged upstream theorem.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DeterminantDualPairing
--uses exterior_dual_pairing_exists` reports seven downstream modules and the
three actual external users of the theorem. Current claim files show all seven
unclaimed. The item's dispatcher assignment is D6.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualPairing | D6 | Withdraw duplicate; attach node upstream. |
| Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso | unclaimed | Migrate private import; prove upstream pairing invertible and transport the isomorphism; unchanged signature. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | unclaimed | Migrate private import; compose upstream local bijectivity with comparison bijections; unchanged signature. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection | unclaimed | Migrate private import; compose upstream local bijectivity with comparison bijections; unchanged signature. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive user; no changes. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive user; no changes. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | unclaimed | Transitive user; no changes. |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | unclaimed | Transitive user; no changes. |

Validation: all three adapted files compile cleanly through `lcompile.py --all`
(3.2 seconds for the determinant isomorphism; 8.0 and 10.7 seconds for the
Koszul consumers after incorporating K4).
The delivery preflight checks the axiom probes for the complete set. The
withdrawal scan must find no importer of the retired module after applying
this packet. The construction node's parents keep their mathematical edges,
which now reach its unchanged upstream declaration.

## Status

landed 20261020T233118-L-895066 2026-10-20 (merge of deliver/D6/Sheaf.AlgebraicGeometry.DeterminantDualPairing)

# WeilConjectures.VerdierExchange restoration and shared definition ownership

## Reason

The current rework row requires restoration of the quarantined theorem module.
During this session the live definition node def-sf-verdier-exchange-data changed to
Sheaf.SixFunctors.VerdierExchangeData, independently reviewed under Q38. The review
explicitly says restored quarantined parents must import the new module and drop their
copies. Restore the theorem/package while preserving that shared definition ownership.
The first reconciled compile reported:

```text
Dependency Sheaf.SixFunctors.VerdierExchangeData from
81eb595e191ab0fb4c77a1363e75103b9fa74c2f failed in the private compile overlay:
timeout after 60 s
```

The data module is unclaimed and is repaired in this same packet. While delivery
waited, its live source disappeared but the DAG retained the reviewed attachment.
The packet preserves the reviewed copy with the documented construction repair.
The current downstream tool therefore reports zero modules (--allow-missing); the
consumer list below includes the direct and archived consumers checked before that
source disappearance. No mathematical
statement, field, canonical map or normalization equation changes.
This is the assigned build repair; the existing theorem hole remains.

## Old

The archive has public imports followed by local definitions composition through
integralAlphaRealization, including the original smallSite instance. It then declares
Package, Assertion and verdier_exchange in the same namespace. The complete archived
bodies are at quarantine/Sheaf/Paper/VerdierExchange.lean.

For example its first data declaration is:

```lean
def composition
    {X : Type a} {Y : Type b} {S : Type c}
    [Category.{v} X] [Category.{w} Y] [Category.{z} S]
    {Ff : X ⥤ Y} {Gf : Y ⥤ X} {Fa : Y ⥤ S} {Ga : S ⥤ Y}
    {Fx : X ⥤ S} {Gx : S ⥤ X}
    (adjf : Ff ⊣ Gf) (adja : Fa ⊣ Ga) (adjx : Fx ⊣ Gx)
    (alpha : Ff ⋙ Fa ≅ Fx) : Ga ⋙ Gf ≅ Gx :=
  conjugateIsoEquiv (adjf.comp adja) adjx alpha.symm
```

## New

```lean
public import Sheaf.SixFunctors.VerdierExchangeData
```

The reviewed owner now supplies all 34 data definitions with their original names.
Only Package, Assertion and verdier_exchange are declared by the restored theorem
module. Their complete signatures, fields and docstrings are preserved; the existing
coefficient applications merely make their inferred universe u explicit, for example
Operation.{u} l Ω X Y s, C.{u} l Ω T s and System.{u} l Ω D hl. All original imports
remain. Optional unused genInjectivity/genSizeOf/genSizeOfSpec/genCtorIdx helpers are
disabled for the remaining package record; no consumer uses them.

The existing data module now makes the inferred coefficient universes explicit and
suppresses unused generated record helpers. Its old signedShift body was:

```lean
  (CategoryTheory.SignedDoubleHomCone.comparison.{u + 1, u, u + 1, u + 1}
    (R := (s.coefficients l).ring T) (homTarget l T s O)).choose P m
```

Its new body is:

```lean
  let shift {A : Type (u + 1)} [Category.{u} A] {J : GrothendieckTopology A}
      [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
      (R : Sheaf J CommRingCat.{u + 1})
      (I K : CategoryTheory.SignedDoubleHomCone.Complex.{u + 1, u, u + 1, u + 1} R) (m : ℤ) :
      homComplex.{u + 1, u, u + 1, u + 1} (R := R) (K⟦m⟧) I ≅
        (homComplex.{u + 1, u, u + 1, u + 1} (R := R) K I)⟦-m⟧ :=
    (CategoryTheory.SignedDoubleHomCone.comparison.{u + 1, u, u + 1, u + 1} (R := R) I).choose K m
  shift ((s.coefficients l).ring T) (homTarget l T s O) P m
```

Beta reduction gives the identical archived choice predicate and witness. The generic
comparison is proved, with product-component equations determining the shift map.
No new declaration, axiom or existence assumption appears. The original
ringInclusionShift match is replaced by `by cases s <;> infer_instance`, supplying
the same finite/integral instances while avoiding generated match equations.
Profiling in the original full restoration isolated 11.9 s and 10.6 s kernel checks
in signedShift; the same local abstraction compiled that full restoration in 42 s.
No new module or node is introduced by B2. The final two-file packet
compiled successfully together through lcompile.py --all (exit code 0). This is not a
new file split to meet a time bound; it implements the reviewed ownership instruction.

## Users

The live and archived import scan originally found the four theorem consumers below.
They retain the identical public names, signatures and normalization fields through
the new public import. The data module's consumers now share precisely those same
declarations instead of a second copy with clashing names. No source-library module
is edited or withdrawn.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.VerdierExchange | B2 | Restore package/theorem; import the reviewed data owner. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Repair construction elaboration; all 34 signatures/fields preserved. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unmodified | Direct importer of the data owner; identical interface, no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Identical public data names and package; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Identical interfaces and canonical maps; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Identical ProjectionTensor and DualShiftModel; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Identical assertion and package; no adaptation. |

## Status

landed 20261025T013859-L-4029736 2026-10-25 (merge of deliver/B2/Sheaf.Paper.VerdierExchange)

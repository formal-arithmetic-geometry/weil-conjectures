# AlgebraicGeometry.torsionControlled_completion_hom_lift_raw

## Reason

Reviewer X-a7def, head a7defd588, point 4 requires retaining the prescribed completed
comparison. With J=0 on Spec(k), a=id and a′=0 satisfy both torsion conditions but
no g can satisfy g≫a′=a. Adding θ and hθ is the exact requested minimum repair:
the counterexample then fails hθ. This changes an intermediate theorem, no definition
or Challenge target. The corrected theorem remains a named sorry; no proof is claimed.

## Old

```lean
theorem torsionControlled_completion_hom_lift_raw
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F F' : CoherentModules X) (a : F ⟶ H) (a' : F' ⟶ H)
    (ha : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))))
    (ha' : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))) :
    ∃ g : F ⟶ F', g ≫ a' = a
```

## New

```lean
theorem torsionControlled_completion_hom_lift_raw
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F F' : CoherentModules X) (a : F ⟶ H) (a' : F' ⟶ H)
    (ha : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))))
    (ha' : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom))))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a) :
    ∃ g : F ⟶ F', g ≫ a' = a
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftRaw
--uses torsionControlled_completion_hom_lift_raw` lists exactly these direct users:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftRaw | D3 | Own statement gains θ and hθ; proof remains sorry. |
| Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists | unclaimed | Forced one-line proof adaptation passes the already bound θ and hθ; signature and visibility unchanged. |

All transitive users see the unchanged Exists interface. No target statement or
underlying definition changes. The completion node is the sole DAG citer; its
hypotheses supply both new arguments, so raw existence remains available there.
Its independent claim about arbitrary raw lifts is not repaired by this change.

The original Exists module compiled against the baseline. Against the repaired raw
module it fails at line 41 with:

```
Tactic `rcases` failed: `x✝ : ∀ (θ : (completion X J).obj F ⟶
  (completion X J).obj F'),
  θ ≫ (completion X J).map a' = (completion X J).map a → ∃ g, g ≫ a' = a`
is not an inductive datatype
```

The only forced source edit appends `θ hθ` to the raw theorem application at line 41.
The two delivered modules compile in import order after that edit. The second reader
should rerun the original against the repaired raw module to verify necessity.

## Status

landed 20261013T034203-L-3765583 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftRaw)

# Ring.residueField_projectiveDimension_le_depth

## Reason

Restore the quarantined depth-bound module and its sole quarantined direct consumer after
synchronization. The archive imports the old Sheaf global-dimension definitions, but the
minimal-resolution dependency now imports the adopted definitions. The recorded rework error
is a duplicate `Ring.HasFiniteGlobalDimension`. The old Sheaf global-dimension module has
since been withdrawn, and its natural-valued `ModuleCat.projectiveDimension` no longer exists.

The adopted source already contains complete proofs of both residue-field bounds, ported to
Mathlib's `CategoryTheory.projectiveDimension`. Restore both Sheaf paths as public imports
of those source modules. This preserves the declarations through those import paths without
creating second constants with the same names. Reattach both DAG nodes to the existing source
declarations and retain their mathematical proof dependencies. No source-library file changes.

## Old

`Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` publicly imported
`Sheaf.RingTheory.GlobalDimension` and declared:

```lean
theorem residueField_projectiveDimension_le_depth
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R))) :
    (ModuleCat.projectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R)) h : ℕ∞) ≤
        IsLocalRing.depth (R := R) R
```

Its quarantined consumer `Sheaf.RingTheory.ResidueFieldProjectiveDimension` used the same
obsolete API and declared:

```lean
lemma residueField_projectiveDimension_le_ringKrullDim
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R))) :
    (ModuleCat.projectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R)) h : WithBot ℕ∞) ≤ ringKrullDim R ∧
      ∀ D : ℕ, ringKrullDim R = (D : WithBot ℕ∞) →
        ModuleCat.HasProjectiveResolutionLE
          (ModuleCat.of R (IsLocalRing.ResidueField R)) D
```

## New

`Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` publicly imports
`WeilConjectures.RingTheory.ResidueFieldProjectiveDimensionDepth`, exporting its existing
complete proof with signature:

```lean
theorem residueField_projectiveDimension_le_depth
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R))) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≤
      ((IsLocalRing.depth (R := R) R : ℕ∞) : WithBot ℕ∞)
```

`Sheaf.RingTheory.ResidueFieldProjectiveDimension` publicly imports
`WeilConjectures.RingTheory.ResidueFieldProjectiveDimension`, exporting its existing complete
proof with signature:

```lean
lemma residueField_projectiveDimension_le_ringKrullDim
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R))) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≤
        ringKrullDim R ∧
      ∀ D : ℕ, ringKrullDim R = (D : WithBot ℕ∞) →
        ModuleCat.HasProjectiveResolutionLE
          (ModuleCat.of R (IsLocalRing.ResidueField R)) D
```

The mathematical statements are unchanged. The residue field of a local ring is nonzero.
The adopted proof converts finite Ext projective dimension to existence of a bounded
resolution, takes its least length d, proves d <= depth by the original minimal-resolution
and last-minor argument, and identifies categorical dimension with d using
`ModuleCat.projectiveDimension_eq_of_hasProjectiveResolutionLE`. Thus the categorical value
is precisely the old natural minimum, embedded in WithBot ENat. The consumer uses
`CategoryTheory.projectiveDimension_le_iff` and the bounded-resolution equivalence for its
unchanged second conclusion. Both canonical declarations have only the three allowed axioms.
No target statement or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth | M1 | Restored as the canonical source import; its theorem remains available. |
| Sheaf.RingTheory.ResidueFieldProjectiveDimension | unclaimed | Sole quarantined direct consumer; restored as the canonical source import using the synchronized dimension API. |

`tools/downstream.py ... --allow-missing --uses ...` reports no active users for either
absent path. Searching both `lean/Sheaf` and `quarantine/Sheaf` additionally finds exactly the
consumer above for the depth module and no textual consumers of the Krull-dimension module.
Both nodes retain their statements and dependency edges, including the depth-to-dimension
edge; they are reattached to the complete source proofs. Other parent DAG references continue
to refer to the same nodes and declaration names. These nodes do not realize a unit statement
or a step in `dag/units/sk-thm-p1.json`; its route is unchanged.

Both restored modules compiled individually with lcompile.py and together via --all with no
warnings. A temporary consumer imported both Sheaf paths, applied the depth theorem and the
finite-resolution conclusion, and printed axioms of both public theorems: exactly propext,
Classical.choice, Quot.sound. The temporary check is outside the delivery.

## Status

landed 20261020T155433-L-3241987 2026-10-20 (merge of deliver/M1/Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth)

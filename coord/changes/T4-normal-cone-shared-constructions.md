# AlgebraicGeometry.HilbertSamuel normal-cone fibre constructions

## Reason

The existing theorem `near_normal_cone_nonreduced` gives the entire conclusion of
`near_normal_cone` with the reducedness assumption omitted. Its old public import of
`HilbertSamuelNearNormalCone` supplies only the five plain constructions. Moving those
constructions to a shared module permits specialization without an import cycle.
No mathematical definition or theorem statement changes. No adopted source module changes.

## Old

The following declarations lived in
`Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone`:

```lean
/-- The ideal of the closed centre in the stalk at its point. Source: ILO VIII 2.3.13;
Stacks Tag 0630 (blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable abbrev centerStalkIdeal {X C : Scheme.{u}} (c : C ⟶ X) (z : C) :
    Ideal (X.presheaf.stalk (c z)) := RingHom.ker (c.stalkMap z).hom

/-- The canonical quotient-to-residue-field scalar action. Source: CJS Theorem 2.3,
normal-cone fibre (blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable instance centerResidueAlgebra {X C : Scheme.{u}} (c : C ⟶ X) (z : C) :
    Algebra (X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z) (X.residueField (c z)) :=
  (Ideal.Quotient.factor (IsLocalRing.le_maximalIdeal
    (RingHom.ker_ne_top (c.stalkMap z).hom))).toAlgebra

/-- The normal-cone fibre algebra, with the tensor factors commuted from the paper's
`G ⊗_A k`. Source: CJS Theorems 2.3 and 2.14
(blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
abbrev normalFibre {X C : Scheme.{u}} (c : C ⟶ X) (z : C) : Type u :=
  X.residueField (c z) ⊗[X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z]
    Ideal.associatedGraded (centerStalkIdeal c z)

/-- The degree-n part of the tensor-product grading, spanned by homogeneous pure tensors.
Source: CJS Theorems 2.3 and 2.14
(blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable def normalFibreGrade {X C : Scheme.{u}} (c : C ⟶ X) (z : C) (n : ℕ) :
    Submodule (X.residueField (c z)) (normalFibre c z) :=
  Submodule.span (X.residueField (c z))
    {s | ∃ a : Ideal.associatedGradedPiece (centerStalkIdeal c z) n,
      s = (1 : X.residueField (c z)) ⊗ₜ[X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z]
        DirectSum.of (Ideal.associatedGradedPiece (centerStalkIdeal c z)) n a}

/-- Total-degree grading of `B[T]`: a coefficient of degree j times a monomial of
 degree d has degree j+d. Source: CJS Theorem 2.14, characteristic-zero linear directrix
(blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable def normalPolynomialGrade {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (𝓑 : ℕ → Submodule k B) (r n : ℕ) : Submodule k (MvPolynomial (Fin r) B) :=
  Submodule.span k {p | ∃ (d : Fin r →₀ ℕ) (j : ℕ) (b : B),
    b ∈ 𝓑 j ∧ j + d.degree = n ∧ p = MvPolynomial.monomial d b}

```

`Sheaf.AlgebraicGeometry.SchemeNearPointNormalCone` had:

```lean
public import Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone
```

## New

All five declarations above, including their names, universes, instance status,
reducibility, signatures and bodies, are moved verbatim to the new module
`Sheaf.AlgebraicGeometry.NormalConeFibreConstructions`. It publicly imports the
same fifteen modules as the old reduced module. Both near-point modules now use:

```lean
public import Sheaf.AlgebraicGeometry.NormalConeFibreConstructions
```

The reduced module additionally privately imports `SchemeNearPointNormalCone`
and proves its existing theorem by:

```lean
exact near_normal_cone_nonreduced p i c hconstant z y hy hnear
```

The nonreduced module changes only its one public import line. Its definitions,
theorem signatures, docstrings and both existing proof holes stay verbatim.
The definition node's Lean attachment moves to the shared module. The reduced
node records the specialization as its proof and drops its obsolete tool uses.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone` | T4 | Reexports the same constructions and proves the same theorem from the stronger existing theorem. |
| `Sheaf.AlgebraicGeometry.SchemeNearPointNormalCone` | unclaimed | The sole direct importer and sole other user of the moved declarations; changes its construction import, avoiding the resulting cycle. |
| `Sheaf.AlgebraicGeometry.NormalConeFibreConstructions` | new in this delivery | Owns the five unchanged constructions and the original public dependency surface. |

`tools/downstream.py ... --uses` and a full Lean source search found only the two
existing modules above using `centerStalkIdeal`, `normalFibre`, `normalFibreGrade`
and `normalPolynomialGrade`. There are no current direct importers of
`SchemeNearPointNormalCone`. Both existing modules are compiled against the moved
constructions in the same sandbox; this includes the only direct importer of the
changed reduced module. No target type or meaning changes.

## Status

landed 20261026T092656-L-3452799 2026-10-26 (merge of deliver/T4/Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone)

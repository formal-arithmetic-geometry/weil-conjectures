module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.FieldFibreHomology

/-!
# Field fibre homology

The upstream module supplies the identical `single_field_fibre_homology` theorem.
Re-export it here instead of maintaining a duplicate proof and private helpers.
Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: new-field-fibre-homology).
-/

@[expose] public section

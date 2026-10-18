module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.FieldTheory.PurelyTranscendentalExtension
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Affine elementary etale finite-over-smooth local structure

Source: literature/stacks-project/more-morphisms.tex, Tags 057K and 057L,
lemma-local-local-structure-finite-type, clauses (1)--(6), and
lemma-local-local-structure-finite-type-affine, clause (7).
(blueprint: lem-trf-etale-finite-smooth-local-structure)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
For a locally finite type morphism, the marked point admits an affine etale
neighbourhood finite over a smooth family with geometrically integral fibres.

Proof (Stages 3 will fill the details), following the proof steps of Stacks
Tags 052E, 057K and 057L:

1. Choose affine neighbourhoods of `s` and `z`.  The affine-pairs criterion
   makes the restricted morphism finite type, and the open fibre-product
   identification preserves the fibre germ and its local dimension.
2. Apply the refined quasi-finite polynomial chart to obtain an affine-space
   chart over an affine base, with quasi-finite map and purely transcendental
   marked residue extension.  The affine-space projection is smooth of relative
   dimension `n`.
3. Apply the elementary etale finite-neighbourhood lemma over affine space.
   Base change and composition of etale maps give the map to `Z`; relative
   dimension permanence gives the smooth map to the first affine base, while
   finiteness and the singleton marked fibre come from the lemma.
4. Shrink around the marked point to affine neighbourhoods.  Finiteness,
   etaleness, residue fields and the singleton fibre persist; affine qcqs and
   smooth local finite presentation give finite presentation of the smooth map.
5. In the fibre over `s`, use smooth base change and the affine fibre formula
   to obtain a finite-type smooth scheme.  The smooth-component lemma applied
   to its purely transcendental marked point supplies an open geometrically
   integral component.
6. Apply elementary etale spreading to this component.  It gives an affine
   etale base change and an open family with geometrically integral fibres and
   the prescribed marked special fibre.  Smooth relative dimension is preserved
   by base change and restriction.
7. The fibre-product point and residue-field lemmas identify the unique point
   over the marked pair `(y,s₁)` and transport the purely transcendental residue
   extension.
8. Pull back the finite neighbourhood along the spread.  Fibre-product points
   and residue fields show that the marked fibre remains a singleton and that
   its residue field is unchanged; finite and etale permanence gives the other
   morphism properties and the pullback identity.
9. Choose affine opens of the new base and source around the marked points.
   Flatness and local finite presentation make the smooth map open; choosing the
   target open inside the image makes the restricted smooth map surjective and
   affine, while preserving its relative dimension.
10. Every final fibre is a nonempty open in a geometrically integral fibre.
    After arbitrary residue-field extension it remains nonempty, irreducible and
    reduced, hence integral by the integral and geometrically irreducible
    definitions.
11. Pull back the finite neighbourhood to the final affine source.  It is
    affine over the affine target, and all marked equalities, residue-field
    isomorphisms, the singleton fibre, etaleness, smoothness, geometric
    integrality and the commutative identity are retained.

The non-elementary facts in these steps are exactly the proof dependencies
recorded by the DAG item: affine opens and affine pairs; the refined polynomial
chart; affine-space smoothness; elementary etale neighbourhoods and spreading;
etale, finite, open-fibre, fibre-point and residue-field permanence; smooth
relative-dimension permanence; affine qcqs and flat-lfp openness; and the
integral/geometrically irreducible definitions.
Source: literature/stacks-project/more-morphisms.tex, Tags 057K and 057L,
lemma-local-local-structure-finite-type, clauses (1)--(6), and
lemma-local-local-structure-finite-type-affine, clause (7).
(blueprint: lem-trf-etale-finite-smooth-local-structure)
-/
theorem exists_affine_etale_finite_smooth_local_structure
    {Z S : Scheme.{u}} (p : Z ⟶ S) [LocallyOfFiniteType p] (z : Z) :
    ∃ (n : ℕ),
      topologicalKrullDimAt (p.asFiber z) = (n : WithBot ℕ∞) ∧
      ∃ (W Y S₁ : Scheme.{u}) (w : W) (y : Y) (s₁ : S₁)
        (b : W ⟶ Z) (a : S₁ ⟶ S) (π : W ⟶ Y) (h : Y ⟶ S₁),
        IsAffine W ∧ IsAffine Y ∧ IsAffine S₁ ∧
        b w = z ∧ π w = y ∧ h y = s₁ ∧
        b ≫ p = π ≫ h ≫ a ∧
        Etale b ∧ Etale a ∧
        IsIso (b.residueFieldMap w) ∧
        IsIso (a.residueFieldMap s₁) ∧
        IsFinite π ∧
        π ⁻¹' ({y} : Set Y) = ({w} : Set W) ∧
        SmoothOfRelativeDimension n h ∧
        GeometricallyIntegral h ∧
        @Algebra.IsPurelyTranscendentalExtension
          (S₁.residueField (h y)) (Y.residueField y) _ _
          ((h.residueFieldMap y).hom.toAlgebra) := by
  sorry

end AlgebraicGeometry

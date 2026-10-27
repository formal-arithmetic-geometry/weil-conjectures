module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Algebra.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.TraceFormula.FiniteResiduePointClosedInFibre

/-!
# Morphisms between alteration objects

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II,
Proposition 1.1.10 and §1.2.3, printed pp. 24--25; Stacks Project,
Tags 01T6, 01T8, 01OY and 03GI for finite type
(blueprint: lem-per-alteration-arrow-properties).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- Every arrow of `alt/S` is of finite type, preserves component generic points, and
induces finite extensions of residue fields at those points, including for an empty source.

Source: ILO, Travaux de Gabber, Exposé II, Proposition 1.1.10 and §1.2.3,
printed pp. 24--25; Stacks Project, Tags 01T6, 01T8, 01OY and 03GI
(blueprint: lem-per-alteration-arrow-properties).

Proof:
1. Write `a : X → S` and `b : T → S` for the structural maps. Both are finite type by
   `def-per-prime-to-ell-alteration-topology`. The finite-type-over-Noetherian theorem
   `lem-weil-pbc-finite-type-over-noetherian` makes both sources Noetherian. Thus `X`
   is quasi-compact and `T` is quasi-separated, using
   `lem-weil-pbc-locally-noetherian-quasi-separated`. By clause (1) of
   `lem-weil-pbc-qcqs-morphism-permanence`, `u` is quasi-compact. Cancellation from
   `u ≫ b = a` by `lemma-nagata-finite-type-to-separated-target` makes `u` locally of
   finite type. Together these say finite type, without separatedness of `b`.
2. For a component generic point `x` of `X`, put `s = a x` and `y = u x`. Choose a
   component of `T` containing `y` by `lem-sc-irreducible-components-cover`, and its
   generic point `y'` by `lem-sc-scheme-sober`. The object conditions make both `s`
   and `b y'` generic points of components of `S`. Continuity gives a specialization
   from `b y'` to `s`; maximality of components and uniqueness of generic points
   force `b y' = s`.
3. The object condition makes the residue extension at `y'` over `s` finite.
   Apply `lem-trf-finite-residue-point-closed-in-fibre` to `b` at `y'`.
   The fibre topology is the subspace topology by `def-pc-scheme-fibre`. Hence the
   specialization from `y'` to `y` in that fibre and closedness of `y'` give `y = y'`.
   In particular `u x` is a component generic point of `T`.
4. Functoriality of the induced residue-field maps gives the tower
   `κ(s) → κ(u x) → κ(x)`. Each map is injective, being a field homomorphism, and
   the composite is finite by the object condition on `X`. A finite spanning family
   over `κ(s)` also spans over `κ(u x)`, proving finiteness for the specified map.
   For an empty `X` the generic-point assertions are vacuous and Step 1 still applies.
   An empty `S` or `T` forces the corresponding source to be empty.
-/
theorem alterationArrow_properties {S : Scheme.{u}} [IsNoetherian S]
    (ell : ℕ) [Fact ell.Prime] {X T : Alt S} (u : X ⟶ T) :
    LocallyOfFiniteType u.hom.left ∧ QuasiCompact u.hom.left ∧
      ∀ x : X.obj.left, closure ({x} : Set X.obj.left) ∈ irreducibleComponents X.obj.left →
        closure ({u.hom.left x} : Set T.obj.left) ∈ irreducibleComponents T.obj.left ∧
          (u.hom.left.residueFieldMap x).hom.Finite := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration

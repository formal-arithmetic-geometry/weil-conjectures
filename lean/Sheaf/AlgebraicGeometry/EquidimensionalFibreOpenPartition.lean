module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.RingTheory.Depth
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.RestrictedFibreLocallyNoetherian

/-! # Equidimensional fibre pieces

Source: Stacks Project, Tags 02NM and 02NJ.
(blueprint: lem-sbc-cohen-macaulay-equidimensional-fibre-pieces)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A fibre Cohen-Macaulay open decomposes into pieces with pure-dimensional fibres.

Source: Stacks Project, Tags 02NM and 02NJ.
Proof: Restrict the base to U and the source to W; hW makes the latter restriction
possible. Open immersions and composition preserve flatness and local finite
presentation. Fibres are locally of finite type over residue fields, hence locally
Noetherian. The open restriction pullback squares identify their stalks with those
of the original fibres, including the canonical residue-field isomorphisms.
Depth and ring Krull dimension are invariant under these ring isomorphisms, so hW
says the restricted fibres are Cohen-Macaulay. Apply Tag 02NM to W → U. Its clopen
pieces W_n partition W and, by the definition in Tag 02NJ, all irreducible components
of every nonempty fibre of W_n have dimension n. Map W_n into X to get V_n.
The fibre of W_n identifies, as a topological space, with the inverse image of V_n
under the original fibre inclusion. A homeomorphism identifies irreducible
components and preserves their Krull dimensions, giving the last assertion.
The pieces cover W and are disjoint because W_n form a coproduct. Empty fibres
have no irreducible components, and empty W uses empty pieces.
(blueprint: lem-sbc-cohen-macaulay-equidimensional-fibre-pieces) -/
theorem exists_equidimensional_fibre_open_partition_of_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] (W : X.Opens)
    (hW : ∀ y ∈ W, f y ∈ U ∧
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ V : ℕ → X.Opens, (⨆ n, V n) = W ∧
      Pairwise (fun m n => Disjoint (V m) (V n)) ∧
      ∀ n t, ∀ C ∈ irreducibleComponents
        ↥((f.fiberι t) ⁻¹ᵁ V n), topologicalKrullDim C = (n : WithBot ℕ∞) := by sorry

end AlgebraicGeometry

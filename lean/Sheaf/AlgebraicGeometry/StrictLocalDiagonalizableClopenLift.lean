module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.GroupTheory.Finiteness
import Sheaf.Paper.StrictHenselizationPointedMap
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.FiniteStability
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # A diagonalizable clopen subgroup over the strict local base

Source: Conrad, Reductive group schemes, Theorem B.4.1 proof, printed pp.298--299,
the clopen lifting claim using only the special fibre
(blueprint: lem-sfb-strict-local-diagonalizable-clopen-lift).

The special fibre is the pullback of the actual homomorphism along the canonical residue
quotient of the pointed-neighbourhood ring colimit. Its source is canonically D_k(M).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A diagonalizable geometric fibre lifts to a diagonalizable clopen subgroup over the
strict henselization, with an isomorphism on the entire special fibre.
Source: Conrad, Reductive group schemes, Theorem B.4.1 proof, printed pp.298--299
(blueprint: lem-sfb-strict-local-diagonalizable-clopen-lift).

Proof:
1. Base change G to T. Affineness, flatness and finite presentation persist by
   lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-flat-morphism-base-change and
   lem-weil-pbc-qcqs-morphism-permanence. The chosen colimit C is strictly henselian by
   lem-weil-pbc-strict-henselization-local-structure. The pointed residue embedding into Omega
   from lem-weil-pbc-strict-henselization-pointed-map identifies the scalar extension of H_k
   with G_Omega. Apply lem-sfb-geometric-diagonalizable-separably-closed-split to split H_k
   as D_k(M) for a finitely generated M.
2. Apply lem-sfb-henselian-flat-group-split-fibre-model to descend the group and this splitting
   to a henselian local Noetherian G-ring A mapping locally to C. The model is affine, flat
   and finitely presented, and its residue splitting induces the specified splitting of H_k.
3. Complete A at its maximal ideal. Use lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-local-completion-local-ring and lem-weil-pbc-module-completion-complete for
   the complete Noetherian local base with the same residue field. The completed coordinate
   algebra is flat and finitely presented by lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-flat-module-base-change and
   lem-weil-pbc-finite-presentation-base-change-composition. Apply
   lem-sfb-complete-local-diagonalizable-fibre-hom-lift to lift the residue isomorphism to a
   clopen group homomorphism over the completion.
4. By lem-sbc-finitely-generated-abelian-group-structure, the group algebra A[M] has a finite
   presentation using invertible generators and cyclic relations. Apply
   lem-sfb-henselian-clopen-group-hom-approximation to obtain a clopen homomorphism over A
   agreeing with the completed lift on the residue field.
5. Base change to C and use the model isomorphism. The canonical coefficient map identifies
   C tensor_A A[M] with C[M], preserving all Hopf operations on basis elements. Use
   lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-open-immersion-base-change and
   lem-weil-pbc-closed-immersion-base-change. The residue map is the original splitting
   by the residue compatibility of the model and approximation, so it is an isomorphism. -/
theorem strictLocalDiagonalizableClopenLift
    {S : Scheme.{u}} (G : Grp (Over S))
    [IsAffineHom G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barS : Spec (.of Ω) ⟶ S)
    (M₀ : Type u) [AddCommGroup M₀] [AddGroup.FG M₀]
    (hgeom : Nonempty ((Over.pullback barS).mapGrp.obj G ≅ ringDiagonalizableGroup Ω M₀)) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      ∃ j : ringDiagonalizableGroup (Scheme.strictHenselizationRing barS) M ⟶
          (Over.pullback (Scheme.strictHenselizationStructuralMap barS)).mapGrp.obj G,
        IsOpenImmersion j.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left ∧
        IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom
          (@IsLocalRing.residue (Scheme.strictHenselizationRing barS) _
            (Classical.choose (strictHenselizationLocalStructure barS)))))).map
              j.hom.hom).left) := by
  sorry

end AlgebraicGeometry

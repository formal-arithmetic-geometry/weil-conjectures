module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
public import Sheaf.Paper.EtaleHypercoverProduct
public import Sheaf.Paper.FiniteSplitHypercoverExistence
public import Sheaf.Paper.FiniteSplitHypercoverReplacement
public import Sheaf.Paper.EtaleHypercoverHomotopyEqualizer
public import Sheaf.Paper.SemiRepresentableHypercoverEtale
public import Sheaf.Paper.FiniteSplitLocalReplacementZero
public import Sheaf.Paper.FiniteSplitLocalReplacementExtension
public import Sheaf.Paper.FiniteSplitLocalReplacementAssembly

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Finite refinements and local lifting

Source: blueprint `lem-weil-pbc-hypercover-refinement`, order 947;
Stacks Project, Hypercoverings, Tags 0DAV, 094K, 01GJ, 01GK, 01GS.
(blueprint: lem-weil-pbc-hypercover-refinement)

Cofilteredness is stated by its three defining conditions. Covering sieves encode
restriction-stable local lifting requirements; lifts are on the finite constituent
pieces, as in the semi-representable interpretation of hypercovers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

private theorem finite_inf_covering
    {C : Type*} [Category* C] (J : GrothendieckTopology C) {T : C}
    {I : Type} (F : I → Sieve T) (s : Finset I) (hF : ∀ i ∈ s, F i ∈ J T) :
    s.inf F ∈ J T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [J.top_mem]
  | @insert i s hi ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hF i (Finset.mem_insert_self _ _))
        (ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)))

end AlgebraicGeometry.FiniteSplitEtaleHypercover

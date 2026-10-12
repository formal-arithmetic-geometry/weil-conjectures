module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Proper pushforward preserves support proper over a separated finite-type base.
Source: Stacks Project, Theorem 088E, the paragraph on the support of H, using
Tags 02O5, 0CYQ (1), and 0CYN (https://stacks.math.columbia.edu/tag/088E).
(blueprint: new-chow-algebraization-support)

Proof: Let C be the closed support of F, proper over S by hF. The image q(C) is
closed and proper over S because f is separated (Tag 0CYQ (1)). Proper coherent
pushforward (Tag 02O5) makes q_*F coherent on the Noetherian Z, hence its support D
is closed. Outside q(C), the preimage of the open complement has only zero stalks
of F. The sheaf axiom implies its sections on every open are zero, so q_*F has
zero stalks outside q(C). Thus D is a closed subset of q(C). Tag 0CYN implies
that D is proper over S, which is precisely the asserted support condition. -/
theorem chow_algebraization_pushforward_support
    {S Z Y : Scheme.{u}} [IsNoetherian Z]
    (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (q : Y ⟶ Z) [IsProper q] (F : CoherentModules Y)
    (hF : Scheme.Modules.HasSupportProperOver (q ≫ f) F.obj) :
    Scheme.Modules.HasSupportProperOver f ((Scheme.Modules.pushforward q).obj F.obj) := by
  sorry

end AlgebraicGeometry

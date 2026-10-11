import Mathlib.CategoryTheory.Sites.Plus
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# The plus construction of a sheaf is isomorphic to the sheaf

Source: literature/stacks-project/sites.tex, Theorem 00WB (part (3), item-plus-iso)
(blueprint: lem-weil-pbc-site-plus-of-sheaf-iso)
-/

open CategoryTheory

namespace CategoryTheory.GrothendieckTopology

universe u

/-- For a sheaf, the canonical map to the plus construction is an isomorphism,
    and the plus construction is a sheaf.

Source: literature/stacks-project/sites.tex, Theorem 00WB (part (3), item-plus-iso)
(blueprint: lem-weil-pbc-site-plus-of-sheaf-iso)
Proof (Stacks 00WE, expanding the four steps of the node):
1. For each covering, the sheaf equalizer condition identifies `P(U)` bijectively
   with its compatible families `H⁰` (def-weil-pbc-sites-and-cohomology and
   def-weil-pbc-site-plus-construction).
2. If two sections have the same image under the canonical map, the refinement
   criterion of lem-weil-pbc-site-plus-construction-presheaf gives a covering on
   which their restrictions agree. Step 1 then makes the sections equal.
3. Every plus section is represented by a compatible family on a covering
   (lem-weil-pbc-site-plus-construction-presheaf). Step 1 glues it to a section
   `a`. The refinement from that covering to the trivial identity covering sends
   `a` to this family, so the colimit cocone identity identifies the represented
   plus section with the image of `a` (def-weil-pbc-site-plus-construction).
4. The canonical map is natural by
   lem-weil-pbc-site-plus-construction-presheaf. Its componentwise inverses are
   therefore natural and give a presheaf inverse. These bijections identify each
   covering equalizer diagram with the corresponding diagram for the plus
   presheaf, transporting the sheaf condition.

The dependency def-weil-pbc-site-plus-construction records Mathlib's covering
sieve construction for `J.toGrothendieck`; its canonical comparison with the
covering-family colimit is the stage-3 bridge.
-/
theorem isIso_toPlus_of_isSheaf_and_isSheaf_plus
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (P : Cᵒᵖ ⥤ Type u)
    (hP : Presheaf.IsSheaf J.toGrothendieck P) :
    IsIso (J.toGrothendieck.toPlus P) ∧
      Presheaf.IsSheaf J.toGrothendieck (J.toGrothendieck.plusObj P) := by
  sorry

end CategoryTheory.GrothendieckTopology

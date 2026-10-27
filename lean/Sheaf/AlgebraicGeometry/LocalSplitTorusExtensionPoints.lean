module

public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RingTheory.LocalRing.Defs

import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Sections of split-torus extensions over local rings

Source: Stacks Project, Etale Cohomology, Tag 03P8 (theorem-picard-group), and
Groupoid Schemes, Tags 0499 and 049A; the local-ring finite-product consequence.
(blueprint: lem-sfb-local-split-torus-extension-points).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- An fppf exact extension by a finite-rank split torus is surjective on sections
of the spectrum of a nonzero local ring. The kernel condition is the cartesian
square with the unit section; local lifting is imposed on the represented
presheaves over the big fppf site, not on global sections.

Source: Stacks Project, Etale Cohomology, Tag 03P8 (theorem-picard-group), and
Groupoid Schemes, Tags 0499 and 049A.
(blueprint: lem-sfb-local-split-torus-extension-points).

Proof:
1. For j in J(C), form P = E times_J Spec C. The kernel square makes translation
   by T simply transitive on every nonempty set of test-scheme points of P.
   Fppf local surjectivity supplies local sections p_a of P.
2. On overlaps write p_b = i(g_ab) p_a. Uniqueness gives the cocycle equation
   g_ac = g_bc g_ab. In each of the r coordinates these are units. An fppf cover
   is fpqc (lem-trf-fppf-covering-is-fpqc), so effective descent of quasi-coherent
   modules (lem-pc-fpqc-descent, part 3) produces invertible modules L_h with
   frames e_b,h = g_ab,h e_a,h.
3. Each L_h is trivial near the unique maximal ideal m. A basic open D(f)
   containing m inside that trivializing open has f outside m, hence f a unit.
   Thus D(f) is the whole spectrum and L_h has a global frame v_h. Write
   v_h = u_a,h e_a,h; on overlaps u_a = g_ab u_b.
4. The corrected lifts z_a = i(u_a) p_a agree. Representable fpqc descent
   (lem-weil-pbc-fpqc-representable-descent) glues them to z. Its uniqueness,
   applied to the targets Spec C and J, ensures z is over Spec C and q z = j.
   For r = 0 the tuples are empty and the original lifts already agree.
   Every field is a nonzero local ring, so fields are included. -/
theorem localSplitTorusExtensionPoints_surjective
    (C : Type u) [CommRing C] [IsLocalRing C] (r : ℕ)
    (E J : Grp (Over (Spec (.of C)))) [IsCommMonObj E.X] [IsCommMonObj J.X]
    (i : relativeSplitTorus (Spec (.of C)) r ⟶ E) (q : E ⟶ J)
    (_hkernel : IsPullback i.hom.hom (toUnit (relativeSplitTorus (Spec (.of C)) r).X)
      q.hom.hom η[J.X])
    (_hlocallySurjective : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (.of C))) (yoneda.map q.hom.hom)) :
    Function.Surjective
      (fun e : Over.mk (𝟙 (Spec (.of C))) ⟶ E.X ↦ e ≫ q.hom.hom) := by
  sorry

end AlgebraicGeometry

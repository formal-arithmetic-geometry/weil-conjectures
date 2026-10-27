module

public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded

/-! # Closed immersions and relative pseudo-coherence

Source: Stacks Project, More on Morphisms, Tag 09VG, restricted to closed immersions
(blueprint: lem-sfb-closed-support-relative-pseudocoherence).

The equivalence concerns arbitrary objects of the unbounded derived category of modules.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Derived direct image along a closed immersion over `S` preserves and reflects relative
`m`-pseudo-coherence, without any quasi-coherence assumption on the object.
Source: Stacks Project, More on Morphisms, Tag 09VG, closed-immersion case
(blueprint: lem-sfb-closed-support-relative-pseudocoherence).

Proof:
1. Choose affine opens V covering S and affine opens W covering the preimage of V in Y,
   using lem-weil-pbc-affine-opens-basis. The inverse images U in X are affine because i
   is a closed immersion (def-weil-closed-immersion). By the embedding-existence clause of
   lem-sfb-relative-pseudocoherence-all-affine-charts, choose j : W → affine n-space over V.
   Then k = i|U followed by j is closed by lem-weil-pbc-closed-immersion-comp.
2. Put F = Ri_*E. By lem-pc-restrict-derived-direct-image-open and
   lem-pc-derived-direct-image-composition, Rj_*(F|W) is isomorphic to Rk_*(E|U).
   These comparisons hold for arbitrary unbounded module complexes. The approximation
   criterion def-sfb-m-pseudo-coherent-complex is invariant under this isomorphism:
   compose each strictly perfect approximation map with the isomorphism or its inverse.
   The cohomology isomorphisms above m and the surjection in degree m are preserved.
3. If E is relatively m-pseudo-coherent, apply
   lem-sfb-relative-pseudocoherence-all-affine-charts on U over V with the embedding k.
   Step 2 gives m-pseudo-coherence of Rj_*(F|W). The chosen covers and j witness relative
   m-pseudo-coherence of F by def-sfb-relative-pseudo-coherent-complex.
4. Conversely apply lem-sfb-relative-pseudocoherence-all-affine-charts to F on W over V
   with j. Step 2 gives m-pseudo-coherence of Rk_*(E|U). The covers and k witness relative
   m-pseudo-coherence of E. The integer m is arbitrary, covers need not be finite, and
   empty source opens impose no additional condition. -/
theorem isMPseudoCoherentRelativeTo_iff_closedImmersion_pushforward
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (i : X ⟶ Y) [IsClosedImmersion i] (_hi : i ≫ fY = fX)
    (m : ℤ) (E : schemeDerivedCategory X) :
    IsMPseudoCoherentRelativeTo fX m E ↔
      IsMPseudoCoherentRelativeTo fY m ((schemeDerivedDirectImage i).obj E) := by
  sorry

end AlgebraicGeometry.Scheme

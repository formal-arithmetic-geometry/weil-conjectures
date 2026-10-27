module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.ClosedSupportRelativePseudoCoherence
import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Relative pseudo-coherence in a flat ambient scheme

Source: Stacks Project, More on Morphisms, Tag 09UU, equivalence of (1) and (3)
for every integer degree (blueprint: lem-sfb-flat-ambient-relative-pseudocoherence).

The statement concerns arbitrary unbounded derived objects and requires only a closed
immersion into an ambient scheme flat and locally of finite presentation over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Relative pseudo-coherence over `S` is equivalent to absolute pseudo-coherence of the
derived direct image along a closed immersion into a flat, locally finitely presented
`S`-scheme. Source: Stacks Project, More on Morphisms, Tag 09UU, (1) iff (3), for all degrees
(blueprint: lem-sfb-flat-ambient-relative-pseudocoherence).

Proof:
1. The ambient morphism is locally of finite type because it is locally of finite
   presentation (def-sbc-locally-finite-presentation, def-pc-morphism-conventions).
   A closed immersion is locally of finite type (def-weil-closed-immersion): on affine
   charts it is a quotient B → B/I, and finite algebra generators of B over the base
   also generate B/I. Thus the composite is locally of finite type as well.
2. Set F = Ri_*E (def-pc-derived-direct-image) and fix an integer m. By
   lem-sfb-closed-support-relative-pseudocoherence, E is relatively m-pseudo-coherent
   over S iff F is. By lem-sfb-flat-lfp-structure-relative-pseudocoherence, the structure
   sheaf of P in degree zero is pseudo-coherent relative to S. Apply
   lem-sfb-relative-pseudocoherence-composition to the identity of P: relative
   m-pseudo-coherence of F over S is equivalent to relative m-pseudo-coherence over P.
3. For the identity of P, lem-sfb-relative-pseudocoherence-all-affine-charts identifies
   this with absolute m-pseudo-coherence (def-sfb-m-pseudo-coherent-complex), using the
   identity embedding V → affine zero-space over V on every affine open V
   (def-nagata-relative-affine-space). Conversely restrict local strictly perfect
   approximations to affine opens and use those identity embeddings. Derived pullback
   along an open immersion (def-pc-derived-pullback) is exact restriction, preserving
   the strictly perfect complexes of def-pc-perfect-complex and the required cohomology
   isomorphisms above m and surjection at m. These give the relative witnesses of
   def-sfb-relative-pseudo-coherent-complex.
4. Quantify over every integer m, using def-sfb-relative-pseudo-coherent-complex and
   the all-degrees characterization of def-pur-pseudo-coherent-complex. Covers can vary
   with m. No finite cover, quasi-compactness, properness, Noetherianity or hypothesis
   on the cohomology of E is used. -/
theorem isPseudoCoherentRelativeTo_iff_flatAmbient_pushforward
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {X P S : Scheme.{u}}
    [∀ U : P.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings P.toRingedSpace).over U))]
    (i : X ⟶ P) (g : P ⟶ S) [IsClosedImmersion i] [Flat g]
    [LocallyOfFinitePresentation g] (E : schemeDerivedCategory X) :
    IsPseudoCoherentRelativeTo (i ≫ g) E ↔
      IsPseudoCoherent P ((schemeDerivedDirectImage i).obj E) := by
  sorry

end AlgebraicGeometry.Scheme

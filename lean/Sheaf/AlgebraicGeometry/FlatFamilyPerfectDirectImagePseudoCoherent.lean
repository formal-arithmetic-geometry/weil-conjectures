module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex

/-! # Pseudo-coherent perfect direct images between flat families

Source: Stacks Project, More on Morphisms, Tags 0695, 0683, 09UU and 09UT;
Derived Categories of Schemes, the Kiehl assertion following Tag 0CSD;
Duality for Schemes, Tag 0A9P, footnote. The common-flat-base specialization
is agent-formulated (blueprint: lem-sfb-flat-family-perfect-direct-image-pseudocoherent).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A proper morphism over a common base between flat, locally finitely presented
families sends perfect complexes to pseudo-coherent complexes. No flatness of `f`,
Noetherianity, or absolute quasi-compactness or quasi-separatedness is assumed.
Source: Stacks Project, Tags 0695, 0683, 09UU, 09UT and the Kiehl assertion following
Tag 0CSD; Tag 0A9P, footnote. The common-flat-base specialization is agent-formulated
(blueprint: lem-sfb-flat-family-perfect-direct-image-pseudocoherent).

Proof:
1. By `lem-pc-perfect-pseudo-coherent-locally-finite-tor`, `P` is pseudo-coherent on
   `X`. Only pseudo-coherence is used; no global Tor-amplitude bound is chosen.
2. Apply `lem-sfb-flat-ambient-relative-pseudocoherence` to the identity closed
   immersion of `X` into the flat, locally finitely presented ambient family `X`.
   The identity is a closed immersion by `def-weil-closed-immersion`, and its
   derived direct image is the identity by `def-pc-derived-direct-image`: identity
   pushforward is exact and applying it to a K-injective resolution changes nothing.
   Thus `P` is pseudo-coherent relative to `S`.
3. By `lem-sfb-flat-lfp-structure-relative-pseudocoherence`, the structure sheaf
   of `Y` in degree zero is pseudo-coherent relative to `S`. The structure maps
   are locally of finite type since finite presentation implies finite type, and
   `f` is locally of finite type since it is proper. For every integer `m`,
   `lem-sfb-relative-pseudocoherence-composition` identifies relative
   `m`-pseudo-coherence over `S` and over `Y`. Hence `P` is pseudo-coherent relative
   to `Y`, by `def-sfb-relative-pseudo-coherent-complex`.
4. Apply `lem-sfb-kiehl-relative-pseudocoherent-direct-image` to `f` and `P`.
   Properness and relative pseudo-coherence give pseudo-coherence of `Rf_*P`,
   without flatness of `f` or global finiteness hypotheses on the schemes.
-/
theorem isPseudoCoherent_directImage_of_perfect_flat_families
    {S X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (x : X ⟶ S) (y : Y ⟶ S)
    [Flat x] [LocallyOfFinitePresentation x]
    [Flat y] [LocallyOfFinitePresentation y]
    (f : X ⟶ Y) [IsProper f] (_hOver : f ≫ y = x)
    (P : schemeDerivedCategory X) (_hP : IsPerfect X P) :
    IsPseudoCoherent Y ((schemeDerivedDirectImage f).obj P) := by
  sorry

end AlgebraicGeometry.Scheme

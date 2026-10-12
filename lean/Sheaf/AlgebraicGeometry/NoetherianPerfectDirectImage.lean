/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Perfect direct image over a Noetherian base

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.2, Tag 0DJQ
(blueprint: lem-pc-noetherian-perfect-direct-image).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Over a Noetherian base, the derived direct image of a perfect object tensored with a
bounded complex of finitely presented, relatively flat modules with proper support is perfect.
Source: Stacks Project, Lemma 36.27.2, Tag 0DJQ, specialized to a finitely presented morphism.

Proof:
1. Finite presentation implies locally finite type (def-pc-morphism-conventions,
   def-weil-finite-type-morphism), so X is locally Noetherian (pqf-def-locnoeth, Tag 01T6).
   The finitely presented terms of G are therefore coherent (pqf-lem-coherent-ft-locnoeth).
   Their finitely many nonzero supports have a closed union Z proper over S, hence compact.
   Cover Z by finitely many opens on which E has strictly perfect representatives
   (def-pc-perfect-complex). Tensoring these with G gives bounded complexes of coherent
   modules: their terms are summands of finite sums of terms of G. Outside Z the tensor
   vanishes. Thus E tensor^L G has bounded coherent cohomology, using Tag 01Y0.
2. The cohomology supports are closed subsets of Z, hence proper over S
   (def-weil-pbc-closed-subset-proper-over-base), since closed immersions and composites
   of proper morphisms are proper.
3. The local tensor representatives consist of modules flat over the inverse image of O_S.
   The finite cover gives uniform bounds [a,b]. Tag 08CI gives Tor amplitude [a,b] on
   each open, and vanishing outside this range is local (Tag 08CG). Thus the tensor has
   finite Tor dimension over the inverse image of O_S, also being zero outside Z.
4. Apply lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect (Tag 08EV) to the
   tensor object: bounded coherence, proper cohomology supports and finite relative Tor
   dimension give a perfect derived direct image (def-pc-perfect-complex).
(blueprint: lem-pc-noetherian-perfect-direct-image). -/
theorem noetherian_perfect_directImage
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, Scheme.Modules.IsFlatOver (G.X n) f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      (E ⊗ DerivedCategory.Q.obj G)) := by
  sorry

end AlgebraicGeometry

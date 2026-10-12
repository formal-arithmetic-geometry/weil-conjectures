/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.Dimension
public import Sheaf.AlgebraicGeometry.SheafExt
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.SheafExtCoherent
import Sheaf.AlgebraicGeometry.SheafExtStalkLocalization
import Sheaf.Paper.SupportDimensionCohomologyVanishing
import Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree
import Sheaf.RingTheory.RegularLocalExtVanishing
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Support-dimension vanishing for sheaf Ext

Source: literature/stacks-project/equiv.tex, Lemma 0FZ3 and Proposition 02UZ
(blueprint: lem-sc-ext-support-cohomology-vanishing).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

/-- Support of sheaf Ext has dimension at most `d - q`, and its cohomology vanishes above
that bound. Source: Stacks Project, Lemma 0FZ3 (Tag 0FZ3), proof of (1), and Proposition
02UZ (blueprint: lem-sc-ext-support-cohomology-vanishing).

Proof:
1. By lem-sc-ext-stalk-localization the stalk is local Ext. Coherence makes the first
   stalk finitely generated; lem-sc-regular-local-ext-vanishing makes it zero above the
   local ring dimension.
2. By lem-sc-sheaf-ext-coherent, pqf-lem-coherent-ft-locnoeth and
   lem-weil-pbc-finite-type-module-support-closed the support is closed. For a chain
   in this support, its largest member has generic point x with local dimension at
   least q. By lem-sc-scheme-stalk-dimension-generalization-chains concatenate the
   chain with a chain of length dim O_{X,x}; def-pc-dimension bounds its length by d.
   The original chain has length at most d-q.
3. Apply lem-sc-support-dimension-cohomology-vanishing to the underlying abelian sheaf
   with this closed support, using def-sc-topological-abelian-cohomology and
   def-weil-pbc-module-stalk. Transfer vanishing through
   lem-sc-zariski-module-abelian-cohomology-agree to pqf-def-cohomology.
4. If q>d, every stalk is zero by step 1 and def-pc-dimension, so the sheaf and all its
   cohomology are zero. Negative-degree cohomology of a module is zero by convention.

The dimension bound uses natural subtraction only under q≤d. The cohomology inequality
uses integer subtraction, including degree zero when q>d. The negative-degree branch
extends the recorded nonnegative right-derived functors by zero. HasDerivedCategory is
only the size infrastructure required by the recorded sheaf Ext definition.
-/
theorem ext_support_cohomology_vanishing (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (hregular : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U))
    (d : ℕ) (hdim : X.dim = (d : WithBot ℕ∞))
    (F G : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (q : ℤ) (hq : 0 ≤ q) :
    (q ≤ (d : ℤ) →
      topologicalKrullDim
          {x : X // ¬ Subsingleton
            ((Scheme.Modules.presheaf
              (AlgebraicGeometry.moduleSheafExt X q F G)).stalk x)}
        ≤ (((d : ℤ) - q).toNat : WithBot ℕ∞)) ∧
    ((d : ℤ) < q →
      (∀ x : X, Subsingleton
        ((Scheme.Modules.presheaf
              (AlgebraicGeometry.moduleSheafExt X q F G)).stalk x))) ∧
    (∀ p : ℤ, (d : ℤ) - q < p →
      IsZero
        (if 0 ≤ p then
          (RingedSpace.moduleCohomology X.toRingedSpace p.toNat).obj
            (AlgebraicGeometry.moduleSheafExt X q F G) else 0)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

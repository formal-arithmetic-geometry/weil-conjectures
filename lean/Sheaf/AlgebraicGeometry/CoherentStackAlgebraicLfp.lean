/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.FlatCoherentModuli
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Algebraicity of the stack of flat finitely presented modules with proper support

Source: Stacks Project, quot.tex, Situation 08KB and Theorem 08WC; moduli.tex,
Lemma 0DLZ (blueprint: lem-sfb-coherent-stack-algebraic-lfp).

The category is the concrete construction of def-sfb-flat-coherent-moduli.
The conclusion retains both algebraicity and a locally finitely presented atlas composite.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The coherent-family category is algebraic, with a locally finitely presented atlas
composite to the base. No Noetherian hypothesis is imposed.
Source: Stacks, quot.tex, Theorem 08WC and Situation 08KB; moduli.tex, Lemma 0DLZ
(blueprint: lem-sfb-coherent-stack-algebraic-lfp).
Proof:
1. Regard X and S as their representable algebraic spaces (def-trf-scheme-algebraic-space).
   Identity charts identify local finite presentation. Quasi-compactness and
   quasi-separatedness persist on all scheme base changes by
   lem-pc-quasi-compact-base-change and lem-weil-pbc-proper-fp-permanence. The diagonal
   is the representable closed scheme diagonal, so separatedness agrees too
   (def-sfb-space-morphism-properties, lem-sfb-space-local-properties-chart-test).
2. On each X_T, lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies
   quasi-coherent modules on the two sites. Finite type and finite presentation agree
   by lem-sfb-scheme-etale-module-exact-finiteness-comparison. Relative flatness agrees
   on the identity chart and on all etale charts by lem-trf-relative-flatness-source-cover.
   A closed subspace of X_T is a scheme, by pulling its closed immersion back along the
   identity chart. Closed pushforward respects the site equivalence. Its projection to T
   is proper exactly when its scheme morphism is proper, by
   lem-sfb-space-representable-proper-tests and lem-weil-pbc-proper-fp-permanence.
   Hence the proper-support presentations agree with def-sfb-space-proper-quot-functor.
   Tensor pullback comparisons identify every arrow, including identity and composition.
3. Apply lem-sfb-space-coherent-stack-general with parameter base B=S. Its atlas and
   representable diagonal transport through this equivalence; so does effective etale
   descent. Its scheme-base clause gives the locally finitely presented atlas composite.
   The stack condition and atlas conditions are exactly def-sfb-algebraic-moduli-stack.
   The general theorem needs neither Noetherianity nor flatness of the ambient family;
   the stated flatness hypothesis is therefore harmless. -/
theorem coherent_stack_algebraic_lfp {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] :
    IsAlgebraicModuliStack (FlatCoherentModuli.category f) ∧
      ∃ (U : Over S)
        (a : BasedFunctor (discreteModuli (yoneda.obj U)) (FlatCoherentModuli.category f)),
        IsSmoothModuliAtlas (FlatCoherentModuli.category f) U a ∧
          LocallyOfFinitePresentation U.hom := by
  sorry

end AlgebraicGeometry

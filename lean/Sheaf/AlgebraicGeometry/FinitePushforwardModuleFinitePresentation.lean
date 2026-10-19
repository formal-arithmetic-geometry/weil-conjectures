/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation
import Sheaf.TraceFormula.FiniteSingletonFibreStalkRing

/-!
# Finite presentation under finite pushforward near a singleton fibre

Source: Stacks Project, Flatness, Tag 057T, comparison of conditions (2) and (3)
and of conditions (b) and (c); Descent, Tag 05B4; More on Morphisms, Tag 05B8.
(blueprint: lem-trf-finite-pushforward-module-finite-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite pushforward preserves and reflects finite presentation on neighbourhoods
of a singleton fibre, and also finite presentation of the two stalk modules.
Source: Stacks Project, Flatness, Tag 057T; Descent, Tag 05B4; More on Morphisms,
Tag 05B8 (blueprint: lem-trf-finite-pushforward-module-finite-presentation).

The direct image is the Zariski direct image `pushforward p`, with sections on `V`
equal to those of `M` on `p ⁻¹ᵁ V` and scalars acting through `p.app V`.
Since `p` is finite, local finite presentation already gives finite presentation:
quasi-compactness and quasi-separatedness follow from finiteness.

Proof:
1. A finite morphism is closed (lem-weil-pbc-finite-closed-map-finite-fibres).
   For a neighbourhood W of t, remove p(T \ W) from U. The resulting neighbourhood
   of p(t) has inverse image contained in W, since the fibre is exactly {t}.
   Refine it to an affine neighbourhood (lem-weil-pbc-affine-opens-basis).
2. Over an affine V = Spec R, finiteness gives p^{-1}V = Spec S with S finite
   over R. Local finite presentation makes S a finitely presented R-algebra
   (lem-weil-pbc-lfp-affine-opens-finite-presentation). The direct image is
   quasi-coherent (lem-weil-pbc-affine-pushforward-base-change), and its sections
   are the same module N = M(p^{-1}V) with scalars restricted from S to R
   (lem-weil-pbc-pushforward-spec-global-sections).
3. The affine criterion (lem-weil-pbc-quasi-coherent-finite-type-affine) identifies
   sheaf finite presentation on these two affine opens with finite presentation
   of N over S and over R. These are equivalent by
   lem-trf-finite-extension-module-finite-presentation.
4. Use step 1 to shrink any neighbourhood of t to an inverse image of an affine
   neighbourhood of p(t). Finite presentations restrict to smaller opens.
   Step 3 now gives both directions of the neighbourhood equivalence.
5. The germ map (p_*M)_{p(t)} to M_t is bijective: cofinality from step 1 gives
   representatives for surjectivity and a common smaller neighbourhood for
   injectivity. The defining germ scalar actions (def-weil-pbc-module-stalk)
   show that this is linear over O_{U,p(t)} via the canonical stalk ring map.
6. That ring map is finite and finitely presented by
   lem-trf-finite-singleton-fibre-stalk-ring. Apply
   lem-trf-finite-extension-module-finite-presentation to M_t and use step 5
   to obtain the stalk equivalence. No inference from a stalk to a neighbourhood
   is used. -/
theorem finitePresentation_near_and_stalk_iff_pushforward_of_singleton_fibre
    {T U : Scheme.{u}} (p : T ⟶ U) [IsFinite p] [LocallyOfFinitePresentation p]
    (t : T) (_hfibre : p ⁻¹' ({p t} : Set U) = ({t} : Set T))
    (M : T.Modules) [M.IsQuasicoherent] :
    ((∃ W : T.Opens, t ∈ W ∧ (M.over W).IsFinitePresentation) ↔
      ∃ V : U.Opens, p t ∈ V ∧ (((pushforward p).obj M).over V).IsFinitePresentation) ∧
    (Module.FinitePresentation (T.presheaf.stalk t)
        ((RingedSpace.moduleStalkFunctor T.toRingedSpace t).obj M) ↔
      Module.FinitePresentation (U.presheaf.stalk (p t))
        ((RingedSpace.moduleStalkFunctor U.toRingedSpace (p t)).obj
          ((pushforward p).obj M))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.CategoryTheory.Sites.CoherentToposRepair
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.EtaleToposPointsGeometric
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.Paper.FinitarySiteEnoughPoints
import Sheaf.Paper.QcqsOrientedTriplePresentation
import Sheaf.TraceFormula.FinitarySiteCoherentGenerators
import Sheaf.TraceFormula.ProperGeometricSpecializationLift
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismStalkBijection

/-!
# Proper base change and coherent conservative vanishing topoi

Source: Orgogozo, author draft, §8.1, printed p. 17, and proof of Lemma 9.1.5,
printed p. 21 (blueprint: lem-trf-proper-base-change-coherent-conservative).
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.CoherentToposRepair

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- A proper surjective base change has Noetherian source, preserves finite presentation,
and induces a coherent conservative morphism of vanishing topoi.
Source: Orgogozo, author draft, §8.1, printed p. 17, and proof of Lemma 9.1.5,
printed p. 21 (blueprint: lem-trf-proper-base-change-coherent-conservative).
Proof: the Noetherian and finite-presentation assertions follow from properness,
Noetherian finite-type permanence, and stability of finite presentation under base
change. Coherence follows from the finite triple-site presentation and the coherent-
generator criterion. Conservativity follows by lifting geometric points through the
proper surjective map and testing isomorphisms on the resulting enough family of
points, as detailed in the node proof steps and the cited dependency nodes.
-/
theorem proper_baseChange_coherent_conservative
    {S X T : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (p : T ⟶ S) [IsProper p] [Surjective p] :
    IsNoetherian T ∧
      LocallyOfFinitePresentation (pullback.snd f p) ∧
      QuasiCompact (pullback.snd f p) ∧
      QuasiSeparated (pullback.snd f p) ∧
      IsCoherentVanishingTopos.{u, v} f ∧
      IsCoherentVanishingTopos.{u, v} (pullback.snd f p) ∧
      IsCoherentVanishingSquare f (pullback.snd f p) (pullback.fst f p) p
        (pullback.condition (f := f) (g := p)) ∧
      IsConservativeVanishingSquare f (pullback.snd f p) (pullback.fst f p) p
        (pullback.condition (f := f) (g := p)) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.CategoryTheory.SiteStackification
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Reduced locally Noetherian atlases from fppf scheme covers

Source: Stacks Project, Tags 04YF and 06MP, proof of (2) implies (1), generalized
from a field cover to a reduced locally Noetherian scheme cover; Tags 034C and 034E
(blueprint: lem-sfb-stack-reduced-locnoeth-fppf-descent).

Algebraicity is unpacked using the fppf stack condition, the algebraic-space diagonal,
and existence of a smooth surjective atlas. The covering map is tested on its actual
algebraic-space base changes and their étale scheme charts.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

/-- A representable surjective flat locally finitely presented map from a reduced
locally Noetherian scheme supplies a reduced locally Noetherian smooth atlas.
Source: Stacks Project, Tags 04YF and 06MP, proof of (2) implies (1), with a reduced
locally Noetherian scheme replacing the field; Tags 034C, 034E, 06MI and 06MJ
(blueprint: lem-sfb-stack-reduced-locnoeth-fppf-descent).

Proof:
1. Choose a smooth surjective atlas W of F. Represent W ×_F V by an algebraic space
   and choose a surjective étale scheme chart T of it (def-trf-algebraic-space).
   By lem-sfb-stack-chartwise-smooth-etale-calculus, the composite T → V is smooth,
   and T → W is flat, locally of finite presentation and surjective.
2. Apply the smooth-ascent clause of lem-trf-smooth-reduced-dense-pullback to T → V:
   T is reduced and locally Noetherian. No density clause or surjectivity of T → V
   is needed.
3. At each w in W, choose t in T above it. The stalk map is flat and local
   (def-weil-flat-morphism), hence faithfully flat by
   lem-weil-pbc-flat-local-hom-faithfully-flat, and injective by
   lem-weil-pbc-faithfully-flat-ideal-contraction with the zero ideal. A nilpotent
   in the stalk of W maps to zero in the reduced stalk of T and is therefore zero.
   Thus W is reduced (def-pc-reduced-scheme).
4. Apply lem-sfb-scheme-locnoeth-fppf-descent to T → W to deduce that W is locally
   Noetherian. The original atlas W → F has both desired properties. -/
theorem exists_reduced_locallyNoetherian_smoothAtlas_of_fppf_cover
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hstack : IsFppfModuliStack F) (hdiag : HasAlgebraicSpaceDiagonal F)
    (hatlas : ∃ (W : Over S) (q : BasedFunctor (discreteModuli (yoneda.obj W)) F),
      IsSmoothModuliAtlas F W q)
    (V : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj V)) F)
    (hp : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange p T t Z a ∧ SpaceMapIsSurjective Z T a ∧
          ∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            Flat (yoneda.preimage (b ≫ a)).left ∧
              LocallyOfFinitePresentation (yoneda.preimage (b ≫ a)).left)
    [IsReduced V.left] [IsLocallyNoetherian V.left] :
    ∃ (W : Over S) (q : BasedFunctor (discreteModuli (yoneda.obj W)) F),
      IsSmoothModuliAtlas F W q ∧ IsReduced W.left ∧ IsLocallyNoetherian W.left := by
  sorry

end AlgebraicGeometry

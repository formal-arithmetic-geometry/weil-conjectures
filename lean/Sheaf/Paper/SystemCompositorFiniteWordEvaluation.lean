/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.SystemCompatibleCompositorData

/-! # Finite evaluation of the compatible proper/open word

Source: Stacks Project, Tag 0F7J, four identifications; Zheng, Lemma 4.10
(blueprint: lem-pur-system-compositor-finite-word-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits WeilConjectures
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Evaluation of the actual system word equals the specified finite etale compositor,
through the canonical support comparisons and a supplied identity-scalar origin.
Source: Stacks Project, more-etale.tex, Tag 0F7J, four displayed identifications;
Zheng, Lemma 4.10; normalization proof Steps 4--6
(blueprint: lem-pur-system-compositor-finite-word-evaluation).

Proof: Expand the word into the proper/open mate, the direct-image compositor and
then the open compositor. Apply gamma_finite to the open extension of the supplied
origin. The canonical open comparison supplies this origin with the same coefficient
ring and scalar map. Finite clopen-mate site transport and proper/open coefficient
mate compatibility identify its normalized finite mate with the open-adjunct
interchange of FiniteSiteTower. Evaluation of the direct-image and open compositors
agrees with their finite versions: both are the mates of the section-normalized
pullback composition maps, so their transposes coincide. Whisker the three equations
and use naturality to move the supplied origin isomorphism to the two ends. The
finite-site tower paste gives AE, whose etale compositor normalization is exactly
coherenceEtaleCompositor in the three displayed compactifications. Associativity
and cancellation of comparison inverse pairs give the equation below. All these
are equations before evaluation; no conservativity on morphism equality is used.
Identity factors satisfy the same normalized mate equations. For an empty open,
exact extension is zero and the corresponding equations hold by uniqueness of maps
between zero objects. No constructibility, common interval or Tor bound is needed
once the bounded-below origin is supplied. -/
theorem systemCompositorFiniteWordEvaluation
    {X V XB Y YB Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian V] [IsNoetherian XB]
    [IsNoetherian Y] [IsNoetherian YB] [IsNoetherian Z]
    (j : X ⟶ V) (b : V ⟶ XB) (q : V ⟶ Y) (p : XB ⟶ YB)
    (i : Y ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact j] [QuasiCompact b] [QuasiCompact i]
    [IsProper q] [IsProper p] [IsProper s]
    (sq : IsPullback b q p i) (h : b ≫ p = q ≫ i)
    (n : ℕ) [Finite (C n)] (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M))
    (hC : w.Λ = (C n : Type (u + 1))) (hφ : HEq w.φ (RingHom.id (C n))) :
    (compositorFiniteSource C τ j q i s n M w).hom ≫
        (compositorLevel C τ Z n).map ((compatibleCompositorWord C τ j b q p i s h).app M) =
      (StrictTower.HD (C n) Z w.Λ w.φ).map
        ((coherenceEtaleCompositor w.Λ
          (FiniteSiteTower.compactificationF j q)
          (FiniteSiteTower.compactificationG s i)
          (FiniteSiteTower.compactificationGF j b p s i q sq)).hom.app w.origin.L) ≫
        (compositorFiniteTarget C τ j b p s n M w).hom := by sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

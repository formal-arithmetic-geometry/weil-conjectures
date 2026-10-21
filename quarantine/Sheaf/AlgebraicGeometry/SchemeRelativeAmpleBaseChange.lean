/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.AmplePullback
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover

/-!
# Relative ampleness for schemes under arbitrary base change

Source: Stacks Project, Morphisms, Tag 0893 (lemma-ample-base-change), with relative
ampleness as in Tag 01VH (definition-relatively-ample)
(blueprint: lem-trf-scheme-relative-ample-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Relative ampleness of an invertible module survives arbitrary base change.
Restrictions are tensor pullbacks along the indicated open immersions. The existential
invertibility proofs supply the proof argument of absolute `IsAmple`; they introduce no
extra geometric assumption.

Source: Stacks Project, Morphisms, Tag 0893, using Tags 01VH and 01VJ
(blueprint: lem-trf-scheme-relative-ample-base-change).

Proof, following the node's five steps:
1. Absolute ampleness over every affine open implies quasi-compactness of each inverse
image (def-weil-pbc-ample-invertible-module), hence of f
(def-weil-finite-type-morphism).
2. Pullback preserves invertibility (lem-weil-pbc-invertible-pullback-tensor), and base
change preserves quasi-compactness (lem-pc-quasi-compact-base-change).
3. Choose affine neighbourhoods U'_i covering T', each mapping into an affine open U_i
of T (lem-weil-pbc-affine-opens-basis). The fibre-product universal property
(def-pc-fibre-product) identifies the inverse image of U'_i with the base change of
f inverse-image U_i along U'_i to U_i.
4. The latter base map is affine (lem-weil-pbc-morphism-affine-schemes-affine), so its
base change is affine (lem-weil-pbc-affine-morphism-permanence). Affine pullback preserves
ampleness (lem-weil-pbc-pullback-ample-invertible). Functoriality of tensor pullback
(def-pc-module-pullback) identifies this module with the restriction of the pullback L.
5. Apply lem-trf-scheme-relative-ample-affine-cover to f', its pulled-back invertible
module, and this affine cover of T'. Quasi-compactness from step 2 and ampleness from
step 4 give ampleness over every affine open V' of T'. -/
theorem isAmple_on_affineOpens_tensorPullback_baseChange
    {X T T' : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T)
    (L : X.Modules) [L.IsInvertible]
    (hL : ∀ V : T.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj L).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) h) :
    ∀ V' : T'.Opens, IsAffineOpen V' →
      ∃ h : ((tensorPullback ((pullback.snd f g) ⁻¹ᵁ V').ι).obj
          ((tensorPullback (pullback.fst f g)).obj L)).IsInvertible,
        @IsAmple ((pullback.snd f g) ⁻¹ᵁ V').toScheme
          ((tensorPullback ((pullback.snd f g) ⁻¹ᵁ V').ι).obj
            ((tensorPullback (pullback.fst f g)).obj L)) h := by
  sorry

end AlgebraicGeometry.Scheme.Modules

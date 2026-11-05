/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # The additive ideal image is the pushforward of the relative additive kernel.

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-ideal-additive-image-relative-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

-- Affine opens of each etale test scheme suffice: base changes of a closed immersion
-- have surjective maps on global functions when their targets are affine.

-- Restriction agrees with the canonical composition isomorphism of pushforwards.

-- The map from the first kernel to the second is the pullback of the epimorphism f.
-- Its epi-mono factorization therefore exhibits the second kernel as the image.

end AlgebraicGeometry.Scheme

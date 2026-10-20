/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1, Nailin Guan, SHEAF group A3
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-!
# Higher direct images as sheafified cohomology presheaves

Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).
The presheaf is written using derived Hom from the free abelian sheaf of an etale
representable. This is the standard representation of restricted hypercohomology:
Hom(Z[U ×_X Y][0], K[q]) = H^q(U ×_X Y, K|). Its restriction maps are precomposition.
-/

@[expose] public section

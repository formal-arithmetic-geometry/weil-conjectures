/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.RingTheory.LocalRing.ArtinSchreierKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Artin–Schreier exactness for schemes of characteristic p

Source: Stacks Project, Tag 0A3J, opening sequence
(blueprint: lem-sc-artin-schreier-sequence-scheme).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The additive étale structure sheaf occurs as both middle terms of a short exact
Artin–Schreier sequence for every scheme of characteristic `p`.
Source: Stacks Project, Tag 0A3J, opening sequence
(blueprint: lem-sc-artin-schreier-sequence-scheme).

Proof: Identify the pullback of the structure module to an étale `U` with its structure
module, compatibly with restrictions. Thus the displayed sheaf has sections
`ULift Γ(U, ⊤)`. Pulling back `hp` makes `p` vanish in every section ring.
Frobenius minus identity is additive and natural, so defines `wp`. The prime-field
maps `ZMod p → Γ(U, ⊤)` induce `iota` through constant sheafification. Fermat's identity
makes their composite zero. Étale locally a section `a` has a preimage: on an affine
open `Spec A`, adjoin a root of the monic polynomial `T^p - T - a`. This algebra is
finite free of positive rank, hence faithfully flat, and étale since the derivative
is `-1`; its spectra therefore form an étale covering. For the kernel, the factorization
`T^p - T = ∏ c : ZMod p, (T - c)` has pairwise comaximal factors. A root is consequently
locally a prime-field constant, by the idempotent decomposition supplied by these
factors; constants are distinguished on every nonempty pointed neighborhood. This identifies
the kernel sheaf with the constant sheaf, including
on the empty scheme. Local surjectivity of `wp` and this kernel identification give
short exactness. Neither affineness nor a ground field is needed. -/
theorem exists_artinSchreier_shortExact (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) :
    let G := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Modules.etaleTensorSectionsSheaf (Modules.unit X))
    ∃ (iota : X.constantZMod p ⟶ G) (wp : G ⟶ G) (hzero : iota ≫ wp = 0),
      (ShortComplex.mk iota wp hzero).ShortExact := by
  sorry

end AlgebraicGeometry.Scheme

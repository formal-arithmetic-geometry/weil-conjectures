/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFiniteAffineCechBasis
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.EtaleStandardCoverCech
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent

/-! # Čech vanishing for lifted tensor-section sheaves
Source: Stacks Project, Tags 03P2 and 03OZ.
(blueprint: new-etale-affine-tensor-cech-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The lifted tensor-section sheaf has zero positive Čech cohomology on finite affine covers.
Source: Stacks Project, Étale Cohomology Tags 03P2 (affine case) and 03OZ;
faithfully flat Amitsur exactness.
(blueprint: new-etale-affine-tensor-cech-vanishing)

Proof: pull F back to U; it remains quasi-coherent. Pullback composition identifies
its tensor-section presheaf on U with the restriction of the tensor-section
presheaf on X. Replace the finite affine cover by the disjoint union of its
members. Reindex the finite type I by Fin n, so the standard-cover theorem
with a small index type applies. Regard each V i as an étale U-scheme; the
equivalence with the over category over U preserves its finite products.
This disjoint union is affine, étale and surjective over U, so its ring of sections
is faithfully flat over the ring of sections of U. The standard-cover comparison
identifies the family Čech complex with the one-map Čech complex of this cover.
Unique isomorphisms between the chosen product cones identify SiteCechComplex
with Mathlib's cechComplexFunctor, compatibly with projections and face maps.
Affine pullback sections identify the terms with M tensor B tensor ... tensor B,
where M is the section module of the pullback of F to U. Compatibility of the
pullback composition isomorphisms with restrictions identifies the face maps
with the Amitsur maps. Faithfully flat Amitsur exactness kills positive homology.
Finally lift this argument: a lifted cocycle has an underlying cocycle; an
underlying preimage lifts to a preimage of the lifted cocycle. Finite products
of lifted groups identify with lifts of finite products. Thus lifted homology
is zero too. The argument applies to the empty cover of the empty affine scheme,
where the relevant section modules and cohomology groups are zero. -/
theorem isZero_etaleTensorSectionsSheaf_ulift_cech
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (hf : finiteAffineEtaleCechCover X U I V f) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)).homology p) := by
  sorry

end AlgebraicGeometry.Scheme

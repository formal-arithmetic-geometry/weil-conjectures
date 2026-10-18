/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion

/-!
# Flat cokernels from ordinary tensor cohomology on the small etale site

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-tor-cokernel-flat` (blueprint: lem-kun-tor-cokernel-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

set_option synthInstance.maxHeartbeats 100000 in
-- Tensor totalization through ringedSiteModules needs more coproduct-instance search steps.
set_option synthInstance.maxSize 1024 in
/-- The cokernel in degree `a` of a complex of flat constant-coefficient module sheaves
is flat if ordinary tensor with every module sheaf has zero cohomology below `a`.
`mapBifunctor` is direct-sum totalization, and `singleFunctor _ 0` places the test
module sheaf in degree zero. The opcycle is the cokernel of `K.d (a - 1) a`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-tor-cokernel-flat.md`
(blueprint: lem-kun-tor-cokernel-flat).

Proof:
1. Apply the vanishing hypothesis with `n = a - 1`. By
`def-pc-acyclic-complex-modules`, zero cohomology is exactness in that degree.
2. Pass to the small-site representative of the small etale site, as in
`def-weil-size-convention`. The total tensor with a degree-zero sheaf has term
`K.X j` tensor `M` in degree `j`, with differential `d_K` tensor the identity.
The symmetry to `M` tensor `K.X j` has sign `(-1)^(j * 0) = 1`; both composites
with the differentials send `x` tensor `m` to `m` tensor `d_K x`.
Thus the hypothesis gives the universal tensor exactness required by
`lem-weil-pbc-site-flat-opcycles-tor-criterion`, with ring sheaf the constant
sheaf of `Λ`, complex `K`, and degree `a`. All terms are flat by hypothesis.
Its opcycle `K.opcycles a` is precisely the cokernel of the incoming differential,
so that criterion gives the asserted flatness. Transport back from the small-site
representative; equivalences preserve tensor, cohomology, cokernels and exactness.
-/
theorem isFlat_opcycles_of_tensor_cohomology_vanishing
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (K : CochainComplex
      (ringedSiteModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology)
      (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
        (CommRingCat.of Λ)) (K.X i))
    (a : ℤ)
    (hvanish : ∀ M : ringedSiteModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ))),
      ∀ n : ℤ, n < a → IsZero
        ((CochainComplex.mapBifunctor K ((CochainComplex.singleFunctor _ 0).obj M)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory
            ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of Λ))))).homology n)) :
    SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology)
      (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
        (CommRingCat.of Λ)) (K.opcycles a) := by
  sorry

end AlgebraicGeometry.Etale

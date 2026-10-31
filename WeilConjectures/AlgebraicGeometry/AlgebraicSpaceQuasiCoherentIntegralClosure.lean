/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.RingTheory.Smooth.IntegralClosure
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover

/-!
# Quasi-coherent integral closure on an algebraic space

Source: Stacks Project, Morphisms of Spaces, Tag 0820 (lemma-integral-closure),
with uniqueness from affine objects of the small étale site
(blueprint: lem-sfb-space-quasicoherent-integral-closure).

Subalgebras are subobjects in the category of commutative algebra sheaves, so their
inclusions retain the ambient algebra. The affine condition concerns the image of
this inclusion, not an abstract isomorphism with an integral closure.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a unique quasi-coherent subalgebra whose affine étale sections are exactly
those integral over the regular functions, through the given structure map.
Source: Stacks Project, Morphisms of Spaces, Tag 0820 (lemma-integral-closure)
(blueprint: lem-sfb-space-quasicoherent-integral-closure).

Proof:
1. Restrict the algebra to each scheme chart. The cartesian-chart description of
quasi-coherent modules and the scheme Zariski/étale equivalence identify this with a
quasi-coherent Zariski algebra. Apply the scheme integral-closure theorem (Tag 035F)
to its subsheaf of stalkwise integral sections.
2. Every map between étale charts is étale by representable_etale_scheme_tests.
The affine pullback formula and integral-closure étale base change identify the
pullback closure with the next chart's closure. On pure tensors the map into the
ambient algebra is t ⊗ d ↦ t f*(d).
3. These maps agree on overlaps since their composites with the ambient inclusion
agree. They glue to isomorphisms by preservation of quasi-coherence under pullback
and the affine-cover isomorphism criterion. Their identity and cocycle equations
follow from the same pure-tensor formula and injectivity of the inclusions.
4. Descend the resulting cartesian family and its inclusions by the cartesian-chart
equivalence. Covering a chart by affine opens shows that its inclusion is injective.
5. The affine integral closures contain scalars and are closed under ring operations.
These operations glue through the injective inclusion, giving a subalgebra with the
already constructed quasi-coherent underlying module and the stated affine images.
6. For uniqueness, membership in either subsheaf can be checked on an affine open
cover. There it means precisely integrality for both subalgebras. The sheaf axiom
therefore identifies the subsheaves and their inclusions, hence their subobjects. -/
theorem existsUnique_quasiCoherent_integralClosure
    {S : Scheme.{u}} (X : AlgebraicSpace S) (A : X.CommAlgebraSheaf)
    (hA : A.toModule.IsQuasicoherent) :
    ∃! C : Subobject A,
      (C : X.CommAlgebraSheaf).toModule.IsQuasicoherent ∧
        ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
          ∀ a : A.right.obj.obj (op U),
            a ∈ Set.range ((Subobject.arrow C).right.hom.app (op U)) ↔
              (A.hom.hom.app (op U)).hom.IsIntegralElem a := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

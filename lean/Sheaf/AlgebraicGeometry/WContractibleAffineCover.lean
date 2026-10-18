/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Sheaf.RingTheory.IndPrincipalZariski

import Sheaf.RingTheory.StrictWCoverProperties
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.EtaleComparison
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Coverings by w-contractible affines

Source: the Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-thm-pe-weakly-contractible-basis/det-pe-wcb-cover.md`
(blueprint: det-pe-wcb-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every small pro-etale object has a pro-etale covering by spectra of w-contractible
rings, with each covering map factoring through an affine open by a faithfully flat
ind-etale ring map. The isomorphism `e` identifies the covering object with `Spec D`;
`j` identifies `Spec B` with an affine open of the target.

Source: the Weil conjectures blueprint, `det-pe-wcb-cover.md`
(blueprint: det-pe-wcb-cover).

Proof:
1. Index by all affine opens `Spec B` of `U.left`. For each `B`, the strict cover
   `lem-weil-pbc-strict-w-cover` gives a faithfully flat ind-etale algebra `C` that is
   w-local with strictly henselian maximal local rings. Thus it is w-strictly local
   by `det-pe-wlocal-strict-contractible`. Apply `det-pe-wc-cover-second-stage` to a
   Stonean cover of its component space, obtaining a faithfully flat ind-Zariski map
   `C` to a w-contractible ring `D`. By `lem-weil-pbc-ind-etale-stability`, the composite
   `B` to `D` is ind-etale. It is faithfully flat: exactness after tensoring with `D`
   reflects to exactness after tensoring with `C`, and then to exactness over `B`, by
   `def-weil-pbc-faithfully-flat-ring-map`.
2. The map `Spec D` to `Spec B` is weakly etale by
   `det-pe-morphisms-etale-comparison`. The affine open immersion into `U.left` is
   etale by `lem-weil-pbc-open-immersion-etale`, hence weakly etale by the same
   comparison. The map from `U.left` to `X` is weakly etale by
   `def-weil-pbc-proetale-site`. Composition preserves weak etaleness by
   `lem-weil-pbc-weakly-etale-composition-base-change`, so these give objects and
   morphisms of `X.ProEt` with the displayed factorization.
3. For any affine open `V` of `U.left`, choose its own index. Its corresponding
   `Spec D` factors through `V`, so its pullback to `V` is itself and is affine.
   Faithful flatness makes its image all of `V` by
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`. This single affine open
   satisfies the finite refinement condition of `def-weil-pbc-proetale-covering`.
   Consequently the family belongs to `precoverage X U`.
-/
theorem exists_wContractible_affine_cover (X : Scheme.{u}) (U : X.ProEt) :
    ∃ (I : Type u) (W : I → X.ProEt) (f : ∀ i : I, W i ⟶ U),
      Presieve.ofArrows W f ∈ precoverage X U ∧
      ∀ i : I, ∃ (D : CommRingCat.{u}), IsWContractibleRing D ∧
        ∃ (e : Spec D ≅ (W i).left) (B : CommRingCat.{u})
          (φ : B ⟶ D) (j : Spec B ⟶ U.left),
          IsOpenImmersion j ∧ φ.hom.FaithfullyFlat ∧ φ.hom.IndEtale ∧
          e.hom ≫ (f i).left = Spec.map φ ≫ j := by
  sorry

end AlgebraicGeometry.Scheme.ProEt

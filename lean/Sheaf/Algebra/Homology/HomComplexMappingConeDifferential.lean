/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Differential compatibility of the internal Hom mapping-cone comparison

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, the displayed Hom
differential, and Section 08J7, the proof of Lemma 21.35.4.
(blueprint: lem-sc-hom-complex-mapping-cone-differential).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option synthInstance.maxHeartbeats 80000 in
-- Inferring the additive Hom types unfolds the chosen Hom-complex product objects.
-- A higher heartbeat limit is therefore needed.
set_option backward.isDefEq.respectTransparency false in
/-- A degreewise cone comparison with the specified product components is a chain map.
This assertion constructs no degreewise isomorphism.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, the displayed Hom
differential, and Section 08J7, the proof of Lemma 21.35.4.
(blueprint: lem-sc-hom-complex-mapping-cone-differential).

Proof: fix adjacent degrees `n` and `m = n+1`. Postcompose the proposed equality
with each product projection in degree `m`. The projections are jointly monic.
By the assumed component equation, this becomes an equality into the internal Hom
from `E^p` to `G^(p+m+1) ⊞ I^(p+m)`. Postcompose further with internal Hom of
the two cone projections. These are jointly monic: internal Hom preserves this
binary product, as is checked sectionwise on local linear maps. The first projection
of the degreewise comparison is the first cone projection followed by the degree
`n+1` Hom-product projection; the second is the second cone projection followed
by the degree `n` Hom-product projection. Expand the Hom differentials using
`homComplex_projections_exists`, and the cone differential using its two projection
formulas. The first component on either side is
`-d_G a + (-1)^(n+1) a d_E`; the second is
`f a + d_I b - (-1)^n b d_E`. The two expressions agree by
`(-1)^(n+1) = -(-1)^n` and associativity of local linear-map composition.
Composition distributes over addition, subtraction and the sign scalar.
Hence equality holds after both cone projections and all product projections,
which proves the chain-map equation. The argument applies to zero objects,
zero maps, empty sites and unbounded complexes, and requires no exactness of
infinite products. -/
theorem homComplex_mappingCone_differential
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (E G I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (f : G ⟶ I) :
    let π := Classical.choose
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
    let hf := ((homComplexFunctor (R := R)).obj (op E)).map f
    let K := HomologicalComplex.homotopyCofiber hf
    let cf := HomologicalComplex.homotopyCofiber f
    let H := ((homComplexFunctor (R := R)).obj (op E)).obj cf
    ∀ (e : ∀ n : ℤ, K.X n ≅ H.X n),
      (∀ n p : ℤ, (e n).hom ≫ π E cf n p (p + n) rfl =
        (show K.X n ⟶ SheafOfModules.homObj (R := R) (E.X p) (cf.X (p + n)) from
        HomologicalComplex.homotopyCofiber.fstX hf n (n + 1) rfl ≫
          π E G (n + 1) p (p + (n + 1)) rfl ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inlX f (p + (n + 1)) (p + n)
              (by change (p + n) + 1 = p + (n + 1); omega)) +
        HomologicalComplex.homotopyCofiber.sndX hf n ≫ π E I n p (p + n) rfl ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inrX f (p + n)))) →
      ∀ n m : ℤ, n + 1 = m →
        (e n).hom ≫ H.d n m = K.d n m ≫ (e m).hom := by sorry

end CategoryTheory

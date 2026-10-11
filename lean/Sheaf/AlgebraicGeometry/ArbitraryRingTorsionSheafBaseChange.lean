/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf

/-!
# Sheaf-level proper base change for arbitrary coefficient rings

Source: Stacks Project, Etale Cohomology, Lemma 0A4B, proof paragraphs 2–3
(blueprint: lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Lemma 0A4B, proof paragraphs 2–3, with coefficients in `Λ`
(blueprint: lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change).
Coefficient-wise injective acyclicity for `Λ/ℓ` implies derived base change for each
`Λ`-module sheaf whose underlying abelian sheaf is torsion.

Proof:
1. Write the underlying torsion sheaf as the filtered colimit of `F[n]`, by
`lemma-weil-pbc-prime-torsion-devissage`. Properness gives quasi-compactness and
quasi-separatedness after every base change. Higher direct images commute with this
colimit by `lemma-weil-pbc-direct-image-filtered-colimit`, and inverse images do so by
`lem-weil-pbc-inverse-image-preserves-colimits`. Exactness of inverse image identifies
cohomology of exchange with the higher-direct-image exchange maps. Naturality
(`lemma-weil-pbc-derived-exchange-replacement`) makes the exchange for `F` the colimit
of those for `F[n]`. Use `lem-weil-pbc-derived-plus-iso-on-cohomology` to reduce to `F[n]`.
2. For a sheaf killed by `n`, use the sequences `0 → G[ℓ] → G → ℓG → 0`
from `lemma-weil-pbc-prime-torsion-devissage`. Exchange respects the long exact sequences
by `lem-weil-pbc-derived-exchange-triangulated`; the five lemma
(`lem-weil-pbc-five-lemma`, `lemma-weil-pbc-five-lemma-transfer`) and
`lemma-weil-pbc-prime-factor-induction` reduce to a sheaf killed by one prime `ℓ`.
3. Choose an injective resolution in `Λ/ℓ`-module sheaves using
`lem-weil-pbc-module-sheaves-enough-injectives`. The hypothesis gives acyclicity after
pullback; its identity-square case gives acyclicity for `f_*`. Compare this resolution
with the chosen abelian K-injective resolution (`def-weil-pbc-kinjective-resolutions`,
`lem-weil-pbc-kinjective-hom-derived`). By `lem-weil-pbc-derived-exchange-termwise`,
exchange is computed by underived exchange followed by the resolution comparison.
Termwise naturality (`lemma-weil-pbc-underived-exchange-naturality`) and the Leray
criterion (`lemma-weil-pbc-leray-acyclicity`, part 3) make the comparison maps
quasi-isomorphisms. Underived exchange is a termwise isomorphism by
`lemma-weil-pbc-proper-underived-exchange`, since the terms are torsion and `f` is proper.
Thus the derived exchange morphism is an isomorphism. -/
theorem isIso_derivedBaseChangeMapPlus_of_primeQuotient_injective_acyclicity
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hIA : ∀ (ℓ : ℕ), ℓ.Prime →
      ∀ {Y' X' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X},
        IsPullback g' f' f g →
        ∀ (I : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (Λ ⧸ Ideal.span ({(ℓ : Λ)} : Set Λ)))),
          Injective I → ∀ q : ℤ, 0 < q →
            IsZero ((DerivedCategory.Plus.homologyFunctor
              (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
              ((lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                  ((upperStar AddCommGrpCat.{u + 1} g').obj
                    ((sheafCompose X.smallEtaleTopology
                      (forget₂ (ModuleCat.{u + 1}
                        (Λ ⧸ Ideal.span ({(ℓ : Λ)} : Set Λ)))
                        AddCommGrpCat.{u + 1})).obj I))))))
    {Y' X' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsTorsionAbelianSheaf
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F))) := by
  sorry

end AlgebraicGeometry.Etale

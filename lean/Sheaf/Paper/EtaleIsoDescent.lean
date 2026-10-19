/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Isomorphisms descend along étale surjections

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
unit sk-prop-cohsm, lem-pur-etale-iso-descent, order 2336
(blueprint: lem-pur-etale-iso-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Pullback along a surjective étale morphism of separated finite-type k-schemes
reflects isomorphisms between bounded constructible complexes at the fixed finite
coefficient level. The morphism is in the full constructible subcategory; pullback
is evaluated in the ambient derived category, so no preservation hypothesis is needed.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-etale-iso-descent, order 2336 (blueprint: lem-pur-etale-iso-descent).

Proof:
1. The singleton family given by f is an etale cover by surjectivity. Mathlib's
   etalePrecoverage_le_proetalePrecoverage makes it a pro-etale cover.
2. The published upperStarIsoLocalizationRestriction identifies inverse image with
   restriction for the weakly etale map f. The published sheaf-axiom argument
   isIso_of_isIso_localizationRestriction detects isomorphisms on this cover.
3. The actual intrinsic finite-coefficient inverse image is the conjugate of this
   fixed-scalar inverse image by the canonical module realization equivalences.
   Thus it also reflects isomorphisms.
4. The natural mapDerivedCategoryHomologyFunctorIso identifies inverse image of
   every cohomology map with cohomology of derived inverse image. Reflect these
   isomorphisms on module sheaves and apply DerivedCategory.isIso_iff.
5. The inclusion of the full bounded constructible subcategory reflects the
   resulting ambient isomorphism.
-/
theorem isIso_of_surjective_etale_pullback (P : PurityFiniteSetting.{u})
    (U X : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : U ⟶ X) [Surjective f.left] [Etale f.left]
    (M N : (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left).FullSubcategory)
    (φ : M ⟶ N)
    (hφ : IsIso ((@sfIntrinsicDerivedPullback P.Ring _
      (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension
        P.level P.level_pos) U.left X.left f.left).map φ.hom)) :
    IsIso φ := by
  let A := P.Ring
  let : Finite A := Padic.finite_coefficientExtensionRing P.coefficients.l P.extension
    P.level P.level_pos
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have hc : Presieve.ofArrows (fun _ : Unit ↦ U.left) (fun _ ↦ f.left) ∈
      Scheme.proetalePrecoverage X.left := by
    apply Scheme.etalePrecoverage_le_proetalePrecoverage
    apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    obtain ⟨y, hy⟩ := f.left.surjective x
    exact ⟨(), y, hy⟩
  have hF : (ProEtale.upperStar B f.left).ReflectsIsomorphisms := by
    constructor
    intro K L a ha
    apply ProEtale.isIso_of_isIso_localizationRestriction B a
      (fun _ : Unit ↦ f.left) hc
    intro i
    exact (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoLocalizationRestriction B f.left inferInstance) a).mp ha
  have hI : (sfIntrinsicPullback A f.left).ReflectsIsomorphisms := by
    dsimp only [sfIntrinsicPullback, sfIntrinsicTransport]
    infer_instance
  have hD : (sfIntrinsicDerivedPullback A f.left).ReflectsIsomorphisms := by
    constructor
    intro K L a ha
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((sfIntrinsicPullback A f.left).map
        ((DerivedCategory.homologyFunctor _ n).map a)) :=
      (NatIso.isIso_map_iff
        ((sfIntrinsicPullback A f.left).mapDerivedCategoryHomologyFunctorIso n) a).mpr
        (by change IsIso ((DerivedCategory.homologyFunctor _ n).map
              ((sfIntrinsicDerivedPullback A f.left).map a)); infer_instance)
    exact isIso_of_reflects_iso _ (sfIntrinsicPullback A f.left)
  have : IsIso φ.hom := isIso_of_reflects_iso φ.hom (sfIntrinsicDerivedPullback A f.left)
  change IsIso ((intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
    P.level P.level_pos X.left).ι.map φ) at this
  exact isIso_of_reflects_iso φ
    (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left).ι

end WeilConjectures

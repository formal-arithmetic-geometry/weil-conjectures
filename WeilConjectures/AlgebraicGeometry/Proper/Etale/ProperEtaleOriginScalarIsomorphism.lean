/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleOriginScalarData
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarProjectionSquare
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula

/-! # Proper scalar comparison on bounded etale origins

Source: Stacks Project, Tag 0F0G, lemma-projection-formula-proper-mod-n;
Tags 09A6, 0E48 and 0B56 for the canonical comparison and scalar mate.
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism).

## Main definitions and statement

- `properOriginTensorIso`: canonical constant-B tensor comparison.
- `properOriginMateIso`: the specified bounded-below direct-image mate.
- `properOriginEtaleProjection`: the actual etale projection arrow.
- `properEtaleOriginScalarIsomorphism`: invertibility and the restriction formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Etale.scalarTensorIso Scheme.completedAdicDerivedChange

private theorem properOriginEtaleProjection_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (M : Etale.DerivedCategoryModule A Z) :
    IsIso (properOriginEtaleProjection φ p M) := by
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) p).app M).app (Etale.scalarCoefficient φ Y)) :=
    Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
      A isAddTorsion_of_finite p M (Etale.scalarCoefficient φ Y)
  unfold properOriginEtaleProjection
  infer_instance

private theorem scalarMateRestriction_reflectsIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u}) :
    (scalarMateRestriction φ Y).mapDerivedCategory.ReflectsIsomorphisms := by
  let r := scalarMateRestriction φ Y
  have : PreservesFiniteLimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).1
  have : PreservesFiniteColimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.1
  have : r.ReflectsIsomorphisms :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.2
  refine ⟨fun f _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (r.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff (r.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ r

/-- The specified B-linear proper scalar mate is invertible at a bounded-below
etale origin whose tensor with B is also bounded below. The equality is the
precise conjugation formula after the canonical restriction/direct-image
identification. The two b factors are the recorded counit mates at E_e and H_e;
q = properOriginTensorIso is the constant-B tensor comparison expressed through
US = tensor B. No flatness, finite Tor dimension, Noetherian hypothesis or bound
on the tensor of Rp_* E_e is imposed.

Source: Stacks Project, etale-cohomology.tex, Tag 0F0G,
lemma-projection-formula-proper-mod-n; proetale.tex, Tag 09A6;
sites-cohomology.tex, Tags 0E48 and 0B56.
(blueprint: lem-fix-proper-etale-origin-scalar-isomorphism).

Proof:
1. Properness implies quasi-compactness and quasi-separatedness by
pqf-lem-proper-basic. Geometric inverse image preserves the constant module B
by lem-sfb-geometric-inverse-image-constant-module. Thus the two boundedness
hypotheses here are exactly those on K and L in
lem-sfb-projection-comparison-etale-proetale.
2. The additive group of finite A has positive exponent, so A is a torsion ring.
Apply proposition-proper-direct-image-constructible-complexes--9 to E_e and the degree-zero constant
module B_Y. It makes properOriginEtaleProjection invertible; its last factor is just p*B_Y = B_Z.
No flatness or Tor bound is required by that theorem.
3. Specialize lem-sfb-projection-comparison-etale-proetale to these inputs.
The tensor comparisons are those of lem-weil-pbc-ringed-topoi-derived-tensor-pullback;
the two direct-image comparisons are the actual counit mates from
lem-weil-pbc-comparison-direct-image-canonical-mate. Its equation is
R_p(h) b_H F_Y(pi_e) = pi_p (b_E tensor 1) t_Y.
4. Compose with t_Y inverse and b_E inverse tensor 1. This gives the displayed
conjugation formula. Its factors are invertible: the tensor comparisons by
construction, b_E and b_H by the two D+ hypotheses, and pi_e by step 2.
The helpers merely implement coefficient realization and the canonical
US = tensor B identifications; their section and representative normalizations
identify their q factors with these tensor comparisons.
5. lem-fix-proetale-scalar-mate-normalization identifies the restriction of the
actual directImageScalarComparison with this same pi_p, using the canonical
restriction/direct-image comparison scalarMateRestrictionPush. Hence its
restriction equals the displayed composite. Exact coefficient restriction
reflects isomorphisms by lem-weil-pbc-ring-sheaf-change-adjunction, so the
specified B-linear mate itself is invertible. -/
theorem properEtaleOriginScalarIsomorphism
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (E : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hH : ∃ n : ℤ,
      (properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj).IsGE n) :
    IsIso ((directImageScalarComparison φ p).app
      ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ∧
    (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((directImageScalarComparison φ p).app
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ≫
      (scalarMateRestrictionPush φ p).hom.app
        ((directImageScalarExtension φ Z).obj
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) =
    (directImageScalarExtension φ Y ⋙ (scalarMateRestriction φ Y).mapDerivedCategory).map
        (properOriginMateIso A p E).inv ≫
      (properOriginTensorIso φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          E.obj)).inv ≫
      (finiteCoefficientIntrinsicDerivedComparison Y A).map
        (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) ≫
      (properOriginMateIso A p
        ⟨properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj, hH⟩).hom ≫
      (directImageConstantPush A p).map (properOriginTensorIso φ Z E.obj).hom := by
  let U := (scalarMateRestriction φ Y).mapDerivedCategory
  let S := directImageScalarExtension φ Y ⋙ U
  let M := (Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj E.obj
  let e := properOriginMateIso A p E
  let q := properOriginTensorIso φ Y M
  let χ := (directImageScalarComparison φ p).app
    ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)
  let d := (scalarMateRestrictionPush φ p).hom.app
    ((directImageScalarExtension φ Z).obj
      ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj))
  have hs := etaleOriginScalarProjectionSquare φ p E hH
  have heq : U.map χ ≫ d =
      S.map e.inv ≫ q.inv ≫
        (finiteCoefficientIntrinsicDerivedComparison Y A).map
          (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) ≫
        (properOriginMateIso A p
          ⟨properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj, hH⟩).hom ≫
        (directImageConstantPush A p).map (properOriginTensorIso φ Z E.obj).hom := by
    apply (cancel_epi (S.map e.hom)).1
    apply (cancel_epi q.hom).1
    simpa only [Category.assoc, ← S.map_comp_assoc, e.hom_inv_id,
      S.map_id, Category.id_comp, q.hom_inv_id_assoc] using hs
  have : IsIso (properOriginEtaleProjection
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) :=
    properOriginEtaleProjection_isIso _ p E.obj
  have : IsIso (U.map χ ≫ d) := by
    rw [heq]
    infer_instance
  have : IsIso (U.map χ) := IsIso.of_isIso_comp_right _ d
  have : U.ReflectsIsomorphisms := scalarMateRestriction_reflectsIso φ Y
  exact ⟨isIso_of_reflects_iso χ U, heq⟩

end AlgebraicGeometry.ProEtale

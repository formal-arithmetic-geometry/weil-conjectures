/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange
public import Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicity
import WeilConjectures.AlgebraicGeometry.ConstantRingModuleSheafEquivalence
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic

/-!
# Proper base change implies injective acyclicity

Source: Stacks Project, Tag 0A4B, direction (1) implies (2)
(blueprint: lem-weil-pbc-property-implies-acyclicity).
-/

@[expose] public section

universe u_forward

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a proper morphism, base change for torsion abelian sheaves implies injective
acyclicity for every prime. Source: Stacks Project, Tag 0A4B, direction (1) implies (2)
(blueprint: lem-weil-pbc-property-implies-acyclicity).

Fix a prime `r`, a cartesian square, and an injective prime-field module sheaf `I`.
1. Its underlying abelian sheaf is killed by `r`, hence torsion. Apply the specified
exchange isomorphism of `def-weil-pbc-property` to this sheaf in degree zero.
2. By `lem-weil-pbc-injective-module-direct-image-acyclic`, its positive higher direct
images along `f` vanish; degree zero is the ordinary direct image, by
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
3. Inverse image is exact (`prop-weil-pbc-inverse-image-exact`), is computed termwise
on the derived category (`def-weil-pbc-derived-inverse-image`), and commutes with
cohomology (`lem-weil-pbc-exact-functor-complex-cohomology`). Thus the source of the
exchange map has zero cohomology in every positive degree.
4. Apply cohomology to the exchange isomorphism. Its target has the same vanishing;
termwise inverse image takes `I[0]` to the pullback sheaf in degree zero, so this is
exactly the higher direct image required by `def-weil-pbc-direct-image`.
5. The square, injective sheaf, and prime were arbitrary, proving every `IA_r(f)` of
`def-weil-pbc-injective-acyclicity-property`. -/
theorem hasAllPrimeInjectiveAcyclicity_of_hasTorsionAbelianBaseChange
    {X Y : Scheme.{u_forward}} (f : X ⟶ Y) [IsProper f]
    (hf : HasTorsionAbelianBaseChange f) : HasAllPrimeAbelianInjectiveAcyclicity f := by
  intro r hr Y' X' g f' g' sq I hI q hq
  let : Fact r.Prime := ⟨hr⟩
  let : Injective I := hI
  lift q to ℕ using hq.le
  have hn : 0 < q := by exact_mod_cast hq
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u_forward + 1} (ULift.{u_forward + 1} (ZMod r)))
      AddCommGrpCat.{u_forward + 1})).obj I
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u_forward + 1}) 0).obj F
  have hF : Scheme.IsTorsionAbelianSheaf F :=
    (Scheme.isTorsionAbelianSheaf_characterizations F).1.mpr
      ((Scheme.isTorsionModuleSheaf_iff_isTorsion I).mp inferInstance)
  have : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u_forward + 1}
      sq.toCommSq).app K) := hf sq F hF
  obtain ⟨E, ⟨e⟩⟩ := constantRing_moduleSheaf_equivalence X r
  let J := E.functor.obj I
  have : Injective J := (E.map_injective_iff I).2 hI
  have hJ := isZero_higherDirectImage_of_injective_module f
    (ULift.{u_forward} (ZMod r)) J q hn
  have hsource : CategoryTheory.Limits.IsZero
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar AddCommGrpCat.{u_forward + 1} f).rightDerivedFunctorPlus.obj K)) :=
    hJ.of_iso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      ((lowerStar AddCommGrpCat.{u_forward + 1} f).rightDerivedFunctorPlus.mapIso
        ((DerivedCategory.Plus.singleFunctor _ 0).mapIso (e.app I))))
  have hpull : CategoryTheory.Limits.IsZero
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((upperStar AddCommGrpCat.{u_forward + 1} g).mapDerivedCategoryPlus.obj
          ((lowerStar AddCommGrpCat.{u_forward + 1} f).rightDerivedFunctorPlus.obj K))) :=
    ((upperStar AddCommGrpCat.{u_forward + 1} g).map_isZero hsource).of_iso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{u_forward + 1} g) (q : ℤ)).app _).symm
  refine (hpull.of_iso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
    (asIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u_forward + 1}
      sq.toCommSq).app K))).symm).of_iso ?_
  exact ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
    ((lowerStar AddCommGrpCat.{u_forward + 1} f').rightDerivedFunctorPlus.mapIso
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (upperStar AddCommGrpCat.{u_forward + 1} g') 0).app F))).symm

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!
# Étale localization of the exceptional inverse image

For an étale morphism `u : U ⟶ X` and `f : X ⟶ Y` admitting compactifications, the exceptional
inverse image localizes along `u`: `Lu^* Rf^! ≅ R(u ≫ f)^!`
(`lemma-affine-space-etale-localization`).

The extension by zero `u_!` is left adjoint to `u^*`, and its derived functor `De_!` agrees with
the derived lower shriek `Ru_!` (`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`).
So `Ru_! ⊣ Lu^*`, and composing with `Rf_! ⊣ Rf^!` and `R(u ≫ f)_! ≅ Ru_! ⋙ Rf_!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) gives the isomorphism by
uniqueness of right adjoints.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`:
  the localization isomorphism exists;
- `AlgebraicGeometry.Etale.etaleAmbientAdjointLocalityIso`: on Noetherian schemes, the localization
  isomorphism normalized by its compatibility with the counits of the two exceptional adjunctions,
  the unique such isomorphism
  (`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lemma-affine-space-etale-localization`: Étale localization of the ambient adjoint.

For a separated étale morphism `u : U ⟶ X` of finite type, and `f : X ⟶ Y` such that `f` and
`h = u ≫ f` admit compactifications, the exceptional inverse image localizes along `u`:

`Lu^* Rf^! K ≅ R(u ≫ f)^! K`,

naturally in `K`. The blueprint also records that the extension by zero `u_!` along `u` is
exact and left adjoint to `u^*`. The isomorphism is the uniqueness of right adjoints for
`R(u ≫ f)_! ≅ Ru_! ⋙ Rf_! ⊣ Rf^! ⋙ Lu^*`, where `Ru_! ⊣ Lu^*` is the adjunction
`De_! ⊣ Le^*` of the extension by zero `u_!`, transported along the comparison isomorphism
`De_! ≅ Ru_!` (`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`); only its
existence is recorded.

The normalized form of the isomorphism, on Noetherian schemes, is
`AlgebraicGeometry.Etale.etaleAmbientAdjointLocalityIso`. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale
    {U X Y : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (f : X ⟶ Y) (h : U ⟶ Y) (w : u ≫ f = h) [HasCompactification f]
    [HasCompactification h] :
    Nonempty (R(f)^![Λ] ⋙ L((u)^*[ModuleCat.{u + 1} Λ]) ≅
      R(h)^![Λ]) := by
  subst h
  let c := HasCompactification.compactification (u ≫ f)
  let a : U ⟶ pullback c.g f := pullback.lift c.i u c.comm.symm
  have : IsImmersion (a ≫ pullback.fst c.g f) := by
    change IsImmersion ((pullback.lift c.i u c.comm.symm) ≫ pullback.fst c.g f)
    rw [pullback.lift_fst]
    infer_instance
  have : IsImmersion a := IsImmersion.of_comp a (pullback.fst c.g f)
  have : HasCompactification u :=
    HasCompactification.of_isImmersion a (pullback.snd c.g f) (pullback.lift_snd _ _ _)
  let cu := HasCompactification.compactification u
  have := isIso_compactificationEtaleComparison Λ u cu
  let e : R(u)_![ModuleCat.{u + 1} Λ] ≅
      (etaleLowerShriek (ModuleCat.{u + 1} Λ) u inferInstance).mapDerivedCategory :=
    (asIso (compactificationEtaleComparison Λ u cu)).symm
  let adj :=
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) u
      inferInstance).mapDerivedCategoryAdjunction).ofNatIsoLeft e.symm
  obtain ⟨ec⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ u f
  exact ⟨Functor.isoWhiskerLeft _
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) u) ≪≫
      (adj.comp (rightDerivedUpperShriekAdjunction Λ f)).rightAdjointUniq
        ((rightDerivedUpperShriekAdjunction Λ (u ≫ f)).ofNatIsoLeft ec)⟩

section Normalized

variable (A : Type (u + 1)) [CommRing A] [Finite A] {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
  [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
  [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
  (c : Compactification f) (d : Compactification (u ≫ f))
  {F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
  {G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U}
  (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
  (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G)

/-- Blueprint `lemma-affine-space-etale-localization`, the normalized localization isomorphism:
for right adjoints `F` of `Rf_!` and `G` of `R(u ≫ f)_!` (given by compactifications `c`, `d`),
the isomorphism `F ⋙ u^* ≅ G` characterized by its compatibility with the two counits
(`etaleAmbientAdjointLocalityIso_spec`); it is the unique such isomorphism
(`etaleAmbientAdjointLocalityIso_unique`, from
`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`). -/
noncomputable def etaleAmbientAdjointLocalityIso :
    F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G :=
  (existsUnique_etaleAmbientAdjointLocalityIso A u f c d F G adjF adjG).exists.choose

/-- The normalized localization isomorphism is compatible with the counits: `R(u ≫ f)_!` applied
to its component at `K`, followed by the counit of `adjG`, is the comparison
`R(u ≫ f)_! u^* ≅ Rf_! u_! u^*`, the counit of `u_! ⊣ u^*` and the counit of `adjF`. -/
theorem etaleAmbientAdjointLocalityIso_spec (N : EtaleCompactSupportNormalization A)
    (K : DerivedCategoryModule A S) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((etaleAmbientAdjointLocalityIso A u f c d adjF adjG).hom.app K) ≫ adjG.counit.app K =
      (etaleAmbientLeftComparison A N u f c d).inv.app
          ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj K)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u inferInstance).counit.app (F.obj K)) ≫
        adjF.counit.app K :=
  (existsUnique_etaleAmbientAdjointLocalityIso A u f c d F G adjF adjG).exists.choose_spec N K

/-- Any isomorphism `F ⋙ u^* ≅ G` compatible with the counits is the normalized localization
isomorphism. -/
theorem etaleAmbientAdjointLocalityIso_unique
    (e : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G)
    (he : ∀ (N : EtaleCompactSupportNormalization A) (K : DerivedCategoryModule A S),
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          (e.hom.app K) ≫ adjG.counit.app K =
        (etaleAmbientLeftComparison A N u f c d).inv.app
            ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj K)) ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
            ((derivedEtaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) u inferInstance).counit.app (F.obj K)) ≫
          adjF.counit.app K) :
    e = etaleAmbientAdjointLocalityIso A u f c d adjF adjG :=
  (existsUnique_etaleAmbientAdjointLocalityIso A u f c d F G adjF adjG).unique he
    (etaleAmbientAdjointLocalityIso_spec A u f c d adjF adjG)

end Normalized

end Etale

end AlgebraicGeometry

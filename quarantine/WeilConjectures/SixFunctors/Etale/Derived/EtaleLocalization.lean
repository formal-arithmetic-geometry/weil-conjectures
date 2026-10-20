/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-!
# Étale localization of the derived categories of étale sheaves

Two facts about a surjective or arbitrary étale morphism `u : U ⟶ X` and the derived categories
`D(X_ét, Λ)`:

* isomorphisms descend along surjective étale morphisms: a morphism `φ` of `D(X_ét, Λ)` with
  `Lu^* φ` invertible is invertible (blueprint `lem-pur-etale-iso-descent`). Pullback along `u`
  is exact, so it commutes with the cohomology sheaves, and the pullbacks along the members of a
  jointly surjective family of étale maps reflect isomorphisms of sheaves;
* the exceptional inverse image localizes along étale maps,
  `Lu^* Rf^! ≅ R(u ≫ f)^!` (blueprint `lem-amb-etale-adjoint-locality`, a node of the blueprint
  subsection `sk-prop-sf-cbc`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-pur-etale-iso-descent`: Isomorphisms descend along étale surjections.

Let `u : U ⟶ X` be a surjective étale morphism and `φ : M ⟶ N` a morphism of `D(X_ét, Λ)`. If
`Lu^* φ` is an isomorphism, then so is `φ`. It suffices that the cohomology sheaves `ℋʳ(φ)` are
isomorphisms; as `u^*` is exact, `u^* ℋʳ(φ) ≅ ℋʳ(Lu^* φ)` is an isomorphism, and since `u` is
surjective every geometric point of `X` lifts to `U`, where the stalks of `u^* ℋʳ(φ)` are those
of `ℋʳ(φ)` (`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`).

The blueprint states this for bounded constructible complexes on separated schemes of finite
type over a field; neither hypothesis is needed. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_surjective {U X : Scheme.{u}} (u : U ⟶ X)
    [Etale u] [Surjective u]
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : IsIso ((L((u)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  have h' : IsIso (D((u)^*[ModuleCat.{u + 1} Λ]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ u) φ).1 h
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun _ : PUnit.{u + 1} ↦ u) (fun x ↦ ⟨⟨⟩, u.surjective x⟩) _ fun _ ↦ ?_
  exact (NatIso.isIso_map_iff
    (((u)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((u)^*[ModuleCat.{u + 1} Λ]).map φ))



variable [Finite Λ]

/-- Blueprint `lem-amb-etale-adjoint-locality`: Étale localization of the ambient adjoint.

For a separated étale morphism `u : U ⟶ X` of finite type, and `f : X ⟶ Y` such that `f` and
`h = u ≫ f` admit compactifications, the exceptional inverse image localizes along `u`:

`Lu^* Rf^! K ≅ R(u ≫ f)^! K`,

naturally in `K`. The blueprint also records that the extension by zero `u_!` along `u` is
exact and left adjoint to `u^*`; the graph comparison identifies its degreewise derived
functor with compact-support pushforward. The canonical isomorphism is the mate of the
composition `R(u ≫ f)_! ≅ Rf_! ⋙ Ru_!` with `Ru_! ⊣ Lu^*`; only its existence is recorded.

This is a node of the blueprint subsection `sk-prop-sf-cbc`.
(blueprint: lem-etale-exceptional-locality-arbitrary-schemes)

Proof: construct a compactification of `u` by its graph in the proper base change of a
compactification of `u ≫ f`. The graph comparison identifies `Ru_!` with exact sum extension.
Compose its adjunction with the exceptional adjunction for `f`, use compact-support
composition, and apply uniqueness of right adjoints. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale
    {U X Y : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (f : X ⟶ Y) (h : U ⟶ Y) (w : u ≫ f = h) [HasCompactification f]
    [HasCompactification h] :
    Nonempty (R(f)^![ModuleCat.{u + 1} Λ] ⋙ L((u)^*[ModuleCat.{u + 1} Λ]) ≅
      R(h)^![ModuleCat.{u + 1} Λ]) := by
  subst h
  -- Compactify u without requiring f or its composite to be quasi-compact.
  let c := HasCompactification.compactification (u ≫ f)
  let a : U ⟶ pullback c.g f := pullback.lift c.i u c.comm.symm
  have ha : a ≫ pullback.fst c.g f = c.i := pullback.lift_fst _ _ _
  have : IsImmersion a := by
    have : IsImmersion (a ≫ pullback.fst c.g f) := by rw [ha]; infer_instance
    exact IsImmersion.of_comp a (pullback.fst c.g f)
  have : HasCompactification u := HasCompactification.of_isImmersion a
    (pullback.snd c.g f) (pullback.lift_snd _ _ _)
  let e := canonicalEtaleCompactSupportComparison Λ u
    (HasCompactification.compactification u)
  let adjU := (derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) u inferInstance).ofNatIsoLeft e.symm
  obtain ⟨ecomp⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ u f
  exact ⟨Functor.isoWhiskerLeft R(f)^![ModuleCat.{u + 1} Λ]
      (leftDerivedUpperStarIsoMapDerivedCategory _ u) ≪≫
    Adjunction.rightAdjointUniq
      ((adjU.comp (rightDerivedUpperShriekAdjunction _ f)).ofNatIsoLeft ecomp.symm)
      (rightDerivedUpperShriekAdjunction _ (u ≫ f))⟩

end Etale

end AlgebraicGeometry

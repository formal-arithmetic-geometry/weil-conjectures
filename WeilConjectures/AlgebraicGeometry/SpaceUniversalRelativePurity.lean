/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.RelativeAssassin
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Universal relative purity of modules on algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 0CV8 and 0CVD(2),(4);
Divisors on Spaces, Tag 0CV0 and lemma-relative-assassin
(blueprint: def-sfb-space-universal-relative-purity).

The relative assassin is the union of the scheme relative assassins on all
representable étale charts. An impurity is an associated point with no specialization
above a specified specialization of its image. Universal relative purity excludes
such impurities after every scheme base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative assassin on a space over a scheme, computed on all representable
étale scheme charts. Scheme modules are obtained by the canonical restriction to
Zariski opens, and scheme association is fibrewise association of stalk modules.
For finite type quasi-separated morphisms the chart fibres are locally Noetherian,
so the assassin agrees with the weak assassin in Tag 0CV0.
Source: Stacks, Divisors on Spaces, Tag 0CV0 and lemma-relative-assassin (3),(4)
(blueprint: def-sfb-space-universal-relative-purity). -/
def relativeAssassin {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : Over S) (f : X ⟶ schemeSpace Y) (M : X.Modules) : Set (Point X.obj.obj) :=
  {ξ | ∃ (T : X.EtaleSite) (t : X.etaleForget.obj T),
    t ∈ Scheme.Modules.relativeAssassin
      (yoneda.preimage (T.obj.hom ≫ f.hom.hom)).left ((X.schemeRestriction T).obj M) ∧
        schemePointMap T.obj.hom t = ξ}

/-- An impurity for the displayed space over a scheme: an associated point over `b'`
has no specialization over `b`, although `b'` specializes to `b`.
The equalities use the canonical scheme point classes, not an arbitrary point map.
Applied after a scheme base change this is the impurity of Tag 0CV8.
Source: Stacks, Morphisms of Spaces, Tag 0CV8, definition-impurity
(blueprint: def-sfb-space-universal-relative-purity). -/
def IsImpurityOverScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : Over S) (f : X ⟶ schemeSpace Y) (M : X.Modules)
    (b' b : Y.left) (ξ : Point X.obj.obj) : Prop :=
  b ∈ closure ({b'} : Set Y.left) ∧ ξ ∈ relativeAssassin Y f M ∧
    mapPoint f.hom.hom ξ = schemePointMap (𝟙 (yoneda.obj Y)) b' ∧
      ¬ ∃ θ : Point X.obj.obj, θ ∈ closure ({ξ} : Set (Point X.obj.obj)) ∧
        mapPoint f.hom.hom θ = schemePointMap (𝟙 (yoneda.obj Y)) b

/-- A finite type quasi-coherent module is universally pure relative to the scheme
base if every fibrewise associated point, after every scheme base change, specializes
above each specialization of its image. The morphism is finite type with quasi-compact
diagonal. The ambient base is Spec ℤ, lifted to the chosen scheme universe.
Source: Stacks, Morphisms of Spaces, Tags 0CV8 and 0CVD(2),(4)
(blueprint: def-sfb-space-universal-relative-purity). -/
def IsUniversallyPureRelativeToScheme
    {X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (f : X ⟶ schemeSpace Y)
    (_hf : MapIsFiniteType f) (_hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (M : X.QCoh) (_hM : SheafOfModules.IsFiniteType M.obj) : Prop :=
  ∀ (B : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (g : B ⟶ Y),
    let gSpace : schemeSpace B ⟶ schemeSpace Y := ObjectProperty.homMk ⟨yoneda.map g⟩
    let XB := enlargedFibreProduct f gSpace
    let fB : XB ⟶ schemeSpace B :=
      ObjectProperty.homMk (Limits.pullback.snd f.hom gSpace.hom)
    let MB := (moduleTensorPullback (enlargedFibreProductFst f gSpace)).obj M.obj
    ∀ (b' b : B.left) (ξ : Point XB.obj.obj), b ∈ closure ({b'} : Set B.left) →
      ξ ∈ relativeAssassin B fB MB →
        mapPoint fB.hom.hom ξ = schemePointMap (𝟙 (yoneda.obj B)) b' →
          ∃ θ : Point XB.obj.obj, θ ∈ closure ({ξ} : Set (Point XB.obj.obj)) ∧
            mapPoint fB.hom.hom θ = schemePointMap (𝟙 (yoneda.obj B)) b

end AlgebraicGeometry.AlgebraicSpace

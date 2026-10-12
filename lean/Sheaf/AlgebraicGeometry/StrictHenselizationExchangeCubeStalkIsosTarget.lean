/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.AlgebraicGeometry.AbelianExchangeCubeComparisons
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.GeometricPointFieldExtension

/-! # Invertibility of the canonical strict-local stalk comparisons

Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-target).
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- The fixed target cube restriction map is invertible on the indicated closed-point
stalk. This says nothing about either exchange map or compatibility with exchange.
Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images, and Tag 03QO,
lemma-cohomology-strictly-henselian.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-target).

Proof:
1. Enlarge τ along ν. Étale stalks are unchanged under extensions of separably
closed fields, including inseparable extensions, by the bijection on pointed étale lifts.
2. The cartesian square sq makes f' quasi-compact and quasi-separated by base change.
Exact inverse image identifies D+(g'^*)G[0] with (g'^*G)[0].
3. Apply unrestricted 03Q9 to f' at ντ with coefficient g'^*G. Transport its chosen
cartesian model to X₁ using sqB and eB. The equation hb, inverse-image composition,
and the single-complex isomorphism identify the pulled-back coefficient with
p₁^*p₀^*G. No source comparison or invertibility of exchange for g is used.
4. Use exact global sections on the strict local base and the sections-to-closed-point
stalk isomorphism (03QO) to express this restriction on higher-direct-image stalks.
The residue equations identify the specified geometric points. The inverse-image germ
formula and the section-restriction components of 03Q9 identify the composite with the
fixed derivedStalkComparison in the conclusion; all remaining factors are images of
composition, single-complex, or exact-pullback isomorphisms. Hence it is invertible.
For q = 0 this is the usual section restriction; the argument also handles zero sheaves,
empty total spaces, and arbitrary chosen cartesian models. -/
theorem Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_target
    {S T X X' : Scheme.{u}} {g : T ⟶ S} {f : X ⟶ S}
    [QuasiCompact f] [QuasiSeparated f] {f' : X' ⟶ T} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    {X₀ X₁ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))
    (p₁ : X₁ ⟶ X₀) (f₁ : X₁ ⟶ Spec (.of B))
    (sq₁ : IsPullback p₁ f₁ f₀ (Spec.map (CommRingCat.ofHom φ)))
    (b : X₁ ⟶ X')
    (sqB : IsPullback b f₁ f'
      (eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ)))
    (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let jA := eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)
    let jB := eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ)
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let ht : t ≫ jB = τ := by simpa only [t, jB, Category.assoc] using hρB
    let h : jB ≫ g = g₀ ≫ jA := by simpa only [jB, g₀, jA, Category.assoc] using hφ.symm
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
    let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
    let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
    let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
    IsIso (derivedStalkComparison jB t τ ht M₂ N₂
      (exchangeCubeTargetComparison sqB.toCommSq hb G) (q : ℤ)) := by sorry

end AlgebraicGeometry

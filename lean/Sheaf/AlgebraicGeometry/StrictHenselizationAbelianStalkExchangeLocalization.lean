/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Localization of an abelian stalk exchange to strict henselian bases

Source: Stacks Project, Tag 03Q9 (restriction complexes), Tag 03QO (closed-point germs),
and the total-space restriction portion of Tag 095T.
(blueprint: lem-weil-pbc-abelian-stalk-exchange-localization).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- Restriction to compatible strict henselizations conjugates the original exchange
on abelian stalks to the exchange on the strict local bases. Both sides are stalks;
this statement makes no identification with Ext cohomology and claims no invertibility
of either exchange. The morphism f need only be quasi-compact and quasi-separated.

Source: Stacks Project, Tag 03Q9, proof of theorem-higher-direct-images, restriction
complexes; Tag 03QO, exactness of closed-point germs; Tag 095T, final stalk calculation.
(blueprint: lem-weil-pbc-abelian-stalk-exchange-localization).

Proof:
1. Enlarge the separably closed point fields along ν and ν ≫ ι. Lifts to an etale
neighbourhood are unchanged: its fibre is a disjoint union of spectra of finite
separable field extensions, and these extensions of k or k' are already trivial.
Precomposition therefore gives isomorphisms of the point fibre functors, natural in
sheaves. Commute exact inverse image with homology and apply the inverse-image stalk
comparison to identify the source with the direct-image stalk at σ.
2. Apply the unrestricted 03Q9 restriction to f at ν ≫ ι ≫ σ and to f' at ν ≫ τ.
The second morphism is qcqs by base change. Transport the first total space to X₀
using sq₀ and eA. The square sq₁ and the equation hφ identify X₁ with the base change
of X' to Spec B: paste sq₁ and sq₀, then cancel the original pullback sq.
The inverse-image composition isomorphisms identify the resulting coefficients with
p₀^*G and p₁^*p₀^*G, including the degree-zero derived single-complex comparisons.
3. The closed-point germ on either strict local base is an exact isomorphism by
03QO. Locality of φ and hρ identify the image of the closed B-point with the closed
A-point; hρA and hρB identify its reparametrizations with σ and τ. The Leray comparison
and exactness of closed-point sections now identify the two total-space homologies
in step 2 with the two local higher-direct-image stalks in the conclusion. Compose
these isomorphisms with step 1 and take the underlying additive equivalences.
4. Resolve G by a bounded below injective abelian complex I and replace g'^*I by a
K-injective complex J. The termwise exchange is pullback of sections followed by
I -> J. At each pointed affine neighbourhood, restriction before or after this map
agrees: the structural square hφ and the residue square hρ give the same pointed
etale lift, and strict henselian pointed-lift uniqueness identifies the two lifts.
Thus the section-complex square commutes. Filtered colimits are exact, so passing
to homology gives the displayed equation. Conjugation by the unique pullback
isomorphisms used in step 2 preserves this equation by naturality of the mate.
The argument works in degree zero, for the zero sheaf, for inseparable field
extensions, and for nonstandard pullback models; no torsion is used. -/
theorem Etale.exists_addEquiv_strictHenselization_abelian_stalkExchange
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
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let G₀ := (p₀)^*[AddCommGrpCat.{u + 1}].obj G
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj G₀
    let C₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let C₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let L₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀)
    let L₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    let e₀ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁.toCommSq).app K₀)
    let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    ∃ (c₁ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₁ ≃+
        (t₀.sheafFiber (A := AddCommGrpCat.{u + 1})).obj L₁)
      (c₂ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₂ ≃+
        (t₀.sheafFiber (A := AddCommGrpCat.{u + 1})).obj L₂),
      ∀ x, c₂ ((((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        ((t₀.sheafFiber (A := AddCommGrpCat.{u + 1})).map e₀).hom (c₁ x) := by sorry

end AlgebraicGeometry

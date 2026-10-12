/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.Paper.StrictHenselizationFunctoriality

/-! # Original abelian stalk exchange on total strict-local projective lines

Source: Stacks Project, Tag 03Q9 and the stalk calculation in Tag 095T.
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- The geometric part of the original-stalk calculation, with abelian coefficients.
No module resolution, comparison of coefficient categories, or closed fibre is involved.

Source: Stacks Project, Tag 03Q9 and the final stalk calculation of Tag 095T.
(blueprint: lem-weil-pbc-p1-abelian-original-stalk-total-exchange).

Proof:
1. The projective-line projection is proper, hence qcqs; its base change f' is qcqs.
The inverse-image stalk comparison identifies the source stalk with the stalk at σ.
Extension from the separably closed fields k and k' to Ω induces equivalences of the
pointed neighbourhood systems: finite separable residue extensions already split.
2. The unrestricted abelian strict-henselization stalk formula (03Q9) identifies these
higher-direct-image stalks with cohomology over S_(νισ) and T_(ντ). Transport along eA
and eB and the unique isomorphisms of pullback squares identifies their total spaces
with P¹_A and P¹_B. Inverse images compose, so the coefficients become G₀ and φ^*G₀.
3. Resolve G by a bounded below injective abelian complex I, and replace g'^*I by a
K-injective complex J. The termwise mate is pullback of sections along the base-changed
projection followed by I -> J. In every pointed neighbourhood its restriction to the
total strict-local space commutes with Spec φ: the structural square and residue square
specify the same pointed étale lift, which is unique over a strict henselian local ring.
Thus the two section-complex maps agree. Exact filtered colimits commute with homology,
so the equality holds in degree q. The restriction-complex maps induce the same Ext
pullback as cohomologyMap by the derived adjunction and constant-sheaf comparison.
4. For a nonstandard pullback X', conjugate the calculation by the unique pullback
isomorphism. All comparisons are natural, so the equality persists. The argument uses
03Q9 for arbitrary abelian sheaves and therefore requires no torsion assumption. It
also applies to q = 0, the zero sheaf, and purely inseparable extensions.
-/
theorem Etale.projectiveLine_abelian_originalStalk_totalExchange
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
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
    (G : Sheaf (ProjectiveLine S).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let G₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[
      AddCommGrpCat.{u + 1}].obj G
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let C₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((ProjectiveLine S ↘ S)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let C₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₁ ≃+ Sheaf.H G₀ q)
      (a₂ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₂ ≃+
        Sheaf.H ((ProjectiveSpace.map _ g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (a₁ x) := by sorry

end AlgebraicGeometry

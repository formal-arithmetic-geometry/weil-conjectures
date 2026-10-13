/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem

/-! # The differential identity for signed localized Koszul evaluation

Source: Stacks Project, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
The degree maps are constructed using the inverse of scalar multiplication on principal
opens. Only their compatibility with adjacent differentials remains to be proved.
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A]
variable (S : SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) (s : A)

/-- Inverse to multiplication by s^e on sections over D(s).
Source: Stacks, Tag 08D0 (blueprint: lem-sc-koszul-cech-localized-differential).
The inverse is constructed from Mathlib's proved invertibility of s on D(s). -/
noncomputable def koszulCechScalarDivision (e : ℕ) :
    ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) ≃ₗ[A]
      ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) := by
  let N := (affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S
  have hu : IsUnit (algebraMap A (Module.End A (↑N)) s) :=
    Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := S) s le_rfl
  exact (LinearEquiv.ofBijective (algebraMap A (Module.End A (↑N)) (s ^ e))
    ((Module.End.isUnit_iff _).mp (by simpa only [map_pow] using hu.pow e))).symm

variable (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Signed restriction of evaluation followed by division by the principal product.
Source: Stacks, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
The parameter B supplies the vectors to evaluate on, independently of total degree.
Linearity follows from linearity of cochains, restrictions and scalar division. -/
noncomputable def koszulCechLocalizedDegreeMap (e : ℕ) (n : ℤ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ))) :
    ModuleCat.of A (CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n) ⟶
        principalCechTerms r f F n :=
  ModuleCat.ofHom
    { toFun := fun z J ↦
        (Int.negOnePow
          ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
          koszulCechScalarDivision A (F.X (n + 1 - (J.val.card : ℤ))) (∏ j ∈ J.val, f j) (e + 1)
            ((modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
              (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
              ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ)) (by ring)) (B J)))
      map_add' := by
        intro z z'
        funext J
        simp only [CochainComplex.HomComplex.Cochain.add_v, ModuleCat.hom_add,
          LinearMap.add_apply,
          map_add, smul_add, Pi.add_apply]
      map_smul' := by
        intro a z
        funext J
        simp only [CochainComplex.HomComplex.Cochain.smul_v, ModuleCat.hom_smul,
          LinearMap.smul_apply,
          map_smul, Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }

/-- The explicit localized degree maps commute with adjacent differentials when B
is the ordered exterior basis transported into the extended Koszul tail.
Source: Stacks Project, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
Proof: In degree n and at a nonempty subset J, put p=card(J)-1 and q=n-p.
The Hom differential is postcomposition by d_F plus (-1)^n precomposition by the
positive Koszul boundary, since the tail uses the negative boundary. On the ordered
wedge, that boundary is the sum over deleting a generator, with coefficient
(-1)^position f_j^(e+1). After restriction to D(product f_j), division by the full
product to power e+1 cancels f_j^(e+1) and leaves the denominator of J.erase j.
Restrictions compose and commute with d_F; inverses to scalar multiplication
commute with these A-linear maps. The singleton case has no incoming horizontal
term, since the tail has no augmentation term in positive cohomological degree.
For S(p,n)=p*(n-p)+p*(p-1)/2, one has S(p,n+1)=S(p,n)+p, and
S(p,n+1)+n-S(p-1,n) is even. These identities give the vertical sign (-1)^p and
the horizontal alternating signs of principalCechDifferentialValue, respectively.
Use the increasing enumeration of J to match the deletion positions with the
number of elements less than j, and use the increasing enumeration of J.erase j
for the remaining ordered wedge. Equality of all subset components proves the
linear-map identity. No quasi-coherence is used. For r=0 there are no components;
if a product is zero or nilpotent, its principal open is empty and sections are zero. -/
theorem koszulCechLocalizedDegreeMap_comm (e : ℕ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ)))
    (hB : ∀ J, B J =
      ((koszulOpenTail A r f e).extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f (J.val.card - 1) =
          1 - (J.val.card : ℤ) by
          simp only [ComplexShape.embeddingDownNat_f]
          have h : 0 < J.val.card := Finset.card_pos.mpr J.property
          omega)).inv
        (exteriorPower.ιMulti A (J.val.card - 1 + 1)
          (fun i ↦ Finsupp.single (J.val.orderEmbOfFin
            (show J.val.card = J.val.card - 1 + 1 by
              have h : 0 < J.val.card := Finset.card_pos.mpr J.property
              omega) i) (1 : A)))) (n : ℤ) :
    (CochainComplex.moduleHomComplex
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).d
        n (n + 1) ≫ koszulCechLocalizedDegreeMap A r f F e (n + 1) B =
      koszulCechLocalizedDegreeMap A r f F e n B ≫ (principalCechTotal r f F).d
        n (n + 1) := by sorry

end AlgebraicGeometry

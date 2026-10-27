/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Nilpotent.Basic
import Sheaf.AlgebraicGeometry.NilpotentTowerMonomorphismRigidity

/-! # Effectivity of flat inverse systems with proper support

Source: Stacks Project, spaces-flat.tex, Tags 0CX4 and 0CXB
(blueprint: lem-sfb-space-flat-proper-support-inverse-effectivity).

Index n represents A_{n+1}. Fibres and their maps are the existing sheaf fibre products;
the conclusion retains compatibility with every supplied transition isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The spectrum of the actual inverse limit, as the representable base space.
Source: Stacks 0CX4
(blueprint: lem-sfb-space-flat-proper-support-inverse-effectivity). -/
abbrev inverseEffectivityBase (D : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    AlgebraicSpace (Spec (limit D)) :=
  schemeSpace (Over.mk (𝟙 (Spec (limit D))))

/-- The canonical test Spec A_{n+1} over Spec (lim A_n), with its Yoneda map.
Source: Stacks 0CX4
(blueprint: lem-sfb-space-flat-proper-support-inverse-effectivity). -/
def inverseEffectivityTest (D : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    ProperQuotTest (inverseEffectivityBase D) :=
  CostructuredArrow.mk (yoneda.map
    (Over.homMk (U := Over.mk (Spec.map (limit.π D (op n))))
      (Spec.map (limit.π D (op n))) (Category.comp_id _)))

/-- The canonical adjacent spectrum map is a map over the inverse-limit spectrum.
Source: Stacks 0CX4
(blueprint: lem-sfb-space-flat-proper-support-inverse-effectivity).
Proof: the limit cone identity says pi_{n+1} followed by the ring transition is pi_n.
Contravariant functoriality of Spec gives precisely the displayed equality. -/
theorem inverseEffectivityStep_w (D : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    Spec.map (D.map (homOfLE (Nat.le_succ n)).op) ≫
        Spec.map (limit.π D (op (n + 1))) = Spec.map (limit.π D (op n)) := by
  sorry

/-- The adjacent spectrum map also commutes with the Yoneda test maps.
Source: Stacks 0CX4
(blueprint: lem-sfb-space-flat-proper-support-inverse-effectivity).
Proof: the two maps from Spec A_{n+1} to the identity object of the slice agree:
apply Over morphism extensionality and the over-triangle identity. Apply Yoneda
functoriality to this equality. The over-triangle is inverseEffectivityStep_w. -/
theorem inverseEffectivityTestStep_w (D : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    yoneda.map (Over.homMk (Spec.map (D.map (homOfLE (Nat.le_succ n)).op))
        (inverseEffectivityStep_w D n)) ≫ (inverseEffectivityTest D (n + 1)).hom =
      (inverseEffectivityTest D n).hom := by
  sorry

/-- The actual adjacent test morphism, not an arbitrarily chosen transition map.
Source: Stacks 0CX4
(blueprint: lem-sfb-space-flat-proper-support-inverse-effectivity). -/
def inverseEffectivityTestStep (D : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    inverseEffectivityTest D n ⟶ inverseEffectivityTest D (n + 1) :=
  CostructuredArrow.homMk
    (Over.homMk (Spec.map (D.map (homOfLE (Nat.le_succ n)).op))
      (inverseEffectivityStep_w D n)) (inverseEffectivityTestStep_w D n)

/-- Grothendieck existence for relatively flat, finitely presented algebraic-space modules
with proper support over an arbitrary surjective ring tower with locally nilpotent kernels.
No Noetherian hypothesis or ambient flatness is assumed. Index n means the source's n+1.
Source: Stacks Project, spaces-flat.tex, Tags 0CX4 and 0CXB
(blueprint: lem-sfb-space-flat-proper-support-inverse-effectivity).

Proof:
1. Apply lem-sfb-space-inverse-modules-near-special-fibre to the specified system.
   It gives an open W containing the common infinitesimal locus, a finitely presented
   quasi-coherent F on W, and compatible identifications of its reductions with M_n.
2. Apply lem-sfb-space-inverse-module-proper-shrinking to the first reduction. Shrink
   W while retaining every X_n; now F has proper support over the limit ring.
3. Choose a proper closed carrier Z in W and its finite type quasi-coherent G, as in
   def-sfb-space-proper-quot-functor. Separatedness of X and properness of Z imply
   that Z to X has closed image C. The cover W, X minus C verifies it is a closed
   immersion. Extend F by direct image along W to X. On this cover it is F and zero,
   hence is quasi-coherent and finitely presented; it equals the direct image of G
   along Z to X. This supplies proper support and the compatible reduction isomorphisms.
4. Apply lem-sfb-space-proper-support-universal-flattening to this extension. Its
   universal flattening is a scheme monomorphism of finite presentation over Spec A.
   The flatness of every M_n makes Spec A_n factor uniquely through it.
5. Apply lem-sfb-nilpotent-tower-monomorphism-rigidity: this monomorphism is an
   isomorphism. The flattening universal property therefore makes the extension flat
   over A. Together with step 3 this gives all the asserted properties and the
   compatibility equation, using the canonical tensor composition comparison. -/
theorem flat_properSupport_inverse_effectivity
    (D : ℕᵒᵖ ⥤ CommRingCat.{u})
    (hsurj : ∀ n : ℕ,
      Function.Surjective (D.map (homOfLE (Nat.le_succ n)).op).hom)
    (hnil : ∀ (n : ℕ) (x : D.obj (op (n + 1))),
      (D.map (homOfLE (Nat.le_succ n)).op).hom x = 0 → IsNilpotent x)
    (X : AlgebraicSpace (Spec (limit D))) (a : X ⟶ inverseEffectivityBase D)
    (hsep : MapIsSeparated a) (hfp : ProperQuotFinitePresentation a)
    (Mn : ∀ n : ℕ, (properQuotFibre a (inverseEffectivityTest D n)).Modules)
    (hqc : ∀ n : ℕ, (Mn n).IsQuasicoherent)
    (hmfp : ∀ n : ℕ, (Mn n).IsFinitePresentation)
    (hflat : ∀ (n : ℕ) (U : (properQuotFibre a (inverseEffectivityTest D n)).EtaleSite),
      ((schemeRestriction _ U).obj (Mn n)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫
          (properQuotSnd a (inverseEffectivityTest D n)).hom.hom)).left)
    (hsupp : ∀ n : ℕ,
      ∃ (Z : AlgebraicSpace (Spec (limit D)))
        (i : Z ⟶ properQuotFibre a (inverseEffectivityTest D n)),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
        MapIsProper (i ≫ properQuotSnd a (inverseEffectivityTest D n)) ∧
        ∃ G : Z.Modules, G.IsQuasicoherent ∧ G.IsFiniteType ∧
          Nonempty ((moduleDirectImage i).obj G ≅ Mn n))
    (transition : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap a (inverseEffectivityTestStep D n))).obj
        (Mn (n + 1)) ≅ Mn n) :
    ∃ M : X.Modules, M.IsQuasicoherent ∧ M.IsFinitePresentation ∧
      (∀ U : X.EtaleSite, ((schemeRestriction X U).obj M).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ a.hom.hom)).left) ∧
      (∃ (Z : AlgebraicSpace (Spec (limit D))) (i : Z ⟶ X),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
        MapIsProper (i ≫ a) ∧ ∃ G : Z.Modules,
          G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M)) ∧
      ∃ e : ∀ n : ℕ,
        (moduleTensorPullback (properQuotFst a (inverseEffectivityTest D n))).obj M ≅ Mn n,
        ∀ n : ℕ,
          (properQuotSourceIso a M (inverseEffectivityTestStep D n)).hom ≫ (e n).hom =
            (moduleTensorPullback (properQuotFibreMap a (inverseEffectivityTestStep D n))).map
              (e (n + 1)).hom ≫ (transition n).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

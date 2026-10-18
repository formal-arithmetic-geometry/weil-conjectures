/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift
import Sheaf.AlgebraicGeometry.SmoothLisseRelativeDualBounded
import Sheaf.AlgebraicGeometry.SmoothLisseCompactDualExchange
import Sheaf.AlgebraicGeometry.SmoothGenericDirectImageCohomology
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange
import Sheaf.AlgebraicGeometry.FiniteLisseFieldDual
import WeilConjectures.Compactification.BaseChange
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion

/-!
# Generic direct images from a smooth source

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-asd-smooth-generic-direct-image.md`, statement and proof
(blueprint: lem-asd-smooth-generic-direct-image).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem exists_dense_open_lisse_restriction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (S : Scheme.{u}) (C : DerivedCategoryModule Λ S)
    (hC : DerivedCategory.isBoundedConstructible Λ S C) :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
          ((L((U.ι)^*[ModuleCat.{u + 1} Λ])).obj C))) ∧
      ∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor _ i).obj
          ((L((U.ι)^*[ModuleCat.{u + 1} Λ])).obj C)) := by
  classical
  obtain ⟨hc, a, b, hab, hz⟩ := hC
  have key : ∀ s : Finset ℤ, ∃ U : S.Opens, Dense (U : Set S) ∧ ∀ i ∈ s,
      Scheme.IsFiniteLocallyConstantSheaf
        (((U.ι)^*[ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, by simp, by simp⟩
    | insert i s _ ih =>
      obtain ⟨V, hV, hs⟩ := ih
      have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)
      obtain ⟨W, hW, hi⟩ := Scheme.IsConstructibleSheaf.exists_dense_open
        ((_root_.DerivedCategory.homologyFunctor _ i).obj C)
      refine ⟨V ⊓ W, hV.inter_of_isOpen_left hW V.isOpen, fun j hj ↦ ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
          (V ⊓ W).ι W.ι (by simp) _
      · have := hs j hj
        exact Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
          (V ⊓ W).ι V.ι (by simp) _
  obtain ⟨U, hU, hl⟩ := key (Finset.Icc a b)
  have hzU (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        ((L((U.ι)^*[ModuleCat.{u + 1} Λ])).obj C)) :=
    (((U.ι)^*[ModuleCat.{u + 1} Λ]).map_isZero (hz i hi)).of_iso
      ((leftDerivedUpperStarHomologyFunctorIso _ U.ι i).app C).symm
  refine ⟨U, hU, ⟨a, b, hab, hzU⟩, fun i ↦ ?_⟩
  by_cases hi : a ≤ i ∧ i ≤ b
  · have := hl i (Finset.mem_Icc.mpr hi)
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
      (F := ((U.ι)^*[ModuleCat.{u + 1} Λ]).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj C))
      ((leftDerivedUpperStarHomologyFunctorIso _ U.ι i).app C)
  · exact Scheme.IsFiniteLocallyConstantSheaf.of_isZero (hzU i (by omega))

private theorem bounded_finite_lisse_dual
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (hℓ : IsUnit (ℓ : Γ(T, ⊤)))
    (C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T)
    (hb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj C))
    (hl : ∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj
          (Opposite.op C)).obj (constantComplex (ULift.{u + 1} (ZMod ℓ)) T))) := by
  obtain ⟨_, hcoh, _⟩ := finiteLisseFieldDual ℓ T hℓ C hb hl
  obtain ⟨a, b, hab, hz⟩ := hb
  refine ⟨-b, -a, by omega, fun i hi ↦ ?_⟩
  obtain ⟨e⟩ := hcoh i
  exact (MonoidalCategory.isZero_ihom_obj_of_isZero (hz (-i) (by omega)) _).of_iso e

/-- A finite locally constant prime-field sheaf on a separated smooth finite-type source
has bounded finite locally constant ordinary derived direct image on a nonempty base open,
where its canonical ordinary exchange is invertible for every Noetherian test scheme.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-asd-smooth-generic-direct-image.md`
(blueprint: lem-asd-smooth-generic-direct-image).

Proof:
1. The schemes are Noetherian by pqf-lem-locnoeth-lft. The locally constant relative
   dimension (sbc-lem-smooth-relative-dimension-locally-constant) and quasi-compactness
   split X into finitely many open-and-closed pure-dimensional pieces. Compactify each
   by thm-nagata-compactification.
2. On one piece put omega = f^times lambda and N = L^dual tensor omega.
   By thm-asd-smooth-tensor, omega is a rank-one lisse sheaf shifted by 2d. Finite-free
   biduality gives L = RHom(N, omega): compute on trivializing etale neighborhoods and
   use lemma-weil-pbc-geometric-stalk-conservative. Thus N is bounded constructible.
3. prop-asd-internal-adjunction identifies Rf_*L with RHom(Rf_!N, lambda).
   lem-fin-compact-bounded-and-base-change makes C = Rf_!N bounded constructible.
   In each of its finitely many cohomological degrees, the stratum through the generic
   point contains a nonempty open. Intersect these opens and apply lem-fin-lisse-field-dual
   to obtain bounded finite locally constant cohomology of the dual.
4. For every Noetherian T, prop-asd-smooth-base-change identifies the pulled-back omega
   and N with those for f_T. Base-changed compactification and finite type make the
   ambient adjunction available (lemma-nagata-compactification-base-change and
   lem-pod-separated-finite-type-base-change). Compact-support exchange and
   lem-fin-lisse-field-dual then give an isomorphism between the desired objects.
5. Identify this map with sbc-def-base-change-map: transpose the internal-adjunction
   pairing obtained from the ordinary counit f^*Rf_*L -> L and evaluation L tensor N ->
   omega. Compact exchange is natural for this pairing; exceptional exchange is the
   transpose of compact exchange followed by the exceptional counit. Pulling back these
   pairings therefore gives precisely the ordinary inverse-image square comparison
   followed by the pulled-back ordinary counit. Equality of adjunction transposes proves
   equality with the specified ordinary exchange, hence its invertibility.
6. Intersect the opens from all dimensions. Direct image and exchange on a finite
   disjoint union are finite products, which are exact in the abelian sheaf category.
   Take common bounds; finite sums of finite locally constant sheaves remain so.
   For empty X use the zero complex and the whole integral base as the open. -/
theorem exists_nonempty_open_smooth_directImage_lisse_baseChange
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    ∃ U : S.Opens, Nonempty U ∧
      ∀ (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
        IsPullback p fU f U.ι →
        (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        (∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
          ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
          (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
          (sq : IsPullback vX fT fU v),
          IsIso ((derivedBaseChangeMap
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sq.toCommSq).app
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L)))  := by
  obtain ⟨U, hU, hcoh⟩ := smooth_generic_directImage_cohomology k S aS ℓ hℓ X f L hL
  refine ⟨U, hU, fun XU p fU sqU ↦ ?_⟩
  obtain ⟨hb, hl⟩ := hcoh XU p fU sqU
  refine ⟨hb, hl, ?_⟩
  exact isIso_smooth_lisse_ordinary_exchange ℓ S aS hℓ X f L hL U XU p fU sqU

end AlgebraicGeometry.Etale

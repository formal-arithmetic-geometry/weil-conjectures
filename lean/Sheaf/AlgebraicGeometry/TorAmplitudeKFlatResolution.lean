/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Paper.KFlatRingedToposPullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Sheaf.Paper.EtaleFlatKFlatResolution
import Mathlib.Algebra.Homology.Additive
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES
import Sheaf.Paper.EtaleKFlatCriteria
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import Sheaf.AlgebraicGeometry.EtaleTensorCokernelFlat
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Tor amplitude and K-flat resolutions

Source: Stacks Project, Tag 0F1M, lemma-bounded-below-tor-amplitude
(blueprint: lem-kun-0f1m).

The scalar restriction below identifies a module over the constant ring sheaf with a
module-valued sheaf, using the sheafification unit on constants. It lets the existing
ringed-site K-flat and flatness predicates use the same representative as the recorded
module-valued derived category. The representative in the theorem is fixed before the
universal quantification over pullbacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uD vD

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The constant commutative coefficient ring on the small etale site.
Source: Stacks Tag 0F1M (blueprint: lem-kun-0f1m). -/
abbrev torModelCoefficientRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology CommRingCat.{u + 1} :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Forget commutativity of the constant coefficient sheaf.
Source: Stacks Tag 0F1M (blueprint: lem-kun-0f1m). -/
abbrev torModelRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (sheafCompose T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (torModelCoefficientRing Λ T)

/-- The unit from constant scalars to the constant ring sheaf.
Source: Stacks Tag 0H7J, used in 0F1M (blueprint: lem-kun-0f1m). -/
def torModelScalarUnit (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    (Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ (torModelRing Λ T).obj :=
  Functor.whiskerRight
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the action to constant scalars, keeping the underlying sheaf and maps.
Source: Stacks Modules on Sites, Section 093I, and Tag 0F1M
(blueprint: lem-kun-0f1m). -/
def torModelRestriction (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj M :=
    { obj :=
        { obj := fun X ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).obj X
          map := fun f ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).map f
          map_id := fun X ↦ by ext x; simp; rfl
          map_comp := fun f g ↦ by ext x; simp; rfl }
      property := by
        apply Presheaf.isSheaf_of_isSheaf_comp T.smallEtaleTopology _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        exact M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((torModelScalarUnit Λ T).app X).hom).map (f.val.app X)
      naturality := fun {_ _} g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x }
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Scalar restriction is additive, so it applies termwise to complexes.
Source: Stacks Section 093I, used in Tag 0F1M (blueprint: lem-kun-0f1m).
Proof: all maps are the original additive maps, restricted to constant scalars, so
restriction carries the pointwise sum of two maps to their pointwise sum. -/
@[instance]
theorem torModelRestriction_additive (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    (torModelRestriction Λ T).Additive := by
  sorry

/-- Tor amplitude in `[a, infinity)` is equivalent to a K-flat, flat-term representative
vanishing below `a`. This one representative remains K-flat and flat-term after every
module pullback along a morphism of ringed topoi.
Source: Stacks Tag 0F1M, lemma-bounded-below-tor-amplitude, and Tag 0G7E
(blueprint: lem-kun-0f1m).

Proof:
1. A K-flat representative computes derived tensor with every sheaf in degree zero
(def-kun-derived-tensor). Its terms below a vanish, so the cohomology of each tensor
vanishes below a, the condition of def-kun-tor-amplitude.
2. Conversely take a K-flat flat-term resolution K of a representative of E using
lem-kun-flat-resolution-existence, in the larger universe of def-weil-size-convention.
The amplitude assumption says H^n(K tensor M)=0 for n<a and every module sheaf M.
Testing with the unit gives H^n(K)=0 below a.
3. By lem-kun-tor-cokernel-flat, N=coker(K^(a-1) -> K^a) is flat.
4. The good lower truncation P has N at a, K^i above a, and zero below a
(def-kun-truncations). Its quotient map q:K -> P is a quasi-isomorphism: at a its
cohomology is ker(d^a)/im(d^(a-1)), at a+1 the incoming image is unchanged, and above
that the complexes coincide. Below a both cohomologies vanish. Thus P represents E.
5. The kernel L of q has K^i below a, im(d^(a-1)) at a, and zero above a. The image
is flat by lem-weil-pbc-site-flat-quotient-tensor-ses since K^a and N are flat.
Hence L is bounded above with flat terms, so K-flat by lem-kun-kflat-criteria.
6. Tensor the degreewise short exact sequence 0 -> L -> K -> P -> 0 with any
acyclic complex A. Flatness of P and lem-weil-pbc-site-flat-quotient-tensor-ses give
short exact sequences in each bidegree. Finite direct sums preserve exactness;
lem-pc-module-filtered-colimits-tensor makes their filtered colimit, the full
sum over p+q=n, exact. Chain-map identities and the sign (-1)^p identify the
result as a short exact sequence of total complexes. The first two are acyclic
by K-flatness; lem-weil-pbc-complex-ses-homology-long-exact makes the third
acyclic. Thus P is K-flat.
7. Apply lem-weil-pbc-ringed-topos-kflat-pullback to this fixed P, simultaneously
for every ringed-topos morphism. No exactness of module pullback or flatness of
the coefficient homomorphism is assumed. -/
theorem DerivedCategory.hasTorAmplitudeGE_iff_exists_kFlat_flat_model
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) (E : DerivedCategoryModule Λ T)
    (a : ℤ) :
    DerivedCategory.hasTorAmplitudeGE Λ T a E ↔
      ∃ P : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := torModelCoefficientRing Λ T) P ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := T.smallEtaleTopology) (R := torModelCoefficientRing Λ T) (P.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (P.X i)) ∧
        Nonempty (_root_.DerivedCategory.Q.obj
          (((torModelRestriction Λ T).mapHomologicalComplex (.up ℤ)).obj P) ≅ E) ∧
        (∀ {D : Type uD} [Category.{vD} D] [EssentiallySmall.{u + 1} D]
          (J : GrothendieckTopology D) (RI S : Sheaf J CommRingCat.{u + 1})
          (uInv : Sheaf T.smallEtaleTopology (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
          (uPush : Sheaf J (Type (u + 1)) ⥤ Sheaf T.smallEtaleTopology (Type (u + 1)))
          (_adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
          (I : SheafOfModules.AlgebraicInverseImage uInv (torModelCoefficientRing Λ T) RI)
          (c : RI ⟶ S)
          (uStar : SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
            SheafOfModules.{u + 1}
              ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
          (hobj : ∀ M : SheafOfModules.{u + 1} (torModelRing Λ T),
            uStar.obj M = SheafOfModules.changeOfRings c (I.modules.obj M))
          (_hmap : ∀ {M N : SheafOfModules.{u + 1} (torModelRing Λ T)} (f : M ⟶ N),
            uStar.map f = eqToHom (hobj M) ≫
              SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
              eqToHom (hobj N).symm) [uStar.Additive],
          CochainComplex.IsKFlatIndependentCoefficients (R := S)
            ((uStar.mapHomologicalComplex (.up ℤ)).obj P) ∧
          ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{uD, vD, u + 1, u + 1} (J := J) (R := S)
            (((uStar.mapHomologicalComplex (.up ℤ)).obj P).X i)) := by
  sorry

end AlgebraicGeometry.Etale

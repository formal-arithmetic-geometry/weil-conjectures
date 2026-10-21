/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules

/-! # Counit-normalized exceptional comparisons for section families

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc, opening fibre restrictions,
Local construction and Gluing (blueprint: lem-trf-section-exceptional-fibre-coherence).

The records below package the geometric diagrams, not their cohomological comparisons.
Every comparison is constructed from the existing counit mate or the unique counit-normalized
locality isomorphism. The two fibre labels are `false` (zero) and `true` (one).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- A smooth compactifiable map with a closed section, as in the opening fibre restrictions
of blueprint sk-thm-dnc (blueprint: lem-trf-section-exceptional-fibre-coherence).
This is only a record of the geometric hypotheses; it contains no comparison maps. -/
structure ExceptionalSectionPair (B : Scheme.{u}) (d : ℕ) where
  total : Scheme.{u}
  map : total ⟶ B
  sect : B ⟶ total
  section_map : sect ≫ map = 𝟙 B
  [base_noetherian : IsNoetherian B]
  [total_noetherian : IsNoetherian total]
  [compactifiable : HasCompactification map]
  [separated : IsSeparated map]
  [smooth : SmoothOfRelativeDimension d map]
  [closed : IsClosedImmersion sect]

attribute [instance] ExceptionalSectionPair.total_noetherian ExceptionalSectionPair.compactifiable
  ExceptionalSectionPair.separated ExceptionalSectionPair.smooth ExceptionalSectionPair.closed

/-- A Cartesian change of a section pair, including the compatibility of the sections.
Source: blueprint sk-thm-dnc, fibre restrictions and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalSectionChange {B B' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionPair B d) (P' : ExceptionalSectionPair B' d) (v : B' ⟶ B) where
  upper : P'.total ⟶ P.total
  square : IsPullback upper P'.map P.map v
  section_comm : P'.sect ≫ upper = v ≫ P.sect

/-- Pullback along the two equal composites in a commuting square, using the canonical
inverse-image compositors. Source: blueprint sk-thm-dnc, Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def sectionCoherencePullbackIso
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' : Scheme.{u}} (v : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X')
    (r : X' ⟶ X) (h : v ≫ i = i' ≫ r) (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.obj K) ≅
      (upperStar (ModuleCat.{u + 1} A) i').leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r (v ≫ i) h).app K

/-- Section pullback of the actual counit-defined exceptional comparison at the coefficient
unit. Source: blueprint sk-thm-dnc, opening fibre restrictions
(blueprint: lem-trf-section-exceptional-fibre-coherence). The input map is the existing
`dualizingComplexBaseChangeMap`, not a chosen isomorphism of its source and target. -/
noncomputable def sectionExceptionalComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' : Scheme.{u}} {d : ℕ} {P : ExceptionalSectionPair B d}
    {P' : ExceptionalSectionPair B' d} {v : B' ⟶ B}
    (e : ExceptionalSectionChange P P' v) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        (sectionInvariant A P.map P.sect) ⟶ sectionInvariant A P'.map P'.sect :=
  (sectionCoherencePullbackIso A v P.sect P'.sect e.upper
      e.section_comm.symm (dualizingComplex (ModuleCat.{u + 1} A) P.map)).hom ≫
    (upperStar (ModuleCat.{u + 1} A) P'.sect).leftDerivedFunctor.map
      (dualizingComplexBaseChangeMap A e.square)

/-- The zero or one section of the affine line. Source: blueprint sk-thm-dnc, opening
fibre restrictions (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def exceptionalFamilyPoint (S : Scheme.{u}) (t : Bool) :
    S ⟶ AffineSpace (ULift.{u} (Fin 1)) S :=
  if t then AffineSpace.oneSection (ULift.{u} (Fin 1)) S
  else AffineSpace.zeroSection (ULift.{u} (Fin 1)) S

/-- A section family over the affine line with its two Cartesian fibre pairs.
Source: blueprint sk-thm-dnc, opening fibre restrictions
(blueprint: lem-trf-section-exceptional-fibre-coherence).
No isomorphism of derived objects is a field of this geometric record. -/
structure ExceptionalSectionFamily (S : Scheme.{u}) (d : ℕ) where
  ambient : ExceptionalSectionPair (AffineSpace (ULift.{u} (Fin 1)) S) d
  fibre : Bool → ExceptionalSectionPair S d
  restriction : ∀ t : Bool,
    ExceptionalSectionChange ambient (fibre t) (exceptionalFamilyPoint S t)

/-- The specified fibre map: `theta` at one and `eta` at zero. Source: blueprint sk-thm-dnc,
opening fibre restrictions (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def ExceptionalSectionFamily.fibreMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d) (t : Bool) :=
  sectionExceptionalComparison A (P.restriction t)

/-- A base-changed family and its Cartesian fibre diagram. The last equations express
that these are the induced maps of the fibres. Source: blueprint sk-thm-dnc, Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalFamilyBaseChange {S S' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionFamily S d) (P' : ExceptionalSectionFamily S' d) (v : S' ⟶ S) where
  ambient : ExceptionalSectionChange P.ambient P'.ambient
    (AffineSpace.map (ULift.{u} (Fin 1)) v)
  fibre : ∀ t : Bool, ExceptionalSectionChange (P.fibre t) (P'.fibre t) v
  point_comm : ∀ t : Bool, v ≫ exceptionalFamilyPoint S t =
    exceptionalFamilyPoint S' t ≫ AffineSpace.map (ULift.{u} (Fin 1)) v
  fibre_comm : ∀ t : Bool, (fibre t).upper ≫ (P.restriction t).upper =
    (P'.restriction t).upper ≫ ambient.upper

/-- The canonical counit-normalized locality isomorphism for a structural map and an etale
map into its source, evaluated at the constant unit. Source: blueprint sk-thm-dnc, Local
construction (blueprint: lem-trf-section-exceptional-fibre-coherence). The choice is from the
unique counit-normalized isomorphism of `lem-amb-etale-adjoint-locality`; hence its data are
determined, rather than chosen from an uncharacterized existence assertion. -/
noncomputable def sectionStructuralLocalityIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ B) [HasCompactification f] (f' : U ⟶ B) [HasCompactification f']
    (hf : h ≫ f = f') :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
      (dualizingComplex (ModuleCat.{u + 1} A) f) ≅
        dualizingComplex (ModuleCat.{u + 1} A) f' := by
  subst f'
  exact (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).app _ ≪≫
    (Classical.choose (existsUnique_etaleAmbientAdjointLocalityIso A h f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (h ≫ f))
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (h ≫ f))
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (h ≫ f)))).app (𝟙_ _)

/-- An etale finite-type map of section pairs with Cartesian centres. Source: blueprint
sk-thm-dnc, Local construction (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalSectionEtaleMap {B : Scheme.{u}} {d : ℕ}
    (P P₁ : ExceptionalSectionPair B d) where
  upper : P₁.total ⟶ P.total
  map_comm : upper ≫ P.map = P₁.map
  section_comm : P₁.sect ≫ upper = P.sect
  centres : IsPullback (𝟙 B) P₁.sect P.sect upper
  [etale : Etale upper]
  [separated : IsSeparated upper]
  [finite_type : LocallyOfFiniteType upper]
  [quasi_compact : QuasiCompact upper]

attribute [instance] ExceptionalSectionEtaleMap.etale ExceptionalSectionEtaleMap.separated
  ExceptionalSectionEtaleMap.finite_type ExceptionalSectionEtaleMap.quasi_compact

/-- Section pullback of the counit-normalized etale locality isomorphism. Source: blueprint
sk-thm-dnc, Local construction (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def sectionExceptionalLocalityIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B : Scheme.{u}} {d : ℕ} {P P₁ : ExceptionalSectionPair B d}
    (h : ExceptionalSectionEtaleMap P P₁) :
    sectionInvariant A P.map P.sect ≅ sectionInvariant A P₁.map P₁.sect :=
  letI := P.base_noetherian
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) P₁.sect h.upper
      P.sect h.section_comm.symm).app _ ≪≫
    (upperStar (ModuleCat.{u + 1} A) P₁.sect).leftDerivedFunctor.mapIso
      (sectionStructuralLocalityIso A h.upper P.map P₁.map h.map_comm)

/-- An etale map of the whole family and its induced fibre maps. Source: blueprint
sk-thm-dnc, Local construction (blueprint: lem-trf-section-exceptional-fibre-coherence). -/
structure ExceptionalFamilyEtaleMap {S : Scheme.{u}} {d : ℕ}
    (P P₁ : ExceptionalSectionFamily S d) where
  ambient : ExceptionalSectionEtaleMap P.ambient P₁.ambient
  fibre : ∀ t : Bool, ExceptionalSectionEtaleMap (P.fibre t) (P₁.fibre t)
  fibre_comm : ∀ t : Bool, (fibre t).upper ≫ (P.restriction t).upper =
    (P₁.restriction t).upper ≫ ambient.upper

/-- Normalization of a family isomorphism at the one fibre, including the inverse-image
unit compositor. Source: blueprint sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
def ExceptionalSectionFamily.IsNormalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect)) : Prop :=
  (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S true)).leftDerivedFunctor.map
      κ.hom ≫
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      (AffineSpace.oneSection_comp_over _ _)).hom.app _ = P.fibreMap A true

/-- The specialization determined by a normalized family isomorphism, from the one fibre
to the zero fibre. Source: blueprint sk-thm-dnc, final paragraph
(blueprint: lem-trf-section-exceptional-fibre-coherence). -/
noncomputable def ExceptionalSectionFamily.specialization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} {d : ℕ} (P : ExceptionalSectionFamily S d)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect)) :
    sectionInvariant A (P.fibre true).map (P.fibre true).sect ⟶
      sectionInvariant A (P.fibre false).map (P.fibre false).sect :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.zeroSection_comp_over _ _)).inv.app _ ≫
  (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S false)).leftDerivedFunctor.map
    κ.inv ≫ P.fibreMap A false


/-- The specified base-change maps are invertible, and the two fibre squares commute.
Source: blueprint sk-thm-dnc, opening fibre restrictions and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (1) write the exceptional comparison as the transpose of inverse compact-support
exchange followed by the pulled-back counit. Smooth exceptional base change makes it
invertible, including at the constant unit. (2) Compact-support pasting and mate pasting give
transitivity, with the canonical inverse-image and unit compositors. (3) The paths through
the old fibre and through the new affine line are the two factorizations of the same outer
Cartesian rectangle. Transitivity identifies their exceptional comparisons. Pull back by the
new fibre section, using its compatibility with the other sections. At true this is the theta
square, and at false it is the eta square. This is equality of the prescribed maps.
-/
theorem sectionExceptional_fibre_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S S' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionFamily S d) (P' : ExceptionalSectionFamily S' d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (v : S' ⟶ S) (e : ExceptionalFamilyBaseChange P P' v) :
    IsIso (sectionExceptionalComparison A e.ambient) ∧
    ∀ t : Bool,
      IsIso (P.fibreMap A t) ∧ IsIso (P'.fibreMap A t) ∧
      IsIso (sectionExceptionalComparison A (e.fibre t)) ∧
      (sectionCoherencePullbackIso A v (exceptionalFamilyPoint S t)
        (exceptionalFamilyPoint S' t) (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (e.point_comm t) (sectionInvariant A P.ambient.map P.ambient.sect)).hom ≫
          (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S' t)).leftDerivedFunctor.map
            (sectionExceptionalComparison A e.ambient) ≫ P'.fibreMap A t =
        (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map (P.fibreMap A t) ≫
          sectionExceptionalComparison A (e.fibre t) := by
  sorry

/-- Transitivity of the structural section comparison for successive changes of base.
Source: blueprint sk-thm-dnc, Gluing; Stacks 0F7L, compatibility with composite base changes
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: paste inverse compact-support exchange squares, and apply mate-pasting to their
adjunctions. Both sides transpose to the pulled-back structural counit through the same
inverse exchange. Evaluate at the unit, use unit-composition coherence, and pull back by
the compatible final section. The displayed compositor inserts the canonical identification
of the iterated inverse image. This applies to each of q, g and pi in the section family.
-/
theorem sectionExceptional_comparison_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' B'' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionPair B d) (P' : ExceptionalSectionPair B' d)
    (P'' : ExceptionalSectionPair B'' d)
    (hInvertible : ∀ b : B, IsUnit (N : B.presheaf.stalk b))
    (v : B' ⟶ B) (w : B'' ⟶ B')
    (e : ExceptionalSectionChange P P' v) (e' : ExceptionalSectionChange P' P'' w)
    (e'' : ExceptionalSectionChange P P'' (w ≫ v))
    (hUpper : e''.upper = e'.upper ≫ e.upper) :
    sectionExceptionalComparison A e'' =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app
        (sectionInvariant A P.map P.sect) ≫
      (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.map
        (sectionExceptionalComparison A e) ≫ sectionExceptionalComparison A e' := by
  sorry

/-- Counit-normalized etale locality commutes with both exceptional fibre comparisons.
Source: blueprint sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (4) etale locality is the right-adjoint conjugate of compact-support composition;
its transpose is the inverse composition comparison followed by the sum-extension evaluation
and the structural counit. (5) The specified etale sum-extension base-change comparison
preserves evaluation: compare transposes under the composite adjunction, expand underived
exchange, and use naturality and the triangle identities. This equality descends degreewise
to the unbounded categories. (6) Transpose locality followed by exceptional base change in
both orders. Compact-support composition/base-change compatibility, step (5), and the mate
pasting rules give the same transpose. (7) Apply this to q and each fibre inclusion, evaluate
at the unit and pull back by the sections. The resulting equalities are precisely the two
squares below, for the actual counit-normalized locality maps.
-/
theorem sectionExceptional_etale_fibre_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S : Scheme.{u}} {d : ℕ}
    (P P₁ : ExceptionalSectionFamily S d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (h : ExceptionalFamilyEtaleMap P P₁) :
    ∀ t : Bool,
      (upperStar (ModuleCat.{u + 1} A) (exceptionalFamilyPoint S t)).leftDerivedFunctor.map
          (sectionExceptionalLocalityIso A h.ambient).hom ≫ P₁.fibreMap A t =
        P.fibreMap A t ≫ (sectionExceptionalLocalityIso A (h.fibre t)).hom := by
  sorry

/-- Uniquely normalized family isomorphisms, and their specializations, respect the actual
exceptional base-change maps. Source: blueprint sk-thm-dnc, Gluing and final restriction
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (8) transport kappa by the invertible ambient comparison and the pulled-back one-fibre
comparison. The fibre square above and inverse-image composition show that this transported
isomorphism is normalized by theta prime. Uniqueness identifies it with kappa prime.
(9) Restrict that equality to zero, invert its isomorphism part, and compose with eta prime.
The zero-fibre square cancels the ambient comparison and gives the specialization square.
The first equation below is the kappa formula multiplied by b_F on the source; invertibility
of b_F, supplied by sectionExceptional_fibre_coherence, gives exactly the formula with b_F⁻¹.
-/
theorem sectionExceptional_normalized_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S S' : Scheme.{u}} {d : ℕ}
    (P : ExceptionalSectionFamily S d) (P' : ExceptionalSectionFamily S' d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (v : S' ⟶ S) (e : ExceptionalFamilyBaseChange P P' v)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect))
    (κ' : sectionInvariant A P'.ambient.map P'.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj
          (sectionInvariant A (P'.fibre true).map (P'.fibre true).sect))
    (hκ : P.IsNormalized A κ ∧ ∀ τ, P.IsNormalized A τ → τ = κ)
    (hκ' : P'.IsNormalized A κ' ∧ ∀ τ, P'.IsNormalized A τ → τ = κ') :
    sectionExceptionalComparison A e.ambient ≫ κ'.hom =
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) v)).leftDerivedFunctor.map κ.hom ≫
      (sectionCoherencePullbackIso A
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') v
        (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.map_over v).symm
        (sectionInvariant A (P.fibre true).map (P.fibre true).sect)).inv ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.map
          (sectionExceptionalComparison A (e.fibre true)) ∧
    sectionExceptionalComparison A (e.fibre true) ≫ P'.specialization A κ' =
      (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map (P.specialization A κ) ≫
        sectionExceptionalComparison A (e.fibre false) := by
  sorry

/-- Uniquely normalized family isomorphisms and their specializations respect etale maps
of families. Source: blueprint sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-section-exceptional-fibre-coherence).
Proof: (10) transport kappa by the counit-normalized etale locality isomorphisms. The one-fibre
locality square makes the transported isomorphism normalized, so uniqueness identifies it
with kappa subscript one. Restrict to zero, invert, and apply the zero-fibre locality square
to obtain the specialization identity. The first equation is equivalently the stated
formula with the inverse of the ambient locality isomorphism.
-/
theorem sectionExceptional_normalized_etale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S : Scheme.{u}} {d : ℕ} (P P₁ : ExceptionalSectionFamily S d)
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (h : ExceptionalFamilyEtaleMap P P₁)
    (κ : sectionInvariant A P.ambient.map P.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P.fibre true).map (P.fibre true).sect))
    (κ₁ : sectionInvariant A P₁.ambient.map P₁.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A (P₁.fibre true).map (P₁.fibre true).sect))
    (hκ : P.IsNormalized A κ ∧ ∀ τ, P.IsNormalized A τ → τ = κ)
    (hκ₁ : P₁.IsNormalized A κ₁ ∧ ∀ τ, P₁.IsNormalized A τ → τ = κ₁) :
    (sectionExceptionalLocalityIso A h.ambient).hom ≫ κ₁.hom =
      κ.hom ≫
        (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.map
            (sectionExceptionalLocalityIso A (h.fibre true)).hom ∧
    (sectionExceptionalLocalityIso A (h.fibre true)).hom ≫ P₁.specialization A κ₁ =
      P.specialization A κ ≫ (sectionExceptionalLocalityIso A (h.fibre false)).hom := by
  sorry

end AlgebraicGeometry.Etale

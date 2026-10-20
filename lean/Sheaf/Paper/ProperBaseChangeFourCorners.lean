/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
/-!
# Four finite-level proper base-change corners
Source: blueprint `def-weil-pbc-four-corners`, order 1342; Stacks Tags 099N,
09C9, 0B56 and 0944 (blueprint: def-weil-pbc-four-corners).
The finite constant coefficient presentation and its inverse limit are the recorded
completed-coefficient datum. Its normalized comparison identifies finite coefficients
with sheafified continuous component functions and respects quotient transitions.
The reduction/pullback comparison is characterized on K-flat representatives by
the mate of sectionwise restriction/direct-image commutation, fixing its tensor map.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A]

/-- The standard unbounded derived category of the existing coefficient modules.
Source: blueprint order 1342 (blueprint: def-weil-pbc-four-corners). -/
abbrev fourCornerDerived (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  DerivedCategory (proEtaleRingModules T R)

/-- Existing restriction of scalars along a coefficient projection.
Source: blueprint order 1342; Stacks 03D3 (blueprint: def-weil-pbc-four-corners). -/
abbrev fourCornerRestrict (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)

/-- The actual quotient ring tower, with exponent n+1 and its consecutive quotient maps.
Source: blueprint order 1342 (blueprint: def-weil-pbc-four-corners). -/
def fourCornerRingTower (I : Ideal A) : ℕᵒᵖ ⥤ CommRingCat.{t + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ CommRingCat.of (A ⧸ I ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)))

/-- Every quotient in the adic datum is finite, including the first positive level.
Source: blueprint order 1342 (blueprint: def-weil-pbc-four-corners). -/
instance fourCornerRingTowerFinite (d : ProEtaleAdicCoefficientDatum A) (n : ℕᵒᵖ) :
    Finite ((fourCornerRingTower d.ideal).obj n) := d.quotientFinite n.unop

/-- Constant sheafification commutes with the presentation of the strict quotient sequence.
Source: blueprint order 1342 (blueprint: def-weil-pbc-four-corners).
Proof: the two functors have identical objects. Each consecutive arrow is the constant
sheaf image of the same quotient map. Every arrow is a finite composite of consecutive
arrows; functoriality identifies its two images. This also covers identity arrows. -/
theorem fourCornerCoefficientTowerNaturality (T : Scheme.{t})
    (d : ProEtaleAdicCoefficientDatum A) {i j : ℕᵒᵖ} (h : i ⟶ j) :
    (proEtaleCoefficientTower T (fourCornerRingTower d.ideal)).map h =
      (adicLisseRingSystem T d.ideal).map h := by
  sorry

/-- The identity-on-objects isomorphism of the two strict coefficient presentations.
Source: blueprint order 1342 (blueprint: def-weil-pbc-four-corners). -/
def fourCornerCoefficientTowerIso (T : Scheme.{t}) (d : ProEtaleAdicCoefficientDatum A) :
    proEtaleCoefficientTower T (fourCornerRingTower d.ideal) ≅
      adicLisseRingSystem T d.ideal :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun h ↦ (Category.comp_id _).trans
      ((fourCornerCoefficientTowerNaturality T d h).trans (Category.id_comp _).symm))

/-- The specified profinite inverse-image comparison at the actual completed ring.
Source: blueprint order 1342; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
def fourCornerCoefficientIso {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj (adicDatumRing V d) ≅
      adicDatumRing U d :=
  (proEtaleSheafInverseImage f CommRingCat.{t + 1}).mapIso
      (lim.mapIso (fourCornerCoefficientTowerIso V d)).symm ≪≫
    @asIso _ _ _ _ (proEtaleProfiniteComparison f (fourCornerRingTower d.ideal))
      ((proEtale_profinite_coefficient_inverse_image (fourCornerRingTower d.ideal)).2.1 U V f) ≪≫
    lim.mapIso (fourCornerCoefficientTowerIso U d)

/-- The specified finite coefficient comparison, normalized by constant sections.
Source: blueprint order 1342; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
def fourCornerFiniteIso {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj
        ((adicLisseRingSystem V d.ideal).obj (op n)) ≅
      (adicLisseRingSystem U d.ideal).obj (op n) :=
  @asIso _ _ _ _ ((proEtaleConstantComparison f).app
    ((fourCornerRingTower d.ideal).obj (op n)))
      ((proEtale_profinite_coefficient_inverse_image (fourCornerRingTower d.ideal)).1 U V f (op n))

/-- The completed and finite comparisons commute with their actual limit projections.
Source: blueprint order 1342; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: use the projection clause of profinite-coefficient-inverse-image and naturality
of the identity-on-objects diagram isomorphism. Its limit map carries each projection
to the same projection, so the conjugations cancel. -/
theorem fourCornerProjectionComm {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    (fourCornerCoefficientIso f d).hom ≫ adicDatumProjection U d n =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
        (adicDatumProjection V d n) ≫ (fourCornerFiniteIso f d n).hom := by
  sorry

/-- The existing additive scalar extension applied termwise to cochain complexes.
Source: blueprint order 1342; Stacks 06YY (blueprint: def-weil-pbc-four-corners). -/
abbrev fourCornerChangeComplex (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Ordinary integral derived pullback, without completion.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
abbrev fourCornerPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :=
  proEtaleRingDerivedPullback f (adicDatumRing V d)
    (adicDatumRing U d) (fourCornerCoefficientIso f d)
/-- Ordinary integral derived direct image, resolved in all module sheaves.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
abbrev fourCornerPushforward {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) :=
  proEtaleRingDerivedDirectImage f (adicDatumRing V d)
    (adicDatumRing U d) (fourCornerCoefficientIso f d)
/-- Ordinary finite derived pullback retaining its finite coefficient action.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
abbrev fourCornerFinitePullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  proEtaleRingDerivedPullback f ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)
/-- Ordinary finite derived direct image retaining its finite coefficient action.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
abbrev fourCornerFinitePushforward {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  proEtaleRingDerivedDirectImage f ((adicLisseRingSystem V d.ideal).obj (op n))
    ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)
/-- Quotient transitions commute with the specified finite identifications.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: use the finite transition identity of profinite-coefficient-inverse-image.
The identity-on-objects coefficient tower isomorphism identifies its quotient maps. -/
theorem fourCornerFiniteTransitionComm {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    (fourCornerFiniteIso f d b).hom ≫ (adicLisseRingSystem U d.ideal).map (homOfLE h).op =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
        ((adicLisseRingSystem V d.ideal).map (homOfLE h).op) ≫
          (fourCornerFiniteIso f d a).hom := by
  sorry
/-- Coefficient identifications are compatible with identity arrows and composition.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: specialize the identity and composition clauses of the profinite inverse-image
lemma. Conjugate by the identity-on-objects coefficient tower comparison and its limit.
Functoriality cancels each adjacent inverse pair. The same computation works at every
finite level. -/
theorem fourCornerCoefficientCoherence (d : ProEtaleAdicCoefficientDatum A) :
    (∀ T : Scheme.{t}, (fourCornerCoefficientIso (𝟙 T) d).hom =
      (proEtaleRingInverseImageId T).hom.app (adicDatumRing T d)) ∧
    (∀ (T : Scheme.{t}) (n : ℕ), (fourCornerFiniteIso (𝟙 T) d n).hom =
      (proEtaleRingInverseImageId T).hom.app ((adicLisseRingSystem T d.ideal).obj (op n))) ∧
    (∀ (U V W : Scheme.{t}) (f : U ⟶ V) (g : V ⟶ W),
      (fourCornerCoefficientIso (f ≫ g) d).hom =
        (proEtaleRingInverseImageComp f g).hom.app
          (adicDatumRing W d) ≫
          (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
            (fourCornerCoefficientIso g d).hom ≫ (fourCornerCoefficientIso f d).hom) ∧
    (∀ (U V W : Scheme.{t}) (f : U ⟶ V) (g : V ⟶ W) (n : ℕ),
      (fourCornerFiniteIso (f ≫ g) d n).hom =
        (proEtaleRingInverseImageComp f g).hom.app ((adicLisseRingSystem W d.ideal).obj (op n)) ≫
          (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
            (fourCornerFiniteIso g d n).hom ≫ (fourCornerFiniteIso f d n).hom) := by
  sorry
/-- Restriction and ordinary direct image commute by the identity on underlying sections.
Source: blueprint four corners; Stacks 03EK (blueprint: def-weil-pbc-four-corners).
Proof: both objects have sections N(U times_V W). Their scalar actions coincide by
fourCornerProjectionComm and the adjoint coefficient maps. Identity sections therefore
give inverse linear sheaf maps, natural in N. Their section formula proves uniqueness. -/
theorem fourCornerRestrictionPushforward_exists {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    ∃! e : fourCornerRestrict U (adicDatumProjection U d n) ⋙
        proEtaleRingModuleDirectImage f (adicDatumRing V d)
          (adicDatumRing U d) (fourCornerCoefficientIso f d) ≅
      proEtaleRingModuleDirectImage f ((adicLisseRingSystem V d.ideal).obj (op n))
          ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n) ⋙
        fourCornerRestrict V (adicDatumProjection V d n),
      ∀ (N : proEtaleRingModules U ((adicLisseRingSystem U d.ideal).obj (op n)))
        (W : V.ProEtᵒᵖ) (x : N.val.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app N).val.app W x = x := by
  sorry
/-- The ordinary balancing comparison is the conjugate of identity on direct-image
sections under the two tensor-unit-normalized adjunctions. This fixes the local tensor
map (u*Q) tensor P to u_n*(Q tensor P) and its finite coefficient action.
Source: blueprint four corners; Stacks 07A4 (blueprint: def-weil-pbc-four-corners). -/
def fourCornerOrdinaryComparison {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingModulePullback f (adicDatumRing V d)
        (adicDatumRing U d) (fourCornerCoefficientIso f d) ⋙
      completedConstantExtension U (adicDatumProjection U d n) ≅
    completedConstantExtension V (adicDatumProjection V d n) ⋙
      proEtaleRingModulePullback f ((adicLisseRingSystem V d.ideal).obj (op n))
        ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n) :=
  (conjugateIsoEquiv
    ((adicDatumOrdinaryAdjunction V (adicDatumProjection V d n)).comp
      (proEtaleRingModuleAdjunction f ((adicLisseRingSystem V d.ideal).obj (op n))
        ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)))
    ((proEtaleRingModuleAdjunction f (adicDatumRing V d)
      (adicDatumRing U d) (fourCornerCoefficientIso f d)).comp
        (adicDatumOrdinaryAdjunction U (adicDatumProjection U d n)))).symm
          (fourCornerRestrictionPushforward_exists f d n).exists.choose.symm
/-- Restriction of coefficients commutes with identified-coefficient pullback.
The isomorphism is fixed by the two normalized adjunction units and the specified
identity on direct-image sections, not by an arbitrary choice of an isomorphism.
Source: blueprint order 1342; Stacks 03EK, 07A4
(blueprint: def-weil-pbc-four-corners).
Proof: transpose the finite pullback unit under integral pullback, using the identity
restriction/direct-image comparison. On inverse-image module sections the resulting
map is the identity with its transported scalar action. Projection compatibility
identifies the two actions, so this map is invertible. The adjunction bijection fixes
its components uniquely; naturality of the units gives naturality in the module. -/
theorem fourCornerRestrictionPullback_exists {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    ∃! e : fourCornerRestrict V (adicDatumProjection V d n) ⋙
        proEtaleRingModulePullback f (adicDatumRing V d)
          (adicDatumRing U d) (fourCornerCoefficientIso f d) ≅
      proEtaleRingModulePullback f ((adicLisseRingSystem V d.ideal).obj (op n))
          ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n) ⋙
        fourCornerRestrict U (adicDatumProjection U d n),
      ∀ M : proEtaleRingModules V ((adicLisseRingSystem V d.ideal).obj (op n)),
        (proEtaleRingModuleAdjunction f (adicDatumRing V d)
          (adicDatumRing U d) (fourCornerCoefficientIso f d)).homEquiv _ _ (e.hom.app M) =
          (fourCornerRestrict V (adicDatumProjection V d n)).map
            ((proEtaleRingModuleAdjunction f
              ((adicLisseRingSystem V d.ideal).obj (op n))
              ((adicLisseRingSystem U d.ideal).obj (op n))
              (fourCornerFiniteIso f d n)).unit.app M) ≫
            (fourCornerRestrictionPushforward_exists f d n).exists.choose.inv.app
              ((proEtaleRingModulePullback f
                ((adicLisseRingSystem V d.ideal).obj (op n))
                ((adicLisseRingSystem U d.ideal).obj (op n))
                (fourCornerFiniteIso f d n)).obj M) := by
  sorry

/-- The restriction/pullback identification specified by its adjunction-unit formula.
Source: blueprint order 1342; Stacks 03EK
(blueprint: def-weil-pbc-four-corners). -/
def fourCornerRestrictionPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  (fourCornerRestrictionPullback_exists f d n).exists.choose

/-- The same finite-linear tensor comparison with its scalars restricted to A_U.
Source: blueprint order 1342; Stacks 07A4
(blueprint: def-weil-pbc-four-corners). -/
def fourCornerOrdinaryComparisonUnderlying {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ)
    (M : proEtaleRingModules V (adicDatumRing V d)) :
    (adicDatumOrdinaryReduction U d n).obj
        ((proEtaleRingModulePullback f (adicDatumRing V d)
          (adicDatumRing U d) (fourCornerCoefficientIso f d)).obj M) ⟶
      (proEtaleRingModulePullback f (adicDatumRing V d)
        (adicDatumRing U d) (fourCornerCoefficientIso f d)).obj
          ((adicDatumOrdinaryReduction V d n).obj M) :=
  (fourCornerRestrict U (adicDatumProjection U d n)).map
      ((fourCornerOrdinaryComparison f d n).hom.app M) ≫
    (fourCornerRestrictionPullback f d n).inv.app
      ((completedConstantExtension V (adicDatumProjection V d n)).obj M)

/-- The specified tensor comparison commutes with every quotient transition.
This is an equality of A_U-linear maps; the individual comparison before restriction
retains its P_n-action. Applied in each degree of a flat K-flat representative, this
is the equality of the two representative maps for the derived comparisons.
Source: blueprint order 1342, quotient-transition paragraph; Stacks 07A4
(blueprint: def-weil-pbc-four-corners).
Proof: the normalized adjunction units compute both comparisons by the balanced tensor
map. Either composite sends a local pure tensor to the pulled-back module element
tensored with the quotient image of its scalar. Pure tensors generate locally, so
sheafification gives equality. Degreewise equality gives equality of chain maps;
localization and fourCornerReductionPullback_exists identify their images with the
specified derived comparisons. This includes equal and nonconsecutive indices. -/
theorem fourCornerOrdinaryComparison_transition {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b)
    (M : proEtaleRingModules V (adicDatumRing V d)) :
    fourCornerOrdinaryComparisonUnderlying f d b M ≫
        (proEtaleRingModulePullback f (adicDatumRing V d)
          (adicDatumRing U d) (fourCornerCoefficientIso f d)).map
            ((adicDatumOrdinaryTransition V d (op b) (op a) (homOfLE h).op).app M) =
      (adicDatumOrdinaryTransition U d (op b) (op a) (homOfLE h).op).app
          ((proEtaleRingModulePullback f (adicDatumRing V d)
            (adicDatumRing U d) (fourCornerCoefficientIso f d)).obj M) ≫
        fourCornerOrdinaryComparisonUnderlying f d a M := by
  sorry

/-- Apply the ordinary tensor comparison degree by degree, with its chain-map law.
Source: blueprint four corners; Stacks 07A4 (blueprint: def-weil-pbc-four-corners). -/
def fourCornerOrdinaryComplexComparison {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ)
    (P : CochainComplex
      (proEtaleRingModules V (adicDatumRing V d)) ℤ) :
    (fourCornerChangeComplex U (adicDatumProjection U d n)).obj
      (((proEtaleRingModulePullback f (adicDatumRing V d)
        (adicDatumRing U d)
          (fourCornerCoefficientIso f d)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
    ((proEtaleRingModulePullback f ((adicLisseRingSystem V d.ideal).obj (op n))
      ((adicLisseRingSystem U d.ideal).obj (op n))
        (fourCornerFiniteIso f d n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((fourCornerChangeComplex V
            (adicDatumProjection V d n)).obj P) where
  f i := (fourCornerOrdinaryComparison f d n).hom.app (P.X i)
  comm' i j _ := ((fourCornerOrdinaryComparison f d n).hom.naturality (P.d i j)).symm
/-- The canonical comparison retains quotient coefficients and is characterized on every
flat-term K-flat representative by the specified ordinary tensor map.
Source: blueprint four corners; Stacks 07A4, 0G7E, 06YY
(blueprint: def-weil-pbc-four-corners).
Proof: choose a degreewise surjective flat-term K-flat resolution. Pullback preserves
K-flatness and flat terms by the ringed-topos tensor comparison, so both derived scalar
extensions are computed by the displayed ordinary tensors. The adjunction formula for
fourCornerOrdinaryComparison is the balanced pure-tensor map and is linear over the
finite quotient by fourCornerProjectionComm. Its inverse is tensor reassociation.
The complex maps commute with quasi-isomorphisms between K-flat resolutions; localization
gives the natural isomorphism and its normalization square below. All four normalization
maps are invertible on these representatives, so the square and essential surjectivity
of K-flat representatives determine the comparison uniquely. For a quotient transition,
both ordinary composites send a pure tensor to the pulled-back element tensored with
its quotient image; the resulting equality descends through the same localization. -/
theorem fourCornerReductionPullback_exists {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    ∃! e : fourCornerPullback f d ⋙
        adicDatumExtension U (adicDatumProjection U d n) ≅
      adicDatumExtension V (adicDatumProjection V d n) ⋙
        fourCornerFinitePullback f d n,
      ∀ P : CochainComplex
        (proEtaleRingModules V (adicDatumRing V d)) ℤ,
        CochainComplex.IsAcyclicTensorKFlat
          (R := adicDatumRing V d) P →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology V)
          (R := adicDatumRing V d) (F := P.X i)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (fourCornerFinitePullback f d n).map
              (adicDatumComplexCounit V
                (adicDatumProjection V d n) P) ≫
            (proEtaleRingDerivedPullbackFactors f ((adicLisseRingSystem V d.ideal).obj (op n))
              ((adicLisseRingSystem U d.ideal).obj (op n)) (fourCornerFiniteIso f d n)).hom.app
                ((fourCornerChangeComplex V
            (adicDatumProjection V d n)).obj P) =
          (adicDatumExtension U (adicDatumProjection U d n)).map
              ((proEtaleRingDerivedPullbackFactors f
                (adicDatumRing V d)
                (adicDatumRing U d)
                  (fourCornerCoefficientIso f d)).hom.app P) ≫
            adicDatumComplexCounit U (adicDatumProjection U d n)
              (((proEtaleRingModulePullback f (adicDatumRing V d)
                (adicDatumRing U d)
                  (fourCornerCoefficientIso f d)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map (fourCornerOrdinaryComplexComparison f d n P) := by
  sorry
/-- The specified reduction/pullback identification in the finite coefficient category.
Source: blueprint four corners; Stacks 07A4 (blueprint: def-weil-pbc-four-corners). -/
def fourCornerReductionPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  (fourCornerReductionPullback_exists f d n).exists.choose
/-- E tensor P_n is identified with E_n by the specified comparison at K.
Source: blueprint four corners; Stacks 07A4 (blueprint: def-weil-pbc-four-corners). -/
def fourCornerEReductionIso {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A)
    (K : fourCornerDerived V (adicDatumRing V d)) (n : ℕ) :
    (adicDatumReduction U d n).obj ((fourCornerPullback f d).obj K) ≅
      (fourCornerFinitePullback f d n).obj ((adicDatumReduction V d n).obj K) :=
  (fourCornerReductionPullback f d n).app K
/-- The four objects A_n,B_n,C_n,D_n in the finite coefficient derived category.
The exponent represented by n is n+1, so every positive level occurs exactly once.
C represents K; the completeness condition is invertibility of its actual Koszul
completion unit, transported along eC. E uses ordinary, uncompleted pullback.
Source: blueprint order 1342 (blueprint: def-weil-pbc-four-corners). -/
def properBaseChangeFourCorners
    {X' X Y' Y : Scheme.{t}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (_sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (d : ProEtaleAdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : fourCornerDerived X (adicDatumRing X d))
    (C : CochainComplex (proEtaleRingModules X (adicDatumRing X d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC) (n : ℕ) :
    fourCornerDerived Y' ((adicLisseRingSystem Y' d.ideal).obj (op n)) ×
      fourCornerDerived Y' ((adicLisseRingSystem Y' d.ideal).obj (op n)) ×
      fourCornerDerived Y' ((adicLisseRingSystem Y' d.ideal).obj (op n)) ×
      fourCornerDerived Y' ((adicLisseRingSystem Y' d.ideal).obj (op n)) :=
  ((fourCornerFinitePullback g d n).obj
      ((adicDatumReduction Y d n).obj ((fourCornerPushforward f d).obj K)),
    (fourCornerFinitePullback g d n).obj
      ((fourCornerFinitePushforward f d n).obj ((adicDatumReduction X d n).obj K)),
    (adicDatumReduction Y' d n).obj
      ((fourCornerPushforward f' d).obj ((fourCornerPullback g' d).obj K)),
    (fourCornerFinitePushforward f' d n).obj
      ((fourCornerFinitePullback g' d n).obj ((adicDatumReduction X d n).obj K)))
end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Canonical closed calculus for the recorded ringed-site internal Hom

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 08J9, 08JB and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
The original tensor, restriction and exactness statements are retained by public import.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.SignedRingedHom

/-- The module category of the ringed site.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev Modules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

/-- The sheafified tensor, before deriving.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleMonoidal : MonoidalCategory (Modules J R) :=
  SheafOfModules.monoidalCategory R

/-- The ordinary symmetry of module sheaves.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleSymmetric : SymmetricCategory (Modules J R) :=
  SheafOfModules.symmetricCategory R

/-- The sheaf tensor--Hom adjunction.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleClosed : MonoidalClosed (Modules J R) :=
  SheafOfModules.monoidalClosed (R := R)

/-- The module category is Grothendieck abelian.
Source: Stacks 07A5 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: sheafification is exact and module sheaves have the local free generators. -/
instance moduleGrothendieck : IsGrothendieckAbelian.{u} (Modules J R) :=
  SheafOfModules.isGrothendieckAbelian _

/-- Additivity of tensoring module sheaves in either variable.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: tensor is the sheafification of the sectionwise module tensor, whose
maps are additive in each factor; sheafification is additive. -/
theorem moduleMonoidalPreadditive : MonoidalPreadditive (Modules J R) := by
  sorry

attribute [instance] moduleMonoidalPreadditive

/-- Functorial flat covers used to construct the ordinary K-flat derived tensor.
Source: Stacks 06YL and 06YS, local free covers and their functorial direct sums
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: take the sum of the free modules extended by zero from site objects, indexed
by all local sections of the module. The evaluation is an epimorphism, each free
summand is flat, and sums of flat modules are flat. A module map sends the summand
indexed by a section to the summand indexed by its image. This gives a functorial
flat cover, and hence the flat resolutions used in the tensor--Hom construction. -/
theorem moduleFlatResolution : Abelian.HasFunctorialFlatResolution (Modules J R) := by
  sorry

attribute [instance] moduleFlatResolution

/-- The unbounded module derived category, with its small Hom universe.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev D [HasDerivedCategory.{u} (Modules J R)] := DerivedCategory (Modules J R)

/-- The countable-colimit convention used by the native derived tensor API.
Source: Stacks 06YS (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleCountableColimits : HasColimitsOfSize.{0, 0} (Modules J R) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} (Modules J R)

variable [HasDerivedCategory.{u} (Modules J R)]

/-- The ordinary K-flat derived monoidal structure, with coherences descended
from total tensor complexes.
Source: Stacks 06YS, 08J9
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance derivedMonoidal : MonoidalCategory (D J R) :=
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory (Modules J R)

/-- Cache the native localization tensor map with the same monoidal instance.
Source: Stacks 06YS (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance localizationLaxMonoidal :
    (DerivedCategory.Q : CochainComplex (Modules J R) ℤ ⥤ D J R).LaxMonoidal :=
  DerivedCategory.laxMonoidalQ (Modules J R)

/-- The signed tensor shifts, descended from ordinary totalization.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance derivedTensorShift : (curriedTensor (D J R)).CommShift₂Int :=
  DerivedCategory.commShift₂CurriedTensor (Modules J R)

/-- The native derived tensor and its explicit localization implementation agree.
Source: Stacks 06YS, 08J9
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: both are the localization monoidal structure induced by the same K-flat
left derivability structure and the same ordinary total tensor. Unfold the
native instance and identify the localization structure fields. -/
theorem derivedMonoidal_eq_localization :
    derivedMonoidal J R =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules J R) (ComplexShape.up ℤ)) := by
  sorry


/-- The recorded derived internal Hom, with independent-universe implementation
specialized to this small site.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def homFunctor : (D J R)ᵒᵖ × D J R ⥤ D J R :=
  derivedInternalHomOfUniverses.{u, u, u, u} J R

/-- The unary recorded Hom functor.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable abbrev hom (K : D J R) : D J R ⥤ D J R :=
  Prod.sectR (op K) (D J R) ⋙ homFunctor J R

/-- The ordinary Koszul braiding descended from complexes.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance derivedBraiding : BraidedCategory (D J R) :=
  Eq.mp (congrArg (fun m ↦ @BraidedCategory (D J R) _ m)
    (derivedMonoidal_eq_localization J R).symm)
    (DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules J R) (ComplexShape.up ℤ)))

set_option backward.isDefEq.respectTransparency false

/-- The total tensor used in the representative model is the native complex tensor.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: both are the totalization of the curried sheaf tensor, with the same
summands, differential and Koszul sign. Unfold the two totalizations. -/
theorem totalTensor_eq_native (P L : CochainComplex (Modules J R) ℤ) :
    (WeilConjectures.coefficientTotalTensor.{u, u, u} J R).obj (P, L) = P ⊗ L := by
  sorry

/-- The explicit identification of the two ordinary total-tensor implementations.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def totalTensorNativeIso (P L : CochainComplex (Modules J R) ℤ) :
    (WeilConjectures.coefficientTotalTensor.{u, u, u} J R).obj (P, L) ≅ P ⊗ L :=
  eqToIso (totalTensor_eq_native J R P L)

/-- The tensor--Hom adjunction is uniquely fixed by ordinary evaluation on
K-flat representatives, for the actual derived monoidal structure.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: compute the tensor by a K-flat source and Hom by a K-injective target.
Componentwise evaluation identifies the two Hom sets by ordinary currying.
The Hom differential and total-tensor Koszul differential agree under this
identification. Quasi-isomorphism invariance descends the equivalence through
the two localizations. It is natural also in the source, giving a closed
structure S. The total-tensor localization comparison is its representative
model. Conversely that model fixes uncurrying on every K-flat representative;
these representatives present the derived category, so it fixes the Hom
bijections everywhere. An adjunction is determined by its Hom bijections. -/
theorem normalizedAdjunction_existsUnique :
    ∃! S : WeilConjectures.CoefficientClosedStructure (homFunctor J R),
      ∃ (h : S.monoidal = derivedMonoidal J R)
        (M : WeilConjectures.CoefficientTensorModels.{u, u, u, u} J R S),
        ∀ P L, (M.comparison.app (P, L)).hom ≫
          eqToHom (congrArg (fun (m : MonoidalCategory (D J R)) ↦
            @MonoidalCategory.tensorObj (D J R) _ m.toMonoidalCategoryStruct
            (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj L.obj)) h) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj ≫
          DerivedCategory.Q.map (totalTensorNativeIso J R P.obj L.obj).inv = 𝟙 _ := by
  sorry

/-- The unique evaluation-normalized adjunction, not an arbitrary chosen adjoint.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def adjunction (K : D J R) : tensorRight K ⊣ hom J R K :=
  Eq.mp (congrArg (fun (m : MonoidalCategory (D J R)) ↦ ∀ P : D J R,
      @MonoidalCategory.tensorRight (D J R) _ m P ⊣ hom J R P)
    (normalizedAdjunction_existsUnique J R).choose_spec.1.choose)
    (normalizedAdjunction_existsUnique J R).choose.adjunction K

/-- Moving a shift between the two tensor inputs, using ordinary totalization.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def tensorParameterShiftIso (K : D J R) (s : ℤ) (X : D J R) :
    X ⊗ K⟦s⟧ ≅ X⟦s⟧ ⊗ K :=
  (((curriedTensor (D J R)).obj X).commShiftIso s).app K ≪≫
    ((((curriedTensor (D J R)).flip.obj K).commShiftIso s).app X).symm

/-- Naturality of the ordinary tensor shift comparison.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: the second-input total-tensor shift is natural in the first input by the
bifunctor shift structure. The inverse first-input shift is natural by its
functor commutation with shifts. Compose these two naturality equations. -/
theorem tensorParameterShift_naturality (K : D J R) (s : ℤ)
    (X Y : D J R) (f : X ⟶ Y) :
    (tensorRight (K⟦s⟧)).map f ≫ (tensorParameterShiftIso J R K s Y).hom =
      (tensorParameterShiftIso J R K s X).hom ≫
        (shiftFunctor (D J R) s ⋙ tensorRight K).map f := by
  sorry

/-- The natural tensor parameter shift comparison.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def tensorParameterShift (K : D J R) (s : ℤ) :
    tensorRight (K⟦s⟧) ≅ shiftFunctor (D J R) s ⋙ tensorRight K :=
  NatIso.ofComponents (tensorParameterShiftIso J R K s)
    (fun {X Y} f ↦ tensorParameterShift_naturality J R K s X Y f)

/-- The signed source shift of internal Hom, defined as the unique adjunction
mate of the ordinary total-tensor shift. It has the signed reindexing of the
Hom complex; changing its normalization by a scalar depending only on s
multiplies every component by that same scalar.
Source: Stacks 0A8X and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def sourceShift (K : D J R) (s : ℤ) :
    hom J R (K⟦s⟧) ≅ hom J R K ⋙ shiftFunctor (D J R) (-s) :=
  (adjunction J R (K⟦s⟧)).rightAdjointUniq
    (((shiftEquiv (D J R) s).toAdjunction.comp (adjunction J R K)).ofNatIsoLeft
      (tensorParameterShift J R K s).symm)

end CategoryTheory.SignedRingedHom

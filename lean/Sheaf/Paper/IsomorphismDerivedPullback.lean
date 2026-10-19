/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IntegralReductionTowerWellDefined
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.IsomorphismReductionTower
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.PurInverseImageTensorHom
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # Isomorphism pullback and termwise inverse image

Source: Weil blueprint, ordinary compact cohomology, order 1510, coefficient-object
paragraph; Stacks Project, Tags 015F, 06YS and 08TC; Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-weil-isomorphism-derived-pullback).

The integral structure isomorphism is fixed by all its finite quotient projections.
Termwise inverse image transports the module action by restriction along its inverse;
it does not apply a completed tensor product to each term.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed coefficient comparison is uniquely determined by its composites with
all finite quotient projections. These equations specify exactly the inverse-limit
comparison followed by the limit of the canonical constant-coefficient comparisons.
Source: blueprint order 1510; Stacks Tags 09A5 and 00WX
(blueprint: lem-weil-isomorphism-derived-pullback).
Proof: by lem-weil-proetale-isomorphism-inverse-image, inverse image preserves limits.
Its canonical limit comparison followed by the limit of the finite constant-ring
isomorphisms gives the required isomorphism. Naturality of those constant comparisons
makes a morphism of towers. Composing with the nth projection gives the displayed
identity. Joint monicity of limit projections proves uniqueness, also for inverses. -/
theorem isomorphismCompletedCoefficientComparison_existsUnique
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l E Y) ≅
        completedIntegralCommRingSheafUnrestricted l E X,
      ∀ n : ℕ, c.hom ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
        (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
          proEtaleCoefficientInverseImageMap g (Padic.coefficientExtensionRing l E (n + 1)) := by
  sorry

/-- The uniquely normalized completed coefficient isomorphism c_O_E.
Source: blueprint order 1510; Stacks Tags 09A5 and 00WX
(blueprint: lem-weil-isomorphism-derived-pullback). -/
def isomorphismCompletedCoefficientComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ≅
      completedIntegralCommRingSheafUnrestricted l E X :=
  (isomorphismCompletedCoefficientComparison_existsUnique l E g).exists.choose

/-- Inverse image of module sheaves, with the scalar action transported through c.
The inverse image is the recorded module inverse image, and restriction along c.inv
makes it an S-module without replacing it by a tensor model.
Source: Stacks Tags 00YV and 03D2; blueprint order 1510
(blueprint: lem-weil-isomorphism-derived-pullback). -/
def isomorphismTermwiseModuleInverseImage {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModules Y R ⥤ proEtaleRingModules X S :=
  proEtaleModuleInverseImage g R ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)

/-- Exactness of the termwise coefficient transport used in this node.
Source: Stacks Tag 015F; blueprint order 1510
(blueprint: lem-weil-isomorphism-derived-pullback).
Proof: lem-weil-proetale-isomorphism-inverse-image identifies inverse image with
relabelling along the covering-preserving site equivalence. Relabel the action maps
as well as the underlying abelian sheaves. Restriction along c.inv only transports
the scalars, so it preserves sums of maps, kernels and cokernels. Relabelling back
is its inverse, proving exactness and additivity. -/
theorem isomorphismTermwiseModuleInverseImage_exact {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (isomorphismTermwiseModuleInverseImage g R S c).Additive ∧
      PreservesFiniteLimits (isomorphismTermwiseModuleInverseImage g R S c) ∧
      PreservesFiniteColimits (isomorphismTermwiseModuleInverseImage g R S c) := by
  set_option backward.defeqAttrib.useBackward false in
    set_option backward.isDefEq.respectTransparency false in
      let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
        integralCoefficientAbSheafify.{u, u} Y
      let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
        integralCoefficientAbSheafify.{u, u} X
      let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
        integralCoefficientAbLocallyBijective.{u, u} Y
      let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
        integralCoefficientAbLocallyBijective.{u, u} X
      let A := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
      let B := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
      let T := isomorphismTermwiseModuleInverseImage g R S c
      let V := SheafOfModules.toSheaf B
      obtain ⟨e⟩ := (proEtale_moduleInverseImage_comparison g R).1
      let d : T ⋙ V ≅ SheafOfModules.toSheaf A ⋙
          proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} := e
      let := (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g AddCommGrpCat.{u + 1}).1
      let : PreservesFiniteLimits (T ⋙ V) := preservesFiniteLimits_of_natIso d.symm
      let : PreservesFiniteColimits (T ⋙ V) := preservesFiniteColimits_of_natIso d.symm
      let : (T ⋙ V).Additive := Functor.additive_of_preserves_binary_products _
      let : T.Additive := Functor.additive_of_comp_faithful T V
      exact ⟨inferInstance, preservesFiniteLimits_of_reflects_of_preserves T V,
        preservesFiniteColimits_of_reflects_of_preserves T V⟩

/-- Additivity for termwise inverse image. Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
instance isomorphismTermwiseModuleInverseImage_additive {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (isomorphismTermwiseModuleInverseImage g R S c).Additive :=
  (isomorphismTermwiseModuleInverseImage_exact g R S c).1

/-- Left exactness for termwise inverse image. Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
instance isomorphismTermwiseModuleInverseImage_preservesFiniteLimits {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    PreservesFiniteLimits (isomorphismTermwiseModuleInverseImage g R S c) :=
  (isomorphismTermwiseModuleInverseImage_exact g R S c).2.1

/-- Right exactness for termwise inverse image. Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
instance isomorphismTermwiseModuleInverseImage_preservesFiniteColimits {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    PreservesFiniteColimits (isomorphismTermwiseModuleInverseImage g R S c) :=
  (isomorphismTermwiseModuleInverseImage_exact g R S c).2.2

/-- Termwise finite inverse image on the derived localization, with c_A the canonical
constant-ring comparison. The index n denotes the positive exponent n+1.
Source: blueprint order 1510; Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
def isomorphismFiniteTermwiseInverseImage {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) :=
  (isomorphismTermwiseModuleInverseImage g
    (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleIsoConstantRingComparison g
      (CommRingCat.of
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))).mapDerivedCategory

/-- Termwise integral inverse image in the ambient derived category over the completed
coefficient sheaf. The scalar action uses the specified limit comparison c_O_E.
Source: blueprint order 1510; Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
def isomorphismIntegralTermwiseInverseImage {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
  (isomorphismTermwiseModuleInverseImage g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (isomorphismCompletedCoefficientComparison l E g)).mapDerivedCategory

/-- Finite coefficients: termwise inverse image preserves bounded constructibility,
and the specified derived pullback is naturally isomorphic to it on that full
subcategory. The last clause spells out the coefficient object in degree zero.
The natural isomorphism is stated in the full constructible target category.
Source: blueprint order 1510; Stacks Tags 015F and 06YS
(blueprint: lem-weil-isomorphism-derived-pullback).
Proof:
1. Relabelling by lem-weil-proetale-isomorphism-inverse-image transports module
   actions and is exact, so cohomology commutes with inverse image by
   lem-weil-pbc-exact-functor-complex-cohomology. Its termwise localization is
   triangulated by lem-sf-exact-functor-derived-triangulated.
2. For a K-flat resolution P → K (lem-pc-kflat-resolution), multiplication
   m tensor a ↦ a m identifies module pullback of P with inverse image of P;
   its inverse is m ↦ m tensor 1. Exactness makes inverse image of P → K a
   quasi-isomorphism. These multiplication maps are natural in chain maps and
   descend through localization, giving the natural comparison with
   def-weil-derived-pullback-tensor-hom independently of resolutions.
3. Pull back the finite constructible partitions and their trivializing covers
   through the scheme isomorphism. The constant finite stalk modules are unchanged.
   Exactness preserves the finite cohomological support, giving constructibility
   as defined in def-weil-finite-torsion-constructibility.
4. Apply the comparison to the finite regular coefficient module in degree zero;
   lem-weil-constant-coefficient-objects-constructible supplies its membership. -/
theorem isomorphismFiniteDerivedPullback_termwise {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ) :
    ∃ h : ∀ K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)),
      intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y K →
        intrinsicFiniteTorsionConstructible l E (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n)) X ((finiteDerivedPullback l E n g).obj K) ∧
          intrinsicFiniteTorsionConstructible l E (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n)) X
            ((isomorphismFiniteTermwiseInverseImage l E g n).obj K),
    Nonempty
      ((intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) X).lift
        ((intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y).ι ⋙ finiteDerivedPullback l E n g)
        (fun K ↦ (h K.obj K.property).1) ≅
      (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) X).lift
        ((intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y).ι ⋙
            isomorphismFiniteTermwiseInverseImage l E g n)
        (fun K ↦ (h K.obj K.property).2)) ∧
    Nonempty ((finiteDerivedPullback l E n g).obj (finiteConstantCoefficientObject l E Y n) ≅
      (isomorphismFiniteTermwiseInverseImage l E g n).obj
        (finiteConstantCoefficientObject l E Y n)) := by
  sorry

/-- Completed integral coefficients: termwise inverse image preserves the recorded
uniformly bounded constructible derived-complete subcategory, and agrees naturally
there with the specified completed derived pullback. The last clause is its
specialization to the completed coefficient sheaf in degree zero.
The natural isomorphism has source the recorded constructible integral pullback
and is stated in the full category D^b_c(X,O_E).
Source: blueprint order 1510; Bhatt--Scholze Definition 3.5.2; Stacks Tag 08TC
(blueprint: lem-weil-isomorphism-derived-pullback).
Proof:
1. Use the completed comparison fixed by the finite quotient projections. Exact
   relabelling transports module actions, tensor products and cohomology. It
   preserves flat terms and K-flatness by relabelling an acyclic test complex back.
2. Choose a K-flat resolution with flat terms (lem-pc-kflat-resolution). Tensor
   relabelling and the coefficient projection equations identify every finite
   reduction with the reduction of the relabelled resolution, including the maps
   x ↦ x tensor 1 and x tensor a ↦ x tensor rho(a). The identifications respect
   resolution comparisons by lem-weil-integral-reduction-tower-well-defined.
3. Exact countable products (lem-weil-proetale-countable-products-exact) represent
   derived products by lem-weil-derived-limit-existence. For B(P)=product Res_n P_n,
   C(P)=Cone(1-s)[-1] has differential d(y,x)=(-d y-(1-s)x,d x). The quotient
   maps a:P→B(P) satisfy (1-s)a=0, so x ↦ (0,a(x)) is the canonical comparison.
   The L=E case of lem-weil-finite-free-completed-scalar-comparison says this
   comparison eta is natural and invertible on derived-complete objects.
4. Relabelling both coordinates commutes with this cone and its product
   projections, giving theta:Lg* K ≅ F C(P) for the actual construction of
   def-pur-integral-derived-operations. The normalized descent in
   lem-pur-integral-operations-well-defined gives naturality independent of
   resolutions. Compose theta with the inverse of F(eta) to get lambda.
5. Transport the defining Roos triangle and its quotient-unit first map to show
   completeness of FK. Every reduction is the finite inverse image of the old
   reduction. The finite case preserves constructibility and each vanishing
   degree, so the same single interval works for all reductions, exactly as in
   def-weil-derived-complete-integral-detailed. Fullness gives the required iso.
6. Specialize to the completed regular module in degree zero, whose membership
   is lem-weil-constant-coefficient-objects-constructible. Its auxiliary finite
   field can be chosen of any prime characteristic different from l; it imposes
   no structure morphism or restriction on X or Y. -/
theorem isomorphismIntegralDerivedPullback_termwise {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ h : ∀ K : DerivedCategory (scalarReductionSource l E Y),
      sfIntegralConstructible l E Y K →
        sfIntegralConstructible l E X ((isomorphismIntegralTermwiseInverseImage l E g).obj K),
    Nonempty (constructibleIntegralPullback l E g ≅
      (sfIntegralConstructible l E X).lift
        ((sfIntegralConstructible l E Y).ι ⋙ isomorphismIntegralTermwiseInverseImage l E g)
        (fun K ↦ h K.obj K.property)) ∧
    Nonempty ((integralDerivedPullback l E g).obj (integralConstantCoefficientObject l E Y) ≅
      (isomorphismIntegralTermwiseInverseImage l E g).obj
        (integralConstantCoefficientObject l E Y)) := by
  sorry

end WeilConjectures

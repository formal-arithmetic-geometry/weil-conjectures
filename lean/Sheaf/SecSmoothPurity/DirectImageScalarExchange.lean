/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Scalar extension and direct-image geometric exchange

Source: literature/stacks-project/sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal` (blueprint: lem-fix-direct-image-scalar-exchange).

All functors and comparisons below specialize existing canonical constructions to
constant coefficients. No functor, adjunction, tensor comparison or square comparison
is supplied as an arbitrary parameter.
- `directImageScalarExtension` is the universal K-flat scalar extension.
- `directImageScalarPullbackIso` is its canonical tensor/inverse-image comparison.
- `directImageScalarComparison` is the mate defining chi.
- `directImageConstantExchange` is the existing ambient ringed exchange for constants.
- `directImageScalarExchange` is the equality of the two specified composites.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The universal derived extension along the actual map of constant ring sheaves.
The defining functor carries its universal counit and K-flat tensor computation.
Source: Stacks Tag 06YY (blueprint: lem-fix-direct-image-scalar-exchange). -/
abbrev directImageScalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B :=
  Scheme.proEtaleRingDerivedExtension (Scheme.proEtaleConstantRingMap (T := T) φ)

/-- Canonical constant-coefficient derived direct image, using its normalized adjunction.
This is a specialization of the existing ordinary, uncompleted ringed direct image.
Source: Stacks Tags 07A5 and 07A6 (blueprint: lem-fix-direct-image-scalar-exchange). -/
abbrev directImageConstantPush (A : Type u) [CommRing A]
    {T V : Scheme.{u}} (f : T ⟶ V) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory V A :=
  Scheme.proEtaleRingDerivedDirectImage f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)

/-- The canonical scalar/inverse-image isomorphism. The existing reduction/pullback
construction is the inverse mate of the exact restriction comparison, whose ordinary
map is fixed by identity on sections. Its tensor-unit normalization is the balancing
map on flat K-flat representatives, sending the pullback of x tensor b to the
pullback of x tensor b. Naturality of the constant-section comparison supplies the
coefficient square, with no extra hypothesis.
Source: Stacks Tags 03EL, 06YY and 0D6D
(blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageScalarPullbackIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V) :
    directImageScalarExtension φ V ⋙ Scheme.proEtaleConstantRingDerivedPullback B f ≅
      Scheme.proEtaleConstantRingDerivedPullback A f ⋙ directImageScalarExtension φ T :=
  Scheme.proEtaleReductionPullbackIso f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The direct-image scalar map chi is the mate of the specified tensor comparison,
under the canonical tensor-unit-normalized geometric adjunctions.
Source: Stacks Tag 0E47 (blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageScalarComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V) :
    directImageConstantPush A f ⋙ directImageScalarExtension φ V ⟶
      directImageScalarExtension φ T ⋙ directImageConstantPush B f :=
  (mateEquiv
    (Scheme.proEtaleRingDerivedAdjunction f
      (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
      (Scheme.proEtaleConstantRingComparison f A))
    (Scheme.proEtaleRingDerivedAdjunction f
      (Scheme.proEtaleConstantRing V B) (Scheme.proEtaleConstantRing T B)
      (Scheme.proEtaleConstantRingComparison f B))
    (directImageScalarPullbackIso φ f).hom).natTrans

/-- The ambient ringed exchange specialized to the canonical constant rings.
Its pullback square is built from the canonical composition comparisons. The two
composite coefficient identifications are the constant comparison for the same
scheme map; the proof below supplies that compatibility, rather than assuming it.
Source: Stacks Tags 07A7, 0D6D and 0E47
(blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageConstantExchange (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    directImageConstantPush A f ⋙ Scheme.proEtaleConstantRingDerivedPullback A g ⟶
      Scheme.proEtaleConstantRingDerivedPullback A h ⋙ directImageConstantPush A f' :=
  Scheme.proEtaleAmbientRingedExchange sq
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing Y A)
    (Scheme.proEtaleConstantRing X' A) (Scheme.proEtaleConstantRing Y' A)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison g A)
    (Scheme.proEtaleConstantRingComparison h A)
    (Scheme.proEtaleConstantRingComparison f' A)
    ((heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq h f A)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ Scheme.proEtaleConstantRingComparison q A)
        sq.w).trans
          (heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm))

/-- Scalar extension respects direct-image geometric exchange, naturally in M.
Source: literature/stacks-project/sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal` (blueprint: lem-fix-direct-image-scalar-exchange).

Proof:
1. Choose flat-term K-flat resolutions using lem-pc-kflat-resolution. The scalar
   functor is computed by ordinary tensor by lem-pur-derived-change-of-rings.
   The tensor/inverse-image comparison of
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback sends the inverse image of
   q tensor b to the inverse image of q tensor b. The composition comparisons of
   lem-weil-pbc-proetale-derived-pullback-composition have their ordinary termwise
   normalization. Thus the two routes around the coefficient/pullback cube agree
   on every pure tensor. Those tensors locally generate, so they agree on complexes
   and descend to an equality of natural transformations on the derived category.
2. By def-weil-pbc-adjunction-mate and def-weil-pbc-ambient-ringed-exchange, chi is
   the mate of lambda and Ex is the mate of the canonical inverse-image square.
   These are exactly the definitions above, with the specified adjunctions.
3. Apply clause 1 of lem-weil-pbc-mate-pasting first with left adjoints f_A^-1,
   f_B^-1, f'_B^-1 and squares lambda_f, theta_B; then with f_A^-1, f'_A^-1,
   f'_B^-1 and squares theta_A, lambda_f'. The top/bottom functors are respectively
   (S_Y,S_X,g_B^-1,h_B^-1) and (g_A^-1,h_A^-1,S_Y',S_X'). Whiskering a square by
   sigma on its bottom and tau on its top whiskers its mate by R(sigma) and
   tau(R), as follows from the unit/counit formula and naturality. Taking
   sigma=lambda_h and tau=lambda_g identifies the resulting mates with the two
   displayed composites.
4. Equal squares from Step 1 have equal mates under the same adjunctions. Evaluate
   that equality at M. All constituent maps are natural transformations, giving
   naturality in M. This uses only K-flat computations, exact inverse image and
   adjunctions; no properness, boundedness, constructibility, Tor-amplitude or
   flatness of the ring map is needed. -/
theorem directImageScalarExchange
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare h f' f g)
    (M : Scheme.proEtaleDerivedCategory X A) :
    (Scheme.proEtaleConstantRingDerivedPullback B g).map
        ((directImageScalarComparison φ f).app M) ≫
      (directImageConstantExchange B sq).app ((directImageScalarExtension φ X).obj M) ≫
      (directImageConstantPush B f').map ((directImageScalarPullbackIso φ h).hom.app M) =
    (directImageScalarPullbackIso φ g).hom.app ((directImageConstantPush A f).obj M) ≫
      (directImageScalarExtension φ Y').map ((directImageConstantExchange A sq).app M) ≫
      (directImageScalarComparison φ f').app
        ((Scheme.proEtaleConstantRingDerivedPullback A h).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ImmersionProjectionScalarNormalization
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.Algebra.Homology.RingedScalarHomExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ScalarSixDirectImage

import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ScalarSixCtf
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence

/-! # Scalar change of the specified immersion internal-adjunction pairing

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-tensor-hom.proof.md, The generator and It is v.
(blueprint: lem-sfb-scalar-internal-adjunction-pairing-change).

The exceptional adjunctions are supplied on the full localizing subcategories. No
finite-cohomological-dimension hypothesis on the standing field is imposed. The support
map and projection are exactly the closed-counit/open-tensor maps of the recorded
normalization. Right evaluation is left evaluation preceded by the Koszul symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The source Ra_* RHom(L,N) of the specified pairing, in ordinary uncompleted
module-derived categories. Source: The generator
(blueprint: lem-sfb-scalar-internal-adjunction-pairing-change). -/
abbrev immersionPairingSource (Λ : ScalarSixRing.{u}) {S X : Scheme.{u}} (f : S ⟶ X)
    (L N : DerivedCategory (supportModules Λ.X S)) :=
  (RootCoordinateFace.lower Λ.X f).obj (((derivedHom Λ.X S).obj (.op L)).obj N)

/-- The displayed tensor--Hom transpose: rho, ordinary counit tensor identity,
right evaluation, then the supplied exceptional counit. The initial symmetry converts
only the library's left-tensor adjunction convention to the displayed right pairing.
Source: The generator (blueprint: lem-sfb-scalar-internal-adjunction-pairing-change). -/
def immersionInternalAdjunction (Λ : ScalarSixRing.{u}) (k : Type u) [Field k]
    {S Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : S ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion i.left]
    (L N : DerivedCategory (supportModules Λ.X S.left))
    (M : DerivedCategory (supportModules Λ.X X.left))
    (ε : (sfbScalarCompactModel Λ j.left i.left).obj N ⟶ M) :
    immersionPairingSource Λ (j.left ≫ i.left) L N ⟶
      ((derivedHom Λ.X X.left).obj
        (.op ((sfbScalarCompactModel Λ j.left i.left).obj L))).obj M :=
  letI := DerivedCategory.braidedCategory' (supportModules Λ.X X.left)
  letI := DerivedCategory.braidedCategory' (supportModules Λ.X S.left)
  (derivedTensorHomAdjunction Λ.X
    ((sfbScalarCompactModel Λ j.left i.left).obj L)).homEquiv _ _
    ((β_ _ _).hom ≫ immersionProjection Λ k j i _ L ≫
      (sfbScalarCompactModel Λ j.left i.left).map
        (((RootCoordinateFace.adjunction Λ.X (j.left ≫ i.left)).counit.app _ ⊗ₘ 𝟙 L) ≫
          (β_ _ L).hom ≫ (derivedTensorHomAdjunction Λ.X L).counit.app N) ≫ ε)

/-- The evaluation-defined scalar Hom comparison, using the existing K-flat tensor
comparison inversely. Neither this arrow nor any Hom comparison is assumed invertible.
Source: It is v (blueprint: lem-sfb-scalar-internal-adjunction-pairing-change). -/
def immersionPairingScalarHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (L N : DerivedCategory (supportModules Λ.X X)) :
    (scalarSixChange a X).obj (((derivedHom Λ.X X).obj (.op L)).obj N) ⟶
      ((derivedHom Λ'.X X).obj (.op ((scalarSixChange a X).obj L))).obj
        ((scalarSixChange a X).obj N) :=
  letI := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  (derivedTensorHomAdjunction Λ'.X ((scalarSixChange a X).obj L)).homEquiv _ _
    (inv (((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).leftDerivedTensorComparison.app L).app
         (((derivedHom Λ.X X).obj (.op L)).obj N)) ≫
      (scalarSixChange a X).map ((derivedTensorHomAdjunction Λ.X L).counit.app N))

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
  {S Z X : Over (Spec (.of k))}
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : S ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion i.left]
  (hE : ∀ K, localizingClosureProEtale Λ.X S.left K →
    localizingClosureProEtale Λ.X X.left ((sfbScalarCompactModel Λ j.left i.left).obj K))
  (G : (localizingClosureProEtale Λ.X X.left).FullSubcategory ⥤
    (localizingClosureProEtale Λ.X S.left).FullSubcategory)
  (adj : localizingLowerShriek Λ.X (immersionCompactification j.left i.left) hE ⊣ G)
  (hE' : ∀ K, localizingClosureProEtale Λ'.X S.left K →
    localizingClosureProEtale Λ'.X X.left ((sfbScalarCompactModel Λ' j.left i.left).obj K))
  (G' : (localizingClosureProEtale Λ'.X X.left).FullSubcategory ⥤
    (localizingClosureProEtale Λ'.X S.left).FullSubcategory)
  (adj' : localizingLowerShriek Λ'.X (immersionCompactification j.left i.left) hE' ⊣ G')

/-- The supplied localizing right adjoint at a constructible test object, included
in the ambient derived category. No global Dctf-preservation hypothesis is imposed.
Source: The generator (blueprint: lem-sfb-scalar-internal-adjunction-pairing-change). -/
abbrev immersionPairingValue {Γ : ScalarSixRing.{u}} {A B : Scheme.{u}}
    (F : (localizingClosureProEtale Γ.X B).FullSubcategory ⥤
      (localizingClosureProEtale Γ.X A).FullSubcategory)
    (M : ConstantModelConstructibleFiniteTor Γ.X B) :=
  (F.obj ((scalarExceptionalInclusion Γ B).obj M)).obj

/-- The actual counit of the supplied localizing adjunction, with ambient endpoints.
Source: The generator (blueprint: lem-sfb-scalar-internal-adjunction-pairing-change). -/
def immersionPairingCounit (M : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (sfbScalarCompactModel Λ j.left i.left).obj (immersionPairingValue G M) ⟶ M.obj :=
  (adj.counit.app ((scalarExceptionalInclusion Λ X.left).obj M)).hom

/-- The exceptional coefficient mate at M, formed by transposing q_N inverse followed
by scalar extension of the exceptional counit. The inverse uses the immersion-specific
normalization theorem, so the general finite-cd theorem is not needed. This is the same
counit-defined beta, specialized to the supplied immersion adjunctions.
Source: It is v and det-prop-scalar-six-exceptional, definition of beta
(blueprint: lem-sfb-scalar-internal-adjunction-pairing-change). -/
def immersionPairingBeta (M : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (hN : (constantModelBoundedConstructible Λ.X S.left ⊓
      DerivedCategory.finiteTorAmplitude _) (immersionPairingValue G M)) :
    (scalarSixChange a S.left).obj (immersionPairingValue G M) ⟶
      immersionPairingValue G' ((scalarExceptionalChange ell k a ha X).obj M) :=
  let N : ConstantModelConstructibleFiniteTor Λ.X S.left := ⟨immersionPairingValue G M, hN⟩
  let TN := (scalarExceptionalInclusion Λ' S.left).obj
    ((scalarExceptionalChange ell k a ha S).obj N)
  let TM := (scalarExceptionalInclusion Λ' X.left).obj
    ((scalarExceptionalChange ell k a ha X).obj M)
  letI := ((immersionProjectionScalarNormalization ell k a ha j i).2.2.2.2.2.2.2.2 N).1
  ((adj'.homEquiv TN TM)
    (ObjectProperty.homMk
      (inv (immersionScalarMap a j.left i.left N.obj) ≫
        (scalarSixChange a X.left).map (immersionPairingCounit k j i hE G adj M)))).hom

/-- The two specified pairings are isomorphisms and satisfy the displayed coefficient
identity. The membership assumptions are exactly those in the node, for both coefficients;
L' and M' are the actual scalar extensions. The final equality has the specified ambient
source T_X Ra_*Q and target RHom(T_X E L,T_X M).

Source: The generator and It is v
(blueprint: lem-sfb-scalar-internal-adjunction-pairing-change).

Proof:
1. By sk-thm-sf-ctf-stability and det-prop-scalar-six-ctf the source, target and tensor
   test objects belong to Dctf, hence to the full localizing categories.
2. For a Dctf test C apply ordinary pullback/direct-image adjunction, tensor--Hom,
   the supplied exceptional adjunction and the invertible specified rho. Naturality
   of rho computes the resulting Hom bijection as postcomposition with the displayed I.
3. Test at its target to obtain a right inverse and at its source for the left inverse.
   Naturality of all the bijections makes I natural. Repeat for the primed objects.
4. Naturality of the ordinary counit and scalarDirectImageMateCoherence at Q identify
   alpha' a'^*(Ra'_*r gamma) with r T_S(alpha) c, where r = H(1,b) w.
5. The evaluation definition of w and tensor-comparison naturality identify the inside
   pairing with b T_S(ev) T_S(alpha tensor 1) mu inverse. Only tensorators are inverted.
6. Transpose the left route. Apply ImmersionProjectionScalarSquare, cancel mu inverse
   mu, use naturality of q, its equality with the normalized compact-support comparison,
   and the defining exceptional counit equation. The result is T_X(pairing) t_X inverse.
7. The evaluation definition of v gives the same transpose for the right route.
   Injectivity of the tensor--Hom bijection proves equality, without inverting w or v. -/
theorem scalarInternalAdjunctionPairingChange
    (L : ConstantModelConstructibleFiniteTor Λ.X S.left)
    (M : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (hN : (constantModelBoundedConstructible Λ.X S.left ⊓
      DerivedCategory.finiteTorAmplitude _) (immersionPairingValue G M))
    (hEL : (constantModelBoundedConstructible Λ.X X.left ⊓
      DerivedCategory.finiteTorAmplitude _) ((sfbScalarCompactModel Λ j.left i.left).obj L.obj))
    (hN' : (constantModelBoundedConstructible Λ'.X S.left ⊓
      DerivedCategory.finiteTorAmplitude _)
      (immersionPairingValue G' ((scalarExceptionalChange ell k a ha X).obj M)))
    (hEL' : (constantModelBoundedConstructible Λ'.X X.left ⊓
      DerivedCategory.finiteTorAmplitude _)
      ((sfbScalarCompactModel Λ' j.left i.left).obj ((scalarSixChange a S.left).obj L.obj)))
    (hQ : (constantModelBoundedConstructible Λ.X S.left ⊓
      DerivedCategory.finiteTorAmplitude _)
      (((derivedHom Λ.X S.left).obj (.op L.obj)).obj (immersionPairingValue G M)))
    (hA : (constantModelBoundedConstructible Λ.X X.left ⊓
      DerivedCategory.finiteTorAmplitude _)
      (immersionPairingSource Λ (j.left ≫ i.left) L.obj (immersionPairingValue G M)))
    (hQ' : (constantModelBoundedConstructible Λ'.X S.left ⊓
      DerivedCategory.finiteTorAmplitude _)
      (((derivedHom Λ'.X S.left).obj (.op ((scalarSixChange a S.left).obj L.obj))).obj
        (immersionPairingValue G' ((scalarExceptionalChange ell k a ha X).obj M))))
    (hA' : (constantModelBoundedConstructible Λ'.X X.left ⊓
      DerivedCategory.finiteTorAmplitude _)
      (immersionPairingSource Λ' (j.left ≫ i.left) ((scalarSixChange a S.left).obj L.obj)
        (immersionPairingValue G' ((scalarExceptionalChange ell k a ha X).obj M)))) :
    IsIso (immersionInternalAdjunction Λ k j i L.obj (immersionPairingValue G M) M.obj
      (immersionPairingCounit k j i hE G adj M)) ∧
    IsIso (immersionInternalAdjunction Λ' k j i ((scalarSixChange a S.left).obj L.obj)
      (immersionPairingValue G' ((scalarExceptionalChange ell k a ha X).obj M))
      ((scalarSixChange a X.left).obj M.obj)
      (immersionPairingCounit k j i hE' G' adj'
        ((scalarExceptionalChange ell k a ha X).obj M))) ∧
    (immersionScalarMap a j.left i.left (immersionPairingValue G M) ≫
      (sfbScalarCompactModel Λ' j.left i.left).map
        (immersionPairingBeta ell k a ha j i hE G adj hE' G' adj' M hN) ≫
      immersionPairingCounit k j i hE' G' adj'
        ((scalarExceptionalChange ell k a ha X).obj M) =
        (scalarSixChange a X.left).map (immersionPairingCounit k j i hE G adj M)) ∧
    (scalarDirectImageMate a (j.left ≫ i.left)).app
        (((derivedHom Λ.X S.left).obj (.op L.obj)).obj (immersionPairingValue G M)) ≫
      (RootCoordinateFace.lower Λ'.X (j.left ≫ i.left)).map
        (immersionPairingScalarHom a S.left L.obj (immersionPairingValue G M) ≫
          ((derivedHom Λ'.X S.left).obj (.op ((scalarSixChange a S.left).obj L.obj))).map
            (immersionPairingBeta ell k a ha j i hE G adj hE' G' adj' M hN)) ≫
      immersionInternalAdjunction Λ' k j i ((scalarSixChange a S.left).obj L.obj)
        (immersionPairingValue G' ((scalarExceptionalChange ell k a ha X).obj M))
        ((scalarSixChange a X.left).obj M.obj)
        (immersionPairingCounit k j i hE' G' adj'
        ((scalarExceptionalChange ell k a ha X).obj M)) ≫
      ((derivedHom Λ'.X X.left).map
        (immersionScalarMap a j.left i.left L.obj).op).app
          ((scalarSixChange a X.left).obj M.obj) =
      (scalarSixChange a X.left).map
        (immersionInternalAdjunction Λ k j i L.obj (immersionPairingValue G M) M.obj
          (immersionPairingCounit k j i hE G adj M)) ≫
      immersionPairingScalarHom a X.left ((sfbScalarCompactModel Λ j.left i.left).obj L.obj)
        M.obj := by
  sorry

/-- Naturality of the specified pairing in its contravariant L and covariant M
arguments. Source: The generator
(blueprint: lem-sfb-scalar-internal-adjunction-pairing-change).

Proof: In DAG steps 2--3 every Hom bijection is natural. Tracking a test morphism
identifies its image with postcomposition by this exact pairing. Naturality of rho,
ordinary and exceptional counits, and evaluation therefore gives the displayed square. -/
theorem immersionInternalAdjunction_naturality
    (L₁ L₂ : ConstantModelConstructibleFiniteTor Λ.X S.left)
    (M₁ M₂ : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (l : L₂ ⟶ L₁) (m : M₁ ⟶ M₂) :
    (RootCoordinateFace.lower Λ.X (j.left ≫ i.left)).map
        (((derivedHom Λ.X S.left).map l.hom.op).app (immersionPairingValue G M₁) ≫
          ((derivedHom Λ.X S.left).obj (.op L₂.obj)).map
            (G.map ((scalarExceptionalInclusion Λ X.left).map m)).hom) ≫
      immersionInternalAdjunction Λ k j i L₂.obj (immersionPairingValue G M₂) M₂.obj
        (immersionPairingCounit k j i hE G adj M₂) =
      immersionInternalAdjunction Λ k j i L₁.obj (immersionPairingValue G M₁) M₁.obj
        (immersionPairingCounit k j i hE G adj M₁) ≫
      ((derivedHom Λ.X X.left).map
        ((sfbScalarCompactModel Λ j.left i.left).map l.hom).op).app M₁.obj ≫
      ((derivedHom Λ.X X.left).obj
        (.op ((sfbScalarCompactModel Λ j.left i.left).obj L₂.obj))).map m.hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

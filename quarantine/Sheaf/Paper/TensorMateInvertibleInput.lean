/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.CompactSupportProjectionFormula
import Mathlib.CategoryTheory.Equivalence

/-! # The canonical exceptional tensor mate on invertible inputs

Source: main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-composition.proof.md, final base-change sentence
(blueprint: lem-pur-tensor-mate-invertible-input).

We use precisely the comparison coordinates of def-pur-co-smoothness. An input is
an arbitrary etale representative whose comparison image is pro-etale Dctf. Its
inverse is required in pro-etale Dctf by the recorded invertibility predicate.
Full faithfulness and constructible origin make these coordinates cover all objects
and all morphisms of the stated category. The source is pullback first. The canonical
derived symmetry precedes the published counit mate, whose source is omega first.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical Koszul symmetry, expressed with the published derived tensor.
This generic coefficient interface avoids comparing two concrete monoidal elaborations.
The braiding is the published descent of the sheaf symmetry with the Koszul signs.
Source: main-20261015, lem-pur-co-smooth-composition.proof.md, tensor symmetry
(blueprint: lem-pur-tensor-mate-invertible-input). -/
noncomputable def invertibleInputTensorSymmetry
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((Etale.derivedTensor A X).obj K).obj M ⟶
      ((Etale.derivedTensor A X).obj M).obj K :=
  letI := Etale.derivedBraidedCategory A X
  (β_ K M).hom

section CanonicalMaps

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The source functor of the specified tensor mate, in the comparison coordinates
of def-pur-co-smoothness: nu_X^*(Lf^*(-) tensor omega_f).
Source: main-20261015, lem-pur-co-smooth-composition.proof.md, final sentence
(blueprint: lem-pur-tensor-mate-invertible-input). -/
noncomputable def invertibleInputTensorMateSource :
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor ⋙
    (Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f) ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory

/-- The target of the specified mate: the etale exceptional functor followed by nu_X^*.
On constructible inputs this is the recorded transported exceptional inverse image.
Source: main-20261015, lem-pur-co-smooth-composition.proof.md, final sentence
(blueprint: lem-pur-tensor-mate-invertible-input). -/
noncomputable def invertibleInputTensorMateTarget :
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory

/-- The specified canonical theta with the node's pullback-first source. The map
is the canonical Koszul symmetry followed by the published counit transpose,
then the comparison inverse image, exactly as in def-pur-co-smoothness.
Source: main-20261015, lem-pur-co-smooth-composition.proof.md, final sentence
(blueprint: lem-pur-tensor-mate-invertible-input). -/
noncomputable def invertibleInputTensorMate
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (invertibleInputTensorMateSource Λ f).obj K ⟶
      (invertibleInputTensorMateTarget Λ f).obj K :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
    (invertibleInputTensorSymmetry (ModuleCat.{u + 1} Λ) X
      (((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor).obj K)
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f) ≫
      Etale.dualizingComplexTensorMap Λ f K)

end CanonicalMaps

/-- The specified counit mate is invertible on every tensor-invertible Dctf input,
and these same maps commute with every morphism between such inputs.
Source: main-20261015, lem-pur-co-smooth-composition.proof.md, final base-change
sentence (blueprint: lem-pur-tensor-mate-invertible-input).

Proof plan:
1. Tensor closure (lem-sf-tensor-ctf) and pullback/unit preservation
(lem-pur-all-stage-ctf-pullback-unit), together with the canonical pullback tensor
comparison (lem-pur-derived-pullback-tensor-iso), make Q = Lf^*K invertible in Dctf.
Its inverse is the pullback of the specified inverse of K. Tensor by Q on the source
Dctf category and by K on the ambient target category have the tensor-inverse
functors as quasi-inverses, using reassociation, evaluation and the right unitor.
2. By lem-sf-quasi-inverse-hom-bijection these functors give bijections on Hom sets.
Use the canonical projection formula fix-prop-projection-formula, natural in both
arguments, on every bounded constructible source object and finite-Tor input K.
3. Put omega = G(1) and let t : omega tensor Q -> GK be the transpose of the
inverse projection formula followed by counit tensor identity and the left unitor.
For each B, undo tensor by Q on Hom(B tensor Q, omega tensor Q), transpose by
F adjoint G, tensor by K, precompose with inverse projection, and transpose back.
All these operations are bijections. The specified theta is t after symmetry.
4. Every test arrow is uniquely h tensor identity_Q. Naturality of projection
identifies its image under the preceding bijection with t composed with that arrow:
both adjoint transposes are the inverse projection followed by Fh tensor identity,
counit tensor identity and left unitor. Transposition is injective.
5. Every source object A is isomorphic to (A tensor Q_inverse) tensor Q.
Consequently postcomposition with t is bijective on every Hom(A,-). Testing GK gives
a right inverse of t, and injectivity at omega tensor Q makes it a left inverse.
Thus t, and theta including its symmetry, are isomorphisms.
6. Projection naturality in K, the unitor equation and naturality of transposition
give G(a) composed with t_K = t_L composed with identity_omega tensor H(a).
Naturality of symmetry gives the displayed equation in the node's source ordering.
The comparison functor preserves these equations and isomorphisms. Full faithfulness
on constructible origins transports the argument to all pro-etale Dctf inputs.
-/
theorem tensorMate_invertibleInput
    (S : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of S.field.k))] [Y.Over (Spec (.of S.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of S.field.k))]
    [QuasiCompact (X ↘ Spec (.of S.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of S.field.k))]
    [QuasiCompact (Y ↘ Spec (.of S.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of S.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S.Coefficient)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S.Coefficient) Y
      ((comparisonUpperStar (ModuleCat.{u + 1} S.Coefficient) Y).mapDerivedCategory.obj K))
    (hKi : finiteComparedInvertibilityClause S Y
      ((comparisonUpperStar (ModuleCat.{u + 1} S.Coefficient) Y).mapDerivedCategory.obj K)) :
    IsIso (@invertibleInputTensorMate S.Coefficient _ _ X Y f
            (S.finiteComparedCompactification f (Y ↘ Spec (.of S.field.k))).hasCompactification K) ∧
      ∀ (L : _root_.DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S.Coefficient))),
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S.Coefficient) Y
          ((comparisonUpperStar (ModuleCat.{u + 1} S.Coefficient) Y).mapDerivedCategory.obj L) →
        finiteComparedInvertibilityClause S Y
          ((comparisonUpperStar (ModuleCat.{u + 1} S.Coefficient) Y).mapDerivedCategory.obj L) →
        ∀ a : K ⟶ L,
          (@invertibleInputTensorMateSource S.Coefficient _ _ X Y f
            (S.finiteComparedCompactification f
              (Y ↘ Spec (.of S.field.k))).hasCompactification).map a ≫
            @invertibleInputTensorMate S.Coefficient _ _ X Y f
            (S.finiteComparedCompactification f (Y ↘ Spec (.of S.field.k))).hasCompactification L =
            @invertibleInputTensorMate S.Coefficient _ _ X Y f
            (S.finiteComparedCompactification f (Y ↘ Spec (.of S.field.k))).hasCompactification K ≫
            (@invertibleInputTensorMateTarget S.Coefficient _ _ X Y f
            (S.finiteComparedCompactification f
              (Y ↘ Spec (.of S.field.k))).hasCompactification).map a := by
  sorry

end AlgebraicGeometry.ProEtale

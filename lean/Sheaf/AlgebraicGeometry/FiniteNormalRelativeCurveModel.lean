/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.TensorProduct.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.PrimitiveElement

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Finite normal models of relative curves

Source: de Jong, Families of curves and alterations (1997), §§3.2 and 3.5,
pp.605,607--608; Stacks Tags 0307, 0F32, 02FZ and 02FY.
(blueprint: lem-sfb-finite-normal-relative-curve-model)

The five statements give the models, the constant-extension case, functoriality,
group actions, and factorization through intermediate normal models, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

namespace FiniteNormalRelativeCurveModel

/-- The canonical lift of `Spec L` to the generic fibre. The equation `h` says that
its two components use the specified inclusion of the base function field into `L`.
Source: de Jong §§3.2, 3.5; the fibre product universal property.
(blueprint: lem-sfb-finite-normal-relative-curve-model) -/
noncomputable def genericLift {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) (L : Type u) [Field L] [Algebra X.functionField L]
    [Algebra S.functionField L]
    (h : X.fromSpecOfAlgebraFunctionField L ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
        S.fromSpecFunctionField) :
    Spec (.of L) ⟶ pullback f S.fromSpecFunctionField :=
  pullback.lift (X.fromSpecOfAlgebraFunctionField L)
    (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) h

end FiniteNormalRelativeCurveModel

open FiniteNormalRelativeCurveModel

/-- Finite normalization gives the canonical relative curve model, including surjectivity
onto the full fibre product and purity of every geometric fibre. The two spectrum isomorphisms
identify function fields through the specified generic maps, rather than by an arbitrary
abstract field isomorphism. The map `c` is the induced `E`-structure on the normalization
of the generic fibre, characterized on `Spec L` by `hc`.

Source: de Jong §§3.2 and 3.5, pp.605,607--608.
(blueprint: lem-sfb-finite-normal-relative-curve-model)

Proof (DAG steps 1--8):
1. On affine charts take integral closures in L and E. Integral closure is a normal domain
   with the specified fraction field (integral-closure-finite-extension-normal); its
   localizations remain normal (localization-normal-domain). Localization compatibility
   (integral-closure-commutes-localization, 0307) glues them. Lying over gives surjectivity,
   normalization-extension-finite gives finiteness, and finite-over-separated-finite-type
   gives the finite-type assertions. H-projective-composition makes X projective over k.
2. On Spec A over Spec R, the map A tensor_R R_E -> A_L sends a tensor e to ae.
   Monic equations put R_E in A_L, and A-module generators also generate over the tensor
   product. Localization compatibility glues this finite factorization.
3. Geometric integrality makes F tensor_K E a domain, finite-dimensional over F and thus
   a field. The affine fibre-product formula and 0307 identify the generic fibre over X
   of X times_S T with its spectrum, which has one point.
4. The finite dominant normal-base universally-open theorem (0F32) makes T -> S
   universally open. Every nonempty open of the full fibre product contains its one generic
   point. The finite map from Y has closed image containing this point, hence is surjective
   (finite-closed-map-finite-fibres).
5. Finite-over-projective over Spec k makes T and Y projective over k. The graph of Y -> T
   is closed because T/k is separated (projective-implies-proper); change-of-base-closed-
   immersion, closed-immersion-base-change, projective-space-base-change-pullback, and
   closed-immersion-comp embed this graph into a finite projective space over T.
6. Localizing at the nonzero base elements and using 0307 identifies the generic fibre
   over T with the given normalization C, with its E-structure and map to X.
7. By equidimensional-open-local-dimension, C has local dimension one. The locus of local
   fibre dimension at most zero is open (local-fibre-dimension-open, 02FZ); if nonempty it
   contains the generic point of integral Y, a contradiction. Thus dimensions are at least one.
8. Finite base change (finite-radicial-basechange), finite-algebra-is-integral, and
   integral-injective-dimension-equal bound geometric fibre dimensions by one, since the
   original fibres are pure curves. Fibre-dimension-after-base-change (02FY) preserves
   the lower bound. Finite-type-over-noetherian and constant-local-dimension-components
   then give pure dimension one. No flatness is used.
-/
theorem finite_normal_relative_curve_model
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f]
    [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (L E : Type u) [Field L] [Field E]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    [Algebra.IsSeparable X.functionField L]
    [Algebra S.functionField E] [FiniteDimensional S.functionField E]
    [Algebra.IsSeparable S.functionField E]
    [Algebra S.functionField L] [Algebra E L] [IsScalarTower S.functionField E L]
    (h : X.fromSpecOfAlgebraFunctionField L ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
        S.fromSpecFunctionField)
    (c : (genericLift f L h).normalization ⟶ Spec (.of E))
    (hc : (genericLift f L h).toNormalization ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap E L)))
    [Smooth c] [IsHProjective c] [GeometricallyIntegral c]
    (hcurve : (genericLift f L h).normalization.IsPureDimension 1) :
    (∀ t : S.normalizationIn E,
      IsDomain ((S.normalizationIn E).presheaf.stalk t) ∧
        IsIntegrallyClosed ((S.normalizationIn E).presheaf.stalk t)) ∧
    IsIntegral (S.normalizationIn E) ∧
    IsHProjective (S.fromNormalizationIn E ≫ p) ∧
    LocallyOfFiniteType (S.fromNormalizationIn E ≫ p) ∧
    QuasiCompact (S.fromNormalizationIn E ≫ p) ∧
    IsFinite (S.fromNormalizationIn E) ∧ Surjective (S.fromNormalizationIn E) ∧
    (∃ e : Spec (.of E) ≅ Spec (S.normalizationIn E).functionField,
      e.hom ≫ (S.normalizationIn E).fromSpecFunctionField =
        (S.fromSpecOfAlgebraFunctionField E).toNormalization) ∧
    (∀ y : X.normalizationIn L,
      IsDomain ((X.normalizationIn L).presheaf.stalk y) ∧
        IsIntegrallyClosed ((X.normalizationIn L).presheaf.stalk y)) ∧
    IsIntegral (X.normalizationIn L) ∧
    LocallyOfFiniteType (X.fromNormalizationIn L ≫ f ≫ p) ∧
    QuasiCompact (X.fromNormalizationIn L ≫ f ≫ p) ∧
    IsFinite (X.fromNormalizationIn L) ∧
    (∃ e : Spec (.of L) ≅ Spec (X.normalizationIn L).functionField,
      e.hom ≫ (X.normalizationIn L).fromSpecFunctionField =
        (X.fromSpecOfAlgebraFunctionField L).toNormalization) ∧
    (∃! g : X.normalizationIn L ⟶ S.normalizationIn E,
      g ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f ∧
      (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
          (S.fromSpecOfAlgebraFunctionField E).toNormalization) ∧
    ∀ g : X.normalizationIn L ⟶ S.normalizationIn E,
      g ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f →
      (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
          (S.fromSpecOfAlgebraFunctionField E).toNormalization →
      IsHProjective g ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ S.normalizationIn E), (pullback g t).IsPureDimension 1) ∧
      (∃ m : X.normalizationIn L ⟶ pullback f (S.fromNormalizationIn E),
        m ≫ pullback.fst f (S.fromNormalizationIn E) = X.fromNormalizationIn L ∧
        m ≫ pullback.snd f (S.fromNormalizationIn E) = g ∧ IsFinite m ∧ Surjective m) ∧
      ∃ e : pullback g (S.fromSpecOfAlgebraFunctionField E).toNormalization ≅
          (genericLift f L h).normalization,
        e.hom ≫ c = pullback.snd g (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
        e.hom ≫ (genericLift f L h).fromNormalization ≫
            pullback.fst f S.fromSpecFunctionField =
          pullback.fst g (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫
            X.fromNormalizationIn L ∧
        (genericLift f L h).toNormalization ≫ e.inv ≫
            pullback.fst g (S.fromSpecOfAlgebraFunctionField E).toNormalization =
          (X.fromSpecOfAlgebraFunctionField L).toNormalization := by
  sorry

/-- The constant-extension case: the tensor product is a field, finite separable over F,
and the generic normalization is the scalar extension of the original generic curve.
A ring isomorphism with any field L, characterized on pure tensors, presents the tensor
field without selecting a possibly incompatible field structure on its underlying ring.

Source: de Jong §3.2, p.605.
(blueprint: lem-sfb-finite-normal-relative-curve-model)

Proof (DAG steps 3 and 9): on a nonempty affine generic chart geometric integrality makes
its scalar extension a domain. Localizing gives F tensor_K E, a nonzero domain finite over F,
hence a field. A primitive element and the Bezout identity for its separable polynomial and
derivative prove separability after scalar extension (finite-separable-extension-primitive-
element). Smooth-relative-dimension-permanence and projective-base-change give smoothness and
projectivity of the base-changed curve; geometric integrality is preserved. Smooth-normal
makes it normal. Its affine rings are finite, hence integral (finite-algebra-is-integral),
over the original affine rings and have fraction field L. An element of L integral over an
original affine ring is integral over the normal base-changed ring, hence belongs to it.
Thus these affine rings are precisely the integral closures defining the normalization.
-/
theorem finite_normal_relative_curve_model_constant_extension
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f]
    [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    [Algebra S.functionField X.functionField]
    (hKF : Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField)) ≫
      S.fromSpecFunctionField = X.fromSpecFunctionField ≫ f)
    (E : Type u) [Field E] [Algebra S.functionField E]
    [FiniteDimensional S.functionField E] [Algebra.IsSeparable S.functionField E] :
    IsField (TensorProduct S.functionField X.functionField E) ∧
    ∀ (L : Type u) [Field L] [Algebra X.functionField L]
      [Algebra S.functionField L] [Algebra E L]
      [IsScalarTower S.functionField X.functionField L] [IsScalarTower S.functionField E L]
      (eL : TensorProduct S.functionField X.functionField E ≃+* L),
      (∀ (a : X.functionField) (b : E),
        eL (TensorProduct.tmul S.functionField a b) =
          algebraMap X.functionField L a * algebraMap E L b) →
      ∀ h : X.fromSpecOfAlgebraFunctionField L ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
          S.fromSpecFunctionField,
      FiniteDimensional X.functionField L ∧ Algebra.IsSeparable X.functionField L ∧
      ∃ c : (genericLift f L h).normalization ⟶ Spec (.of E),
        (genericLift f L h).toNormalization ≫ c =
          Spec.map (CommRingCat.ofHom (algebraMap E L)) ∧
        Smooth c ∧ IsHProjective c ∧ GeometricallyIntegral c ∧
        (genericLift f L h).normalization.IsPureDimension 1 ∧
        ∃ e : (genericLift f L h).normalization ≅
            pullback (pullback.snd f S.fromSpecFunctionField)
              (Spec.map (CommRingCat.ofHom (algebraMap S.functionField E))),
          e.hom ≫ pullback.fst (pullback.snd f S.fromSpecFunctionField)
              (Spec.map (CommRingCat.ofHom (algebraMap S.functionField E))) =
            (genericLift f L h).fromNormalization ∧
          e.hom ≫ pullback.snd (pullback.snd f S.fromSpecFunctionField)
              (Spec.map (CommRingCat.ofHom (algebraMap S.functionField E))) = c := by
  sorry

/-- Compatible isomorphisms of the scheme and field diagrams lift uniquely to their
normalizations, compatibly with the relative structural map. The absence of a requirement
to fix k includes semilinear isomorphisms. Unique lifting also gives the identity and
composition laws: composing the displayed lifted isomorphisms lifts the composed data.

Source: de Jong §§3.2, 3.5; Stacks Tag 0307.
(blueprint: lem-sfb-finite-normal-relative-curve-model)

Proof (DAG step 10): each isomorphism takes monic integral equations on an affine chart to
monic integral equations on the corresponding chart. It therefore identifies the integral
closures. By 0307 these isomorphisms agree after localization and glue. The inverse, identity,
and composition equations hold in the specified fields and thus in every affine integral
closure. Uniqueness follows because each affine closure embeds into its specified field.
The same test on Spec L proves compatibility with the map between the two normal models.
-/
theorem finite_normal_relative_curve_model_isomorphisms
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f]
    [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (L E : Type u) [Field L] [Field E]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    [Algebra.IsSeparable X.functionField L]
    [Algebra S.functionField E] [FiniteDimensional S.functionField E]
    [Algebra.IsSeparable S.functionField E]
    [Algebra S.functionField L] [Algebra E L] [IsScalarTower S.functionField E L]
    (h : X.fromSpecOfAlgebraFunctionField L ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
        S.fromSpecFunctionField)
    (c : (genericLift f L h).normalization ⟶ Spec (.of E))
    (hc : (genericLift f L h).toNormalization ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap E L)))
    [Smooth c] [IsHProjective c] [GeometricallyIntegral c]
    (hcurve : (genericLift f L h).normalization.IsPureDimension 1)
    (k' : Type u) [Field k']
    (S' X' : Scheme.{u}) [IsIntegral S'] [IsIntegral X']
    (p' : S' ⟶ Spec (.of k'))
    (L' E' : Type u) [Field L'] [Field E']
    [Algebra X'.functionField L'] [FiniteDimensional X'.functionField L']
    [Algebra S'.functionField E'] [FiniteDimensional S'.functionField E']
    [Algebra E' L'] (f' : X' ⟶ S')
    (g : X.normalizationIn L ⟶ S.normalizationIn E)
    (g' : X'.normalizationIn L' ⟶ S'.normalizationIn E')
    (hgf : g ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f)
    (hg : (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
        (S.fromSpecOfAlgebraFunctionField E).toNormalization)
    (hgf' : g' ≫ S'.fromNormalizationIn E' = X'.fromNormalizationIn L' ≫ f')
    (hg' : (X'.fromSpecOfAlgebraFunctionField L').toNormalization ≫ g' =
      Spec.map (CommRingCat.ofHom (algebraMap E' L')) ≫
        (S'.fromSpecOfAlgebraFunctionField E').toNormalization)
    (aX : X ≅ X') (aS : S ≅ S') (aL : Spec (.of L) ≅ Spec (.of L'))
    (aE : Spec (.of E) ≅ Spec (.of E'))
    (ak : Spec (.of k) ≅ Spec (.of k'))
    (hk : aS.hom ≫ p' = p ≫ ak.hom)
    (hf : aX.hom ≫ f' = f ≫ aS.hom)
    (hX : aL.hom ≫ X'.fromSpecOfAlgebraFunctionField L' =
      X.fromSpecOfAlgebraFunctionField L ≫ aX.hom)
    (hS : aE.hom ≫ S'.fromSpecOfAlgebraFunctionField E' =
      S.fromSpecOfAlgebraFunctionField E ≫ aS.hom)
    (hE : aL.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap E' L')) =
      Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫ aE.hom) :
    (∃! a : (X.normalizationIn L ≅ X'.normalizationIn L') ×
        (S.normalizationIn E ≅ S'.normalizationIn E'),
      a.1.hom ≫ X'.fromNormalizationIn L' = X.fromNormalizationIn L ≫ aX.hom ∧
      a.2.hom ≫ S'.fromNormalizationIn E' = S.fromNormalizationIn E ≫ aS.hom ∧
      (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ a.1.hom =
        aL.hom ≫ (X'.fromSpecOfAlgebraFunctionField L').toNormalization ∧
      (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫ a.2.hom =
        aE.hom ≫ (S'.fromSpecOfAlgebraFunctionField E').toNormalization) ∧
    ∀ a : (X.normalizationIn L ≅ X'.normalizationIn L') ×
        (S.normalizationIn E ≅ S'.normalizationIn E'),
      (a.1.hom ≫ X'.fromNormalizationIn L' = X.fromNormalizationIn L ≫ aX.hom ∧
      a.2.hom ≫ S'.fromNormalizationIn E' = S.fromNormalizationIn E ≫ aS.hom ∧
      (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ a.1.hom =
        aL.hom ≫ (X'.fromSpecOfAlgebraFunctionField L').toNormalization ∧
      (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫ a.2.hom =
        aE.hom ≫ (S'.fromSpecOfAlgebraFunctionField E').toNormalization) →
      a.1.hom ≫ g' = g ≫ a.2.hom := by
  sorry

/-- Any compatible group action extends uniquely to both normal models and preserves
the relative structural map. Automorphisms of field spectra encode the contravariant
field actions, so no faithfulness, finiteness of G, or k-linearity is imposed.

Source: de Jong §§3.2 and 3.5, p.607; Stacks Tag 0307.
(blueprint: lem-sfb-finite-normal-relative-curve-model)

Proof (DAG step 10, action clause): apply the integral-closure isomorphism construction
to every group element. Uniqueness on each affine integral closure proves the identity
and multiplication laws, hence gives monoid homomorphisms into the scheme automorphism
groups. Testing on the specified generic fields proves the equivariance of g. Any other
extensions induce the same maps on every affine integral closure and are equal. The
argument never requires a faithful action or preservation of the ground-field elements.
-/
theorem finite_normal_relative_curve_model_actions
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f]
    [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (L E : Type u) [Field L] [Field E]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    [Algebra.IsSeparable X.functionField L]
    [Algebra S.functionField E] [FiniteDimensional S.functionField E]
    [Algebra.IsSeparable S.functionField E]
    [Algebra S.functionField L] [Algebra E L] [IsScalarTower S.functionField E L]
    (h : X.fromSpecOfAlgebraFunctionField L ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
        S.fromSpecFunctionField)
    (c : (genericLift f L h).normalization ⟶ Spec (.of E))
    (hc : (genericLift f L h).toNormalization ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap E L)))
    [Smooth c] [IsHProjective c] [GeometricallyIntegral c]
    (hcurve : (genericLift f L h).normalization.IsPureDimension 1)
    (g : X.normalizationIn L ⟶ S.normalizationIn E)
    (hgf : g ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f)
    (hg : (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
        (S.fromSpecOfAlgebraFunctionField E).toNormalization)
    (G : Type v) [Group G]
    (ρX : G →* Aut X) (ρS : G →* Aut S)
    (ρk : G →* Aut (Spec (.of k)))
    (hk : ∀ a : G, (ρS a).hom ≫ p = p ≫ (ρk a).hom)
    (ρL : G →* Aut (Spec (.of L))) (ρE : G →* Aut (Spec (.of E)))
    (hf : ∀ a : G, (ρX a).hom ≫ f = f ≫ (ρS a).hom)
    (hX : ∀ a : G, (ρL a).hom ≫ X.fromSpecOfAlgebraFunctionField L =
      X.fromSpecOfAlgebraFunctionField L ≫ (ρX a).hom)
    (hS : ∀ a : G, (ρE a).hom ≫ S.fromSpecOfAlgebraFunctionField E =
      S.fromSpecOfAlgebraFunctionField E ≫ (ρS a).hom)
    (hE : ∀ a : G, (ρL a).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap E L)) =
      Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫ (ρE a).hom) :
    (∃! ρ : (G →* Aut (X.normalizationIn L)) × (G →* Aut (S.normalizationIn E)),
      (∀ a : G, (ρ.1 a).hom ≫ X.fromNormalizationIn L =
        X.fromNormalizationIn L ≫ (ρX a).hom) ∧
      (∀ a : G, (ρ.2 a).hom ≫ S.fromNormalizationIn E =
        S.fromNormalizationIn E ≫ (ρS a).hom) ∧
      (∀ a : G, (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ (ρ.1 a).hom =
        (ρL a).hom ≫ (X.fromSpecOfAlgebraFunctionField L).toNormalization) ∧
      (∀ a : G, (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫ (ρ.2 a).hom =
        (ρE a).hom ≫ (S.fromSpecOfAlgebraFunctionField E).toNormalization)) ∧
    ∀ ρ : (G →* Aut (X.normalizationIn L)) × (G →* Aut (S.normalizationIn E)),
      ((∀ a : G, (ρ.1 a).hom ≫ X.fromNormalizationIn L =
        X.fromNormalizationIn L ≫ (ρX a).hom) ∧
      (∀ a : G, (ρ.2 a).hom ≫ S.fromNormalizationIn E =
        S.fromNormalizationIn E ≫ (ρS a).hom) ∧
      (∀ a : G, (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ (ρ.1 a).hom =
        (ρL a).hom ≫ (X.fromSpecOfAlgebraFunctionField L).toNormalization) ∧
      (∀ a : G, (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫ (ρ.2 a).hom =
        (ρE a).hom ≫ (S.fromSpecOfAlgebraFunctionField E).toNormalization)) →
      ∀ a : G, (ρ.1 a).hom ≫ g = g ≫ (ρ.2 a).hom := by
  sorry

/-- The normalization over an open of S maps uniquely and finitely to an intermediate
finite dominant normal model with a specified embedding of its function field in L.
The auxiliary map t is the restriction of the canonical generic map to the open model;
its displayed equality prevents any vacuous interpretation of the field-embedding clause.

Source: de Jong §3.5, pp.607--608; Stacks Tag 0307.
(blueprint: lem-sfb-finite-normal-relative-curve-model)

Proof (DAG step 11): on an affine Spec A in X_U the finite inverse image in Z is Spec B.
The given field embedding embeds B in L. Finite-algebra-is-integral puts B in the integral
closure A_L. These inclusions B -> A_L localize compatibly (0307) and glue to Y_U -> Z.
The canonical generic map restricts to t because the given generic diagram factors
through X_U. The resulting morphism induces exactly the chosen embedding. Any other
morphism inducing it has the same maps on affine rings, as A_L embeds in L. Finally,
normalization-extension-finite supplies finite A-module generators of A_L, which also
generate it as a B-module. Hence the unique morphism is finite. If U is empty there is
no integral Z with a dominant map to X_U; no nonemptiness assumption on U is needed.
-/
theorem finite_normal_relative_curve_model_intermediate
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f]
    [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (L E : Type u) [Field L] [Field E]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    [Algebra.IsSeparable X.functionField L]
    [Algebra S.functionField E] [FiniteDimensional S.functionField E]
    [Algebra.IsSeparable S.functionField E]
    [Algebra S.functionField L] [Algebra E L] [IsScalarTower S.functionField E L]
    (h : X.fromSpecOfAlgebraFunctionField L ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
        S.fromSpecFunctionField)
    (c : (genericLift f L h).normalization ⟶ Spec (.of E))
    (hc : (genericLift f L h).toNormalization ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap E L)))
    [Smooth c] [IsHProjective c] [GeometricallyIntegral c]
    (hcurve : (genericLift f L h).normalization.IsPureDimension 1)
    (U : S.Opens) (Z : Scheme.{u}) [IsIntegral Z]
    (q : Z ⟶ (f ⁻¹ᵁ U).toScheme) [IsFinite q] [IsDominant q]
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z))
    (i : Z.functionField →+* L)
    (hi : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecFunctionField ≫ q ≫ (f ⁻¹ᵁ U).ι =
      X.fromSpecOfAlgebraFunctionField L) :
    ∃ t : Spec (.of L) ⟶ ((X.fromNormalizationIn L) ⁻¹ᵁ (f ⁻¹ᵁ U)).toScheme,
      t ≫ ((X.fromNormalizationIn L) ⁻¹ᵁ (f ⁻¹ᵁ U)).ι =
        (X.fromSpecOfAlgebraFunctionField L).toNormalization ∧
      (∃! m : ((X.fromNormalizationIn L) ⁻¹ᵁ (f ⁻¹ᵁ U)).toScheme ⟶ Z,
        m ≫ q = X.fromNormalizationIn L ∣_ (f ⁻¹ᵁ U) ∧
        t ≫ m = Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecFunctionField) ∧
      ∀ m : ((X.fromNormalizationIn L) ⁻¹ᵁ (f ⁻¹ᵁ U)).toScheme ⟶ Z,
        m ≫ q = X.fromNormalizationIn L ∣_ (f ⁻¹ᵁ U) →
        t ≫ m = Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecFunctionField →
        IsFinite m := by
  sorry

end AlgebraicGeometry

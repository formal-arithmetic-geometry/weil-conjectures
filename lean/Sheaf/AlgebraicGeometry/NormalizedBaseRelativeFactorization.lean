module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FiniteDominantNormalUniversallyOpen
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Relative factorization through a normalized base

Source: Stacks Project, `more-morphisms.tex`, Tag 0F32, together with
`algebra.tex`, Tag 0307; de Jong, *Families of curves and alterations*, §§3.2 and 3.5.
(blueprint: lem-sfb-normalized-base-relative-factorization)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The finite normalization over a normalized intermediate base factors uniquely, is finite
and surjective onto the fibre product, and has the stated generic fibre.  The displayed
equations record the specified embeddings of the function fields; the final isomorphism is
over the generic fibre and fixes the field `L`.

Source: Stacks Project, Tag 0F32 and Tag 0307; de Jong §§3.2 and 3.5.
(blueprint: lem-sfb-normalized-base-relative-factorization)

Proof (the seven steps of the DAG):
1. Apply lem-sfb-finite-normalization-model-functoriality to S in E and X in L.
   On nonempty affine charts U = Spec A in S and V = Spec B above U, dominance
   embeds A in B. By lem-sc-integral-function-field-affine-fraction their fraction
   fields are K and F. Write C and D for their integral closures in E and L.
2. The embedding E into L sends C into D, since monic equations over A remain
   monic equations over B. By lem-weil-pbc-integral-closure-commutes-localization
   these maps agree on principal restrictions and affine refinements of overlaps,
   hence glue to g. A second map with the prescribed field embedding gives the
   same maps C into D, proving uniqueness. The zero prime pulls back to the zero
   prime, so g is dominant.
3. The affine fibre-product formula lem-weil-pbc-fibre-product-affine-spectra gives
   target charts Spec (B tensor_A C) for h, with inverse image Spec D. A finite
   list generating D over B also generates it over B tensor_A C, by coefficients
   b tensor 1. By pqf-lem-affine-local-target the map is affine and therefore finite
   by def-weil-finite-integral-morphism.
4. Localize B at the nonzero elements of A to obtain a generic-base chart B0
   with fraction field F. Geometric integrality makes B0 tensor_K E a domain.
   It is nonzero, as a K-linear functional taking 1 to 1 splits the inclusion of E.
   Localizing at the nonzero elements of B0 gives F tensor_K E by
   lem-weil-pbc-localization-tensor-over-base. This is a nonzero domain finite
   dimensional over F. Multiplication by a nonzero element is an injective linear
   endomorphism, hence surjective, so the ring is a field. Its multiplication map
   into L is a unital map from a field and is therefore injective.
5. Tag 0307 identifies the localization of C at A minus zero with E. The affine
   fibre-product formula then identifies the fibre of W over the generic point
   of X with Spec (F tensor_K E), with the displayed projection maps. It has one point.
6. By lem-sfb-finite-dominant-normal-base-universally-open, q is universally open,
   so W to X is open. Every nonempty open of W meets its one-point generic fibre,
   making that point dense. The image of h contains it and is closed by
   lem-weil-pbc-finite-closed-map-finite-fibres. Thus h is surjective onto all of W.
7. On these charts the generic fibre of Y over T has ring D tensor_C E, namely
   the localization of D at A minus zero. Tag 0307 identifies this ring with the
   integral closure of B0 in L. These identifications commute with restrictions
   and fix B0, E and L, so glue to the asserted isomorphism over X_K, respecting
   the induced E-structure and inducing the identity on L. -/
theorem normalized_base_relative_factorization
    (k : Type u) [Field k]
    (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (f : X ⟶ S) [IsDominant f]
    [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    [Algebra S.functionField X.functionField]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (L E : Type u) [Field L] [Field E]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    [Algebra.IsSeparable X.functionField L]
    [Algebra S.functionField E] [FiniteDimensional S.functionField E]
    [Algebra.IsSeparable S.functionField E]
    [Algebra S.functionField L] [Algebra E L] [IsScalarTower S.functionField E L]
    [IsScalarTower S.functionField X.functionField L]
    (hcompat : X.fromSpecOfAlgebraFunctionField L ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
        S.fromSpecFunctionField) :
    (∃! g : X.normalizationIn L ⟶ S.normalizationIn E,
      g ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f ∧
      (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
          (S.fromSpecOfAlgebraFunctionField E).toNormalization) ∧
    (∀ (g : X.normalizationIn L ⟶ S.normalizationIn E)
      (hfg : g ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f),
      (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
          (S.fromSpecOfAlgebraFunctionField E).toNormalization →
      IsFinite (pullback.lift (X.fromNormalizationIn L) g hfg.symm) ∧
      Surjective (pullback.lift (X.fromNormalizationIn L) g hfg.symm) ∧
      IsDominant g ∧
      ∃ (c : (pullback.lift (X.fromSpecOfAlgebraFunctionField L)
          (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) hcompat).normalization ⟶
          Spec (.of E))
        (e : pullback g (S.fromSpecOfAlgebraFunctionField E).toNormalization ≅
          (pullback.lift (X.fromSpecOfAlgebraFunctionField L)
          (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) hcompat).normalization),
        (pullback.lift (X.fromSpecOfAlgebraFunctionField L)
          (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) hcompat).toNormalization ≫
          c =
          Spec.map (CommRingCat.ofHom (algebraMap E L)) ∧
        e.hom ≫ c = pullback.snd g (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
        e.hom ≫ (pullback.lift (X.fromSpecOfAlgebraFunctionField L)
          (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) hcompat).fromNormalization ≫
            pullback.fst f S.fromSpecFunctionField =
          pullback.fst g (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫
            X.fromNormalizationIn L ∧
        e.hom ≫ (pullback.lift (X.fromSpecOfAlgebraFunctionField L)
          (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) hcompat).fromNormalization ≫
            pullback.snd f S.fromSpecFunctionField =
          pullback.snd g (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫
            Spec.map (CommRingCat.ofHom (algebraMap S.functionField E)) ∧
        (pullback.lift (X.fromSpecOfAlgebraFunctionField L)
          (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) hcompat).toNormalization ≫
          e.inv ≫
            pullback.fst g (S.fromSpecOfAlgebraFunctionField E).toNormalization =
          (X.fromSpecOfAlgebraFunctionField L).toNormalization) ∧
    IsField (X.functionField ⊗[S.functionField] E) ∧
    Function.Injective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom S.functionField X.functionField L)
      (IsScalarTower.toAlgHom S.functionField E L)) ∧
    ∃ e : Spec (.of (X.functionField ⊗[S.functionField] E)) ≅
        pullback X.fromSpecFunctionField (pullback.fst f (S.fromNormalizationIn E)),
      e.hom ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField
          (X.functionField ⊗[S.functionField] E))) ∧
      e.hom ≫ pullback.snd _ _ ≫ pullback.snd f (S.fromNormalizationIn E) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : E →ₐ[S.functionField]
            X.functionField ⊗[S.functionField] E).toRingHom) ≫
          (S.fromSpecOfAlgebraFunctionField E).toNormalization := by
  sorry

end AlgebraicGeometry

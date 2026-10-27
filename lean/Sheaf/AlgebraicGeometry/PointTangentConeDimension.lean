/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.PowerMapSmoothGraphLocalData
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Sheaf.RingTheory.HilbertSamuelGrowthDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Algebraic tangent cones in a smooth ambient scheme

Source: Stacks Project, Algebra, Tags 00KQ, 00P6, 00NO and 00OU;
Milne, Abelian Varieties, I.3.6, printed p.18
(blueprint: lem-sfb-point-tangent-cone-dimension).

The coordinate map is specified on constants and on degree-one classes. The function `c`
sends a maximal-ideal element to evaluation of its differential on tangent vectors, as
specified by the epsilon coefficient of the actual stalk homomorphism. Thus the closed
immersion is the canonical one, rather than an unspecified embedding of affine schemes.
The base-field tangent module is the existing restriction of residue-field scalars.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The algebraic tangent cone of a reduced closed subscheme at a rational point of a
smooth separated geometrically integral finite-type scheme embeds canonically in the
ambient tangent space. Its dimension is the local-ring dimension and satisfies the stated
global bounds. Smooth locally closed subschemes contained in the closed subscheme have
their differential's affine linear image contained in the cone.

Source: Stacks Project, Algebra, Tags 00KQ, 00P6, 00NO and 00OU;
Varieties, Tags 056S, 0A21, 0B2E and 0B2F; Milne AV I.3.6, printed p.18
(blueprint: lem-sfb-point-tangent-cone-dimension).

Proof:
1. Rationality identifies the residue field with k. Smooth regularity
   (lem-weil-pbc-smooth-scheme-over-field-regular) makes the ambient stalk A Noetherian
   regular local. Finite local dimension, rational-point stalk dimension and irreducible
   locally algebraic dimension identify its dimension with the finite integer dim Y.
2. The regular-local graded cotangent criterion identifies gr A with Sym(m_A/m_A^2).
   Rational tangent-cotangent duality identifies this cotangent space with the dual of E,
   by finite-dimensional evaluation, including dimension zero. The epsilon coefficient
   specifies the function c below; its classes span the dual of E.
3. A closed immersion gives the local quotient A to R, by affine-open and Spec-map stalk
   localization. Powers of the maximal ideal map onto powers, so the associated graded
   map is surjective degree by degree (lem-sfb-power-quotient-graded-comparison).
   Its composite with the regular graded isomorphism is F, with the displayed constants
   and degree-one formulas. Spec F is the canonical closed immersion.
4. The maximal-adic graded-length bridge identifies cumulative graded dimensions with
   lengths R/m^n. Hilbert-Samuel growth and the standard-graded cumulative-dimension
   lemma identify dim gr R with dim R, allowing a nonreduced cone and constant polynomial.
5. Rational-point stalk dimension gives dim R <= dim Z. Chains in Z are chains in Y.
   If Z is proper, append irreducible Y to each chain, obtaining dim Z < d. When d=0,
   no proper closed subscheme containing the point can occur.
6. Smooth D is reduced (lem-trf-smooth-geometrically-normal). Reduced-source factorization
   through Z turns the set containment into a factorization. Locally closedness gives
   local quotient maps A to R to B, where B is the regular stalk of D; restriction to
   the open neighborhood does not change the stalk.
7. The graded maps compose on representatives. Regularity identifies gr B with the
   symmetric algebra of the cotangent of D. Rational tangent-cotangent naturality makes
   the dual of the cotangent quotient the actual differential. It is injective. The
   symmetric-algebra universal property identifies its affine linear map with the
   composite through gr R, proving the underlying-space containment. -/
theorem point_tangent_cone_dimension
    (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (s : Y ⟶ Spec (.of k))
    [Smooth s] [IsSeparated s] [GeometricallyIntegral s]
    [LocallyOfFiniteType s] [QuasiCompact s]
    (p : s.fieldPoints k) (y : Y) (hp : p.1 (IsLocalRing.closedPoint k) = y)
    (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsReduced Z]
    (z : Z) (hz : i z = y) :
    ∃ d : ℕ,
      topologicalKrullDim Y = (d : WithBot ℕ∞) ∧
      Module.Finite k (schemeTangentSpace k Y s y) ∧
      Module.finrank k (schemeTangentSpace k Y s y) = d ∧
      ∃ (c : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) →
          Module.Dual k (schemeTangentSpace k Y s y))
        (F : SymmetricAlgebra k (Module.Dual k (schemeTangentSpace k Y s y)) →+*
          Ideal.associatedGraded (IsLocalRing.maximalIdeal (Z.presheaf.stalk z))),
        (∀ (a : IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (θ : schemeTangentSpace k Y s y),
          ∃ hθ : θ.val (IsLocalRing.closedPoint (DualNumber (Y.residueField y))) = y,
            PowerMapLocalData.residueStructure k Y s y (c a θ) =
              ((eqToHom (congrArg (fun t : Y ↦ Y.presheaf.stalk t) hθ.symm) ≫
                Scheme.stalkClosedPointTo θ.val).hom a).snd) ∧
        (∀ b : k,
          F (algebraMap k (SymmetricAlgebra k
              (Module.Dual k (schemeTangentSpace k Y s y))) b) =
            Ideal.associatedGradedRingHom (IsLocalRing.maximalIdeal (Z.presheaf.stalk z))
              (PowerMapLocalData.stalkStructure k Z (i ≫ s) z b)) ∧
        (∀ a : IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
          ∃ ha : PowerMapLocalData.stalkMapAt i z y hz a ∈
              IsLocalRing.maximalIdeal (Z.presheaf.stalk z) ^ 1,
            F (SymmetricAlgebra.ι k (Module.Dual k (schemeTangentSpace k Y s y)) (c a)) =
              DirectSum.of
                (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)))
                1 (Submodule.Quotient.mk ⟨PowerMapLocalData.stalkMapAt i z y hz a, ha⟩)) ∧
        IsClosedImmersion (Spec.map (CommRingCat.ofHom F)) ∧
        topologicalKrullDim
            (Spec (.of (Ideal.associatedGraded
              (IsLocalRing.maximalIdeal (Z.presheaf.stalk z))))) =
          ringKrullDim (Z.presheaf.stalk z) ∧
        ringKrullDim (Z.presheaf.stalk z) ≤ topologicalKrullDim Z ∧
        topologicalKrullDim Z ≤ (d : WithBot ℕ∞) ∧
        (Set.range i ≠ Set.univ →
          topologicalKrullDim
              (Spec (.of (Ideal.associatedGraded
                (IsLocalRing.maximalIdeal (Z.presheaf.stalk z))))) < (d : WithBot ℕ∞)) ∧
        ∀ (D : Scheme.{u}) (j : D ⟶ Y), IsImmersion j → Smooth (j ≫ s) →
          Set.range j ⊆ Set.range i → ∀ q : D, j q = y →
          ∃ (he : Function.Bijective (j.residueFieldMap q).hom)
            (L : schemeTangentSpace k D (j ≫ s) q →ₗ[k] schemeTangentSpace k Y s y),
            Function.Injective L ∧
            (∀ θ : schemeTangentSpace k D (j ≫ s) q,
              HEq (L θ) (schemeTangentMap k D Y (j ≫ s) s j rfl q he θ)) ∧
            Set.range (Spec.map (CommRingCat.ofHom
                (SymmetricAlgebra.lift
                  ((SymmetricAlgebra.ι k
                    (Module.Dual k (schemeTangentSpace k D (j ≫ s) q))).comp
                    L.dualMap)).toRingHom)) ⊆
              Set.range (Spec.map (CommRingCat.ofHom F)) := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.NowhereDenseDimZero
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import Sheaf.AlgebraicGeometry.NormalizationInseparableBaseChange
import Sheaf.TraceFormula.ProjectiveInseparableSpreadNormalization

/-!
# Generic smooth curve and finite étale boundary preparation

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, proof of Theorem 3.5,
Step 5, printed pp. 163--164
(blueprint: lem-trf-generic-smooth-boundary-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Generic smooth curve and étale reduced boundary after purely inseparable preparation.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, Theorem 3.5, proof,
Step 5, printed pp. 163--164
(blueprint: lem-trf-generic-smooth-boundary-preparation).

The algebra in `htrdeg` is the residue-field map of `g` at the generic point `η`.
Likewise the finite purely inseparable extension in the conclusion is induced by `b`
at `y₁`; dominance makes their images generic. Function fields are thus the generic
residue fields, canonically identified with the generic stalks. Generically finite means
finite after restriction to a dense open. Excellence is tested on every affine open.
The boundary morphism is the reduction of the actual pullback of `i` along `c ≫ a`,
followed by its projection to `X₁` and then `f`; its generic fibre is allowed to be empty.

Proof, following the five steps of the DAG node:
1. Put C = (X₀)_ηY. The transcendence-degree dimension formula
   [lem-sc-closed-irreducible-dimension-trdeg] gives dimension one. Apply
   [lem-weil-pbc-normalization-geonormal-insep] to obtain a finite purely inseparable
   K₁/κ(Y) such that the normalization N₁ of C_K₁ is geometrically normal.
2. Purely inseparable base change is a homeomorphism, so (C_K₁)_red is integral.
   Finiteness of normalization [lem-weil-pbc-reduced-algebraic-normalization-field-change]
   makes N₁ integral of finite type. Its function field is algebraic over κ(X₀), hence
   has transcendence degree one over K₁; the dimension formula again gives dimension one.
   The reduced inverse image D₁ of the boundary omits the generic point, since i does
   and a is dominant. It has dimension at most zero [lem-pc-nowhere-dense-dim-zero],
   and is finite [lem-pc-zero-dimensional-closed-subscheme-finite]. Apply
   [lem-pur-finite-inseparable-geometric-reduction] to D₁, obtaining a further finite
   purely inseparable K/K₁ with (D₁_K)_red geometrically reduced. Its finite algebra
   is a product of finite separable fields: an inseparable minimal polynomial would
   give a nilpotent after algebraic closure. Thus the boundary is finite étale by
   [lem-sc-finite-etale-algebra-criterion].
3. By [lem-trf-normalization-inseparable-base-change], the normalization N of (C_K)_red
   equals N₁ × K, remains geometrically normal, and has the reduced boundary (D₁_K)_red.
   Reduced inverse images depend only on supports, so this is the original boundary's
   reduced inverse image too. Its generic field is algebraic over κ(X₀) and contains it;
   the dimension formula gives dimension one over K.
4. Spread K using [lem-trf-projective-inseparable-spread-normalization]. This gives
   excellent integral Y₁, projective proper dominant generically finite b, excellent
   integral X₁, and the commuting maps c and f. The composite c ≫ a is proper dominant
   generically finite, b ≫ q is projective, and the generic fibre is N over κ(y₁) ≅ K.
5. Apply [lem-weil-pbc-geonormal-dim-one-smooth] to this geometrically normal curve.
   It is smooth and geometrically reduced; integrality of the normalized dominant
   component gives nonemptiness and irreducibility. The boundary identification of
   step 3 and the finite étale conclusion of step 2 give the final clause, including
   the empty boundary case.
-/
theorem exists_genericSmoothBoundaryPreparation
    {S X Z Y X₀ : Scheme.{u}}
    (hS : (∃ (k : Type u) (_ : Field k), Nonempty (S ≅ Spec (.of k))) ∨
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
        (_ : IsDiscreteValuationRing R), IsExcellent R ∧ Nonempty (S ≅ Spec (.of R)))
    [IsIntegral X] (p : X ⟶ S) [IsProper p] [IsDominant p]
    (hft : LocallyOfFiniteType p ∧ QuasiCompact p)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : genericPoint X ∉ Set.range i)
    [IsIntegral Y] (hexcY : ∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U))
    (q : Y ⟶ S) [IsHProjective q] [IsDominant q]
    [IsIntegral X₀] (hexcX₀ : ∀ U : X₀.Opens, IsAffineOpen U → IsExcellent Γ(X₀, U))
    (a : X₀ ⟶ X) [IsProper a] [IsDominant a]
    (hafin : ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U))
    (g : X₀ ⟶ Y) [IsProper g] [IsDominant g] (hcomm : a ≫ p = g ≫ q)
    (η : X₀) (hη : IsGenericPoint η Set.univ)
    (htrdeg : @Algebra.trdeg (Y.residueField (g η)) (X₀.residueField η) _ _
      (g.residueFieldMap η).hom.toAlgebra = 1) :
    ∃ (Y₁ X₁ : Scheme.{u}) (b : Y₁ ⟶ Y) (c : X₁ ⟶ X₀) (f : X₁ ⟶ Y₁),
      IsIntegral Y₁ ∧
      (∀ U : Y₁.Opens, IsAffineOpen U → IsExcellent Γ(Y₁, U)) ∧
      IsHProjective b ∧ IsProper b ∧ IsDominant b ∧
      (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (b ∣_ U)) ∧
      IsHProjective (b ≫ q) ∧
      IsIntegral X₁ ∧
      (∀ U : X₁.Opens, IsAffineOpen U → IsExcellent Γ(X₁, U)) ∧
      c ≫ g = f ≫ b ∧ IsProper (c ≫ a) ∧ IsDominant (c ≫ a) ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite ((c ≫ a) ∣_ U)) ∧
      IsProper f ∧ IsDominant f ∧
      ∃ y₁ : Y₁, IsGenericPoint y₁ Set.univ ∧
        (b.residueFieldMap y₁).hom.Finite ∧
        @IsPurelyInseparable (Y.residueField (b y₁)) (Y₁.residueField y₁) _ _
          (b.residueFieldMap y₁).hom.toAlgebra ∧
        Smooth (f.fiberToSpecResidueField y₁) ∧ IrreducibleSpace (f.fiber y₁) ∧
        topologicalKrullDim (f.fiber y₁) = 1 ∧
        IsFinite (((pullback i (c ≫ a)).nilradical.subschemeι ≫
          pullback.snd i (c ≫ a) ≫ f).fiberToSpecResidueField y₁) ∧
        Etale (((pullback i (c ≫ a)).nilradical.subschemeι ≫
          pullback.snd i (c ≫ a) ≫ f).fiberToSpecResidueField y₁) := by
  sorry

end AlgebraicGeometry

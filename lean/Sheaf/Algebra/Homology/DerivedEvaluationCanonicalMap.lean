/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.KFlatConeTrianglePresentation
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # The canonical derived evaluation comparison

Source: Stacks Project, More on Algebra, Tags 0A67, 0A60 and 064J;
Cohomology on Sites, Tag 08JC (blueprint: lem-trf-derived-evaluation-canonical-map).

The comparison is uniquely determined by its adjunction-transpose formula.
Its existence theorem supplies that formula and its functorial and signed
triangulated interface, without importing any downstream invertibility theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

/-- The one-object-site presentation of the ordinary module derived category.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
abbrev evaluationDerivedCategory (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)] := DerivedCategory (RingSiteModules R)

variable (R : Type u) [CommRing R] [HasDerivedCategory.{u} (RingSiteModules R)]

/-- Derived tensor with the fixed derived Hom object.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
abbrev evaluationTensorFunctor (L M : evaluationDerivedCategory R) :
    evaluationDerivedCategory R ⥤ evaluationDerivedCategory R :=
  tensorLeft ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) L).obj M)

/-- Contravariant internal Hom into a fixed target.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
def evaluationDualFunctor (L : evaluationDerivedCategory R) :
    (evaluationDerivedCategory R)ᵒᵖ ⥤ evaluationDerivedCategory R :=
  Prod.sectL (evaluationDerivedCategory R)ᵒᵖ L ⋙
    SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)

/-- The covariant double derived Hom functor.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
def evaluationDoubleHomFunctor (L M : evaluationDerivedCategory R) :
    evaluationDerivedCategory R ⥤ evaluationDerivedCategory R :=
  (evaluationDualFunctor R L).rightOp ⋙ evaluationDualFunctor R M

/-- The signed double contravariant source-shift comparison, including the
triangle-reversal factor `(-1)^m`. Each source shift is the canonical adjunction
mate of the Koszul total-tensor shift, and `shiftFunctor` transports `-(-m)` to `m`.
Source: Stacks 0A60, 08JC (blueprint: lem-trf-derived-evaluation-canonical-map). -/
def evaluationDoubleHomShift (L M K : evaluationDerivedCategory R) (m : ℤ) :
    (evaluationDoubleHomFunctor R L M).obj (K⟦m⟧) ⟶
      ((evaluationDoubleHomFunctor R L M).obj K)⟦m⟧ :=
  m.negOnePow •
    (((evaluationDualFunctor R M).mapIso
      (((SignedRingedHom.sourceShift ⊥
        (CochainComplex.onePointRingSheaf R) K m).app L).op)).inv ≫
      ((SignedRingedHom.sourceShift ⊥ (CochainComplex.onePointRingSheaf R)
        ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)
        (-m)).app M).hom ≫
      eqToHom (congrArg
        (fun n : ℤ ↦ ((evaluationDoubleHomFunctor R L M).obj K)⟦n⟧) (neg_neg m)))

/-- The specified evaluation transpose is natural in all three variables and is
a morphism of exact functors with the standard signed shift comparison.
Source: Stacks 0A67, 0A60, 064J and 08JC
(blueprint: lem-trf-derived-evaluation-canonical-map).

Proof:
1. Use the closed derived tensor--Hom adjunction on the one-object ringed site
(lem-sf-ringed-derived-closed-symmetric-monoidal). Swap the third tensor factor
past the second and compose the two counits. Its transpose is the specified map.
2. Counit naturality identifies the three variable squares after uncurrying:
they evaluate respectively f(u(x)), v(h(f(x))) and h(t(f(x))). Transpose back.
3. K-injective representatives J,I and a K-flat representative P, supplied by
prop-pur-kinjective-resolutions-exist and lem-pc-kflat-resolution, compute the
map as h tensor x sent to f ↦ (-1)^(|x||f|) h(f(x)). This uses
def-pur-derived-internal-hom, lem-weil-pbc-site-derived-tensor-descent,
lem-sc-derived-hom-tensor-total and def-pur-hom-complex. Tensor direct sums have
finite support, so the formula also defines the unbounded comparison.
4. Present triangles by K-flat cones (lem-pc-kflat-cone-triangle-presentation).
The tensor-cone comparison (lem-pc-tensor-mapping-cone-iso) multiplies the
shifted summand by (-1)^|h|. Double contravariant Hom reverses triangles twice
(lem-weil-pbc-ringed-internal-hom-exact-restriction), with the extra (-1)^m.
5. The source-Hom shift multiplies degree-q maps by (-1)^(mq). The resulting
double comparison on g in degree n, tested at f in degree c, is (-1)^(m(n+c)).
For |h|=a, |x|=b and n=a+b-m, the identity
(b-m)(c+m)+m(n+c) ≡ bc+ma mod 2 proves the shift square.
6. Naturality gives the first two triangle squares. Its square on the connecting
map, followed by the shift square, gives the third. Thus the components are
a morphism of distinguished triangles, without asserting invertibility. -/
theorem derived_evaluation_canonical_map :
    ∃ e : ∀ K L M : evaluationDerivedCategory R,
      (evaluationTensorFunctor R L M).obj K ⟶ (evaluationDoubleHomFunctor R L M).obj K,
    (∀ K L M : evaluationDerivedCategory R,
      e K L M =
        (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
          ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)).homEquiv
          _ M ((α_ _ _ _).hom ≫
            _ ◁ ((β_ K _).hom ≫
              (SignedRingedHom.adjunction ⊥
                (CochainComplex.onePointRingSheaf R) K).counit.app L) ≫
            (SignedRingedHom.adjunction ⊥
              (CochainComplex.onePointRingSheaf R) L).counit.app M)) ∧
    (∀ (K K' L L' M M' : evaluationDerivedCategory R)
      (f : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M'),
      ((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
        (l.op, m) ⊗ₘ f) ≫ e K' L' M' =
      e K L M ≫
        (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
          (X := (op ((SignedRingedHom.hom ⊥
            (CochainComplex.onePointRingSheaf R) K).obj L), M))
          (Y := (op ((SignedRingedHom.hom ⊥
            (CochainComplex.onePointRingSheaf R) K').obj L'), M'))
          (((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (f.op, l)).op, m)) ∧
    ∀ L M : evaluationDerivedCategory R,
      (evaluationTensorFunctor R L M).IsTriangulated ∧
      ∃ _ : (evaluationDoubleHomFunctor R L M).CommShift ℤ,
        (∀ (K : evaluationDerivedCategory R) (m : ℤ),
          ((evaluationDoubleHomFunctor R L M).commShiftIso m).hom.app K =
            evaluationDoubleHomShift R L M K m) ∧
        (evaluationDoubleHomFunctor R L M).IsTriangulated ∧
        (∀ (K : evaluationDerivedCategory R) (m : ℤ),
          e (K⟦m⟧) L M ≫
            ((evaluationDoubleHomFunctor R L M).commShiftIso m).hom.app K =
          ((evaluationTensorFunctor R L M).commShiftIso m).hom.app K ≫
            (e K L M)⟦m⟧') ∧
        ∀ (T : Pretriangulated.Triangle (evaluationDerivedCategory R))
          (_hT : T ∈ Pretriangulated.distinguishedTriangles),
          ∃ t : (evaluationTensorFunctor R L M).mapTriangle.obj T ⟶
            (evaluationDoubleHomFunctor R L M).mapTriangle.obj T,
            t.hom₁ = e T.obj₁ L M ∧
            t.hom₂ = e T.obj₂ L M ∧
            t.hom₃ = e T.obj₃ L M := by
  sorry

end DerivedCategory

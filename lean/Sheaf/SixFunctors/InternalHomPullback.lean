/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.FinitePullbackTensorComparison
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.Algebra.Homology.HomComplex

/-! # Internal Hom and pullback with a site-perfect first argument

Source: Weil conjectures blueprint, main-20261015,
sec-six-functors/sk-thm-sf-internal-hom-pullback; Stacks, Tags 08JJ and 07A4
(blueprint: thm-trf-internal-hom-pullback).

The comparison is the closed transpose of pulled-back evaluation using the prescribed
K-flat tensor comparison. The compatibility predicates keep the connecting arrow of
triangles as well as both integer-shift squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace WeilConjectures
namespace TraceFormulaCoefficientConventions

/-- The ambient category at the convention's positive level. Since `T.level ≥ 1`,
`T.level - 1 + 1 = T.level`; the indexing agrees with the recorded finite operations.
Source: blueprint finite coefficient convention (blueprint: thm-trf-internal-hom-pullback). -/
abbrev homPullbackCategory (T : TraceFormulaCoefficientConventions.{u}) (W : Scheme.{u}) :=
  proEtaleDerivedCategory W
    (finiteCoefficientRing T.coefficients.l T.coefficientField (T.level - 1 + 1))

/-- The existing ambient internal Hom, with its contravariant first argument.
Source: blueprint finite operations (blueprint: thm-trf-internal-hom-pullback). -/
abbrev homPullbackHom (T : TraceFormulaCoefficientConventions.{u}) (W : Scheme.{u}) :=
  finiteIntrinsicDerivedInternalHom T.coefficients.l T.coefficientField W (T.level - 1)

/-- The recorded exact module inverse image, with its intrinsic coefficient realization.
Source: blueprint finite operations (blueprint: thm-trf-internal-hom-pullback). -/
abbrev homPullbackFunctor (T : TraceFormulaCoefficientConventions.{u})
    {Y X : Scheme.{u}} (g : Y ⟶ X) :=
  finiteDerivedPullback T.coefficients.l T.coefficientField (T.level - 1) g

/-- The recorded local bounded finite-projective predicate, without imposing
constructibility on the first argument.
Source: blueprint site-perfectness (blueprint: thm-trf-internal-hom-pullback). -/
abbrev homPullbackPerfect (T : TraceFormulaCoefficientConventions.{u}) (W : Scheme.{u}) :=
  IsFiniteCoefficientSitePerfect T.coefficients.l T.coefficientField W (T.level - 1)

/-- The existing bounded constructible finite-Tor predicate on the second argument.
Source: blueprint finite-Tor category (blueprint: thm-trf-internal-hom-pullback). -/
abbrev homPullbackFiniteTor (T : TraceFormulaCoefficientConventions.{u}) (W : Scheme.{u}) :=
  finiteTorConstructible T.coefficients.l T.coefficientField (T.level - 1 + 1)
    (Nat.succ_pos _) W

/-- The inverse of the coefficient prime in each residue field is transported from
its inverse in the geometric base field; no invertibility hypothesis is added.
Source: blueprint global coefficient convention (blueprint: thm-trf-internal-hom-pullback). -/
@[instance_reducible]
def homPullbackUnits (T : TraceFormulaCoefficientConventions.{u}) {W : Scheme.{u}}
    (f : W ⟶ Spec (CommRingCat.of T.datum.k)) :
    ∀ x : W, Invertible (T.coefficients.l : W.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit T.datum T.coefficients.l
      T.coefficients.different).map (f.residueFieldAlgebraMap x) :
        IsUnit (T.coefficients.l : W.residueField x)).invertible

/-- The actual canonical comparison: transpose the inverse tensor comparison followed
by inverse image of evaluation. This defines an arrow for every ambient pair.
Source: blueprint proof step 1 and Stacks 07A4, 08JJ
(blueprint: thm-trf-internal-hom-pullback). -/
def internalHomPullbackComparison (T : TraceFormulaCoefficientConventions.{u})
    {Y : Scheme.{u}} (g : Y ⟶ T.geometricBaseChange)
    (M N : T.homPullbackCategory T.geometricBaseChange) :
    (T.homPullbackFunctor g).obj ((T.homPullbackHom T.geometricBaseChange).obj (op M, N)) ⟶
      (T.homPullbackHom Y).obj
        (op ((T.homPullbackFunctor g).obj M), (T.homPullbackFunctor g).obj N) :=
  letI := T.homPullbackUnits T.structureMap
  letI := T.homPullbackUnits (g ≫ T.structureMap)
  finiteIntrinsicTranspose T.coefficients.l T.coefficientField Y (T.level - 1) _ _ _
    ((canonicalFinitePullbackTensor T.coefficients.l T.coefficientField g (T.level - 1)
      ((T.homPullbackHom T.geometricBaseChange).obj (op M, N)) M).inv ≫
        (T.homPullbackFunctor g).map
          (finiteIntrinsicEvaluation T.coefficients.l T.coefficientField
            T.geometricBaseChange (T.level - 1) M N))

end TraceFormulaCoefficientConventions

/-- The integer-shift square for the specified comparison components. It applies also
on an opposite triangulated category, whose shift has the opposite sign.
Source: blueprint proof step 6 (blueprint: thm-trf-internal-hom-pullback). -/
def TrfHomPullbackShiftSquare
    {C : Type a} {D : Type b} [Category.{v} C] [Category.{w} D]
    [HasShift C ℤ] [HasShift D ℤ] (U V : C ⥤ D)
    [U.CommShift ℤ] [V.CommShift ℤ]
    (β : ∀ X : C, U.obj X ⟶ V.obj X) (P : C → Prop) : Prop :=
  ∀ (n : ℤ) (X : C), P X →
    β (X⟦n⟧) ≫ (V.commShiftIso n).hom.app X =
      (U.commShiftIso n).hom.app X ≫ (β X)⟦n⟧'

/-- The comparison on a distinguished triangle is a morphism of distinguished
triangles, including its connecting-arrow square. All three components are prescribed.
Source: blueprint proof step 6 (blueprint: thm-trf-internal-hom-pullback). -/
def TrfHomPullbackTriangleSquare
    {C : Type a} {D : Type b} [Category.{v} C] [Category.{w} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
    (U V : C ⥤ D) [U.CommShift ℤ] [V.CommShift ℤ]
    (β : ∀ X : C, U.obj X ⟶ V.obj X) (P : C → Prop) : Prop :=
  ∀ (Δ : Triangle C), Δ ∈ distTriang C →
    P Δ.obj₁ → P Δ.obj₂ → P Δ.obj₃ →
      U.mapTriangle.obj Δ ∈ distTriang D ∧ V.mapTriangle.obj Δ ∈ distTriang D ∧
        ∃ φ : U.mapTriangle.obj Δ ⟶ V.mapTriangle.obj Δ,
          φ.hom₁ = β Δ.obj₁ ∧ φ.hom₂ = β Δ.obj₂ ∧ φ.hom₃ = β Δ.obj₃

namespace TraceFormulaCoefficientConventions

/-- The canonical finite-coefficient comparison is invertible for a site-perfect first
argument and a bounded constructible finite-Tor second argument. The two-variable
naturality includes arbitrary, possibly noninvertible, morphisms. The existential
shift structures express the exact Hom functors; pullback has its fixed termwise
shift structure. The right-variable clause supplies the morphism of distinguished
triangles with all three prescribed components.

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-internal-hom-pullback,
node thm-trf-internal-hom-pullback; Stacks 08JJ, 07A4, 08JC.
(blueprint: thm-trf-internal-hom-pullback).

Proof:
1. Use lem-sf-ringed-derived-closed-symmetric-monoidal and
   lem-sfb-ringed-derived-monoidal-comparisons to identify the displayed arrow as
   the closed transpose of pulled-back evaluation with the canonical tensorator.
2. Put D = RHom(M,1). By lem-sfb-ringed-site-perfect-duality and
   lem-sfb-ringed-site-duality-maps the canonical map N tensor D -> RHom(M,N)
   is invertible for every ambient N. Its evaluation is 1_N tensor ev, by the
   composition normalization of def-coef-ringed-tensor-hom-model. The adjunction
   - tensor M left adjoint to - tensor D supplies coevaluation, and its triangle
   identities give an actual dual pair (D,M).
3. Apply pullback to both triangle identities. The tensor, associativity and unit
   comparisons of lem-sfb-ringed-derived-monoidal-comparisons make their images
   the triangle identities of (F D,F M), with transported evaluation e'.
4. Use lem-sfb-dual-tensor-adjunctions. Explicitly, w maps to
   (w tensor 1)(1 tensor coev), with inverse u maps to (1 tensor e')(u tensor 1).
   The two triangle identities show these are inverse. Uniqueness of right
   adjoints identifies V tensor F D with RHom(F M,V), with evaluation 1 tensor e'.
5. Compose F RHom(M,N) -> F(N tensor D) -> F N tensor F D -> RHom(F M,F N).
   All three arrows are invertible. Its transpose equals pulled-back evaluation
   by steps 2--4, so injectivity of transposition identifies it with the defined
   comparison and proves the first clause.
6. Transpose the natural evaluation identity for a:M'->M and b:N->N' to obtain
   the displayed two-variable naturality square. Use exact pullback from
   lem-weil-pbc-ringed-topoi-derived-pullback and Hom exactness from
   lem-weil-pbc-ringed-internal-hom-exact-restriction. On Hom representatives the
   differential is d_N f - (-1)^degree(f) f d_M (def-pur-hom-complex).
   A target shift reindexes; a source shift by s reindexes and multiplies the
   degree-r family by (-1)^(sr). Evaluation commutes with both signed maps.
   Evaluation into a cone is componentwise on N2 plus N1[1], preserving the
   inclusion, projection and cone differential. Descend these identities through
   the normalized representative comparisons. This gives both shift squares and
   the morphism of distinguished triangles, including the connecting arrow.
   Restrict the second argument to the stated finite-Tor constructible category. -/
theorem internalHomPullback
    (T : TraceFormulaCoefficientConventions.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ T.geometricBaseChange)
    [LocallyOfFiniteType (g ≫ T.structureMap)] [QuasiCompact (g ≫ T.structureMap)] :
    (∀ (M N : T.homPullbackCategory T.geometricBaseChange),
      T.homPullbackPerfect T.geometricBaseChange M →
      T.homPullbackFiniteTor T.geometricBaseChange N →
        IsIso (T.internalHomPullbackComparison g M N)) ∧
    (∀ (M M' N N' : T.homPullbackCategory T.geometricBaseChange),
      T.homPullbackPerfect T.geometricBaseChange M →
      T.homPullbackPerfect T.geometricBaseChange M' →
      T.homPullbackFiniteTor T.geometricBaseChange N →
      T.homPullbackFiniteTor T.geometricBaseChange N' →
      ∀ (a : M' ⟶ M) (b : N ⟶ N'),
        (T.homPullbackFunctor g).map
            ((T.homPullbackHom T.geometricBaseChange).map (Prod.mkHom a.op b)) ≫
          T.internalHomPullbackComparison g M' N' =
        T.internalHomPullbackComparison g M N ≫
          (T.homPullbackHom Y).map (Prod.mkHom
            ((T.homPullbackFunctor g).map a).op ((T.homPullbackFunctor g).map b))) ∧
    (∀ (M : T.homPullbackCategory T.geometricBaseChange),
      T.homPullbackPerfect T.geometricBaseChange M →
      ∃ _ : ((Functor.curry.obj (T.homPullbackHom T.geometricBaseChange)).obj
          (op M)).CommShift ℤ,
      ∃ _ : ((Functor.curry.obj (T.homPullbackHom Y)).obj
          (op ((T.homPullbackFunctor g).obj M))).CommShift ℤ,
        ((Functor.curry.obj (T.homPullbackHom T.geometricBaseChange)).obj
          (op M)).IsTriangulated ∧
        ((Functor.curry.obj (T.homPullbackHom Y)).obj
          (op ((T.homPullbackFunctor g).obj M))).IsTriangulated ∧
        TrfHomPullbackShiftSquare
          (((Functor.curry.obj (T.homPullbackHom T.geometricBaseChange)).obj (op M)) ⋙
            T.homPullbackFunctor g)
          (T.homPullbackFunctor g ⋙ ((Functor.curry.obj (T.homPullbackHom Y)).obj
            (op ((T.homPullbackFunctor g).obj M))))
          (T.internalHomPullbackComparison g M) (T.homPullbackFiniteTor T.geometricBaseChange) ∧
        TrfHomPullbackTriangleSquare
          (((Functor.curry.obj (T.homPullbackHom T.geometricBaseChange)).obj (op M)) ⋙
            T.homPullbackFunctor g)
          (T.homPullbackFunctor g ⋙ ((Functor.curry.obj (T.homPullbackHom Y)).obj
            (op ((T.homPullbackFunctor g).obj M))))
          (T.internalHomPullbackComparison g M) (T.homPullbackFiniteTor T.geometricBaseChange)) ∧
    (∀ (N : T.homPullbackCategory T.geometricBaseChange),
      T.homPullbackFiniteTor T.geometricBaseChange N →
      ∃ _ : ((Functor.curry.obj (T.homPullbackHom T.geometricBaseChange)).flip.obj
          N).CommShift ℤ,
      ∃ _ : ((Functor.curry.obj (T.homPullbackHom Y)).flip.obj
          ((T.homPullbackFunctor g).obj N)).CommShift ℤ,
        ((Functor.curry.obj (T.homPullbackHom T.geometricBaseChange)).flip.obj
          N).IsTriangulated ∧
        ((Functor.curry.obj (T.homPullbackHom Y)).flip.obj
          ((T.homPullbackFunctor g).obj N)).IsTriangulated ∧
        TrfHomPullbackShiftSquare
          (((Functor.curry.obj (T.homPullbackHom T.geometricBaseChange)).flip.obj N) ⋙
            T.homPullbackFunctor g)
          ((T.homPullbackFunctor g).op ⋙ ((Functor.curry.obj (T.homPullbackHom Y)).flip.obj
            ((T.homPullbackFunctor g).obj N)))
          (fun M ↦ T.internalHomPullbackComparison g M.unop N)
          (fun M ↦ T.homPullbackPerfect T.geometricBaseChange M.unop)) := by
  sorry

end TraceFormulaCoefficientConventions
end WeilConjectures

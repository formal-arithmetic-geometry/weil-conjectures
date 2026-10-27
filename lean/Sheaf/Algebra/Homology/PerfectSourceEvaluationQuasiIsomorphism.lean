/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Homology.RingedDerivedTensorNative

/-! # Perfect-source tensor evaluation on arbitrary representatives

Source: Stacks Project, more-algebra.tex, Tags 0BYM, 0BYN and 0ATK (1)
(blueprint: lem-trf-perfect-source-evaluation-quasi-isomorphism).
The direct-sum tensor and product Hom are the existing ordinary-module constructions.
The Hom-model normalization below specifies its actual evaluation, and hence fixes
its comparison with the existing K-injective derived internal Hom.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedCategory Opposite
open scoped TensorProduct

namespace CochainComplex

/-- The canonical comparison obtained by transposing tensor with evaluation. The
braiding is the existing localization of the native Koszul braiding, not a choice
of a new braided structure. The existing `ihomTensorToIhom` supplies the comparison
with tensor on the right; the native braiding transports it to tensor on the left.
The internal Hom is exactly
`ordinaryModuleDerivedInternalHom R`, written in its curried form.
Source: Stacks 0BYN (blueprint: lem-trf-perfect-source-evaluation-quasi-isomorphism). -/
def perfectSourceDerivedEvaluation {R : Type u} [CommRing R]
    (M F J : DerivedCategory (ModuleCat.{u} R)) :
    F ⊗ (ihom M).obj J ⟶ (ihom M).obj (F ⊗ J) :=
  (DerivedMonoidal.braiding' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) F ((ihom M).obj J)).hom ≫
    MonoidalClosed.ihomTensorToIhom M J F ≫
    (ihom M).map (DerivedMonoidal.braiding' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) J F).hom

/-- The K-injective Hom identification, normalized by signed evaluation with the
Hom-source placed first. After swapping the two factors, this is the unsigned
formula `h tensor x` sent to `h(x)`. Specifying evaluation makes the derived Hom
identification canonical, rather than an arbitrary isomorphism of objects.
Source: Stacks 0A5W, 0A5Y and 0BYN
(blueprint: lem-trf-perfect-source-evaluation-quasi-isomorphism). -/
def PerfectSourceHomModel {R : Type u} [CommRing R]
    (M V : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : DerivedCategory.Q.obj (moduleHomComplex M V) ≅
      (ihom (DerivedCategory.Q.obj M)).obj (DerivedCategory.Q.obj V)) : Prop :=
  ∃ ev : M ⊗ moduleHomComplex M V ⟶ V,
    (∀ (p r : ℤ) (x : M.X p) (h : (moduleHomComplex M V).X r),
      ev.f (p + r)
        (HomologicalComplex.ιTensorObj M (moduleHomComplex M V) p r (p + r) rfl
          (x ⊗ₜ[R] h)) = (p * r).negOnePow • (h.v p (p + r) rfl) x) ∧
    Functor.LaxMonoidal.μ DerivedCategory.Q M (moduleHomComplex M V) ≫
        DerivedCategory.Q.map ev =
      DerivedCategory.Q.obj M ◁ e.hom ≫
        (ihom.ev (DerivedCategory.Q.obj M)).app (DerivedCategory.Q.obj V)

/-- Perfect-source tensor evaluation is a quasi-isomorphism and is precisely the
canonical derived evaluation comparison, under the evaluation-normalized Hom
models and the native K-flat tensor comparisons. All complexes are unbounded;
only the derived class of M is required to be perfect.
Source: Stacks 0ATK (1), 0BYM and 0BYN
(blueprint: lem-trf-perfect-source-evaluation-quasi-isomorphism).

Proof:
1. Form c_M(f tensor h)(x) = f tensor h(x), then postcompose with q.
The direct-sum tensor has finite support and the Hom coordinates are products.
The Hom differential gives d_F f tensor h + (-1)^p f tensor d_J h
- (-1)^(p+r) f tensor h d_M on both sides. Thus this is a chain map,
with no extra sign (def-pur-hom-complex, def-pc-tensor-complex-sheaves).
2. Choose a bounded finite-projective P representing QM by perfectness.
The projective-source morphism theorem gives a quasi-isomorphism a : P to M
(lem-pc-ring-derived-map-representative). K-injective Hom invariance gives
quasi-isomorphisms Hom(M,V) to Hom(P,V) for V = J,I
(lem-pur-rhom-well-defined).
3. For P, rearrange the finitely many source-degree products into sums.
Finite generation makes Hom(P^s,-) commute with direct sums. The canonical
finite-projective tensor-Hom equivalence on each summand identifies c_P
with a degreewise isomorphism (lem-pc-finite-projective-module-tensor-hom).
4. The projective Hom evaluation model makes Hom(P,q) a quasi-isomorphism
(lem-pod-projective-hom-evaluation-model). Hence t_P is one.
5. Precomposition with a gives the commuting square with rows t_M,t_P.
K-flatness of F makes its left vertical arrow a quasi-isomorphism, and
K-injectivity makes its right vertical arrow one. Two-out-of-three proves
t_M is a quasi-isomorphism, equivalently its localization is invertible.
6. P is K-flat since it is bounded and projective (hence flat), by
lem-weil-pbc-projective-module-flat and lem-pc-module-bounded-flat-kflat.
The one-K-flat uncurrying normalization identifies the transpose of t_P
with q after F tensor evaluation and the native associator
(lem-trf-module-one-kflat-uncurry-normalization). The native tensor
comparisons preserve associators and counits
(lem-pc-source-kflat-module-tensor-model,
lem-sf-ringed-tensor-complex-constraints, lem-sf-ringed-derived-native-tensor).
Thus Q(t_P) is the stated canonical comparison.
7. The K-injective Hom models compute RHom (def-pur-derived-internal-hom).
Naturality of the K-flat comparison and the tensor-Hom adjunction transports
the precomposition square to the derived square
(lem-sf-ringed-derived-tensor-hom-adjunction). Its vertical arrows are
invertible, so the equality for P gives exactly the displayed equality for M. -/
theorem perfect_source_evaluation_quasi_isomorphism
    (R : Type u) [CommRing R] (M F J I : CochainComplex (ModuleCat.{u} R) ℤ)
    (_hM : IsPerfectRingComplex (DerivedCategory.Q.obj M))
    (_hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F)
    [J.IsKInjective] [I.IsKInjective] (q : F ⊗ J ⟶ I) [QuasiIso q] :
    ∃ t : F ⊗ moduleHomComplex M J ⟶ moduleHomComplex M I,
      (∀ (p r s : ℤ) (f : F.X p) (h : (moduleHomComplex M J).X r) (x : M.X s),
        ((t.f (p + r)
          (HomologicalComplex.ιTensorObj F (moduleHomComplex M J) p r (p + r) rfl
            (f ⊗ₜ[R] h))).v s (s + (p + r)) rfl) x =
          q.f (s + (p + r))
            (HomologicalComplex.ιTensorObj F J p (s + r) (s + (p + r))
              (by omega) (f ⊗ₜ[R] (h.v s (s + r) rfl) x))) ∧
      QuasiIso t ∧ IsIso (DerivedCategory.Q.map t) ∧
      ∃ (eJ : DerivedCategory.Q.obj (moduleHomComplex M J) ≅
          (ihom (DerivedCategory.Q.obj M)).obj (DerivedCategory.Q.obj J))
        (eI : DerivedCategory.Q.obj (moduleHomComplex M I) ≅
          (ihom (DerivedCategory.Q.obj M)).obj (DerivedCategory.Q.obj I)),
        PerfectSourceHomModel M J eJ ∧ PerfectSourceHomModel M I eI ∧
        Functor.LaxMonoidal.μ DerivedCategory.Q F (moduleHomComplex M J) ≫
            DerivedCategory.Q.map t ≫ eI.hom =
          DerivedCategory.Q.obj F ◁ eJ.hom ≫
            perfectSourceDerivedEvaluation (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj J) ≫
            (ihom (DerivedCategory.Q.obj M)).map
              (Functor.LaxMonoidal.μ DerivedCategory.Q F J ≫ DerivedCategory.Q.map q) := by
  sorry

end CochainComplex

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Algebra.Homology.TwoStepFilteredTotal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace
import Sheaf.Algebra.Homology.FilteredProjectiveModel
import Sheaf.Algebra.Homology.KFlatScalarExtensionCounit
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Paper.FieldComplexScalarExtension
import Sheaf.Paper.PointFdComplexes

/-!
# Formal laws for the categorical trace

Source: Weil blueprint, main-20261015, `sk-p-trace/prop-trf-trace-formal-laws`,
clauses (1)--(4); Stacks Project, Tags 03TB, 03TJ and 087J
(blueprint: prop-trf-trace-formal-laws).

The first three laws use exactly `A = O_E / ϖ_E^n`, with `n ≥ 1`, from the fixed
finite-field datum and coefficient conventions. The target of scalar extension uses
the same signed dual-frame construction over an arbitrary commutative ring. Perfectness means
a bounded finite-projective
model, never merely bounded finite cohomology. The filtered law is stated on the
filtered derived object itself: its total and graded endomorphisms induce the triangle
in clause (2). In particular every filtration-preserving chain endomorphism is covered.
It asserts no additivity for arbitrary endomorphisms of Verdier triangles. The explicit
`Z/4` counterexample and its middle trace `-2 ≠ 0` are the warning in that clause.

Scalar extension is quantified over a universal left derived functor together with its
counit and universal property. This specifies exactly derived extension of scalars and
allows a nonflat target. The field law applies both to finite coefficient fields and to
the actual ordinary-module category over the algebraic closure. The last statement
separately treats the common-stage category: it characterizes its scalar trace uniquely
by all common-stage presentations, without identifying it with the entire D(Qbar).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex

namespace DerivedCategory

/-- Additivity of the recorded ordinary scalar-extension functor, needed to form its
homotopy functor in clause (3). Source: the termwise tensor construction in the blueprint
(blueprint: prop-trf-trace-formal-laws). -/
noncomputable instance traceExtendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  ModuleCat.extendScalars_additive_sheaf ρ

/-- Conjugacy invariance, clause (1), for the signed perfect-complex trace.
Source: blueprint trace formal laws, clause (1)
(blueprint: prop-trf-trace-formal-laws).
Proof: choose a bounded finite-projective model of `P₁` and transport its representative
isomorphism along `w` for `P₂`. The dual isomorphism reverses composition. The evaluation
and coevaluation transports in `def-trf-categorical-trace` cancel `w` and its dual in the
trace composite; the signed symmetry is natural. Use the intertwining identity.
`lem-trf-chain-supertrace` gives independence of the chosen model and homotopies. -/
theorem perfectCategoricalTrace_conjugacy
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (P₁ P₂ : DerivedCategory.{u}
      (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)))
    (h₁ : IsPerfectRingComplex.{u, u} P₁) (h₂ : IsPerfectRingComplex.{u, u} P₂)
    (v₁ : P₁ ⟶ P₁) (v₂ : P₂ ⟶ P₂) (w : P₁ ≅ P₂)
    (hw : w.hom ≫ v₂ = v₁ ≫ w.hom) :
    WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn P₁ h₁ v₁ =
      WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn P₂ h₂ v₂ := by
  sorry

/-- Additivity for exactly the localized filtered endomorphisms of clause (2).
Source: blueprint trace formal laws, clause (2); Stacks, Tags 03TB and 03TJ
(blueprint: prop-trf-trace-formal-laws).
Proof: `lem-trf-filtered-projective-model` replaces the filtered object and its
endomorphism by a bounded finite-projective filtered chain model. Degreewise splitting
of its short exact sequence makes the endomorphism block triangular. The dual frame
trace is the sum of the two diagonal traces: quotient functionals kill the off-diagonal
image in the subcomplex. Multiply by the degree signs and sum over a common finite
interval. `lem-trf-chain-supertrace` identifies these sums with the three categorical
traces; clause (1) transports back to the original objects and endomorphisms.
This includes all strictly compatible endomorphisms of bounded finite-projective short
exact sequences by applying the canonical filtered localization functor. -/
theorem perfectCategoricalTrace_filtered_additivity
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (P : TwoStepModuleDerived (Padic.coefficientExtensionRing c.l E n)) (v : P ⟶ P)
    (h : IsPerfectRingComplex.{u, u}
      ((twoStepTotal.{u, u} (Padic.coefficientExtensionRing c.l E n)).obj P))
    (h' : IsPerfectRingComplex.{u, u}
      ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) true).obj P))
    (h'' : IsPerfectRingComplex.{u, u}
      ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) false).obj P)) :
    WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn _ h
        ((twoStepTotal.{u, u} (Padic.coefficientExtensionRing c.l E n)).map v) =
      WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn _ h'
        ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) true).map v) +
      WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn _ h''
        ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) false).map v) := by
  sorry

/-- The explicit `Z/4` warning in clause (2): a Verdier triangle endomorphism
with zero end maps and nonzero middle trace. Its middle chain model is `R → R`,
differential `2`, in degrees `0,1`, and its endomorphism has components `0,2`.
Source: blueprint trace formal laws, clause (2); Stacks, Tag 087J
(blueprint: prop-trf-trace-formal-laws).
Proof: take the degreewise split exact sequence `R[-1] → [R → R] → R[0]`.
The middle differential and degree-one endomorphism are multiplication by two;
the chain equation is `2*2=0`. The left triangle square commutes by the homotopy
whose degree-one component is the identity; the right square commutes strictly,
and the last square is zero on both sides. The cone-to-quotient map is a
quasi-isomorphism, with contractible kernel the cone of the identity, so the
triangle is distinguished. The two terms are finite free. The chain supertrace
of the middle endomorphism is `0-2=-2`, nonzero in `Z/4`; both end maps are zero.
The restriction of the chain endomorphism to the subcomplex is two, rather than
the prescribed zero endomorphism, so this triple does not have filtered origin. -/
theorem perfectCategoricalTrace_triangle_counterexample :
    ∃ (M : CochainComplex (ModuleCat.{0} (ZMod 4)) ℤ) (w : M ⟶ M)
      (e₀ : M.X 0 ≅ ModuleCat.of (ZMod 4) (ZMod 4))
      (e₁ : M.X 1 ≅ ModuleCat.of (ZMod 4) (ZMod 4)),
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (M.X i)) ∧
      e₀.inv ≫ M.d 0 1 ≫ e₁.hom = ModuleCat.ofHom (2 • LinearMap.id) ∧
      w.f 0 = 0 ∧ e₁.inv ≫ w.f 1 ≫ e₁.hom = ModuleCat.ofHom (2 • LinearMap.id) ∧
      ∃ (ι : (CochainComplex.singleFunctor (ModuleCat.{0} (ZMod 4)) 1).obj
          (ModuleCat.of (ZMod 4) (ZMod 4)) ⟶ M)
        (π : M ⟶ (CochainComplex.singleFunctor (ModuleCat.{0} (ZMod 4)) 0).obj
          (ModuleCat.of (ZMod 4) (ZMod 4))),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 1
          (ModuleCat.of (ZMod 4) (ZMod 4))).inv ≫ ι.f 1 ≫ e₁.hom = 𝟙 _ ∧
        e₀.inv ≫ π.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (ModuleCat.of (ZMod 4) (ZMod 4))).hom = 𝟙 _ ∧
        ∃ (T : Triangle (DerivedCategory.{0} (ModuleCat.{0} (ZMod 4)))) (f : T ⟶ T),
          T ∈ distTriang _ ∧
          ∃ (a : T.obj₁ ≅ Q.obj ((CochainComplex.singleFunctor
              (ModuleCat.{0} (ZMod 4)) 1).obj (ModuleCat.of (ZMod 4) (ZMod 4))))
            (b : T.obj₂ ≅ Q.obj M)
            (c : T.obj₃ ≅ Q.obj ((CochainComplex.singleFunctor
              (ModuleCat.{0} (ZMod 4)) 0).obj (ModuleCat.of (ZMod 4) (ZMod 4)))),
            T.mor₁ ≫ b.hom = a.hom ≫ Q.map ι ∧
            T.mor₂ ≫ c.hom = b.hom ≫ Q.map π ∧
            f.hom₁ = 0 ∧ f.hom₃ = 0 ∧ f.hom₂ ≫ b.hom = b.hom ≫ Q.map w ∧
            ∃ h : IsPerfectRingComplex.{0, 0} T.obj₂,
              perfectCategoricalTrace.{0} (R := ZMod 4) T.obj₂ h f.hom₂ = -2 ∧
              perfectCategoricalTrace.{0} (R := ZMod 4) T.obj₂ h f.hom₂ ≠ 0 := by
  sorry

/-- Derived scalar extension preserves perfectness and the categorical trace, clause (3).
Source: blueprint trace formal laws, clause (3)
(blueprint: prop-trf-trace-formal-laws).
Proof: represent `P` and its endomorphism by a bounded finite-projective complex and a
chain map (`lem-pc-ring-derived-map-representative`). Projective modules are flat
(`lem-weil-pbc-projective-module-flat`), so `lem-pc-module-bounded-flat-kflat` and
`lem-pc-kflat-scalar-extension-counit` identify the universal derived extension with
termwise tensor, naturally on the endomorphism. Tensor finite-free splittings to see
that the new terms are finite projective. Tensor the dual frames: each new frame trace
is the image under `ρ` of the old one. Apply `lem-trf-chain-supertrace` on both sides and
move `ρ` through the finite signed sum. No flatness of the target ring is needed. -/
theorem perfectCategoricalTrace_scalar_extension
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E]
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [CommRing B]
    (ρ : Padic.coefficientExtensionRing c.l E n →+* B)
    (LF : DerivedCategory.{u} (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)) ⥤
      DerivedCategory.{u} (ModuleCat.{u} B))
    (ε : Qh ⋙ LF ⟶ (ModuleCat.extendScalars ρ).mapHomotopyCategory (.up ℤ) ⋙ Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n))
        (.up ℤ)))
    (P : DerivedCategory.{u} (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)))
    (hP : IsPerfectRingComplex.{u, u} P) (v : P ⟶ P) :
    ∃ hB : IsPerfectRingComplex.{u, u} (LF.obj P),
      ρ (WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn P hP v) =
        perfectCategoricalTrace.{u} (R := B) _ hB (LF.map v) := by
  sorry

/-- The cohomological supertrace, clause (4), including perfectness of its field object.
Source: blueprint trace formal laws, clause (4)
(blueprint: prop-trf-trace-formal-laws).
Proof: split cycles into boundaries and cohomology, and terms into cycles and complements,
using projectivity of vector spaces (`lem-weil-pbc-vector-space-projective` and
`def-weil-pbc-projective-module`). The zero-differential cohomology complex is a bounded
finite-dimensional model. For a bounded model and chain representative of `v`, use the
canonical truncations `T_i`: terms below `i`, cycles in degree `i`, and zero above.
Their successive quotients have image of the differential in degree `i` and cycles in
degree `i+1`. The cone-to-quotient map is a quasi-isomorphism: its kernel is the cone of
the identity, contracted by `(x,y) ↦ (0,x)`. These truncation endomorphisms have filtered
origin. Apply clause (2) and `lem-trf-chain-supertrace`. Splitting boundaries from cycles
cancels their signed traces, leaving the degree `i+1` cohomology trace. Sum over the
bounded degree interval; the increments telescope from zero to the whole model.
The finitely supported sum is independent of the chosen interval. -/
theorem perfectCategoricalTrace_cohomology
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E] :
    (∀ (P : DerivedCategory.{u} (ModuleCat.{u} E))
      (hP : pointFiniteDimensional E P) (v : P ⟶ P),
      ∃ h : IsPerfectRingComplex.{u, u} P,
        perfectCategoricalTrace.{u} (R := E) P h v = ∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace E ((homologyFunctor.{u} (ModuleCat.{u} E) i).obj P)
            (((homologyFunctor.{u} (ModuleCat.{u} E) i).map v).hom)) ∧
    (∀ (P : DerivedCategory.{u} (ModuleCat.{u} c.Qbar))
      (hP : pointFiniteDimensional c.Qbar P) (v : P ⟶ P),
      ∃ h : IsPerfectRingComplex.{u, u} P,
        perfectCategoricalTrace.{u} (R := c.Qbar) P h v = ∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace c.Qbar ((homologyFunctor.{u} (ModuleCat.{u} c.Qbar) i).obj P)
            (((homologyFunctor.{u} (ModuleCat.{u} c.Qbar) i).map v).hom)) := by
  sorry

/-- The common-stage Qlbar trace is the unique scalar computed at every finite
coefficient-field presentation, and is the corresponding cohomological supertrace.
Source: blueprint trace formal laws, clause (4), common-stage paragraph
(blueprint: prop-trf-trace-formal-laws).
Proof: `def-weil-point-fd-qlbar-category` represents an endomorphism at a common finite
stage. Apply the preceding field calculation there and embed its scalar into the fixed
closure. On further extension, exact field scalar extension identifies cohomology with
scalar-extended cohomology (`def-weil-finite-dimensional-complex-scalar-extension`).
The dual-frame calculation of clause (3) shows both traces extend by the same inclusion.
Equality of two presentations is witnessed at a common larger finite stage; hence their
scalars agree. This proves existence, independence and uniqueness, without assuming an
equivalence between the common-stage category and D(Qlbar). -/
theorem perfectCategoricalTrace_common_stage
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X : PointFdQbar c.l c.Qbar) (v : X ⟶ X) :
    ∃! t : c.Qbar, ∀ (E : Padic.FiniteCoefficientFields c.l c.Qbar)
      (P : (pointFiniteDimensional E.val).FullSubcategory)
      (e : (pointFdQbarStage c.l c.Qbar E).obj P ≅ X) (w : P.obj ⟶ P.obj),
      (pointFdQbarStage c.l c.Qbar E).map (ObjectProperty.homMk w) ≫ e.hom = e.hom ≫ v →
      ∃ h : IsPerfectRingComplex.{u, u} P.obj,
        E.val.subtype (perfectCategoricalTrace.{u} (R := E.val) P.obj h w) = t ∧
        E.val.subtype (∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace E.val ((homologyFunctor.{u} (ModuleCat.{u} E.val) i).obj P.obj)
            (((homologyFunctor.{u} (ModuleCat.{u} E.val) i).map w).hom)) = t := by
  sorry

end DerivedCategory

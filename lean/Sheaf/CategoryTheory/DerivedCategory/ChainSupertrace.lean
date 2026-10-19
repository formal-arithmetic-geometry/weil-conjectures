/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import Mathlib.LinearAlgebra.Trace
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy
import Sheaf.CategoryTheory.DerivedCategory.FrameDualMate
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Chain-level supertrace with finite dual frames

Source: Weil conjectures blueprint, trace formula, `sk-p-trace`,
`lem-trf-chain-supertrace` and its twelve-step DAG proof
(blueprint: lem-trf-chain-supertrace).

The frame package is the existing finite-free splitting package: its columns and
coordinate functionals are precisely a finite dual frame, including nonfree projectives.
The dual is the recorded total module Hom into the degree-zero unit. All tensors,
associators and unitors are the canonical total-complex constructions; the braiding
is the Koszul braiding. The interval in the finite sums is any interval supporting `P`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace DerivedCategory

variable {A : Type u} [CommRing A]

/-- Degree zero of the chain tensor unit is the coefficient module.
Source: the unit convention in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceUnitCoordinate :
    (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).X 0 ≅ ModuleCat.of A A :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)

/-- A frame functional placed in dual degree `-i`, zero in every other component.
Source: the displayed dual and dual-frame conventions in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceFrameDual {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (a : Fin (s.N i)) :
    (perfectTraceModelDual P).X (-i) :=
  CochainComplex.HomComplex.Cochain.single
    (ModuleCat.ofHom (perfectTraceFrameFunctional s i a) ≫ chainTraceUnitCoordinate.inv) (-i)

/-- The finite dual-frame tensor in total degree zero.
Source: the coevaluation formula in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceFrameTensor {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (a : Fin (s.N i)) :
    (P ⊗ perfectTraceModelDual P).X 0 :=
  (HomologicalComplex.ιTensorObj P (perfectTraceModelDual P) i (-i) 0
    (add_neg_cancel i)).hom
      (perfectTraceFrameVector s i a ⊗ₜ[A] chainTraceFrameDual s i a)

/-- The ordinary projective-module trace in degree `i`, computed with a finite dual frame.
This definition does not assume that the projective term has a basis.
Source: the ordinary trace convention in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceTerm {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ)
    (t : P.X i ⟶ P.X i) : A :=
  ∑ a : Fin (s.N i), perfectTraceFrameFunctional s i a (t.hom (perfectTraceFrameVector s i a))

/-- The alternating sum of ordinary projective traces on a finite supporting interval.
Source: part (c) of `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainSupertrace {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ) (v : P ⟶ P) : A :=
  ∑ i ∈ Finset.Icc a b, i.negOnePow • chainTraceTerm s i (v.f i)

variable [HasDerivedCategory.{u} (ModuleCat.{u} A)]

/-- The canonical comparison between the image of the chain unit and the derived unit.
Source: the scalar identification and derived-model paragraph of `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceUnitIso :
    Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) ≅
      𝟙_ (DerivedCategory (ModuleCat.{u} A)) :=
  ((singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)).symm ≪≫
    singleFunctorObjUnitIso (ModuleCat.{u} A)

/-- The explicit evaluation and frame coevaluation are chain maps, are independent of
frames, satisfy both triangle identities, and compute the categorical trace and its
derived descent. Source: trace formula, `sk-p-trace/lem-trf-chain-supertrace`, parts
(a)--(c) and the concluding derived-invariance paragraph
(blueprint: lem-trf-chain-supertrace).

Proof (the twelve steps of the DAG node):
1. Split a finite free surjection onto each finite projective term. Its columns and
coordinate maps give a finite dual frame, empty for a zero term. Duals and finite tensors
are again finite projective by taking duals and tensors of these splittings (Stacks 00NX).
2. Expand each vector of one frame in another frame. The two finite double sums show
that the coevaluation tensor is independent of the splitting.
3. For maps between two framed modules expand both frames to prove rectangular cyclicity
of the frame trace. Taking an identity map proves frame independence. A basis gives the
diagonal matrix sum, and its identity trace is its rank times one.
4. The total Hom differential is the stated signed dual differential. Its square and
the tensor differential square vanish. The Koszul symmetry commutes with the differential;
the canonical associators and unitors preserve these differentials and satisfy coherence.
5. Evaluation is zero outside total degree zero. On degree minus one its two differential
terms have coefficients (-1)^(j+1) and (-1)^j and cancel.
6. In degree (i+1,-i) the differential of coevaluation is the sum of d(e_i) tensor eps_i
minus e_(i+1) tensor (eps_(i+1) composed with d). Expanding the two frames cancels it.
7. The two triangle composites are the frame identity and its dual identity, respectively.
8. Apply coevaluation, v, the symmetry, and evaluation. The symmetry contributes
(-1)^(i*(-i)) = (-1)^i, giving the alternating projective trace and the identity formula.
9. For a homotopy v-w=dh+hd use rectangular cyclicity and shift the finite summation index;
the two alternating sums cancel.
10. Projective terms are flat (lem-weil-pbc-projective-module-flat); bounded flat complexes
are K-flat (lem-pc-module-bounded-flat-kflat). The identity K-flat models compute the
derived tensor comparisons (lem-pc-derived-tensor-second-factor-functor). The fully faithful
single functor identifies the scalar with its value at one
(lem-weil-pbc-derived-single-fully-faithful).
11. The homotopy-to-derived Hom map from a bounded projective complex is bijective
(lem-pc-ring-derived-map-representative). Thus every derived endomorphism has a chain
representative, unique up to homotopy; step 9 defines the function on all endomorphisms.
12. Precomposition defines the dual of a chain map. Frame expansion proves naturality of
evaluation and coevaluation. The dual homotopy in degree j is (-1)^j times precomposition
by the original homotopy. Consequently derived representative isomorphisms transport both
duality maps, and naturality of the Koszul symmetry cancels the inverse pairs in the trace.
This is exactly perfectCategoricalTrace, hence its finite-coefficient specialization. -/
theorem chain_supertrace (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfinite : ∀ i : ℤ, Module.Finite A (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective A (P.X i)) :
    (∃ s : ModuleCat.StrictPerfectCoefficientPackage P,
      ∀ i : ℤ, IsZero (P.X i) → s.N i = 0) ∧
    ∃ (ev : perfectTraceModelDual P ⊗ P ⟶ 𝟙_ _) (coev : 𝟙_ _ ⟶ P ⊗ perfectTraceModelDual P)
      (hP : IsPerfectRingComplex (Q.obj P)),
      (∀ (i : ℤ) (φ : (perfectTraceModelDual P).X (-i)) (p : P.X i),
        chainTraceUnitCoordinate.hom.hom
          ((ev.f 0).hom ((HomologicalComplex.ιTensorObj (perfectTraceModelDual P) P
            (-i) i 0 (neg_add_cancel i)).hom (φ ⊗ₜ[A] p))) =
        chainTraceUnitCoordinate.hom.hom ((φ.v i 0 (add_neg_cancel i)).hom p)) ∧
      (∀ n : ℤ, n ≠ 0 → ev.f n = 0) ∧
      (∀ s : ModuleCat.StrictPerfectCoefficientPackage P,
        (∀ i : ℤ, IsZero (P.X i) → s.N i = 0) →
        (coev.f 0).hom (chainTraceUnitCoordinate.inv.hom 1) =
          ∑ i ∈ Finset.Icc a b, ∑ r : Fin (s.N i), chainTraceFrameTensor s i r) ∧
      ((ρ_ (perfectTraceModelDual P)).inv ≫ perfectTraceModelDual P ◁ coev ≫
        (α_ (perfectTraceModelDual P) P (perfectTraceModelDual P)).inv ≫
        ev ▷ perfectTraceModelDual P ≫ (λ_ (perfectTraceModelDual P)).hom = 𝟙 _) ∧
      ((λ_ P).inv ≫ coev ▷ P ≫ (α_ P (perfectTraceModelDual P) P).hom ≫
        P ◁ ev ≫ (ρ_ P).hom = 𝟙 P) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v : P ⟶ P),
        coev ≫ v ▷ perfectTraceModelDual P ≫
          (CochainComplex.Monoidal.braiding P (perfectTraceModelDual P)).hom ≫ ev =
        (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (chainSupertrace s a b v • LinearMap.id))) ∧
      (∀ (s t : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ)
        (v : P.X i ⟶ P.X i), chainTraceTerm s i v = chainTraceTerm t i v) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (n : ℕ)
        (e : Module.Basis (Fin n) A (P.X i)) (v : P.X i ⟶ P.X i),
        chainTraceTerm s i v = ∑ r : Fin n, e.repr (v.hom (e r)) r ∧
        chainTraceTerm s i v = LinearMap.trace A (P.X i) v.hom ∧
        chainTraceTerm s i (𝟙 (P.X i)) = (n : A)) ∧
      (∀ s : ModuleCat.StrictPerfectCoefficientPackage P,
        perfectCategoricalTrace (Q.obj P) hP (𝟙 (Q.obj P)) =
          ∑ i ∈ Finset.Icc a b, i.negOnePow • chainTraceTerm s i (𝟙 (P.X i))) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v w : P ⟶ P),
        Nonempty (Homotopy v w) → chainSupertrace s a b v = chainSupertrace s a b w) ∧
      (∃ (hflat : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
        (δ : Q.obj (perfectTraceModelDual P) ≅ perfectTraceDual (Q.obj P)),
        perfectTraceEvaluation (Q.obj P) =
          (δ.inv ⊗ₘ 𝟙 (Q.obj P)) ≫
            (QObjTensorQObjIsoOfKFlatRight (perfectTraceModelDual P) P hflat).hom ≫
            Q.map ev ≫ chainTraceUnitIso.hom ∧
        perfectTraceCoevaluation (Q.obj P) hP =
          chainTraceUnitIso.inv ≫ Q.map coev ≫
            (QObjTensorQObjIsoOfKFlatLeft P (perfectTraceModelDual P) hflat).inv ≫
            (𝟙 (Q.obj P) ⊗ₘ δ.hom)) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v : P ⟶ P),
        perfectCategoricalTrace (Q.obj P) hP (Q.map v) = chainSupertrace s a b v) ∧
      (∀ v : Q.obj P ⟶ Q.obj P, ∃ w : P ⟶ P, Q.map w = v ∧
        ∀ s : ModuleCat.StrictPerfectCoefficientPackage P,
          perfectCategoricalTrace (Q.obj P) hP v = chainSupertrace s a b w) ∧
      (∀ (T : DerivedCategory (ModuleCat.{u} A)) (hT : IsPerfectRingComplex T)
        (e : Q.obj P ≅ T),
        perfectTraceCoevaluation T hT = perfectTraceCoevaluation (Q.obj P) hP ≫
          (e.hom ⊗ₘ perfectTraceDualMap e.inv) ∧
        perfectTraceEvaluation T = (perfectTraceDualMap e.hom ⊗ₘ e.inv) ≫
          perfectTraceEvaluation (Q.obj P) ∧
        ∀ v : Q.obj P ⟶ Q.obj P,
          perfectCategoricalTrace T hT (e.inv ≫ v ≫ e.hom) =
            perfectCategoricalTrace (Q.obj P) hP v) := by
  sorry

end DerivedCategory

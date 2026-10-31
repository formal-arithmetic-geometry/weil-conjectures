/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace

/-!
# Chain-level supertrace with finite dual frames

Source: literature/blueprint/latest/blueprint/sec-trace-formula/sk-p-trace/
lem-trf-chain-supertrace.md and its proof (blueprint: lem-trf-chain-supertrace).

The tensor product and braiding are the existing signed total tensor. The model dual,
frame vectors and functionals, and derived trace are those of the recorded trace definition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable {A : Type u} [CommRing A] [HasDerivedCategory.{u} (ModuleCat.{u} A)]

/-- The degree-zero coordinate on the chain tensor unit.
Source: blueprint, chain-supertrace, unit convention (blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceUnitCoordinate :
    (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).X 0 ≅ ModuleCat.of A A :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)

/-- Embed the frame functional in dual degree `-i`, using the single cochain.
Source: blueprint, chain-supertrace, dual convention (blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceFrameDual {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (r : Fin (s.N i)) :
    (perfectTraceModelDual P).X (-i) :=
  CochainComplex.HomComplex.Cochain.single (K := P)
    (L := 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) (p := i) (q := 0)
    (ModuleCat.ofHom (perfectTraceFrameFunctional s i r) ≫ chainTraceUnitCoordinate.inv) (-i)

/-- Insert a frame vector tensor its dual functional in total degree zero.
Source: blueprint, chain-supertrace, coevaluation (blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceFrameTensor {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (r : Fin (s.N i)) :
    (P ⊗ perfectTraceModelDual P).X 0 :=
  (HomologicalComplex.ιTensorObj P (perfectTraceModelDual P) i (-i) 0
    (add_neg_cancel i)).hom
      (perfectTraceFrameVector s i r ⊗ₜ[A] chainTraceFrameDual s i r)

/-- The ordinary projective-module trace computed in a finite dual frame.
Source: blueprint, chain-supertrace, ordinary trace (blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceTerm {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (v : P.X i ⟶ P.X i) : A :=
  ∑ r : Fin (s.N i), perfectTraceFrameFunctional s i r
    (v.hom (perfectTraceFrameVector s i r))

/-- The finite alternating sum of projective component traces.
Source: blueprint, chain-supertrace, clause (c) (blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainSupertrace {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ) (v : P ⟶ P) : A :=
  ∑ i ∈ Finset.Icc a b, i.negOnePow • chainTraceTerm s i (v.f i)

/-- The canonical comparison of the localized chain unit with the derived tensor unit.
Source: blueprint, chain-supertrace, derived paragraph (blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceUnitIso :
    Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) ≅
      𝟙_ (DerivedCategory (ModuleCat.{u} A)) :=
  ((singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)).symm ≪≫
    singleFunctorObjUnitIso (ModuleCat.{u} A)

/-- Finite-projective chain duality, its supertrace, and passage to the derived trace.
Source: blueprint, chain-supertrace, clauses (a)--(c) and the derived paragraph
(blueprint: lem-trf-chain-supertrace).

Proof: split each finite projective term off a finite free module to obtain the dual frame,
choosing rank zero on zero terms. Expanding one frame in another proves rectangular cyclicity
and frame independence; in a basis this is the diagonal sum. Construct the pairing by contraction
and the frame tensor sum. The two terms in its differential cancel by the signed total-Hom
formula; the frame identity gives both triangles. Equivalently transport the existing termwise
right-dual pairing along the explicit comparison with total Hom. Its tensor summand formula is
exactly the displayed unsigned evaluation and coevaluation. Uniqueness from the triangles gives
independence of coevaluation. In the trace composite the Koszul swap of degrees `i` and `-i`
contributes `(-1)^i`, giving the finite supertrace and its identity specialization. Rectangular
cyclicity cancels the differential-homotopy terms after shifting the finite sum. The model and
its dual are bounded with flat terms, hence K-flat. Map the pairing through the homotopy quotient
and the monoidal K-flat localization and compare its dual with the canonical internal dual.
This gives the two displayed derived comparison equations. Trace preservation and the
fully faithful degree-zero embedding identify the resulting scalar with the same supertrace.
K-projectivity supplies a chain representative of every derived endomorphism. Naturality of
internal-Hom evaluation and uniqueness of coevaluation give transport under any derived
isomorphism, and conjugacy invariance gives the last equality. Specializing the ring to the
finite coefficient ring gives the existing finite-coefficient trace by its definition.
-/
theorem chain_supertrace (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hfinite : ∀ i : ℤ, Module.Finite A (P.X i)) (hprojective : ∀ i : ℤ,
    Module.Projective A (P.X i)) : (∃ s : ModuleCat.StrictPerfectCoefficientPackage P, ∀ i : ℤ,
    IsZero (P.X i) → s.N i = 0) ∧ ∃ (ev : perfectTraceModelDual P ⊗ P ⟶ 𝟙_ _) (coev : 𝟙_ _ ⟶ P ⊗
    perfectTraceModelDual P) (hP : IsPerfectRingComplex (Q.obj P)), (∀ (i : ℤ) (φ :
    (perfectTraceModelDual P).X (-i)) (p : P.X i), chainTraceUnitCoordinate.hom.hom ((ev.f 0).hom
    ((HomologicalComplex.ιTensorObj (perfectTraceModelDual P) P (-i) i 0 (neg_add_cancel i)).hom
    (φ ⊗ₜ[A] p))) = chainTraceUnitCoordinate.hom.hom ((φ.v i 0 (add_neg_cancel i)).hom p)) ∧ (∀ n
    : ℤ, n ≠ 0 → ev.f n = 0) ∧ (∀ s : ModuleCat.StrictPerfectCoefficientPackage P, (∀ i : ℤ,
    IsZero (P.X i) → s.N i = 0) → (coev.f 0).hom (chainTraceUnitCoordinate.inv.hom 1) = ∑ i ∈
    Finset.Icc a b, ∑ r : Fin (s.N i), chainTraceFrameTensor s i r) ∧ ((ρ_ (perfectTraceModelDual
    P)).inv ≫ perfectTraceModelDual P ◁ coev ≫ (α_ (perfectTraceModelDual P) P
    (perfectTraceModelDual P)).inv ≫ ev ▷ perfectTraceModelDual P ≫ (λ_ (perfectTraceModelDual
    P)).hom = 𝟙 _) ∧ ((λ_ P).inv ≫ coev ▷ P ≫ (α_ P (perfectTraceModelDual P) P).hom ≫ P ◁ ev ≫
    (ρ_ P).hom = 𝟙 P) ∧ (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v : P ⟶ P), coev ≫ v
    ▷ perfectTraceModelDual P ≫ (CochainComplex.Monoidal.braiding P (perfectTraceModelDual P)).hom
    ≫ ev = (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map (ModuleCat.ofHom
    (chainSupertrace s a b v • LinearMap.id))) ∧ (∀ (s t :
    ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (v : P.X i ⟶ P.X i), chainTraceTerm s i v
    = chainTraceTerm t i v) ∧ (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (n : ℕ)
    (e : Module.Basis (Fin n) A (P.X i)) (v : P.X i ⟶ P.X i), chainTraceTerm s i v = ∑ r : Fin n,
    e.repr (v.hom (e r)) r ∧ chainTraceTerm s i v = LinearMap.trace A (P.X i) v.hom ∧
    chainTraceTerm s i (𝟙 (P.X i)) = (n : A)) ∧ (∀ s : ModuleCat.StrictPerfectCoefficientPackage
    P, perfectCategoricalTrace (Q.obj P) hP (𝟙 (Q.obj P)) = ∑ i ∈ Finset.Icc a b, i.negOnePow •
    chainTraceTerm s i (𝟙 (P.X i))) ∧ (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v w :
    P ⟶ P), Nonempty (Homotopy v w) → chainSupertrace s a b v = chainSupertrace s a b w) ∧ (∃
    (hflat : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) (δ : Q.obj
    (perfectTraceModelDual P) ≅ perfectTraceDual (Q.obj P)), perfectTraceEvaluation (Q.obj P) =
    (δ.inv ⊗ₘ 𝟙 (Q.obj P)) ≫ (QObjTensorQObjIsoOfKFlatRight (perfectTraceModelDual P) P hflat).hom
    ≫ Q.map ev ≫ chainTraceUnitIso.hom ∧ perfectTraceCoevaluation (Q.obj P) hP =
    chainTraceUnitIso.inv ≫ Q.map coev ≫ (QObjTensorQObjIsoOfKFlatLeft P (perfectTraceModelDual P)
    hflat).inv ≫ (𝟙 (Q.obj P) ⊗ₘ δ.hom)) ∧ (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v
    : P ⟶ P), perfectCategoricalTrace (Q.obj P) hP (Q.map v) = chainSupertrace s a b v) ∧ (∀ v :
    Q.obj P ⟶ Q.obj P, ∃ w : P ⟶ P, Q.map w = v ∧ ∀ s : ModuleCat.StrictPerfectCoefficientPackage
    P, perfectCategoricalTrace (Q.obj P) hP v = chainSupertrace s a b w) ∧ (∀ (T : DerivedCategory
    (ModuleCat.{u} A)) (hT : IsPerfectRingComplex T) (e : Q.obj P ≅ T), perfectTraceCoevaluation T
    hT = perfectTraceCoevaluation (Q.obj P) hP ≫ (e.hom ⊗ₘ perfectTraceDualMap e.inv) ∧
    perfectTraceEvaluation T = (perfectTraceDualMap e.hom ⊗ₘ e.inv) ≫ perfectTraceEvaluation
    (Q.obj P) ∧ ∀ v : Q.obj P ⟶ Q.obj P, perfectCategoricalTrace T hT (e.inv ≫ v ≫ e.hom) =
    perfectCategoricalTrace (Q.obj P) hP v) := by
  sorry

end DerivedCategory

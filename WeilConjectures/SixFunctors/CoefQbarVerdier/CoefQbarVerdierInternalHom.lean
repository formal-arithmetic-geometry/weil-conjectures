/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierInternalHomComparison
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierInternalHomUniversal

/-! # Internal Hom for the descended Verdier evaluation

Source: blueprint thm-coef-qbar-verdier, proof step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem tensorEvaluationBijective {C : Type*} [Category C]
    (T : C × C ⥤ C) (K w d : C) (H : C ⥤ C)
    (adj : ((Functor.const C).obj K).prod' (𝟭 C) ⋙ T ⊣ H)
    (e : d ≅ H.obj w) (ev : T.obj (K, d) ⟶ w)
    (he : T.map (Prod.mkHom (𝟙 K) e.hom) ≫ adj.counit.app w = ev) (P : C) :
    Function.Bijective (fun h : P ⟶ d ↦ T.map (Prod.mkHom (𝟙 K) h) ≫ ev) := by
  let q := e.homToEquiv.trans ((adj.homEquiv P w).symm)
  have hq : (fun h : P ⟶ d ↦ T.map (Prod.mkHom (𝟙 K) h) ≫ ev) = q := by
    funext h
    change T.map (Prod.mkHom (𝟙 K) h) ≫ ev =
      T.map (Prod.mkHom (𝟙 K) (h ≫ e.hom)) ≫ adj.counit.app w
    rw [← he, ← Category.assoc, ← T.map_comp]
    congr 2
    simp
  rw [hq]
  exact q.bijective

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite-origin evaluation identifies the descended dual with the actual
common-stage internal Hom, and gives its evaluation-transpose universal property.
Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).

Proof: represent K, P, omega and a map at one finite extension. The finite
HomIdentification gives the evaluation transpose bijection at that stage. Its
compatibility with scalar extension follows from the normalized evaluation square
and the scalar Hom comparison. Hence the finite transpose and its inverse induce
inverse maps on the directed-colimit Hom groups. Equality of two representatives
is eventual equality, which the two finite inverse maps preserve, so both induced
composites are identities. The bijection is natural in K and P by finite naturality.
The literal object and representative formulas for commonStageDerivedInternalHom
identify its values with the resulting right adjoint; uniqueness of right adjoints
gives the natural comparison with the descended dual. The evaluation square in
DualityProperties identifies its counit with B.evaluation, so the bijection is the
displayed actual tensor-evaluation composite, not merely an arbitrary equivalence
of Hom sets. All pairs are permitted by commonStageHomPairs_all. -/
theorem internal_hom_descent (B : Duality D l hl Ω X) :
    Nonempty (InternalHom D l hl Ω X B) := by
  obtain ⟨permitted, ⟨comparison⟩⟩ := internal_hom_comparison_exists
    D l hl Ω X B
  refine ⟨{ permitted := permitted, comparison := comparison, universal := ?_ }⟩
  exact internal_hom_universal_of_comparison D l hl Ω X B permitted comparison B.property

omit [IsAlgClosure (Padic l) Ω] in
end WeilConjectures.CoefQbarVerdier

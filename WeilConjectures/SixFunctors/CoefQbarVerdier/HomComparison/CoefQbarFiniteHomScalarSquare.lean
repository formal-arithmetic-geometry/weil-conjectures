/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.HomComparison.CoefQbarVerdierHomComparisonComponents

/-! # The finite dual-to-Hom scalar square by adjunction

Source: blueprint thm-coef-qbar-verdier, retained proof step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

attribute [local irreducible] WeilConjectures.rationalDerivedInternalHom
  WeilConjectures.rationalDerivedTensor WeilConjectures.sfRationalScalarExtension
  WeilConjectures.rationalTensorScalarComparison WeilConjectures.rationalHomScalarComparison
  WeilConjectures.integralCoefficientLinear HasDerivedCategory.standard
  WeilConjectures.sfRationalConstructibleLocalization
  WeilConjectures.commonStageDerivedInternalHom
set_option allowUnsafeReducibility true in
attribute [local reducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local implicit_reducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.Stage
universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier.HomComparison
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem finite_hom_square
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C) (U R : D ⥤ D) (S : C ⥤ D)
    (w d h : C) (z e : D) (a : U ⊣ R)
    (ev : T.obj d ⟶ w) (ew : U.obj e ⟶ z) (eh : T.obj h ⟶ w)
    (p : d ⟶ h) (q : e ⟶ R.obj z) (β : S.obj d ⟶ e) (ω : S.obj w ⟶ z)
    (c : S.obj h ⟶ R.obj (S.obj w))
    (td : U.obj (S.obj d) ⟶ S.obj (T.obj d))
    (th : U.obj (S.obj h) ⟶ S.obj (T.obj h))
    (ht : U.map (S.map p) ≫ th = td ≫ S.map (T.map p))
    (hp : T.map p ≫ eh = ev)
    (hq : U.map q ≫ a.counit.app z = ew)
    (hc : U.map c ≫ a.counit.app (S.obj w) = th ≫ S.map eh)
    (hβ : U.map β ≫ ew = td ≫ S.map ev ≫ ω) :
    S.map p ≫ c ≫ R.map ω = β ≫ q := by
  apply (a.homEquiv _ z).symm.injective
  simp only [Adjunction.homEquiv_counit, U.map_comp, Category.assoc]
  have hn := a.counit.naturality ω
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  rw [← Category.assoc _ _ ω, hc]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (S.map eh ≫ ω), ht]
  simp only [Category.assoc]
  rw [← S.map_comp_assoc, hp, hq, hβ]

omit [IsAlgClosure (Padic l) Ω] in
/-- The normalized finite dual-to-Hom isomorphism commutes with coefficient extension.
Source: blueprint thm-coef-qbar-verdier, retained coefficient-transport step 5.
(blueprint: lem-coef-qbar-finite-hom-scalar-square).

Proof: apply the injective inverse Hom equivalence for tensor with the extended first
input. Counit naturality and tensor-comparison naturality reduce the two transposes
to their evaluations. HomIdentification.evaluation identifies the finite dual-to-Hom
maps with these evaluations, HomScalarCompatibility identifies the scalar Hom map's
transpose, and the normalized finite Verdier extension identifies the remaining
transposed evaluations. Thus the two Hom maps agree. This argument applies also to
the identity field inclusion and zero objects, and needs no common-stage duality. -/
theorem finite_scalar_hom_square
    (F : Finite D l hl Ω X) (E L : Index l Ω) (h : E ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω E) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
      (F.omega E) (F.omega L) (F.datum E) (F.datum L) (F.hom E) (F.hom L))
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    let S := GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h
    let w := (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (F.omega E).omega
    S.map ((F.hom E).duality.hom.app (op K)) ≫
        (rationalHomScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X
          ⟨(op K, w), (F.hom E).permitted K w⟩).hom ≫
        (stageHom l Ω X D hl F L).map
          (Prod.mkHom (𝟙 (op (S.obj K))) (F.scalar E L h).omega.hom) =
      (F.beta E L h).hom.app (op K) ≫
        (F.hom L).duality.hom.app (op (S.obj K)) := by
  dsimp only
  let S := GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h
  let w := (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
    (F.omega E).omega
  let z := (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
    (F.omega L).omega
  let d := (F.datum E).dual.obj (op K)
  let A := RationalOperations.homRight l (Coefficient.{u} l Ω E) X
    (F.hom E).permitted K
  let p := (F.hom E).duality.hom.app (op K)
  let t := @rationalTensorScalarComparison l _ (Coefficient.{u} l Ω E) _ _ _
    (Coefficient.{u} l Ω L) _ _ _
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X
    (RationalVerdier.units D l hl X)
  have ht := t.inv.naturality (Prod.mkHom (𝟙 K) p)
  simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at ht
  have hb := eq_of_heq (F.betaNormalized E L h)
  exact finite_hom_square
    (@RationalOperations.tensorLeft l _ (Coefficient.{u} l Ω E) _ _ _ X
      (RationalVerdier.units D l hl X) K)
    (@RationalOperations.tensorLeft l _ (Coefficient.{u} l Ω L) _ _ _ X
      (RationalVerdier.units D l hl X) (S.obj K))
    (RationalOperations.homRight l (Coefficient.{u} l Ω L) X
      (F.hom L).permitted (S.obj K)) S
    w d (A.obj w) z ((F.datum L).dual.obj (op (S.obj K)))
    ((F.hom L).adjunction (S.obj K))
    ((F.datum E).evaluation K) ((F.datum L).evaluation (S.obj K))
    (((F.hom E).adjunction K).counit.app w) p
    ((F.hom L).duality.hom.app (op (S.obj K)))
    ((F.beta E L h).hom.app (op K)) (F.scalar E L h).omega.hom
    (rationalHomScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X
      ⟨(op K, w), (F.hom E).permitted K w⟩).hom
    (t.inv.app (K, d)) (t.inv.app (K, A.obj w)) ht
    ((F.hom E).evaluation K) ((F.hom L).evaluation (S.obj K)) (hs K w)
    (by simpa only [hb, S, z, t, d, RationalVerdier.scalar,
      GeneralAlgebraicallyClosedCoefficients.transition, Functor.comp_obj,
      RationalOperations.tensorLeft, RationalVerdier.tensor, Functor.comp_map,
      Functor.prod'_obj, Functor.prod'_map, Functor.const_obj_obj,
      Functor.const_obj_map, Functor.id_obj, Functor.id_map] using
      (F.normalized E L h).2.2.1 K)

end WeilConjectures.CoefQbarVerdier.HomComparison

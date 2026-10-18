/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ModelDecomposition

/-!

# The trace formula in degree one

The trace formula of a Weil object `(K, φ)` for `Φ` in degree `m`
(`ProEtale.CondensedRing.WeilBoundedConstructible.TraceFormula`) is a statement about the iterate
`(K, φ_m)`, a Weil object for `Φ_m`. This file introduces the *degree one* trace formula of a
Weil object `(K, φ)` for an endomorphism `Φ`, stated directly with the compactly supported
Frobenius of `(K, φ)` and the Frobenii of its stalks at the points fixed by `Φ`
(`ProEtale.CondensedRing.WeilBoundedConstructible.TraceFormulaOne`), and compares:

* the trace formula in degree `m` with the degree one trace formula of the iterate `(K, φ_m)`
  (`ProEtale.CondensedRing.WeilBoundedConstructible.traceFormula_iff_traceFormulaOne_iterate`);
* the trace formula in degree one with the degree one trace formula
  (`ProEtale.CondensedRing.WeilBoundedConstructible.traceFormula_one_iff`).

The degree one trace formula over a model (`ProEtale.CondensedRing.ModelTraceFormulaOne`) does
not depend on the presentation of the model and is invariant under isomorphisms of models
(`ProEtale.CondensedRing.ModelTraceFormulaOne.of_iso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

/-! ### Transport along equal Frobenius endomorphisms -/

/-- An isomorphism of Weil objects from an equality of carriers compatible with the structure
isomorphisms. -/
noncomputable def isoOfCarrierEq {Φ : X ⟶ X} (K' K : WeilBoundedConstructible ℓ Φ)
    (hc : K'.carrier = K.carrier)
    (hs : K'.str.hom = eqToHom (show (boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K'.carrier =
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K.carrier by
          rw [hc]) ≫ K.str.hom ≫ eqToHom hc.symm) : K' ≅ K :=
  IsoAlgebra.isoMk (eqToIso hc) (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, hs, eqToIso.hom, eqToHom_map]
    simp)

/-- Weil objects for equal endomorphisms `Ψ = Φ` with equal carriers and compatible structure
isomorphisms have compactly supported Frobenii of the same trace. -/
lemma trace_compactFrobenius_eq_of_eq {Ψ Φ : X ⟶ X} (h : Ψ = Φ) [IsFinite Ψ.left]
    [IsUniversalHomeomorphism Ψ.left] [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]
    (K' : WeilBoundedConstructible ℓ Ψ) (K : WeilBoundedConstructible ℓ Φ)
    (hc : K'.carrier = K.carrier)
    (hs : K'.str.hom = eqToHom (show (boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ Ψ).obj K'.carrier =
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K.carrier by
          subst h; rw [hc]) ≫ K.str.hom ≫ eqToHom hc.symm)
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K'.carrier)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)] :
    trace K'.compactFrobenius = trace K.compactFrobenius := by
  subst h
  exact trace_compactFrobenius_eq_of_iso (isoOfCarrierEq K' K hc hs)

/-- The Frobenius `L(𝟙 s)^* Lx^* K ≅ Lx^* K` of the stalk at a point `x` fixed by `Φ` of a Weil
object `(K, φ)` for `Φ`, an endomorphism of the geometric stalk `Lx^* K` (no iterate is taken). -/
noncomputable def weilStalkFrobenius {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ)
    (x : RationalPoint X) (hx : x ≫ Φ = x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier :=
  ((weilStalk ℓ Φ x hx).obj K).frobenius.hom

/-- Isomorphic Weil objects have stalk Frobenii of the same trace. -/
lemma trace_weilStalkFrobenius_eq_of_iso {Ψ : X ⟶ X} {K' K : WeilBoundedConstructible ℓ Ψ}
    (e : K' ≅ K) (x : RationalPoint X) (hx : x ≫ Ψ = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K'.carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    trace (K'.weilStalkFrobenius x hx) = trace (K.weilStalkFrobenius x hx) := by
  have e' := (weilStalk ℓ Ψ x hx).mapIso e
  exact trace_eq_of_iso
    (X := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K'.carrier)
    (X' := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier)
    ((IsoAlgebra.forget _).mapIso e') _ _ (frobenius_hom_naturality e'.hom)

/-- Weil objects for equal endomorphisms `Ψ = Φ` with equal carriers and compatible structure
isomorphisms have stalk Frobenii of the same trace. -/
lemma trace_weilStalkFrobenius_eq_of_eq {Ψ Φ : X ⟶ X} (h : Ψ = Φ)
    (K' : WeilBoundedConstructible ℓ Ψ) (K : WeilBoundedConstructible ℓ Φ)
    (hc : K'.carrier = K.carrier)
    (hs : K'.str.hom = eqToHom (show (boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ Ψ).obj K'.carrier =
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K.carrier by
          subst h; rw [hc]) ≫ K.str.hom ≫ eqToHom hc.symm)
    (x : RationalPoint X) (hx' : x ≫ Ψ = x) (hx : x ≫ Φ = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K'.carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    trace (K'.weilStalkFrobenius x hx') = trace (K.weilStalkFrobenius x hx) := by
  subst h
  exact trace_weilStalkFrobenius_eq_of_iso (isoOfCarrierEq K' K hc hs) x hx

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The computation behind `iterate_one_str_hom`, for an abstract family of pullback functors. -/
lemma iterate_one_str_hom_aux {𝒞 : Type*} [Category 𝒞] {X' : 𝒞} {D : Type*} [Category D]
    (FXX : (X' ⟶ X') → D ⥤ D) (cXXX : ∀ a b : X' ⟶ X', FXX (a ≫ b) ≅ FXX b ⋙ FXX a)
    (ιX : FXX (𝟙 X') ≅ 𝟭 D)
    (hidr : ∀ (a : X' ⟶ X') (K : D), (cXXX a (𝟙 X')).hom.app K ≫ (FXX a).map (ιX.hom.app K) =
      eqToHom (congrArg (fun f ↦ (FXX f).obj K) (Category.comp_id a)))
    {Φ Φ₁ : X' ⟶ X'} {A A' : D} (hA : A' = A) (φ : (FXX Φ).obj A ⟶ A)
    (e₂ : (FXX Φ₁).obj A = (FXX (Φ ≫ 𝟙 X')).obj A) (e₃ : A = A')
    (e₄ : (FXX Φ₁).obj A' = (FXX Φ).obj A) (e₅ : A = A') :
    (FXX Φ₁).map (eqToHom hA) ≫ (eqToHom e₂ ≫ (cXXX Φ (𝟙 X')).hom.app A ≫
      (FXX Φ).map (ιX.hom.app A) ≫ φ) ≫ eqToHom e₃ = eqToHom e₄ ≫ φ ≫ eqToHom e₅ := by
  subst hA
  rw [reassoc_of% hidr]
  simp

/-- The structure isomorphism of the iterate `(K, φ_1)` is `φ`, up to the identifications of
carriers and of `Φ_1 = Φ`. -/
lemma iterate_one_str_hom {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ) :
    (K.iterate 1).str.hom = eqToHom (show (boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ (frobeniusIterate Φ 1)).obj (K.iterate 1).carrier =
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K.carrier by
          rw [iterate_carrier, frobeniusIterate_one]) ≫
      K.str.hom ≫ eqToHom (K.iterate_carrier 1).symm := by
  rw [iterate_str]
  simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [iterateStr.eq_2, iterateStr.eq_1]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, eqToIso.hom]
  exact iterate_one_str_hom_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X)
    (fun a K ↦ boundedConstructibleUpperStarComp_id_right_app _ ℓ a K)
    (K.iterate_carrier 1) K.str.hom _ _ _ _

/-- The local Frobenius of degree `m` has the trace of the stalk Frobenius of the iterate
`(K, φ_m)`, for any choice of duals. -/
lemma trace_stalkFrobenius_eq {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      (K.iterate m).carrier)] :
    trace (K.stalkFrobenius m x hx) = trace ((K.iterate m).weilStalkFrobenius x hx) := by
  refine trace_eq_of_iso (eqToIso (congrArg
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      (K.iterate_carrier m).symm)) _ _ ?_
  rw [stalkFrobenius, eqToIso.hom]
  exact eqToHom_conj_comp _ _ _

/-- The global operator of degree one has the trace of the compactly supported Frobenius. -/
lemma trace_globalOperator_one {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ)
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]
    [IsFinite (frobeniusIterate Φ 1).left] [IsUniversalHomeomorphism (frobeniusIterate Φ 1).left]
    [hK : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)] :
    trace (K.globalOperator 1) = trace K.compactFrobenius := by
  let h1 : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        (K.iterate 1).carrier) := by
    rw [iterate_carrier]
    exact hK
  rw [trace_globalOperator_eq K 1 (hK := hK) (hKm := h1)]
  exact trace_compactFrobenius_eq_of_eq (frobeniusIterate_one Φ) _ _ (K.iterate_carrier 1)
    (iterate_one_str_hom K)

/-- The local Frobenius of degree one has the trace of the stalk Frobenius. -/
lemma trace_stalkFrobenius_one {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ)
    (x : RationalPoint X) (hx1 : x ≫ frobeniusIterate Φ 1 = x) (hx : x ≫ Φ = x)
    [hK : HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    trace (K.stalkFrobenius 1 x hx1) = trace (K.weilStalkFrobenius x hx) := by
  let h1 : HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      (K.iterate 1).carrier) := by
    rw [iterate_carrier]
    exact hK
  rw [trace_stalkFrobenius_eq K 1 x hx1]
  exact trace_weilStalkFrobenius_eq_of_eq (frobeniusIterate_one Φ) _ _ (K.iterate_carrier 1)
    (iterate_one_str_hom K) x hx1 hx

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SingleReduction
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Tor amplitude and K-flat models of étale complexes

This file records the homological-algebra inputs of the ordinary Künneth formula about Tor
amplitude and K-flat complexes of étale sheaves, for a monoidal Grothendieck abelian coefficient
category `A` with functorial flat resolutions (for instance `A = ModuleCat Λ`).

## Main definitions and results

- `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeGE`
- `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_Q_obj_of_flat`
- `AlgebraicGeometry.Etale.kFlat_criteria`
- `AlgebraicGeometry.Etale.exists_quasiIso_flat_kFlat`
- `AlgebraicGeometry.Etale.flat_opcycles_of_exactAt`
- `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeGE_iff_exists_kFlat`
- `AlgebraicGeometry.Etale.DerivedCategory.isGE_derivedTensor_of_torAmplitudeGE`

## Implementation details

* Bounded *below* complexes of flat sheaves need not be K-flat: over `Λ = ℤ/4` the complex
  `ℤ/4 --2--> ℤ/4 --2--> ⋯` in degrees `≥ 0` has flat terms and represents `ℤ/2[0]`, but its
  tensor product with `ℤ/2` has cohomology in all degrees `≥ 0`, whereas `ℤ/2 ⊗ᴸ ℤ/2` has
  cohomology in all degrees `≤ 0`. Hence `kFlat_criteria` only covers bounded above complexes.
* The estimate `H^i(A ⊗ᴸ B) = 0` for `i < a + b` needs a Tor amplitude hypothesis on one factor;
  the hypothesis `H^i(A) = 0` for `i < a` alone does not suffice: for `Λ = ℤ/4` and
  `A = B = ℤ/2` in degree `0`, `H^{-1}(ℤ/2 ⊗ᴸ ℤ/2) = Tor₁^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2 ≠ 0`.

## References

* [Stacks, Tag 0F1M]
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace DerivedCategory

variable (X : Scheme.{u})

/-- An object `E` of `D(X_ét)` has *Tor amplitude in `[a, ∞)`* if for every étale sheaf `𝓜`
placed in degree zero, `H^i(E ⊗ᴸ 𝓜) = 0` for `i < a`. -/
abbrev torAmplitudeGE (a : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  _root_.DerivedCategory.torAmplitudeGE _ a

variable {A X}

/-- Tor amplitude in `[a, ∞)` is the vanishing of `H^i(E ⊗ᴸ 𝓜)` for `i < a` and every sheaf
`𝓜` placed in degree zero. -/
lemma torAmplitudeGE_iff_forall_isZero (a : ℤ)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    torAmplitudeGE A X a E ↔ ∀ (𝓜 : Sheaf X.smallEtaleTopology A) (q : ℤ), q < a →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((-⊗ᴸ-(X)[A]).obj E).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜))) :=
  _root_.DerivedCategory.torAmplitudeGE_iff_forall_isZero a E

/-- Tor amplitude in `[a, b]` is the vanishing of `H^i(E ⊗ᴸ 𝓜)` for `i ∉ [a, b]` and every
sheaf `𝓜` placed in degree zero. -/
lemma torAmplitudeIn_iff_forall_isZero (a b : ℤ)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    torAmplitudeIn A X a b E ↔ ∀ (𝓜 : Sheaf X.smallEtaleTopology A) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((-⊗ᴸ-(X)[A]).obj E).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜))) := by
  refine forall_congr' fun 𝓜 ↦ ⟨fun h q hq ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 h.1 q hq
    · exact (_root_.DerivedCategory.isLE_iff _ b).1 h.2 q hq
  · exact (_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ h q (Or.inl hq)
  · exact (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦ h q (Or.inr hq)

/-- Tor amplitude in `[a, b]` implies Tor amplitude in `[a, ∞)`. -/
lemma torAmplitudeGE_of_torAmplitudeIn {a b : ℤ}
    {E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hE : torAmplitudeIn A X a b E) : torAmplitudeGE A X a E :=
  _root_.DerivedCategory.torAmplitudeGE_of_torAmplitudeIn hE

/-- A complex `𝓔•` of flat étale sheaves supported in degrees `[a, b]` has Tor amplitude in
`[a, b]` as an object of `D(X_ét)`. -/
lemma torAmplitudeIn_Q_obj_of_flat (E : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    (a b : ℤ) [E.IsStrictlyGE a] [E.IsStrictlyLE b] (hE : ∀ n, ObjectProperty.flat (E.X n)) :
    torAmplitudeIn A X a b (_root_.DerivedCategory.Q.obj E) :=
  _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat E a b hE

end DerivedCategory

variable {A}

omit [Abelian.HasFunctorialFlatResolution A] in
/-- K-flat criteria for complexes of étale sheaves.

1. Every bounded above complex of flat sheaves is K-flat.
2. In a distinguished triangle of the homotopy category `K(X_ét)`, if two of the three terms
   are K-flat then so is the third.
3. K-flat complexes are closed under filtered colimits (over small index categories). -/
theorem kFlat_criteria (X : Scheme.{u}) :
    (∀ (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (b : ℤ), K.IsStrictlyLE b →
      (∀ n, ObjectProperty.flat (K.X n)) →
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K) ∧
    (∀ T ∈ distTriang (HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)),
      let P := (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ)).kFlat
      (P T.obj₁ → P T.obj₂ → P T.obj₃) ∧ (P T.obj₁ → P T.obj₃ → P T.obj₂) ∧
        (P T.obj₂ → P T.obj₃ → P T.obj₁)) ∧
    (∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J],
      ObjectProperty.IsClosedUnderColimitsOfShape
        (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ)).kFlat J) := by
  refine ⟨fun K b _ hK ↦ CochainComplex.kFlat_of_isStrictlyLE_of_flat K b hK,
    fun T hT ↦ ⟨fun h₁ h₂ ↦ ?_, fun h₁ h₃ ↦ ?_, fun h₂ h₃ ↦ ?_⟩, fun J _ _ ↦ ?_⟩
  · exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ T hT h₁ h₂
  · exact ObjectProperty.ext_of_isTriangulatedClosed₂ _ T hT h₁ h₃
  · exact ObjectProperty.ext_of_isTriangulatedClosed₁ _ T hT h₂ h₃
  · have (Y : Sheaf X.smallEtaleTopology A) :
        PreservesColimitsOfShape J ((curriedTensor _).flip.obj Y) :=
      preservesColimitsOfShape_of_natIso (F := tensorLeft Y)
        (NatIso.ofComponents (fun Z ↦ β_ Y Z) (by intros; simp [curriedTensor]))
    exact CochainComplex.closedUnderColimitsOfShape_kFlat _ J

/-- Every complex `𝓖•` of étale sheaves on `X` admits a quasi-isomorphism `𝓚• ⟶ 𝓖•` from a
K-flat complex of flat sheaves. Moreover `𝓚•` can be chosen so that all its pullbacks `g^* 𝓚•`
are K-flat (for `A` such that `g^*` preserves flat sheaves). -/
lemma exists_quasiIso_flat_kFlat [Etale.UpperStarPreservesFlat A] {X : Scheme.{u}}
    (G : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    ∃ (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (π : K ⟶ G), QuasiIso π ∧
      (∀ n, ObjectProperty.flat (K.X n)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K ∧
      ∀ {Z : Scheme.{u}} (g : Z ⟶ X), (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K) :=
  exists_quasiIso_flat_kFlat_upperStar A G

omit [Abelian.HasFunctorialFlatResolution A] in
/-- Let `𝓚•` be a complex of flat étale sheaves such that `H^n(𝓚• ⊗ 𝓜) = 0` for every sheaf
`𝓜` and every `n < a`. Then the cokernel `𝓝 = coker(𝓚^{a-1} ⟶ 𝓚^a)` (the opcycles of `𝓚•`
in degree `a`) is flat. -/
lemma flat_opcycles_of_exactAt {X : Scheme.{u}}
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (a : ℤ)
    (hK : ∀ n, ObjectProperty.flat (K.X n))
    (hex : ∀ (𝓜 : Sheaf X.smallEtaleTopology A) (n : ℤ), n < a →
      (((tensorRight 𝓜).mapHomologicalComplex (.up ℤ)).obj K).ExactAt n) :
    ObjectProperty.flat (K.opcycles a) :=
  ObjectProperty.flat_opcycles_of_exactAt K a (hK _) (hK _) fun 𝓜 ↦ hex 𝓜 _ (by lia)

namespace DerivedCategory

/-- An object `E` of `D(X_ét)` has Tor amplitude in `[a, ∞)` if and only if it is represented
by a K-flat complex `𝓔•` of flat sheaves with `𝓔^i = 0` for `i < a`; moreover `𝓔•` may be
chosen so that every pullback `g^* 𝓔•` is again a K-flat complex of flat sheaves. -/
theorem torAmplitudeGE_iff_exists_kFlat [Etale.UpperStarPreservesFlat A] {X : Scheme.{u}}
    (a : ℤ) (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    torAmplitudeGE A X a E ↔
      ∃ (P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (_ : P.IsStrictlyGE a),
        (∀ n, ObjectProperty.flat (P.X n)) ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
        (∀ {Z : Scheme.{u}} (g : Z ⟶ X),
          (∀ n, ObjectProperty.flat (((((g)^*[A]).mapHomologicalComplex (.up ℤ)).obj P).X n)) ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
            ((((g)^*[A]).mapHomologicalComplex (.up ℤ)).obj P)) ∧
        Nonempty (_root_.DerivedCategory.Q.obj P ≅ E) := by
  refine ⟨fun hE ↦ ?_, fun ⟨P, _, _, hPk, _, ⟨e⟩⟩ ↦
    (torAmplitudeGE A X a).prop_of_iso e
      (_root_.DerivedCategory.torAmplitudeGE_Q_obj_of_kFlat P a hPk)⟩
  have := _root_.DerivedCategory.isGE_of_torAmplitudeGE hE
  obtain ⟨P, π, _, hP, hPk, hPg⟩ :=
    exists_quasiIso_flat_kFlat_upperStar A (_root_.DerivedCategory.Q.objPreimage E)
  have : IsIso (_root_.DerivedCategory.Q.map π) := by
    rwa [_root_.DerivedCategory.isIso_Q_map_iff_quasiIso]
  let e : _root_.DerivedCategory.Q.obj P ≅ E :=
    asIso (_root_.DerivedCategory.Q.map π) ≪≫ _root_.DerivedCategory.Q.objObjPreimageIso E
  have : P.IsGE a := by
    rw [← _root_.DerivedCategory.isGE_Q_obj_iff]
    exact _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hex := _root_.DerivedCategory.exactAt_tensorRight_of_torAmplitudeGE P hPk
    ((torAmplitudeGE A X a).prop_of_iso e.symm hE)
  refine ⟨P.truncGE a, inferInstance, P.flat_truncGE_X a hP hex, P.kFlat_truncGE a hP hPk hex,
    fun g ↦ ⟨fun n ↦ Functor.PreservesFlat.flat_obj (F := (g)^*[A]) (P.flat_truncGE_X a hP hex n),
      CochainComplex.kFlat_mapHomologicalComplex_obj_truncGE _ P a hP (hPg g) hex⟩,
    ⟨(asIso (_root_.DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ e⟩⟩

/-- If `A` has Tor amplitude in `[a, ∞)` and `H^i(B) = 0` for `i < b`, then
`H^i(A ⊗ᴸ B) = 0` for `i < a + b`. -/
lemma isGE_derivedTensor_of_torAmplitudeGE {X : Scheme.{u}} {a : ℤ}
    {E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hE : torAmplitudeGE A X a E)
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (b : ℤ) [F.IsGE b] :
    (((-⊗ᴸ-(X)[A]).obj E).obj F).IsGE (a + b) :=
  _root_.DerivedCategory.isGE_tensor_of_torAmplitudeGE hE F b

/-- The symmetric form of
`AlgebraicGeometry.Etale.DerivedCategory.isGE_derivedTensor_of_torAmplitudeGE`, with the Tor
amplitude hypothesis on the second factor. -/
lemma isGE_derivedTensor_of_torAmplitudeGE_right {X : Scheme.{u}} {a : ℤ}
    {E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hE : torAmplitudeGE A X a E)
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (b : ℤ) [F.IsGE b] :
    (((-⊗ᴸ-(X)[A]).obj F).obj E).IsGE (b + a) :=
  _root_.DerivedCategory.isGE_tensor_of_torAmplitudeGE_right hE F b

end DerivedCategory

end Etale

end AlgebraicGeometry

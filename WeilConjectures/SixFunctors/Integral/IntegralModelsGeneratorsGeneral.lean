/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import all WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.GeneralFieldLatticeSubquotientFiltration
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects

/-!
# Integral generators over an arbitrary characteristic

Source: blueprint latest, part-six-operations/sec-reduction-finite-coefficients/
sec-integral-models/sk-lem-integral-models/sk-lem-integral-models-generators.md,
clauses (1)--(3) (blueprint: det-lem-integral-models-generators).

This statement uses the existing canonical coefficient and generator constructions. The
field is arbitrary; the only characteristic condition is that it differs from the fixed
prime `ℓ`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale

universe u

open scoped CategoryTheory.Obj CategoryTheory.Functor

set_option cleanup.letToHave false

namespace WeilConjectures.SixFunctors

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

-- Apply the declared arbitrary-field lattice filtration and identify its spectral topology.
private theorem integralGeneral_latticeSmall
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k ≠ ℓ)] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {S : Scheme.{u}} (d : S ⟶ X) [IsImmersion d] :
    integralModel_latticeTopology ℓ (ULift.{u} E.1) d ULift.topologicalSpace inferInstance := by
  have : TopologicalSpace.NoetherianSpace S :=
    d.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian d
  have : IsNoetherian S := ⟨⟩
  let : S.Over (Spec (.of k)) := ⟨d ≫ (X ↘ Spec (.of k))⟩
  have : d.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (d ≫ (X ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (S ↘ Spec (.of k)) := by
    change QuasiCompact (d ≫ (X ↘ Spec (.of k)))
    infer_instance
  have : IsSeparated (S ↘ Spec (.of k)) := by
    change IsSeparated (d ≫ (X ↘ Spec (.of k)))
    infer_instance
  let t : TopologicalSpace (ULift.{u} E.1) :=
    (fun m : MetricSpace (ULift.{u} E.1) ↦
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
        (spectralNorm.normedField ℚ_[ℓ] (ULift.{u} E.1)).toMetricSpace
  have ht : t = ULift.topologicalSpace := integralModel_liftTopology ℓ E
  have htop : @IsTopologicalRing (ULift.{u} E.1) t inferInstance := by
    rw [ht]
    infer_instance
  have h : integralModel_latticeTopology ℓ (ULift.{u} E.1) d t htop :=
    integralModel_lattice_data ℓ (ULift.{u} E.1) k d
      (exists_latticeSubquotientFiltration_of_char_ne ℓ (ULift.{u} E.1) k
        (Fact.out : ringChar k ≠ ℓ) S X d)
  simpa only [ht] using h

-- Transport both coefficient rings and the filtration together, preserving its inclusion.
set_option backward.isDefEq.respectTransparency.types false in
open scoped CategoryTheory.Obj in
attribute [-instance] integralModel_coefficientMonObj in
attribute [local irreducible] LatticeSubquotientFiltrationData in
private theorem integralGeneral_lisseSmall
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k ≠ ℓ)] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (P : ObjectProperty (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) X))))
    [htri : P.IsTriangulated] [hiso : P.IsClosedUnderIsomorphisms]
    (hP : integralModelGenerator X ℓ E ≤ P) :
    integralModel_lisseExtensions (Profinite.continuousMapRingObj E.1) X P := by
  unfold integralModel_lisseExtensions
  intro S d hd L hL
  let := hd
  have hgen := integralModel_generator_contains X ℓ E P hP
  let E' := ULift.{u} E.1
  have hm := integralModel_liftIntegers.{u} ℓ E
  let O' := Padic.coefficientExtensionIntegers ℓ E'
  let eO : PadicAlgCl.integers ℓ E.1 ≃+* O' :=
    { toFun := fun x ↦ ⟨ULift.up x.val, (hm _).mpr (by
        exact_mod_cast x.property)⟩
      invFun := fun x ↦ ⟨x.val.down, by
        have h := (hm x.val).mp x.property
        exact_mod_cast h⟩
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ by cases x; rfl
      map_mul' := fun x y ↦ rfl
      map_add' := fun x y ↦ rfl }
  let eF : E.1 ≃+* E' := ULift.ringEquiv.symm
  let aO := integralModel_coefficientIso eO
    ((continuous_uliftUp.comp continuous_subtype_val).subtype_mk _)
    ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)
  let aF := integralModel_coefficientIso eF continuous_uliftUp continuous_uliftDown
  let forget := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let A' := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} O')
  let B' := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} E')
  let c' : A' ⟶ B' := forget.map
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} O'.subtype continuous_subtype_val)
  have : IsCommMonObj A' := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} O')
    (fun U (a b : ULift.{u + 1} C(U.unop, O')) ↦ mul_comm a b)
  have : IsCommMonObj B' := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E')
    (fun U (a b : ULift.{u + 1} C(U.unop, E')) ↦ mul_comm a b)
  have : IsMonHom c' := Sheaf.isMonHom_sheafCompose_map _
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} O'.subtype continuous_subtype_val)
  have : IsMonHom (forget.map aO.hom) := Sheaf.isMonHom_sheafCompose_map _ aO.hom
  have : IsMonHom (forget.map aF.hom) := Sheaf.isMonHom_sheafCompose_map _ aF.hom
  have hf := integralGeneral_latticeSmall k ℓ X E d
  apply integralModel_lisse_transport
    (A := Profinite.padicIntegersRingObj ℓ E.1)
    (B := Profinite.continuousMapRingObj E.1) (A' := A') (B' := B')
    (AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj ℓ E)
    c' (forget.map aO.hom) (forget.map aF.hom) ?_ X P hgen d hf L hL
  · dsimp only [aO, aF]
    ext T f
    delta integralModel_coefficientIso
    rfl

-- Every triangulated isomorphism-closed class containing integral models contains the heart.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralGeneral_finiteGeneration
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k ≠ ℓ)] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (finiteCoefficientObject X ℓ E)))
    (hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K) :
    (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
      P.IsClosedUnderIsomorphisms}) K := by
  rw [unary_relation_sInf_iff]
  rintro P ⟨hP, htri, hiso⟩
  let := htri
  let := hiso
  exact integralModel_generation_of_lisse X ℓ (Profinite.continuousMapRingSheaf E.1)
    (Or.inl ⟨E.1, inferInstance, (integralModel_subfieldRing_eq ℓ E).symm⟩) P
    (htri := htri) (hiso := hiso)
    (integralGeneral_lisseSmall k ℓ X E P
      (htri := htri) (hiso := hiso) hP) K hK

-- Descend once, then transport the finite-field construction through exact scalar extension.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem integralGeneral_qlbarOfFinite
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (hfinite : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (finiteCoefficientObject X ℓ E))),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K →
      (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
        P.IsClosedUnderIsomorphisms}) K)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (qlbarCoefficientObject X ℓ)))
    (hK : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K) :
    ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (sInf {P | qlbarModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
        P.IsClosedUnderIsomorphisms}) K := by
  obtain ⟨E, KE, ⟨e⟩⟩ := (coefficient_finite_descent_objects_of_isNoetherian ℓ X).1 ⟨K, hK⟩
  let T := Mod.extendScalars (AlgebraicGeometry.ProEtale.padicSubfieldRingObjToPadicAlgCl X ℓ E)
  refine ⟨E, integralModel_closure_iso (qlbarModelGenerator X ℓ E)
    ((T.leftDerivedFunctorIsoMapDerivedCategory.app KE.obj).symm ≪≫ e) ?_⟩
  apply integralModel_closure_map T.mapDerivedCategory
    (integralModelGenerator X ℓ E) (qlbarModelGenerator X ℓ E) ?_ KE.obj
    (hfinite E KE.obj KE.property)
  rintro L ⟨S, V, j, i, hj, hi, L₀, hL₀, rfl⟩
  let := hj
  let := hi
  refine ⟨_, ⟨S, V, j, i, hj, hi, L₀, hL₀, rfl⟩, ⟨?_⟩⟩
  exact (T.mapDerivedCategorySingleFunctor 0).app
    ((finiteCoefficientExtension X ℓ E).obj
      (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) j i L₀))

/-- Integral locally free models generate bounded constructible categories over any field
whose characteristic differs from `ℓ`, and their reductions are constructible with étale
origin.

Source: blueprint latest, part-six-operations/sec-reduction-finite-coefficients/
sec-integral-models/sk-lem-integral-models/sk-lem-integral-models-generators.md,
clauses (1)--(3) (blueprint: det-lem-integral-models-generators).

Proof:
1. Finite type over a field makes X Noetherian. Coefficient-heart generation reduces
   the finite-extension clause to degree-zero extensions of lisse sheaves.
2. Apply the lattice-subquotient filtration on each locally closed stratum. Its
   canonical spectral-norm coefficients are identified with the specified finite
   coefficient field and its integers, using ULift and equality of the two norms.
   Transporting the filtration gives integral generators as its successive quotients.
   Short exact sequences give distinguished triangles; finite induction on the
   filtration, followed by the heart's cone construction, proves the first clause.
3. Descend an algebraic-closure object to one finite E. Exact scalar extension sends
   its cone construction to a cone construction over the algebraic closure, and its
   values on generators are exactly the specified algebraic-closure generators.
4. A locally free integral module has finite constant local models. Open extension
   and closed pushforward preserve the resulting stratified constructibility, hence
   its extension in degree zero is bounded constructible.
5. Tensor commutes with normalized inverse image. Joint conservativity of closed
   and complementary open restriction therefore detects flatness. The unit, counit
   and off-support zero identities show that open extension and closed pushforward
   preserve flatness. The extended integral module is flat; its single complex is
   K-flat, so derived reduction is ordinary reduction. Ordinary scalar extension
   commutes with both extension functors, again by their support identities.
6. Scalar extension preserves local freeness, so each reduced extension is bounded
   constructible. The quotient ring is finite by the maximal-ideal-power quotient theorem.
   Its quotient topology is discrete because the uniformizer-power ideal contains
   an open ball. Finite discrete coefficient encoding makes the underlying sheaf
   constructible. The specified fixed-scalar realization has the same underlying
   sheaf; finite constructibility transfers along this identification. That
   realization is exact, as detected by the exact faithful underlying-abelian-sheaf
   functor. Its derived functor consequently preserves constructible cohomology and
   bounds. The finite-ring constructible derived-origin theorem now gives etale
   origin for the precise realization in the statement.

The theorem has three conjuncts. The first says every bounded constructible object with
finite coefficient field `E` lies in the smallest triangulated, isomorphism-closed class
containing `integralModelGenerator`. The second says the analogous assertion over the
algebraic closure holds for one finite subextension `E'` depending on the object. The
third says every locally free integral model has bounded constructible derived reductions
at all positive uniformizer powers, with the specified étale-origin realization.
-/
theorem integral_models_generators_general
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k ≠ ℓ)] (X : Scheme.{u})
    [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) :
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (finiteCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K →
      (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
        P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (qlbarCoefficientObject X ℓ)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K →
      ∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        (sInf {P | qlbarModelGenerator X ℓ E' ≤ P ∧ P.IsTriangulated ∧
          P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ (S V : Scheme.{u}) (u : S ⟶ V) (i : V ⟶ X)
      [IsOpenImmersion u] [IsClosedImmersion i]
      (L₀ : CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E)),
      CondensedRing.LocallyFree (integralCoefficientObject S ℓ E) L₀ →
      integralReductionHasEtaleOrigin X ℓ E π u i L₀) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  exact ⟨integralGeneral_finiteGeneration k ℓ X E,
    integralGeneral_qlbarOfFinite ℓ X (integralGeneral_finiteGeneration k ℓ X),
    fun _ _ j i _ _ M hM ↦ integralModel_reductions X ℓ E π hπ j i M hM⟩

end WeilConjectures.SixFunctors

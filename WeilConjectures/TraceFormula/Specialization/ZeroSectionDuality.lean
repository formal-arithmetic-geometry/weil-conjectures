/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCycles

/-!

# The dual form of the zero-section theorem

Let `Z = V(I) ⊆ X`, `e : Z ⊗ k' ⟶ N_Z X ⊗ k'` the zero section of the special fibre of the
deformation to the normal cone and `Ψ = Sp_{X,Z}` its nearby cycles. For a complex `K` with
`Li^* K = 0` (for instance `K = j_! L` with `j` an open immersion into the complement of `Z`), the
target `Ψ_{Z × S}(Li^* K)` of the zero-section map vanishes, so the defect `C_{X,Z}(K)` vanishes
if and only if `Le^* Ψ K` does
(`ProEtale.CondensedRing.isZero_specializationDefect_iff_of_isZero_upperStar`).

By Verdier duality `𝔻(Le^* M) ≅ Re^! 𝔻 M`
(`ProEtale.CondensedRing.verdierDualUpperStarIsoUpperShriek`)
and biduality, this is equivalent to the vanishing of `Re^! 𝔻(Ψ K)`
(`ProEtale.CondensedRing.isZero_specializationDefect_iff_isZero_upperShriek_verdierDual`).
For a rational point `x`, where the commutation of nearby cycles with Verdier duality is available
(`ProEtale.CondensedRing.nonempty_specialization_verdierDual_iso`), this becomes the vanishing of
`Re^! Sp_{X,x}(𝔻 K)`, and for `K = Rj_! L` the vanishing of `Re^! Sp_{X,x}(Rj_* 𝔻 L)`
(`ProEtale.CondensedRing.isZero_specializationDefect_lowerShriek_iff`): the zero-section theorem
for `j_! L` is equivalent to its costalk form for `Rj_* 𝔻 L`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-- In a preadditive monoidal closed category, the internal hom out of a zero object vanishes. -/
lemma CategoryTheory.Limits.IsZero.ihom_obj {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] {A : C} (hA : IsZero A)
    (B : C) : IsZero ((ihom A).obj B) := by
  rw [IsZero.iff_id_eq_zero]
  refine uncurry_injective ?_
  have h : IsZero (A ⊗ (ihom A).obj B) := by
    rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, hA.eq_of_src (𝟙 A) 0,
      MonoidalPreadditive.zero_whiskerRight]
  exact h.eq_of_src _ _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Complexes vanishing on the centre -/

section General

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The defect of a complex vanishing on the centre**: if `Li^* K = 0`, then the target
`Ψ_{Z × S}(Li^* K)` of the zero-section map vanishes, so `C_{X,Z}(K) = 0` if and only if the
restriction `Le^* Sp_{X,Z}(K)` of the specialization to the zero section vanishes. -/
theorem isZero_specializationDefect_iff_of_isZero_upperStar
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : IsZero ((L(((centreι X I).left)^*⟦Λ⟧)).obj K)) :
    IsZero (specializationDefect X I k' Λ K) ↔
      IsZero (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
        (((deformationModel X I k').nearbyCycles Λ).obj K)) := by
  have h := (deformationModel (centre X I) ⊥ k').isZero_nearbyCycles_obj Λ hK
  rw [isZero_specializationDefect_iff]
  refine ⟨fun _ ↦ h.of_iso (asIso (zeroSectionMap X I k' Λ K)), fun h' ↦ ?_⟩
  exact isIso_of_source_target_iso_zero _ h'.isoZero h.isoZero

end General

/-! ### Verdier duality exchanges `Le^*` and `Re^!` -/

section Duality

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]

attribute [local instance] boundedConstructibleBraiding

/-- **Verdier duality exchanges `Lf^*` and `Rf^!`**: `𝔻_X (Lf^* M) ≅ Rf^! 𝔻_Y M`, with `𝔻_X`
relative to `f ≫ a` and `𝔻_Y` relative to `a`. It is the exceptional internal hom exchange
`RHom(Lf^* M, Rf^! ω_Y) ≅ Rf^! RHom(M, ω_Y)` preceded by `ω_X ≅ Rf^! ω_Y`. -/
noncomputable def verdierDualUpperStarIsoUpperShriek (f : X ⟶ Y) (a : Y ⟶ S)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    verdierDual ℓ (f ≫ a) ((boundedConstructibleUpperStar _ ℓ f).obj M) ≅
      (boundedConstructibleUpperShriek _ ℓ f).obj (verdierDual ℓ a M) :=
  haveI := Verdier.isIso_exceptionalHomMap_of_isIso
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleExceptionalProjection _ ℓ f) M (dualizingComplex ℓ a)
  (ihom _).mapIso (upperShriekDualizingComplexIso ℓ f a).symm ≪≫
    asIso (Verdier.exceptionalHomMap (boundedConstructibleUpperShriekAdjunction _ ℓ f)
      (boundedConstructibleExceptionalProjection _ ℓ f) M (dualizingComplex ℓ a))

/-- The Verdier dual over a field detects zero objects, by biduality. -/
theorem isZero_verdierDual_iff (a : X ⟶ point k) (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (verdierDual ℓ a N) ↔ IsZero N := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.ihom_obj _⟩
  have := isIso_verdierBiduality ℓ a N
  exact (h.ihom_obj _).of_iso (asIso (verdierBiduality ℓ a N))

/-- `Lf^* M` vanishes if and only if `Rf^! 𝔻_Y M` does. -/
theorem isZero_upperStar_iff_isZero_upperShriek_verdierDual (f : X ⟶ Y)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleUpperStar _ ℓ f).obj M) ↔
      IsZero ((boundedConstructibleUpperShriek _ ℓ f).obj (verdierDual ℓ (toPoint Y) M)) := by
  rw [← isZero_verdierDual_iff ℓ (f ≫ toPoint Y)]
  exact (verdierDualUpperStarIsoUpperShriek ℓ f (toPoint Y) M).isZero_iff

end Duality

/-! ### The dual form of the vanishing of the defect -/

section Defect

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [IsSepClosed k'] in
variable (k') in
/-- **Dual form of the vanishing of the defect**: for `K` with `Li^* K = 0` and a bounded
constructible model `P` of the specialization `Sp_{X,Z}(K)`, the defect `C_{X,Z}(K)` vanishes if
and only if `Re^! 𝔻(Sp_{X,Z} K) = 0`, for the zero section `e : Z ⊗ k' ⟶ N_Z X ⊗ k'`. -/
theorem isZero_specializationDefect_iff_isZero_upperShriek_verdierDual
    (I : X.left.IdealSheafData) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsZero ((boundedConstructibleUpperStar _ ℓ (centreι X I)).obj K))
    (P : Dᵇc((deformationSpecialFibre X I k').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (eP : P.obj ≅ ((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      K.obj) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) K.obj) ↔
      IsZero ((boundedConstructibleUpperShriek _ ℓ (zeroSectionSpecialFibreMap X I k')).obj
        (verdierDual ℓ (toPoint _) P)) := by
  set Λ := Profinite.padicAlgClRingObj ℓ
  have hK' : IsZero ((L(((centreι X I).left)^*⟦Λ⟧)).obj K.obj) :=
    ((boundedConstructible _).ι.map_isZero hK).of_iso
      ((boundedConstructibleUpperStarCompatibility _ ℓ (centreι X I)).app K).symm
  rw [isZero_specializationDefect_iff_of_isZero_upperStar X I k' Λ K.obj hK',
    ← isZero_upperStar_iff_isZero_upperShriek_verdierDual,
    ← (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).mapIso eP).isZero_iff]
  have e :=
    (boundedConstructibleUpperStarCompatibility _ ℓ (zeroSectionSpecialFibreMap X I k')).app P
  exact ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _ (h.of_iso e),
    fun h ↦ ((boundedConstructible _).ι.map_isZero h).of_iso e.symm⟩

variable (k') in
/-- **Dual form of the zero-section theorem at a rational point**: for `K` with `Li^* K = 0` on
the centre `Z = {x}`, the defect `C_{X,x}(K)` vanishes if and only if `Re^! Sp_{X,x}(𝔻 K) = 0`.
This uses the commutation of nearby cycles with Verdier duality
(`ProEtale.CondensedRing.nonempty_specialization_verdierDual_iso`). -/
theorem isZero_specializationDefect_iff_isZero_upperShriek_specialization_verdierDual
    (x : RationalPoint X) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsZero ((boundedConstructibleUpperStar _ ℓ (centreι X x.left.ker)).obj K)) :
    IsZero (specializationDefect X x.left.ker k' (Profinite.padicAlgClRingObj ℓ) K.obj) ↔
      IsZero ((boundedConstructibleUpperShriek _ ℓ (zeroSectionSpecialFibreMap X x.left.ker k')).obj
        ((specialization k' x).obj (verdierDual ℓ (toPoint X) K))) := by
  rw [isZero_specializationDefect_iff_isZero_upperShriek_verdierDual k' x.left.ker K hK
    ((specialization k' x).obj K)
    ((NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility
      ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel X x.left.ker k')
        (deformationModel_exists_comp_ε X x.left.ker k'))).app K)]
  exact ((boundedConstructibleUpperShriek _ ℓ _).mapIso
    (nonempty_specialization_verdierDual_iso k' x K).some).isZero_iff.symm

variable (k') in
/-- **The open case in dual form**: for an open immersion `j : U ⟶ X` whose image misses the
rational point `x` and `L` on `U`, the defect `C_{X,x}(Rj_! L)` vanishes if and only if
`Re^! Sp_{X,x}(Rj_* 𝔻_U L) = 0`, by `𝔻_X Rj_! L ≅ Rj_* 𝔻_U L`. -/
theorem isZero_specializationDefect_lowerShriek_iff (x : RationalPoint X)
    {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    (hj : Disjoint (Set.range j.left.base) (Set.range (centreι X x.left.ker).left.base))
    (L : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect X x.left.ker k' (Profinite.padicAlgClRingObj ℓ)
        ((boundedConstructibleLowerShriek _ ℓ j).obj L).obj) ↔
      IsZero ((boundedConstructibleUpperShriek _ ℓ (zeroSectionSpecialFibreMap X x.left.ker k')).obj
        ((specialization k' x).obj
          ((boundedConstructibleLowerStar _ ℓ j).obj (verdierDual ℓ (toPoint U) L)))) := by
  have hK : IsZero ((boundedConstructibleUpperStar _ ℓ (centreι X x.left.ker)).obj
      ((boundedConstructibleLowerShriek _ ℓ j).obj L)) :=
    (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j _ hj L).of_iso
      ((boundedConstructibleUpperStar _ ℓ _).mapIso
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek ℓ j).app L))
  have : IsIso (absoluteVerdierExchange ℓ j (toPoint X) L) :=
    IsIso.comp_isIso' inferInstance (isIso_verdierExchange ℓ j L (dualizingComplex ℓ (toPoint X)))
  have hU : j ≫ toPoint X = toPoint U := (isTerminalPoint k).hom_ext _ _
  rw [isZero_specializationDefect_iff_isZero_upperShriek_specialization_verdierDual k' x _ hK]
  have e := asIso (absoluteVerdierExchange ℓ j (toPoint X) L)
  rw [hU] at e
  exact ((boundedConstructibleUpperShriek _ ℓ _).mapIso
    ((specialization k' x).mapIso e)).isZero_iff.symm

end Defect

end AlgebraicGeometry.ProEtale.CondensedRing

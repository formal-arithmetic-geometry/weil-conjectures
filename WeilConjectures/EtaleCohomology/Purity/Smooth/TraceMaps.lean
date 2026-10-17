/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace

/-!
# The traces of the projective line, the affine line and affine space

The blueprint defines the integration maps of `sk-prop-an` *under the input* of the cohomology
of the projective line: an isomorphism `Λ_S ⊕ Λ_S(-1)[-2] ≅ Rq_* Λ_{ℙ¹_S}`
(`thm-amb-p1-decomposition`, whose existence is
`AlgebraicGeometry.Etale.exists_isIso_biprod_desc_projectiveLine`). The definitions here take
this input, twisted by `(1)[2]`, as an argument:

* the *trace of the projective line* `t_q : Rq_* Λ(1)[2] ⟶ Λ_S`: the inverse of the input
  followed by the projection to the second summand (`pur9-def-p1-trace`);
* the *trace of the affine line* `∫_p : Rp_! Λ(1)[2] ⟶ Λ_S`: `Rq_*` of the counit
  `j_! j^* Λ(1)[2] ⟶ Λ(1)[2]` of the open chart `j : 𝔸¹_S ⟶ ℙ¹_S`, followed by `t_q`
  (`pur9-def-affine-line-trace`);
* the *trace of affine space* `∫_{p_c} : Rp_{c!} Λ(c)[2c] ⟶ Λ_S`, by recursion along
  `𝔸^{c+1}_S ≅ 𝔸¹_{𝔸^c_S}` (`pur9-def-affine-space-trace`);
* the *purity comparison* `γ_{π,K} : Lπ^* K(c)[2c] ⟶ Rπ^! K` attached to an integration map
  `∫_π : Rπ_! Λ(c)[2c] ⟶ Λ_Z`, the adjoint of `Rπ_!(Lπ^* K(c)[2c]) ≅ Rπ_!(Λ(c)[2c]) ⊗ K ⟶ K`
  (`pur9-def-purity-comparison`).

## Implementation notes

The composition isomorphisms of compactly supported direct images and the projection formula
are only available as `Nonempty` statements in the library; the definitions use chosen
isomorphisms (`Nonempty.some`) for them.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- The input of the traces over `S`: the decomposition of `Rq_* Λ_{ℙ¹_S}`, twisted by `(1)[2]`,
`Λ_S(1)[2] ⊕ Λ_S ≅ Rq_* (Λ_{ℙ¹_S}(1)[2])`. -/
abbrev ProjectiveLineInput (S : Scheme.{u}) [HasInvertibleExponent Λ S] : Type (u + 1) :=
  (twistShift Λ S 1).obj (constantComplex Λ S) ⊞ constantComplex Λ S ≅
    (R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ])).obj
      ((twistShift Λ (ProjectiveLine S) 1).obj (constantComplex Λ (ProjectiveLine S)))

/-- Blueprint `pur9-def-p1-trace`: Trace of the projective line

Under the input `e` of the cohomology of the projective line, the trace
`t_q : Rq_* Λ(1)[2] ⟶ Λ_S` is the inverse of the input followed by the projection to the second
summand. -/
noncomputable def projectiveLineTrace (S : Scheme.{u}) [HasInvertibleExponent Λ S]
    (e : ProjectiveLineInput Λ S) :
    (R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ])).obj
      ((twistShift Λ (ProjectiveLine S) 1).obj (constantComplex Λ (ProjectiveLine S))) ⟶
      constantComplex Λ S :=
  e.inv ≫ biprod.snd

/-- The compactification of `p : 𝔸¹_S ⟶ S` by the projective line `q : ℙ¹_S ⟶ S`, with the open
chart `j : 𝔸¹_S ≅ 𝔸(PUnit; S) ⟶ ℙ¹_S` (the same as
`AlgebraicGeometry.ProjectiveLine.affineLineCompactification'`, with literal fields). -/
noncomputable def projectiveLineCompactification (S : Scheme.{u}) :
    Compactification (𝔸(ULift.{u} (Fin 1); S) ↘ S) where
  Z := ProjectiveLine S
  g := ProjectiveLine S ↘ S
  i := (ProjectiveLine.affineLineIso S).hom ≫ ProjectiveLine.affineChart S
  comm := by
    rw [Category.assoc, ProjectiveLine.affineChart_over]
    simp [ProjectiveLine.affineLineIso, AffineSpace.reindex_over]
  isProper := inferInstanceAs (IsProper (ProjectiveLine S ↘ S))
  isOpenImmersion := inferInstanceAs
    (IsOpenImmersion ((ProjectiveLine.affineLineIso S).hom ≫ ProjectiveLine.affineChart S))

/-- The identification `Λ_{𝔸¹}(1)[2] ≅ j^* (Λ_{ℙ¹}(1)[2])` for the open chart `j`. -/
noncomputable def affineLineTwistShiftIso (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    (twistShift Λ 𝔸(ULift.{u} (Fin 1); S) 1).obj (constantComplex Λ 𝔸(ULift.{u} (Fin 1); S)) ≅
      (D(((ProjectiveLine.affineLineIso S).hom ≫
          ProjectiveLine.affineChart S)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ (ProjectiveLine S) 1).obj (constantComplex Λ (ProjectiveLine S))) :=
  (twistShift Λ _ 1).mapIso (leftDerivedUpperStarConstantComplexIso Λ
      ((ProjectiveLine.affineLineIso S).hom ≫ ProjectiveLine.affineChart S)).symm ≪≫
    (leftDerivedUpperStarTwistShiftIso Λ
      ((ProjectiveLine.affineLineIso S).hom ≫ ProjectiveLine.affineChart S) 1 _).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ)
      ((ProjectiveLine.affineLineIso S).hom ≫ ProjectiveLine.affineChart S)).app _

/-- Blueprint `pur9-def-affine-line-trace`: Trace of the affine line

Under the input `e`, the trace `∫_p : Rp_! Λ(1)[2] ⟶ Λ_S` of the affine line `p : 𝔸¹_S ⟶ S`:
the comparison `θ` of `Rp_!` with the compactly supported direct image `R_{d_p} = Rq_* j_!` of
the compactification `d_p = (j, q)` by the projective line, `Rq_*` of the counit
`j_! j^* Λ(1)[2] ⟶ Λ(1)[2]`, and the trace `t_q` of the projective line. -/
noncomputable def affineLineTrace (S : Scheme.{u}) [HasInvertibleExponent Λ S]
    (e : ProjectiveLineInput Λ S) :
    (R(𝔸(ULift.{u} (Fin 1); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin 1); S) 1).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin 1); S))) ⟶ constantComplex Λ S :=
  (rightDerivedLowerShriekIso Λ (projectiveLineCompactification S)).inv.app _ ≫
    (R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ])).map
      ((D(((ProjectiveLine.affineLineIso S).hom ≫
          ProjectiveLine.affineChart S)_!open[ModuleCat.{u + 1} Λ])).map
          (affineLineTwistShiftIso Λ S).hom ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
          ((ProjectiveLine.affineLineIso S).hom ≫ ProjectiveLine.affineChart S)).counit.app _) ≫
    projectiveLineTrace Λ S e

section AffineSpace

variable [HasTateTwist.IsNormalized Λ]

/-- The chosen identification
`Rp_{d+1,!} Λ(d + 1)[2(d + 1)] ≅ Rp_{d!}((Rq_! Λ(1)[2])(d)[2d])` along
`𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`, from the composition of compactly supported direct images and the
projection formula. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_succ (d : ℕ)
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Nonempty ((R(𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin (d + 1)); S) (d + 1 : ℕ)).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin (d + 1)); S))) ≅
      (R(𝔸(ULift.{u} (Fin d); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ _ d).obj
        ((R(𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘
            𝔸(ULift.{u} (Fin d); S))_![ModuleCat.{u + 1} Λ]).obj
          ((twistShift Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) 1).obj
            (constantComplex Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S))))))) := by
  set A := ModuleCat.{u + 1} Λ
  set φ := affineSpaceSuccIso d S
  set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘ 𝔸(ULift.{u} (Fin d); S)
  set p := 𝔸(ULift.{u} (Fin d); S) ↘ S
  have : HasCompactification φ.hom :=
    (Compactification.ofIsOpenImmersion φ.hom).hasCompactification
  have h : 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S = φ.hom ≫ q ≫ p :=
    (affineSpaceSuccIso_hom_over_over d S).symm
  have h' : φ.inv ≫ 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S = q ≫ p := by
    rw [h, Iso.inv_hom_id_assoc]
  have : HasCompactification (q ≫ p) := by
    have := HasCompactification.comp_of_isOpenImmersion
      (𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S) φ.inv
    exact .of_eq h'
  have : HasCompactification (φ.hom ≫ q ≫ p) := .of_eq h
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedLowerShriek_of_eq Λ h
  obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ φ.hom (q ≫ p)
  obtain ⟨c₂⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ q p
  obtain ⟨t₀⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_of_iso Λ φ ((d + 1 : ℕ) : ℤ)
  obtain ⟨t₁⟩ := nonempty_iso_rightDerivedLowerShriek_obj_twistShift Λ q d
    ((twistShift Λ _ 1).obj (constantComplex Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S))))
  exact ⟨heq.app _ ≪≫ c₁.app _ ≪≫ (R(q ≫ p)_![A]).mapIso t₀ ≪≫ c₂.app _ ≪≫
    (R(p)_![A]).mapIso ((R(q)_![A]).mapIso
      (eqToIso (by rw [show ((d + 1 : ℕ) : ℤ) = 1 + d by push_cast; ring]) ≪≫
        (twistShiftTwistShiftIso Λ _ 1 d _).symm) ≪≫ t₁)⟩

/-- The input of the traces over every base: a decomposition of the cohomology of the
projective line over every scheme on which the exponent of `Λ` is invertible. -/
abbrev ProjectiveLineInputs : Type (u + 1) :=
  ∀ (S : Scheme.{u}) [HasInvertibleExponent Λ S], ProjectiveLineInput Λ S

/-- The type `Rp_{c!} Λ(c)[2c] ⟶ Λ_S` of the affine-space traces. -/
def AffineSpaceTraceType (c : ℕ) (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Type (u + 1) :=
  (R(𝔸(ULift.{u} (Fin c); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
    ((twistShift Λ 𝔸(ULift.{u} (Fin c); S) c).obj (constantComplex Λ 𝔸(ULift.{u} (Fin c); S))) ⟶
      constantComplex Λ S

/-- The affine-space trace in dimension zero: the identification `Rp_{0!} Λ ≅ Λ_S` along the
isomorphism `p_0 : 𝔸⁰_S ≅ S`. -/
noncomputable def affineSpaceTraceZero (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    AffineSpaceTraceType Λ 0 S :=
  haveI : HasCompactification (asIso (𝔸(ULift.{u} (Fin 0); S) ↘ S)).hom :=
    inferInstanceAs (HasCompactification (𝔸(ULift.{u} (Fin 0); S) ↘ S))
  (nonempty_iso_rightDerivedLowerShriek_twistShift_of_iso Λ
    (asIso (𝔸(ULift.{u} (Fin 0); S) ↘ S)) ((0 : ℕ) : ℤ)).some.hom ≫
    (twistShiftZeroIso Λ S (by simp) _).hom

/-- The inductive step of the affine-space trace: from a trace `tr` of `𝔸^c_S`, the trace of
`𝔸^{c+1}_S ≅ 𝔸¹_{𝔸^c_S}`, the affine-line trace over `𝔸^c_S` followed by `tr`. -/
noncomputable def affineSpaceTraceSucc (c : ℕ) (S : Scheme.{u}) [HasInvertibleExponent Λ S]
    (e : ProjectiveLineInput Λ 𝔸(ULift.{u} (Fin c); S)) (tr : AffineSpaceTraceType Λ c S) :
    AffineSpaceTraceType Λ (c + 1) S :=
  (nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_succ Λ c S).some.hom ≫
    (R(𝔸(ULift.{u} (Fin c); S) ↘ S)_![ModuleCat.{u + 1} Λ]).map ((twistShift Λ _ c).map
      (affineLineTrace Λ 𝔸(ULift.{u} (Fin c); S) e)) ≫ tr

/-- Blueprint `pur9-def-affine-space-trace`: Trace of affine space

Under the inputs `E` of the cohomology of the projective line over every base, the trace
`∫_{p_c} : Rp_{c!} Λ(c)[2c] ⟶ Λ_S` of affine space, by recursion on `c`: for `c = 0` it is the
identification `Rp_{0!} Λ ≅ Λ_S` along the isomorphism `p_0 : 𝔸⁰_S ≅ S`; for `c + 1` it is the
identification `Rp_{c+1,!} Λ(c + 1)[2(c + 1)] ≅ Rp_{c!}((Rq_! Λ(1)[2])(c)[2c])` along
`𝔸^{c+1}_S ≅ 𝔸¹_{𝔸^c_S}`, followed by `Rp_{c!}` of the affine-line trace `∫_q` over `𝔸^c_S`
twisted by `(c)[2c]`, and by `∫_{p_c}`. -/
noncomputable def affineSpaceTrace (E : ProjectiveLineInputs Λ) :
    (c : ℕ) → ∀ (S : Scheme.{u}) [HasInvertibleExponent Λ S], AffineSpaceTraceType Λ c S
  | 0 => fun S _ ↦ affineSpaceTraceZero Λ S
  | c + 1 => fun S _ ↦ affineSpaceTraceSucc Λ c S (E 𝔸(ULift.{u} (Fin c); S))
      (affineSpaceTrace E c S)

end AffineSpace

/-- Blueprint `pur9-def-purity-comparison`: The purity comparison

For a morphism `π : V ⟶ Z` with a compactly supported direct image and an integration map
`∫_π : Rπ_! Λ_V(c)[2c] ⟶ Λ_Z` (for a vector bundle, the trace of the bundle; for `𝔸^c_B`, the
affine-space trace `AlgebraicGeometry.Etale.affineSpaceTrace`), the purity comparison

`γ_{π,K} : Lπ^* K (c)[2c] = Λ_V(c)[2c] ⊗ᴸ Lπ^* K ⟶ Rπ^! K`

is the morphism corresponding under `Rπ_! ⊣ Rπ^!` to
`Rπ_!(Λ_V(c)[2c] ⊗ᴸ Lπ^* K) ≅ Rπ_!(Λ_V(c)[2c]) ⊗ᴸ K ⟶ Λ_Z ⊗ᴸ K ≅ K`, the first isomorphism
being the projection formula (`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`). The
source is written `Λ_V(c)[2c] ⊗ᴸ Lπ^* K`, the form in which the blueprint applies the projection
formula. -/
noncomputable def purityComparison {V Z : Scheme.{u}} [HasInvertibleExponent Λ V]
    (π : V ⟶ Z) [HasCompactification π] (c : ℤ)
    (tr : (R(π)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ V c).obj (constantComplex Λ V)) ⟶
      constantComplex Λ Z)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) V).obj ((twistShift Λ V c).obj
        (constantComplex Λ V))).obj ((L((π)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      (R(π)^![ModuleCat.{u + 1} Λ]).obj K :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π).homEquiv _ _
    (((nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight (ModuleCat.{u + 1} Λ) π K
        (fun M ↦ hasProjectionFormula_of_finite Λ _ M _)).some.app _).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).map tr).app K ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Z K).hom)

end AlgebraicGeometry.Etale

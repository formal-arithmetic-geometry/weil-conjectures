/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Submission.WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Submission.WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Closed subgroup schemes of `GL_n`

A Hopf ideal `I` of `k[x_ij, det⁻¹]` cuts out the closed subgroup scheme
`V(I) = Spec (k[x_ij, det⁻¹] ⧸ I)` of the group scheme `𝔾𝕃(n; k)`: a group object of
`Over (Spec k)` with a closed immersion `V(I) ⟶ 𝔾𝕃(n; k)` of group objects. An inclusion `I ≤ J`
of Hopf ideals gives a closed immersion `V(J) ⟶ V(I)` of group objects.

The `R`-points `Spec R ⟶ V(I)` of this group scheme are identified with the matrix group
`zeroLocus I R` of `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal`: this is
a theorem (`range_homMulEquiv_comp`, packaged as the group isomorphism `zeroLocusMulEquiv`), not a
definition, and it is the only place where the scheme and the matrix groups meet.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.subgroupScheme`: the closed subgroup scheme `V(I)` of
  `𝔾𝕃(n; k)`, with its closed immersion `subgroupSchemeι` into `𝔾𝕃(n; k)`.
- `AlgebraicGeometry.GeneralLinearGroup.subgroupSchemeHom`: the closed immersion `V(J) ⟶ V(I)`
  induced by an inclusion `I ≤ J` of Hopf ideals.
- `AlgebraicGeometry.GeneralLinearGroup.zeroLocusMulEquiv`: the group of `R`-points
  `Spec R ⟶ V(I)` is the matrix group `zeroLocus I R`.
- `AlgebraicGeometry.GeneralLinearGroup.conjHom`,
  `AlgebraicGeometry.GeneralLinearGroup.subgroupSchemeConjIso`: conjugation by a `k`-point of
  `GL_n`, as an endomorphism of the group scheme `𝔾𝕃(n; k)` and as an automorphism of a closed
  subgroup scheme `V(I)` that it preserves.
- `AlgebraicGeometry.GeneralLinearGroup.derivedIdeal`: the Hopf ideal of the derived subgroup
  `[V(I), V(I)]`, the smallest closed subgroup scheme of `V(I)` with commutative quotient.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.range_homMulEquiv_comp`: the `R`-points of `V(I)` are the
  matrices satisfying the equations in `I`.
- `AlgebraicGeometry.GeneralLinearGroup.zeroLocusMulEquiv_map`: the identification of points is
  natural in `R`.
- `AlgebraicGeometry.GeneralLinearGroup.range_subgroupSchemeHom_le_identityComponent`: the closed
  subgroup scheme cut out by the ideal `identityComponent I` is the reduced identity component of
  `V(I)`.
- `AlgebraicGeometry.GeneralLinearGroup.finiteIndex_subgroupOf_zeroLocus_identityComponent`: the
  `k`-points of `G°` have finite index in the `k`-points of `G`.
- `AlgebraicGeometry.GeneralLinearGroup.containsCommutators_subgroupSchemeHom`: if `V(J)(R)`
  contains the commutators of `V(I)(R)` for all `R`, then `V(J) ⟶ V(I)` contains the commutators
  scheme-theoretically.
- `AlgebraicGeometry.GeneralLinearGroup.containsCommutators_iff_le_derivedIdeal`: a closed subgroup
  of `V(I)` contains the commutators if and only if it contains the derived subgroup.

## Blueprint

- `det-d-geometry`: matrix algebraic groups as closed subgroup schemes of `GL(V)`.
- `sk-i-restriction`: closed subgroups containing the commutators, and the derived subgroup.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry WithConv
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]

section AffineFactor

/-- Two morphisms `Spec Γ(X) ⟶ Y` to an affine scheme agreeing after `X ⟶ Spec Γ(X)` agree. -/
theorem _root_.AlgebraicGeometry.Scheme.toSpecΓ_comp_injective (X : Scheme.{u}) {Y : Scheme.{u}}
    [IsAffine Y] {g₁ g₂ : Spec Γ(X, ⊤) ⟶ Y} (h : X.toSpecΓ ≫ g₁ = X.toSpecΓ ≫ g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  have := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at this
  exact (cancel_mono _).1 this

/-- Every morphism from a `k`-scheme `X` to the spectrum of a `k`-algebra factors uniquely through
`X ⟶ Spec Γ(X)`, as a morphism over `Spec k`. -/
theorem _root_.AlgebraicGeometry.Over.exists_bijective_comp_toSpecΓ (X : Over (Spec (.of k))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R)
      (t : X ⟶ (Spec (.of R)).asOver (Spec (.of k))),
      ∀ (B : Type u) [CommRing B] [Algebra k B], Function.Bijective
        fun g : (Spec (.of R)).asOver (Spec (.of k)) ⟶ (Spec (.of B)).asOver (Spec (.of k)) ↦
          t ≫ g := by
  let : Algebra k Γ(X.left, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom.toAlgebra
  have hX : X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, ⊤))) = X.hom := by
    change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) = X.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance, Over.homMk X.left.toSpecΓ hX,
    fun B _ _ ↦ ⟨fun g₁ g₂ h ↦ ?_, fun a ↦ ?_⟩⟩
  · exact Over.OverMorphism.ext
      (Scheme.toSpecΓ_comp_injective (Y := Spec (.of B)) X.left (g₁ := g₁.left) (g₂ := g₂.left)
        (congrArg Over.Hom.left h))
  · obtain ⟨a', ha'⟩ : ∃ a' : X.left ⟶ Spec (.of B), a' = a.left := ⟨_, rfl⟩
    have ha := Scheme.toSpecΓ_naturality a'
    let g : Spec Γ(X.left, ⊤) ⟶ Spec (.of B) :=
      Spec.map a'.appTop ≫ inv (Spec (.of B)).toSpecΓ
    have hg : X.left.toSpecΓ ≫ g = a.left := by
      rw [← Category.assoc, ← ha, Category.assoc, IsIso.hom_inv_id, Category.comp_id, ha']
    refine ⟨Over.homMk g (Scheme.toSpecΓ_comp_injective (Y := Spec (.of k)) X.left ?_),
      Over.OverMorphism.ext hg⟩
    change X.left.toSpecΓ ≫ g ≫ Spec.map _ = X.left.toSpecΓ ≫ Spec.map _
    rw [reassoc_of% hg, hX]
    exact Over.w a

end AffineFactor

section SubgroupScheme

/-- The closed subgroup scheme `V(I) = Spec (k[x_ij, det⁻¹] ⧸ I)` of `GL_n` cut out by a Hopf ideal
`I`. It is a group object by Mathlib's quotient Hopf algebra structure.
(blueprint: `det-d-geometry`) -/
noncomputable abbrev subgroupScheme (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Over (Spec (.of k)) :=
  (Spec (.of (CoordinateRing n k ⧸ I))).asOver (Spec (.of k))

variable (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

noncomputable instance : GrpObj (subgroupScheme I) := inferInstance

instance : IsAffine (subgroupScheme I).left :=
  inferInstanceAs (IsAffine (Spec (.of (CoordinateRing n k ⧸ I))))

instance : LocallyOfFiniteType (subgroupScheme I).hom :=
  locallyOfFiniteType_specOverSpec

/-- The closed immersion of the closed subgroup scheme `V(I)` into `GL_n`.
(blueprint: `det-d-geometry`) -/
noncomputable def subgroupSchemeι : subgroupScheme I ⟶ 𝔾𝕃(n; k) :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k I).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (subgroupSchemeι I) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (Bialgebra.Quotient.mkBialgHom (R := k) I)).op).hom)

instance : IsClosedImmersion (subgroupSchemeι I).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : Mono (subgroupSchemeι I) :=
  Over.mono_of_mono_left _

theorem subgroupSchemeι_comp_injective {X : Over (Spec (.of k))} :
    Function.Injective fun φ : X ⟶ subgroupScheme I ↦ φ ≫ subgroupSchemeι I :=
  fun _ _ h ↦ (cancel_mono _).1 h

theorem mapMulEquiv_comp_subgroupSchemeι {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (CoordinateRing n k ⧸ I →ₐ[k] R)) :
    Spec.mapMulEquiv ψ ≫ subgroupSchemeι I =
      Spec.mapMulEquiv (toConv (ψ.ofConv.comp (Ideal.Quotient.mkₐ k I))) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The `R`-points of the closed subgroup scheme `V(I)` are the invertible matrices over `R`
satisfying the equations in `I`: the identification of `G(R)` with a classical matrix group is a
theorem, not a definition. (blueprint: `det-d-geometry`) -/
theorem range_homMulEquiv_comp (R : Type u) [CommRing R] [Algebra k R] :
    Set.range (fun φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I ↦
      GeneralLinearGroup.homMulEquiv n k R (φ ≫ subgroupSchemeι I)) = zeroLocus I R := by
  have key (χ : CoordinateRing n k ⧸ I →ₐ[k] R) :
      GeneralLinearGroup.homMulEquiv n k R (Spec.mapMulEquiv (toConv χ) ≫ subgroupSchemeι I) =
        algHomMulEquiv n k R (toConv (χ.comp (Ideal.Quotient.mkₐ k I))) := by
    rw [mapMulEquiv_comp_subgroupSchemeι, GeneralLinearGroup.homMulEquiv_mapMulEquiv,
      ofConv_toConv]
  have heval (χ : CoordinateRing n k →ₐ[k] R) :
      evalAlgHom (algHomMulEquiv n k R (toConv χ)) = χ :=
    congrArg ofConv ((algHomMulEquiv n k R).symm_apply_apply (toConv χ))
  ext g
  constructor
  · rintro ⟨φ, rfl⟩ a ha
    obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective φ
    dsimp only
    rw [← toConv_ofConv χ, key, heval, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  · intro hg
    refine ⟨Spec.mapMulEquiv (toConv (Ideal.Quotient.liftₐ I (evalAlgHom g) fun a ha ↦ hg a ha)),
      ?_⟩
    dsimp only
    rw [key]
    exact (algHomMulEquiv n k R).apply_symm_apply g

theorem injective_homMulEquiv_comp (R : Type u) [CommRing R] [Algebra k R] :
    Function.Injective fun φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I ↦
      GeneralLinearGroup.homMulEquiv n k R (φ ≫ subgroupSchemeι I) :=
  (GeneralLinearGroup.homMulEquiv n k R).injective.comp (subgroupSchemeι_comp_injective I)

/-- The `R`-points of the closed subgroup scheme `V(I)` are the group `zeroLocus I R` of matrices
satisfying the equations in `I`: a point `φ : Spec R ⟶ V(I)` corresponds to the matrix of the
point `φ ≫ ι` of `GL_n`, where `ι : V(I) ⟶ GL_n` is the closed immersion.
(blueprint: `det-d-geometry`) -/
noncomputable def zeroLocusMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    zeroLocus I R ≃* ((Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I) :=
  (MulEquiv.subgroupCongr (SetLike.coe_injective (range_homMulEquiv_comp I R)).symm).trans
    (MonoidHom.ofInjective (f := (GeneralLinearGroup.homMulEquiv n k R).toMonoidHom.comp
      (IsMonHom.monoidHom (subgroupSchemeι I) _)) (injective_homMulEquiv_comp I R)).symm

variable {I}

@[simp]
theorem homMulEquiv_zeroLocusMulEquiv_comp {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus I R) :
    GeneralLinearGroup.homMulEquiv n k R (zeroLocusMulEquiv I R g ≫ subgroupSchemeι I) = g :=
  congrArg Subtype.val ((MonoidHom.ofInjective
    (f := (GeneralLinearGroup.homMulEquiv n k R).toMonoidHom.comp
      (IsMonHom.monoidHom (subgroupSchemeι I) _)) (injective_homMulEquiv_comp I R)).apply_symm_apply
      ⟨g, _⟩)

attribute [irreducible] zeroLocusMulEquiv


end SubgroupScheme

section Inclusion

variable {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The closed immersion `V(J) ⟶ V(I)` of closed subgroup schemes of `GL_n` induced by an
inclusion `I ≤ J` of Hopf ideals: the spectrum of the quotient map `k[GL_n] ⧸ I → k[GL_n] ⧸ J`.
(blueprint: `det-d-geometry`) -/
noncomputable def subgroupSchemeHom (h : I ≤ J) : subgroupScheme J ⟶ subgroupScheme I :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorₐ k h).toRingHom)).asOver (Spec (.of k))

variable (h : I ≤ J)

@[reassoc (attr := simp)]
theorem subgroupSchemeHom_comp_subgroupSchemeι :
    subgroupSchemeHom h ≫ subgroupSchemeι I = subgroupSchemeι J := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The inclusions of closed subgroup schemes compose: `V(K) ⟶ V(J) ⟶ V(I)` is `V(K) ⟶ V(I)`. -/
@[reassoc (attr := simp)]
theorem subgroupSchemeHom_comp {K : Ideal (CoordinateRing n k)} [K.IsHopfIdeal k] (h' : J ≤ K) :
    subgroupSchemeHom h' ≫ subgroupSchemeHom h = subgroupSchemeHom (h.trans h') := by
  rw [← cancel_mono (subgroupSchemeι I), Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι,
    subgroupSchemeHom_comp_subgroupSchemeι, subgroupSchemeHom_comp_subgroupSchemeι]

instance : IsClosedImmersion (subgroupSchemeHom h).left :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)

instance : Mono (subgroupSchemeHom h) :=
  mono_of_mono_fac (subgroupSchemeHom_comp_subgroupSchemeι h)

/-- The inclusion `V(J) ⟶ V(I)` is a homomorphism of group schemes: it is the unique morphism
whose composite with the closed immersion `V(I) ⟶ GL_n` is the closed immersion `V(J) ⟶ GL_n`. -/
instance : IsMonHom (subgroupSchemeHom h) where
  one_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeHom_comp_subgroupSchemeι, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeHom_comp_subgroupSchemeι, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, subgroupSchemeHom_comp_subgroupSchemeι]

/-- The inclusion `V(I) ⟶ V(I)` induced by `I ≤ I` is the identity. -/
@[simp]
theorem subgroupSchemeHom_refl : subgroupSchemeHom (le_refl I) = 𝟙 (subgroupScheme I) :=
  (cancel_mono (subgroupSchemeι I)).1 (by simp)

theorem mapMulEquiv_comp_subgroupSchemeHom {R : Type u} [CommRing R] [Algebra k R]
    (ψ : WithConv (CoordinateRing n k ⧸ J →ₐ[k] R)) :
    Spec.mapMulEquiv ψ ≫ subgroupSchemeHom h =
      Spec.mapMulEquiv (toConv (ψ.ofConv.comp (Ideal.Quotient.factorₐ k h))) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

include h in
theorem zeroLocus_le_zeroLocus (R : Type u) [CommRing R] [Algebra k R] :
    zeroLocus J R ≤ zeroLocus I R :=
  fun _ hg a ha ↦ hg a (h ha)

theorem zeroLocusMulEquiv_comp_subgroupSchemeHom {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus J R) :
    zeroLocusMulEquiv J R g ≫ subgroupSchemeHom h =
      zeroLocusMulEquiv I R ⟨g, zeroLocus_le_zeroLocus h R g.2⟩ := by
  apply injective_homMulEquiv_comp I R
  dsimp only
  rw [Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι, homMulEquiv_zeroLocusMulEquiv_comp,
    homMulEquiv_zeroLocusMulEquiv_comp]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure on points of the quotient scheme makes instance search slow
/-- If `V(I)(R)` has its commutators in `V(J)(R)` for every `k`-algebra `R`, then the closed
immersion `V(J) ⟶ V(I)` contains the commutators scheme-theoretically
(`AlgebraicGeometry.IsMonHom.ContainsCommutators`).

Two points `X ⟶ V(I)` factor through the affine scheme `Spec Γ(X)`, where they are matrices over
`Γ(X)`; the hypothesis for `R = Γ(X)`, transported through `zeroLocusMulEquiv`, factors their
commutator through `V(J)`. (blueprint: `sk-i-restriction`) -/
theorem containsCommutators_subgroupSchemeHom
    (hIJ : ∀ (R : Type u) [CommRing R] [Algebra k R],
      ⁅zeroLocus I R, zeroLocus I R⁆ ≤ zeroLocus J R) :
    IsMonHom.ContainsCommutators (subgroupSchemeHom h) := by
  refine ⟨fun {X} a b ↦ ?_⟩
  obtain ⟨R, _, _, t, ht⟩ := Over.exists_bijective_comp_toSpecΓ X
  obtain ⟨a', rfl⟩ := (ht _).2 a
  obtain ⟨b', rfl⟩ := (ht _).2 b
  set x := (zeroLocusMulEquiv I R).symm a'
  set y := (zeroLocusMulEquiv I R).symm b'
  have hmem : ((x * y * x⁻¹ * y⁻¹ : zeroLocus I R) : GL n R) ∈ zeroLocus J R := by
    apply hIJ R
    have := Subgroup.commutator_mem_commutator x.2 y.2
    simpa [commutatorElement_def] using this
  refine ⟨t ≫ zeroLocusMulEquiv J R ⟨_, hmem⟩, ?_⟩
  rw [Category.assoc, zeroLocusMulEquiv_comp_subgroupSchemeHom,
    show (⟨_, zeroLocus_le_zeroLocus h R hmem⟩ : zeroLocus I R) = x * y * x⁻¹ * y⁻¹ from rfl,
    map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul,
    GrpObj.comp_inv, GrpObj.comp_inv]

end Inclusion

section Conjugation

variable (g : GL n k)

/-- Conjugation `x ↦ g * x * g⁻¹` by a `k`-point `g` of `𝔾𝕃(n; k)`, as an endomorphism of the group
scheme: the spectrum of the bialgebra endomorphism `conjBialgHom g` of the coordinate ring. -/
noncomputable def conjHom : 𝔾𝕃(n; k) ⟶ 𝔾𝕃(n; k) :=
  (Spec.map (CommRingCat.ofHom (translate g g⁻¹).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (conjHom g) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (conjBialgHom g)).op).hom)


variable {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
  (hg : ∀ a ∈ I, translate g g⁻¹ a ∈ I) (hg' : ∀ a ∈ I, translate g⁻¹ g a ∈ I)


/-- Conjugation by `g` as an automorphism of the closed subgroup scheme `V(I)`, when it preserves
the Hopf ideal `I` together with conjugation by `g⁻¹`: the spectrum of the automorphism of
`k[GL_n] ⧸ I` induced by `translate g g⁻¹`. -/
noncomputable def subgroupSchemeConjIso : subgroupScheme I ≅ subgroupScheme I where
  hom := (Spec.map (CommRingCat.ofHom
    (Ideal.quotientMapₐ (I := I) I (translate g g⁻¹) hg).toRingHom)).asOver (Spec (.of k))
  inv := (Spec.map (CommRingCat.ofHom
    (Ideal.quotientMapₐ (I := I) I (translate g⁻¹ g) hg').toRingHom)).asOver (Spec (.of k))
  hom_inv_id := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_))
    change Ideal.Quotient.mk I (translate g g⁻¹ (translate g⁻¹ g a)) = Ideal.Quotient.mk I a
    rw [← AlgHom.comp_apply, translate_comp_translate, inv_mul_cancel, translate_one_one,
      AlgHom.id_apply]
  inv_hom_id := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_))
    change Ideal.Quotient.mk I (translate g⁻¹ g (translate g g⁻¹ a)) = Ideal.Quotient.mk I a
    rw [← AlgHom.comp_apply, translate_comp_translate, mul_inv_cancel, translate_one_one,
      AlgHom.id_apply]

/-- The automorphism `subgroupSchemeConjIso` of `V(I)` is the restriction of the conjugation
`conjHom g` of `𝔾𝕃(n; k)`. -/
@[reassoc]
theorem subgroupSchemeConjIso_hom_comp_subgroupSchemeι :
    (subgroupSchemeConjIso g hg hg').hom ≫ subgroupSchemeι I =
      subgroupSchemeι I ≫ conjHom g := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Conjugation by `g` is an automorphism of the group scheme `V(I)`. -/
instance : IsMonHom (subgroupSchemeConjIso g hg hg').hom where
  one_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeConjIso_hom_comp_subgroupSchemeι, IsMonHom.one_hom_assoc, IsMonHom.one_hom,
      IsMonHom.one_hom]
  mul_hom := by
    rw [← cancel_mono (subgroupSchemeι I), Category.assoc,
      subgroupSchemeConjIso_hom_comp_subgroupSchemeι, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom_assoc, subgroupSchemeConjIso_hom_comp_subgroupSchemeι]


end Conjugation

section Derived

/-! ### The derived subgroup

The *derived subgroup* `[G, G]` of `G = V(I)` is the smallest closed subgroup scheme `D ⊆ G` whose
inclusion `D ⟶ G` contains the commutators of `G`
(`AlgebraicGeometry.IsMonHom.ContainsCommutators`), that is, such that `G ⧸ D` is commutative; it
is normal
(`AlgebraicGeometry.IsMonHom.Normal.of_containsCommutators`). In Hopf-ideal terms it is cut out by
the largest Hopf ideal `J ≥ I` with this property, the sum of all of them. -/

variable (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The Hopf ideal of the derived subgroup `[V(I), V(I)]`: the sum of all Hopf ideals `J ≥ I` such
that `V(J) ⟶ V(I)` contains the commutators of `V(I)`. (blueprint: `sk-i-restriction`) -/
noncomputable def derivedIdeal : Ideal (CoordinateRing n k) :=
  sSup {J | ∃ (hJ : J.IsHopfIdeal k) (h : I ≤ J),
    haveI := hJ; IsMonHom.ContainsCommutators (subgroupSchemeHom h)}

/-- The derived subgroup is a subgroup: `[G, G] ⊆ G`. -/
theorem le_derivedIdeal : I ≤ derivedIdeal I :=
  le_sSup ⟨inferInstance, le_refl I,
    IsMonHom.ContainsCommutators.of_eq (subgroupSchemeHom_refl (I := I)).symm⟩

/-- The sum of Hopf ideals is a Hopf ideal, so the derived subgroup is a closed subgroup scheme.

Proof sketch (not formalised): if `Δ(a) ∈ J ⊗ A + A ⊗ J` and `Δ(b) ∈ J' ⊗ A + A ⊗ J'`, then
`Δ(a + b) ∈ (J + J') ⊗ A + A ⊗ (J + J')`; likewise for the counit and the antipode. -/
instance : (derivedIdeal I).IsHopfIdeal k :=
  Ideal.isHopfIdeal_sSup fun _ ⟨hJ, _, _⟩ ↦ hJ

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure on points of the quotient scheme makes instance search slow
set_option maxHeartbeats 2000000 in
-- the factorisation through `Spec Γ(X)` and the commutator computation are slow to elaborate
/-- The derived subgroup contains the commutators of `G`: `G ⧸ [G, G]` is commutative.

Two points `X ⟶ V(I)` factor through the affine scheme `Spec Γ(X)`, where they are matrices over
`Γ(X)`. Their commutator satisfies the equations of every Hopf ideal in the family defining
`derivedIdeal I`, hence those of their sum. (blueprint: `sk-i-restriction`) -/
instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I)) := by
  refine ⟨fun {X} a b ↦ ?_⟩
  obtain ⟨R, _, _, t, ht⟩ := Over.exists_bijective_comp_toSpecΓ X
  obtain ⟨a', rfl⟩ := (ht _).2 a
  obtain ⟨b', rfl⟩ := (ht _).2 b
  have hγ : (t ≫ a') * (t ≫ b') * (t ≫ a')⁻¹ * (t ≫ b')⁻¹ =
      t ≫ (a' * b' * a'⁻¹ * b'⁻¹) := by
    rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
  obtain ⟨ψ, hψ⟩ := Spec.mapMulEquiv.surjective (a' * b' * a'⁻¹ * b'⁻¹)
  obtain ⟨ψ, rfl⟩ : ∃ ψ₀, toConv ψ₀ = ψ := ⟨_, toConv_ofConv ψ⟩
  have hkill (J : Ideal (CoordinateRing n k)) [J.IsHopfIdeal k] (hIJ : I ≤ J)
      (hc : IsMonHom.ContainsCommutators (subgroupSchemeHom hIJ)) :
      J ≤ RingHom.ker (ψ.comp (Ideal.Quotient.mkₐ k I)) := by
    intro j hj
    obtain ⟨c, hc'⟩ := hc.exists_comp_eq_commutator (t ≫ a') (t ≫ b')
    obtain ⟨c', rfl⟩ := (ht _).2 c
    obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective c'
    have e : Spec.mapMulEquiv χ ≫ subgroupSchemeHom hIJ = a' * b' * a'⁻¹ * b'⁻¹ :=
      (ht _).1 (by
        beta_reduce at hc' ⊢
        rw [← Category.assoc, hc', hγ])
    rw [mapMulEquiv_comp_subgroupSchemeHom, ← hψ] at e
    have e' : χ.ofConv.comp (Ideal.Quotient.factorₐ k hIJ) = ψ := by
      simpa using congrArg ofConv (Spec.mapMulEquiv.injective e)
    rw [RingHom.mem_ker, AlgHom.comp_apply, ← e']
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hj]
  have hker : derivedIdeal I ≤ RingHom.ker (ψ.comp (Ideal.Quotient.mkₐ k I)) :=
    sSup_le fun J ⟨hJ, hIJ, hc⟩ ↦ hkill J hIJ hc
  refine ⟨t ≫ Spec.mapMulEquiv (toConv (Ideal.Quotient.liftₐ (derivedIdeal I)
    (ψ.comp (Ideal.Quotient.mkₐ k I)) fun j hj ↦ hker hj)), ?_⟩
  rw [Category.assoc, mapMulEquiv_comp_subgroupSchemeHom, hγ]
  congr 1
  rw [← hψ]
  congr 1
  rw [ofConv_toConv]
  congr 1
  apply Ideal.Quotient.algHom_ext
  ext a
  rfl

variable {I} {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (h : I ≤ J)


end Derived

section OnePoint

variable {k : Type u} [Field k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]


end OnePoint

section IdentityComponent

variable {k : Type u} [Field k] [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]


end IdentityComponent

section Geometry

variable {k : Type u} [Field k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]


end Geometry

end AlgebraicGeometry.GeneralLinearGroup

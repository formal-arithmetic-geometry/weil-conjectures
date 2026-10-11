/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

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

- `sk-d-geometry`: matrix algebraic groups as closed subgroup schemes of `GL(V)`.
- `sk-i-restriction`: closed subgroups containing the commutators, and the derived subgroup.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry WithConv
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]

section SubgroupScheme

/-- The closed subgroup scheme `V(I) = Spec (k[x_ij, det⁻¹] ⧸ I)` of `GL_n` cut out by a Hopf ideal
`I`. It is a group object by Mathlib's quotient Hopf algebra structure.
(blueprint: `sk-d-geometry`) -/
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
(blueprint: `sk-d-geometry`) -/
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
theorem, not a definition. (blueprint: `sk-d-geometry`) -/
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
(blueprint: `sk-d-geometry`) -/
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

/-- The identification `zeroLocusMulEquiv` is natural in the algebra of values: the square
```
V(I)(R) ──zeroLocus.map φ──▶ V(I)(S)
   │                            │
   ▼                            ▼
(Spec R ⟶ V(I)) ──Spec φ ≫ ·──▶ (Spec S ⟶ V(I))
```
commutes. -/
theorem zeroLocusMulEquiv_map {R S : Type u} [CommRing R] [Algebra k R] [CommRing S]
    [Algebra k S] (φ : R →ₐ[k] S) (g : zeroLocus I R) :
    zeroLocusMulEquiv I S (zeroLocus.map I φ g) =
      (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of k)) ≫
        zeroLocusMulEquiv I R g := by
  apply injective_homMulEquiv_comp I S
  simp only [homMulEquiv_zeroLocusMulEquiv_comp, zeroLocus.coe_map_apply, Category.assoc,
    GeneralLinearGroup.homMulEquiv_specMap_comp]

end SubgroupScheme

section Inclusion

variable {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The closed immersion `V(J) ⟶ V(I)` of closed subgroup schemes of `GL_n` induced by an
inclusion `I ≤ J` of Hopf ideals: the spectrum of the quotient map `k[GL_n] ⧸ I → k[GL_n] ⧸ J`.
(blueprint: `sk-d-geometry`) -/
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

/-- If `V(I)(R)` has its commutators in `V(J)(R)` for every `k`-algebra `R`, then the closed
immersion `V(J) ⟶ V(I)` contains the commutators scheme-theoretically
(`AlgebraicGeometry.IsMonHom.ContainsCommutators`).

Proof sketch (not formalised): it suffices to factor the universal commutator, that of the two
projections of `V(I) × V(I)`, through `V(J)`; every other commutator is obtained from it by
precomposition. The product `V(I) × V(I)` is affine, the spectrum of
`(k[GL_n] ⧸ I) ⊗[k] (k[GL_n] ⧸ I)`, so its identity is a point of `V(I) × V(I)` with values in this
algebra, and the hypothesis for this algebra, transported through `zeroLocusMulEquiv`, factors the
universal commutator. (blueprint: `sk-i-restriction`) -/
theorem containsCommutators_subgroupSchemeHom
    (hIJ : ∀ (R : Type u) [CommRing R] [Algebra k R],
      ⁅zeroLocus I R, zeroLocus I R⁆ ≤ zeroLocus J R) :
    IsMonHom.ContainsCommutators (subgroupSchemeHom h) := by
  sorry

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

/-- On `R`-points, `conjHom g` is conjugation by the image of `g` in `GL n R`. -/
theorem homMulEquiv_comp_conjHom {R : Type u} [CommRing R] [Algebra k R]
    (φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) :
    GeneralLinearGroup.homMulEquiv n k R (φ ≫ conjHom g) =
      map (algebraMap k R) g * GeneralLinearGroup.homMulEquiv n k R φ *
        map (algebraMap k R) g⁻¹ := by
  unfold GeneralLinearGroup at φ
  obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective φ
  have h : Spec.mapMulEquiv χ ≫ conjHom g =
      Spec.mapMulEquiv (toConv (χ.ofConv.comp (translate g g⁻¹))) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [h, GeneralLinearGroup.homMulEquiv_mapMulEquiv, GeneralLinearGroup.homMulEquiv_mapMulEquiv]
  apply (algHomMulEquiv n k R).symm.injective
  have hχ : evalAlgHom (algHomMulEquiv n k R χ) = χ.ofConv :=
    congrArg ofConv ((algHomMulEquiv n k R).symm_apply_apply χ)
  rw [MulEquiv.symm_apply_apply, algHomMulEquiv_symm_apply, ← evalAlgHom_comp_translate, hχ]

variable {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
  (hg : ∀ a ∈ I, translate g g⁻¹ a ∈ I) (hg' : ∀ a ∈ I, translate g⁻¹ g a ∈ I)

include hg in
/-- A matrix `x` over `R` satisfying the equations of `I` is conjugated by `g` to such a
matrix, when conjugation by `g` preserves `I`. -/
theorem mul_mul_inv_mem_zeroLocus {R : Type u} [CommRing R] [Algebra k R] {x : GL n R}
    (hx : x ∈ zeroLocus I R) :
    map (algebraMap k R) g * x * map (algebraMap k R) g⁻¹ ∈ zeroLocus I R := fun a ha ↦ by
  rw [← evalAlgHom_comp_translate, AlgHom.comp_apply]
  exact hx _ (hg a ha)

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

/-- On `R`-points, the automorphism `subgroupSchemeConjIso` of `V(I)` is conjugation by the image
of `g` in `GL n R`. -/
theorem zeroLocusMulEquiv_comp_subgroupSchemeConjIso_hom {R : Type u} [CommRing R]
    [Algebra k R] (x : zeroLocus I R) :
    zeroLocusMulEquiv I R x ≫ (subgroupSchemeConjIso g hg hg').hom =
      zeroLocusMulEquiv I R ⟨_, mul_mul_inv_mem_zeroLocus g hg x.2⟩ := by
  apply injective_homMulEquiv_comp I R
  dsimp only
  rw [Category.assoc, subgroupSchemeConjIso_hom_comp_subgroupSchemeι, ← Category.assoc,
    homMulEquiv_comp_conjHom, homMulEquiv_zeroLocusMulEquiv_comp,
    homMulEquiv_zeroLocusMulEquiv_comp]

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
instance : (derivedIdeal I).IsHopfIdeal k := by
  sorry

/-- The derived subgroup contains the commutators of `G`: `G ⧸ [G, G]` is commutative.

Proof sketch (not formalised): a morphism `X ⟶ V(I)` factors through `V(J)` if and only if `J`
maps to zero in `Γ(X, 𝒪_X)`; this holds for every `J` in the family defining `derivedIdeal I`,
hence for their sum. (blueprint: `sk-i-restriction`) -/
instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I)) := by
  sorry

variable {I} {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (h : I ≤ J)

/-- A closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)` if and only if it contains
the derived subgroup `[V(I), V(I)]`, that is, `J ≤ derivedIdeal I`.
(blueprint: `sk-i-restriction`) -/
theorem containsCommutators_iff_le_derivedIdeal :
    IsMonHom.ContainsCommutators (subgroupSchemeHom h) ↔ J ≤ derivedIdeal I := by
  refine ⟨fun hc ↦ le_sSup ⟨inferInstance, h, hc⟩, fun hJ ↦ ⟨fun a b ↦ ?_⟩⟩
  obtain ⟨c, hc⟩ := IsMonHom.ContainsCommutators.exists_comp_eq_commutator
    (subgroupSchemeHom (le_derivedIdeal I)) a b
  exact ⟨c ≫ subgroupSchemeHom hJ, by rw [Category.assoc, subgroupSchemeHom_comp, hc]⟩

end Derived

section IdentityComponent

variable {k : Type u} [Field k] [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The closed subgroup scheme `V(identityComponent I)` cut out by the ideal of the reduced
identity component is the reduced closed subscheme of `V(I)` on the identity component
`GrpObj.identityComponent (subgroupScheme I)`: its image in `V(I)` is the connected component of the
identity point. (blueprint: `sk-p-geometry`) -/
theorem range_subgroupSchemeHom_le_identityComponent :
    Set.range (subgroupSchemeHom (le_identityComponent I)).left.base =
      connectedComponent (GrpObj.onePoint (subgroupScheme I)) := by
  sorry

/-- A `k`-point of `V(I)` whose image lies in the connected component of the identity is a
`k`-point of the identity component: its matrix satisfies the equations `identityComponent I`. -/
theorem mem_zeroLocus_identityComponent_of_range_subset {g : zeroLocus I k}
    (hg : Set.range (zeroLocusMulEquiv I k g).left.base ⊆
      connectedComponent (GrpObj.onePoint (subgroupScheme I))) :
    (g : GL n k) ∈ zeroLocus (identityComponent I) k := by
  obtain ⟨χ, hχ⟩ := Spec.mapMulEquiv.surjective (zeroLocusMulEquiv I k g)
  have hev : evalAlgHom (g : GL n k) = χ.ofConv.comp (Ideal.Quotient.mkₐ k I) := by
    have h := homMulEquiv_zeroLocusMulEquiv_comp g
    rw [← hχ, mapMulEquiv_comp_subgroupSchemeι, GeneralLinearGroup.homMulEquiv_mapMulEquiv] at h
    rw [← h]
    exact congrArg ofConv ((algHomMulEquiv n k k).symm_apply_apply _)
  let pt : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨y, hy⟩ := (range_subgroupSchemeHom_le_identityComponent I).symm ▸ hg ⟨pt, rfl⟩
  intro a ha
  rw [hev]
  have hx := congrArg PrimeSpectrum.asIdeal hy
  rw [← hχ] at hx
  change Ideal.comap _ y.asIdeal = Ideal.comap _ (⊥ : Ideal k) at hx
  have : Ideal.Quotient.mk I a ∈
      Ideal.comap (CommRingCat.Hom.hom (CommRingCat.ofHom χ.ofConv.toRingHom)) ⊥ := by
    rw [← hx, Ideal.mem_comap]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  simpa using this

/-- The `k`-points of the identity component `G°` have finite index in the `k`-points of
`G = V(I)`. This is `AlgebraicGeometry.GrpObj.finiteIndex_range_identityComponentι` for the group
scheme `V(I)`, read on matrices through `zeroLocusMulEquiv`. (blueprint: `sk-p-geometry`) -/
theorem finiteIndex_subgroupOf_zeroLocus_identityComponent :
    ((zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)).FiniteIndex := by
  let X := (Spec (.of k)).asOver (Spec (.of k))
  let e : X ≅ 𝟙_ (Over (Spec (.of k))) := Over.isoMk (Iso.refl (Spec (.of k))) (by
    simp [X, specOverSpec_over, Algebra.algebraMap_self])
  let α : (𝟙_ (Over (Spec (.of k))) ⟶ subgroupScheme I) →* zeroLocus I k :=
    (zeroLocusMulEquiv I k).symm.toMonoidHom.comp
      { toFun p := CartesianMonoidalCategory.toUnit X ≫ p
        map_one' := MonObj.comp_one _
        map_mul' p q := MonObj.comp_mul _ _ _ }
  have hα : Function.Surjective α := fun g ↦ ⟨e.inv ≫ zeroLocusMulEquiv I k g, by
    simp [α, CartesianMonoidalCategory.toUnit_unique (CartesianMonoidalCategory.toUnit X) e.hom]⟩
  have := GrpObj.finiteIndex_range_identityComponentι (subgroupScheme I)
  have hle : (IsMonHom.monoidHom (GrpObj.identityComponentι (subgroupScheme I))
      (𝟙_ (Over (Spec (.of k))))).range ≤
        ((zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)).comap α := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine mem_zeroLocus_identityComponent_of_range_subset I ?_
    rw [← GrpObj.range_identityComponentι]
    rintro _ ⟨x, rfl⟩
    simp only [α, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact ⟨_, rfl⟩
  have := Subgroup.finiteIndex_of_le hle
  rw [Subgroup.finiteIndex_iff, ← Subgroup.index_comap_of_surjective _ hα]
  exact Subgroup.FiniteIndex.index_ne_zero

end IdentityComponent

section Geometry

variable {k : Type u} [Field k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The closed subgroup scheme `V(I)` is reduced when `I` is a radical ideal. -/
theorem isReduced_subgroupScheme (hI : I.IsRadical) : IsReduced (subgroupScheme I).left :=
  haveI : _root_.IsReduced (CoordinateRing n k ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).1 hI
  inferInstanceAs (IsReduced (Spec (.of (CoordinateRing n k ⧸ I))))

/-- The closed subgroup scheme `V(I)` is connected when `I` is the ideal of its own reduced
identity component: `V(I)` is then the closure of the connected component of the identity in
`V(I)`, which is closed. -/
theorem connectedSpace_subgroupScheme (h : IsConnected I) :
    ConnectedSpace (subgroupScheme I).left := by
  set C := connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
    (toPrimeSpectrum 1)
  have h1 : toPrimeSpectrum (1 : GL n k) ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) :=
    fun a ha ↦ (zeroLocus I k).one_mem a ha
  have hC : _root_.IsConnected (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) := by
    have hZ : PrimeSpectrum.zeroLocus (identityComponent I : Set (CoordinateRing n k)) =
        closure C :=
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure C
    rw [h] at hZ
    rw [hZ]
    exact (isConnected_connectedComponentIn_iff.2 h1).closure
  set f := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hf := PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I))
  have hr : Set.range f = PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I)), Ideal.mk_ker]
  change ConnectedSpace (PrimeSpectrum (CoordinateRing n k ⧸ I))
  rw [connectedSpace_iff_univ]
  rw [← hr, ← Set.image_univ] at hC
  exact ⟨hC.1.of_image, (hf.isInducing.isPreconnected_image).1 hC.2⟩

end Geometry

end AlgebraicGeometry.GeneralLinearGroup

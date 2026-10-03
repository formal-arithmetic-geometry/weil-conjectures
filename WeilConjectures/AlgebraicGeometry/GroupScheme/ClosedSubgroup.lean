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
`V(I) = Spec (k[x_ij, det⁻¹] ⧸ I)` of the group scheme `GL(n; k)`: a group object of
`Over (Spec k)` with a closed immersion `V(I) ⟶ GL(n; k)` of group objects. An inclusion `I ≤ J`
of Hopf ideals gives a closed immersion `V(J) ⟶ V(I)` of group objects.

The `R`-points `Spec R ⟶ V(I)` of this group scheme are identified with the matrix group
`zeroLocus I R` of `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal`: this is
a theorem (`range_homMulEquiv_comp`, packaged as the group isomorphism `zeroLocusMulEquiv`), not a
definition, and it is the only place where the scheme and the matrix groups meet.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.subgroupScheme`: the closed subgroup scheme `V(I)` of
  `GL(n; k)`, with its closed immersion `subgroupSchemeι` into `GL(n; k)`.
- `AlgebraicGeometry.GeneralLinearGroup.subgroupSchemeHom`: the closed immersion `V(J) ⟶ V(I)`
  induced by an inclusion `I ≤ J` of Hopf ideals.
- `AlgebraicGeometry.GeneralLinearGroup.zeroLocusMulEquiv`: the group of `R`-points
  `Spec R ⟶ V(I)` is the matrix group `zeroLocus I R`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.range_homMulEquiv_comp`: the `R`-points of `V(I)` are the
  matrices satisfying the equations in `I`.
- `AlgebraicGeometry.GeneralLinearGroup.zeroLocusMulEquiv_map`: the identification of points is
  natural in `R`.
- `AlgebraicGeometry.GeneralLinearGroup.range_subgroupSchemeHom_le_identityComponent`: the closed
  subgroup scheme cut out by the ideal `identityComponent I` is the reduced identity component of
  `V(I)`.

## Blueprint

- `sk-d-geometry`: matrix algebraic groups as closed subgroup schemes of `GL(V)`.
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
noncomputable def subgroupSchemeι : subgroupScheme I ⟶ GL(n; k) :=
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

end Inclusion

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

end IdentityComponent

end AlgebraicGeometry.GeneralLinearGroup

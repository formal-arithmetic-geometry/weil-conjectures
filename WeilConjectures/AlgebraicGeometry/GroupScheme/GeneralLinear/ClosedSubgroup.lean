/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
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

/-- An `R`-point of `V(I)` whose matrix satisfies the equations of `J` factors through
`V(J) ⟶ V(I)`. -/
theorem zeroLocusMulEquiv_comp_subgroupSchemeHom {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus I R) (hg : (g : GL n R) ∈ zeroLocus J R) :
    zeroLocusMulEquiv J R ⟨g, hg⟩ ≫ subgroupSchemeHom h = zeroLocusMulEquiv I R g := by
  apply injective_homMulEquiv_comp I R
  simp only [Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι,
    homMulEquiv_zeroLocusMulEquiv_comp]

/-- Conversely, an `R`-point of `V(I)` which factors through `V(J) ⟶ V(I)` satisfies the
equations of `J`. -/
theorem coe_mem_zeroLocus_of_comp_eq {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus I R) {c : (Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme J}
    (hc : c ≫ subgroupSchemeHom h = zeroLocusMulEquiv I R g) : (g : GL n R) ∈ zeroLocus J R := by
  rw [← SetLike.mem_coe, ← range_homMulEquiv_comp J R]
  refine ⟨c, ?_⟩
  dsimp only
  rw [← subgroupSchemeHom_comp_subgroupSchemeι h, ← Category.assoc, hc,
    homMulEquiv_zeroLocusMulEquiv_comp]

attribute [local instance] Scheme.algebraΓOfOver in
-- Searching for a commutative group structure on the points of `V(I)` times out.
attribute [-instance] Hom.commGroup in
/-- If `V(I)(R)` has its commutators in `V(J)(R)` for every `k`-algebra `R`, then the closed
immersion `V(J) ⟶ V(I)` contains the commutators scheme-theoretically
(`AlgebraicGeometry.IsMonHom.ContainsCommutators`): a point of the affine scheme `V(I)` with
values in `X` factors through `X ⟶ Spec Γ(X, ⊤)`, so it suffices to factor the commutators of
`Γ(X, ⊤)`-points, which is the hypothesis for `R = Γ(X, ⊤)`. (blueprint: `sk-i-restriction`) -/
theorem containsCommutators_subgroupSchemeHom
    (hIJ : ∀ (R : Type u) [CommRing R] [Algebra k R],
      ⁅zeroLocus I R, zeroLocus I R⁆ ≤ zeroLocus J R) :
    IsMonHom.ContainsCommutators (subgroupSchemeHom h) where
  exists_comp_eq_commutator {X} a b := by
    obtain ⟨a, rfl⟩ := Scheme.exists_toSpecΓOver_comp a
    obtain ⟨b, rfl⟩ := Scheme.exists_toSpecΓOver_comp b
    let e := zeroLocusMulEquiv I Γ(X.left, ⊤)
    have hc : (e.symm (a * b * a⁻¹ * b⁻¹) : GL n Γ(X.left, ⊤)) ∈ zeroLocus J Γ(X.left, ⊤) := by
      refine hIJ _ ?_
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      simpa [commutatorElement_def] using
        Subgroup.commutator_mem_commutator (e.symm a).2 (e.symm b).2
    refine ⟨Scheme.toSpecΓOver X ≫ zeroLocusMulEquiv J _ ⟨_, hc⟩, ?_⟩
    rw [Category.assoc, zeroLocusMulEquiv_comp_subgroupSchemeHom, e.apply_symm_apply,
      MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]

end Inclusion

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

/-- The sum of Hopf ideals is a Hopf ideal (`Ideal.isHopfIdeal_sSup`), so the derived subgroup is
a closed subgroup scheme. -/
instance : (derivedIdeal I).IsHopfIdeal k :=
  Ideal.isHopfIdeal_sSup fun _ ⟨hJ, _⟩ ↦ hJ

/-- The derived subgroup contains the commutators of `G`: `G ⧸ [G, G]` is commutative.

By `containsCommutators_subgroupSchemeHom` it suffices to check this on `R`-points: a commutator
of `V(I)(R)` lies in `V(J)(R)` for every `J` in the family defining `derivedIdeal I`, so the
equations of all these `J`, hence of their sum, vanish on it. (blueprint: `sk-i-restriction`) -/
instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I)) := by
  refine containsCommutators_subgroupSchemeHom _ fun R _ _ ↦ Subgroup.commutator_le.2
    fun g hg g' hg' ↦ ?_
  let x : zeroLocus I R := ⟨g, hg⟩
  let y : zeroLocus I R := ⟨g', hg'⟩
  change ((x * y * x⁻¹ * y⁻¹ : zeroLocus I R) : GL n R) ∈ zeroLocus (derivedIdeal I) R
  suffices hle : derivedIdeal I ≤ RingHom.ker (evalAlgHom (R := R)
      ((x * y * x⁻¹ * y⁻¹ : zeroLocus I R) : GL n R)) from fun a ha ↦ hle ha
  refine sSup_le ?_
  rintro J ⟨hJ, hIJ, hc⟩
  let e := zeroLocusMulEquiv I R
  obtain ⟨c, hc⟩ := hc.exists_comp_eq_commutator (e x) (e y)
  have hg := coe_mem_zeroLocus_of_comp_eq hIJ (e.symm (c ≫ _)) (e.apply_symm_apply _).symm
  rwa [hc, map_mul, map_mul, map_mul, map_inv, map_inv, e.symm_apply_apply,
    e.symm_apply_apply] at hg

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
  sorry

/-- The reduced centre `Z(G)` of a reduced `G = V(I)` over an algebraically closed field is
central scheme-theoretically: its points commute with all points of `G`.

Proof sketch (not formalised): the condition that a point `z` of `Z(G)` commutes with a point `g`
of `G` is cut out by equations on `Z(G) × G`; they vanish on the rational points, which are dense
in the reduced scheme `Z(G) × G`, hence everywhere. (blueprint: `sk-p-comparison`) -/
theorem central_subgroupSchemeHom_le_center [IsAlgClosed k] (hI : I.IsRadical)
    {X : Over (Spec (.of k))} (a : X ⟶ subgroupScheme (center I)) (b : X ⟶ subgroupScheme I) :
    (a ≫ subgroupSchemeHom (le_center I)) * b = b * (a ≫ subgroupSchemeHom (le_center I)) := by
  sorry

end Geometry

end AlgebraicGeometry.GeneralLinearGroup

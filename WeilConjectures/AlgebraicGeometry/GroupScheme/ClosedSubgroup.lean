/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Closed subgroup schemes of `GL_n`

A matrix algebraic group, a closed subgroup `G ⊆ GL(V)`, is a closed subgroup scheme of the
group scheme `GL_n`: the spectrum of `k[x_ij, det⁻¹] ⧸ I` for a Hopf ideal `I`. Its `R`-points are
the invertible matrices over `R` on which every equation in `I` vanishes; this is a theorem
(`Matrix.GeneralLinearGroup.range_homMulEquiv_comp`), not a definition.

Conversely, an abstract subgroup `Γ` of `GL n k` has a Zariski closure, cut out by the ideal of
all equations vanishing on `Γ`; this ideal is a Hopf ideal. The identity component and the centre
of a closed subgroup are described by ideals of the coordinate ring of `GL_n` in the same way.

## Main definitions

- `Matrix.GeneralLinearGroup.zeroLocus`: the `R`-points of the closed subgroup scheme `V(I)`, as a
  subgroup of `GL n R`.
- `Matrix.GeneralLinearGroup.vanishingIdeal`: the ideal of equations vanishing on a set of
  matrices; for a subgroup, the ideal of its Zariski closure.
- `Matrix.GeneralLinearGroup.subgroupScheme`: the closed subgroup scheme `V(I)` of `GL_n`, a group
  object in schemes over `k`, with its closed immersion `subgroupSchemeι` into `GL_n`.
- `Matrix.GeneralLinearGroup.identityComponent`: the ideal of the reduced identity component `G°`.
- `Matrix.GeneralLinearGroup.center`: the ideal of the reduced centre `Z(G)`.

## Main results

- `Matrix.GeneralLinearGroup.range_homMulEquiv_comp`: the `R`-points of `V(I)` are the matrices
  satisfying the equations in `I`.
- `Matrix.GeneralLinearGroup.vanishingIdeal_zeroLocus_eq_radical`: the Nullstellensatz for `GL_n`
  over an algebraically closed field.

## Blueprint

- `sk-d-geometry`: matrix algebraic groups as reduced closed subgroups of `GL(V)`, their identity
  component and centre.
- `sk-i-restriction`: the Zariski closure of a subgroup of `GL n k` is an algebraic group.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry WithConv

namespace Matrix.GeneralLinearGroup

section CommRing

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
  {R : Type*} [CommRing R] [Algebra k R]

/-- Evaluation at `g` composed with the antipode is evaluation at `g⁻¹`. -/
theorem evalAlgHom_comp_antipodeAlgHom (g : GL n R) :
    (evalAlgHom g).comp (antipodeAlgHom n k) = evalAlgHom g⁻¹ := by
  have hg : map (evalAlgHom (k := k) g).toRingHom (genericUnit n k) = g :=
    (algHomMulEquiv n k R).apply_symm_apply g
  refine algHom_ext fun i j ↦ ?_
  rw [AlgHom.comp_apply, antipodeAlgHom_coord, evalAlgHom_coord]
  conv_rhs => rw [← hg, ← map_inv]
  rfl

/-- The identity matrix satisfies the equations of a Hopf ideal. -/
theorem evalAlgHom_eq_zero_of_mem_one (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {a : CoordinateRing n k} (ha : a ∈ I) : evalAlgHom (1 : GL n R) a = 0 := by
  have h := congr(($(evalAlgHom_one (n := n) (k := k) (R := R))).ofConv a)
  rw [ofConv_toConv] at h
  rw [h, AlgHom.convOne_apply, Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) ha,
    map_zero]

/-- The product of two matrices satisfying the equations of a Hopf ideal satisfies them. -/
theorem evalAlgHom_eq_zero_of_mem_mul (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g h : GL n R} (hg : ∀ a ∈ I, evalAlgHom g a = 0) (hh : ∀ a ∈ I, evalAlgHom h a = 0)
    {a : CoordinateRing n k} (ha : a ∈ I) : evalAlgHom (g * h) a = 0 := by
  have h := congr(($(evalAlgHom_mul (k := k) g h)).ofConv a)
  rw [ofConv_toConv] at h
  rw [h]
  exact Ideal.IsHopfIdeal.convMul_apply_eq_zero hg hh ha

/-- The inverse of a matrix satisfying the equations of a Hopf ideal satisfies them. -/
theorem evalAlgHom_eq_zero_of_mem_inv (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g : GL n R} (hg : ∀ a ∈ I, evalAlgHom g a = 0) {a : CoordinateRing n k} (ha : a ∈ I) :
    evalAlgHom g⁻¹ a = 0 := by
  rw [← evalAlgHom_comp_antipodeAlgHom, AlgHom.comp_apply]
  exact hg _ (Ideal.IsHopfIdeal.antipode_mem (R := k) ha)

variable (R) in
/-- The `R`-points of the closed subgroup scheme `V(I)` of `GL_n` cut out by a Hopf ideal `I`: the
invertible matrices over `R` on which every equation in `I` vanishes.
(blueprint: `sk-d-geometry`) -/
noncomputable def zeroLocus (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Subgroup (GL n R) where
  carrier := {g | ∀ a ∈ I, evalAlgHom g a = 0}
  one_mem' _ ha := evalAlgHom_eq_zero_of_mem_one I ha
  mul_mem' hg hh _ ha := evalAlgHom_eq_zero_of_mem_mul I hg hh ha
  inv_mem' hg _ ha := evalAlgHom_eq_zero_of_mem_inv I hg ha

@[simp]
theorem mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {g : GL n R} :
    g ∈ zeroLocus R I ↔ ∀ a ∈ I, evalAlgHom g a = 0 :=
  Iff.rfl

theorem zeroLocus_anti {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]
    (h : I ≤ J) : zeroLocus R J ≤ zeroLocus R I :=
  fun _ hg a ha ↦ hg a (h ha)

/-- The ideal of equations vanishing on a set `S` of invertible matrices over `k`. For a subgroup
`S`, it cuts out the Zariski closure of `S`. (blueprint: `sk-i-restriction`) -/
noncomputable def vanishingIdeal (S : Set (GL n k)) : Ideal (CoordinateRing n k) :=
  ⨅ g ∈ S, RingHom.ker (evalAlgHom (k := k) g)

theorem mem_vanishingIdeal {S : Set (GL n k)} {a : CoordinateRing n k} :
    a ∈ vanishingIdeal S ↔ ∀ g ∈ S, evalAlgHom g a = 0 := by
  simp [vanishingIdeal, Submodule.mem_iInf]

theorem vanishingIdeal_anti {S T : Set (GL n k)} (h : S ⊆ T) :
    vanishingIdeal T ≤ vanishingIdeal S :=
  fun _ ha ↦ mem_vanishingIdeal.2 fun g hg ↦ mem_vanishingIdeal.1 ha g (h hg)

theorem le_vanishingIdeal_zeroLocus (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    I ≤ vanishingIdeal (zeroLocus k I : Set (GL n k)) :=
  fun _ ha ↦ mem_vanishingIdeal.2 fun _ hg ↦ hg _ ha

/-- The equation `(g * h)_ij - (h * g)_ij = 0` in the entries of `g`, for a fixed matrix `h`. -/
noncomputable def commutatorEquation (h : GL n k) (i j : n) : CoordinateRing n k :=
  ∑ l, (coord n k i l * algebraMap k _ ((h : Matrix n n k) l j) -
    algebraMap k _ ((h : Matrix n n k) i l) * coord n k l j)

@[simp]
theorem evalAlgHom_commutatorEquation (g h : GL n k) (i j : n) :
    evalAlgHom g (commutatorEquation h i j) =
      ((g : Matrix n n k) * h) i j - ((h : Matrix n n k) * g) i j := by
  simp [commutatorEquation, Matrix.mul_apply, Finset.sum_sub_distrib]

end CommRing

section Field

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

theorem isRadical_vanishingIdeal (S : Set (GL n k)) : (vanishingIdeal S).IsRadical := by
  rintro a ⟨m, hm⟩
  refine mem_vanishingIdeal.2 fun g hg ↦ IsNilpotent.eq_zero ⟨m, ?_⟩
  rw [← map_pow]
  exact mem_vanishingIdeal.1 hm g hg

/-- The Zariski closure of a subgroup of `GL n k` is a closed subgroup scheme: the ideal of
equations vanishing on the subgroup is a Hopf ideal. (blueprint: `sk-i-restriction`) -/
instance instIsHopfIdealVanishingIdeal (Γ : Subgroup (GL n k)) :
    (vanishingIdeal (Γ : Set (GL n k))).IsHopfIdeal k where
  counit_eq_zero a ha := mem_vanishingIdeal.1 ha 1 Γ.one_mem
  map_mkQ_comul_eq_zero a ha := sorry
  antipode_mem a ha := mem_vanishingIdeal.2 fun g hg ↦
    (DFunLike.congr_fun (evalAlgHom_comp_antipodeAlgHom g) a).trans
      (mem_vanishingIdeal.1 ha _ (Γ.inv_mem hg))

theorem subset_zeroLocus_vanishingIdeal (Γ : Subgroup (GL n k)) :
    Γ ≤ zeroLocus k (vanishingIdeal (Γ : Set (GL n k))) :=
  fun g hg _ ha ↦ mem_vanishingIdeal.1 ha g hg

/-- The `k`-points of the Zariski closure of a subgroup `Γ` lie in `Γ` as soon as `Γ` is cut out by
some set `J` of equations. -/
theorem zeroLocus_vanishingIdeal_le {Γ : Subgroup (GL n k)} (J : Set (CoordinateRing n k))
    (hΓ : ∀ g ∈ Γ, ∀ a ∈ J, evalAlgHom g a = 0)
    (hJ : ∀ g : GL n k, (∀ a ∈ J, evalAlgHom g a = 0) → g ∈ Γ) :
    zeroLocus k (vanishingIdeal (Γ : Set (GL n k))) ≤ Γ :=
  fun g hg ↦ hJ g fun a ha ↦ hg a (mem_vanishingIdeal.2 fun h hh ↦ hΓ h hh a ha)

/-- Over an algebraically closed field, every maximal ideal of the coordinate ring of `GL_n` is the
ideal of a point. -/
theorem exists_ker_evalAlgHom_eq [IsAlgClosed k] (m : Ideal (CoordinateRing n k)) [m.IsMaximal] :
    ∃ g : GL n k, RingHom.ker (evalAlgHom g) = m := by
  sorry

/-- The Nullstellensatz for `GL_n`: over an algebraically closed field, an element vanishing at
every point where the equations `J` vanish lies in the radical of `J`. -/
theorem vanishingIdeal_setOf_le_radical [IsAlgClosed k] (J : Ideal (CoordinateRing n k)) :
    vanishingIdeal {g : GL n k | ∀ a ∈ J, evalAlgHom g a = 0} ≤ J.radical := by
  sorry

/-- The Nullstellensatz for closed subgroup schemes of `GL_n`: the ideal of the `k`-points of
`V(I)` is the radical of `I`. (blueprint: `sk-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_eq_radical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : vanishingIdeal (zeroLocus k I : Set (GL n k)) = I.radical :=
  le_antisymm (vanishingIdeal_setOf_le_radical I)
    ((isRadical_vanishingIdeal _).radical_le_iff.2 (le_vanishingIdeal_zeroLocus I))

/-- Over an algebraically closed field, a radical Hopf ideal is the ideal of its `k`-points.
(blueprint: `sk-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_le_of_isRadical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] (hI : I.IsRadical) : vanishingIdeal (zeroLocus k I : Set (GL n k)) ≤ I :=
  ((vanishingIdeal_zeroLocus_eq_radical I).trans hI.radical).le

/-- The point of `Spec k[x_ij, det⁻¹]` given by an invertible matrix `g`: the kernel of evaluation
at `g`. -/
noncomputable def toPrimeSpectrum (g : GL n k) : PrimeSpectrum (CoordinateRing n k) :=
  ⟨RingHom.ker (evalAlgHom (k := k) g), RingHom.ker_isPrime _⟩

theorem toPrimeSpectrum_mem_zeroLocus_iff {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
    {g : GL n k} :
    toPrimeSpectrum g ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) ↔
      g ∈ zeroLocus k I :=
  Iff.rfl

theorem toPrimeSpectrum_injective :
    Function.Injective (toPrimeSpectrum : GL n k → PrimeSpectrum (CoordinateRing n k)) := by
  intro g h hgh
  ext i j
  have hmem : coord n k i j - algebraMap k _ ((g : Matrix n n k) i j) ∈
      (toPrimeSpectrum g).asIdeal := by
    simp [toPrimeSpectrum]
  rw [hgh] at hmem
  exact (sub_eq_zero.1 (by simpa [toPrimeSpectrum] using hmem)).symm

/-- The ideal of the reduced identity component `G°` of the closed subscheme `V(I)` of `GL_n`: the
functions vanishing on the connected component of `V(I)` containing the identity matrix.
(blueprint: `sk-d-geometry`) -/
noncomputable def identityComponent (I : Ideal (CoordinateRing n k)) :
    Ideal (CoordinateRing n k) :=
  PrimeSpectrum.vanishingIdeal
    (connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
      (toPrimeSpectrum 1))

theorem le_identityComponent (I : Ideal (CoordinateRing n k)) : I ≤ identityComponent I :=
  (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal _ I).1 (connectedComponentIn_subset _ _)

theorem isRadical_identityComponent (I : Ideal (CoordinateRing n k)) :
    (identityComponent I).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- The identity component of an algebraic group over an algebraically closed field is a closed
subgroup scheme. (blueprint: `sk-p-geometry`) -/
instance [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    (identityComponent I).IsHopfIdeal k :=
  sorry

theorem one_mem_zeroLocus_identityComponent [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : (1 : GL n k) ∈ zeroLocus k (identityComponent I) := by
  intro a ha
  have h1 : toPrimeSpectrum (1 : GL n k) ∈ PrimeSpectrum.zeroLocus (I : Set _) :=
    toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus k I).one_mem
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha _ (mem_connectedComponentIn h1)

/-- The ideal of the reduced centre `Z(G)` of the closed subgroup scheme `G = V(I)` of `GL_n`: the
Zariski closure of the matrices of `G(k)` commuting with all of `G(k)`.
(blueprint: `sk-d-geometry`) -/
noncomputable def center (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Ideal (CoordinateRing n k) :=
  vanishingIdeal ((zeroLocus k I ⊓ Subgroup.centralizer (zeroLocus k I : Set (GL n k)) :
    Subgroup (GL n k)) : Set (GL n k))

instance (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] : (center I).IsHopfIdeal k :=
  instIsHopfIdealVanishingIdeal _

/-- The `k`-points of the centre of `G = V(I)` are the matrices of `G(k)` commuting with all of
`G(k)`. (blueprint: `sk-d-geometry`) -/
theorem mem_zeroLocus_center_iff (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g : GL n k} :
    g ∈ zeroLocus k (center I) ↔ g ∈ zeroLocus k I ∧ ∀ h ∈ zeroLocus k I, g * h = h * g := by
  sorry

end Field

section Scheme

universe u

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]

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
noncomputable def subgroupSchemeι : subgroupScheme I ⟶ scheme n k :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k I).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (subgroupSchemeι I) := sorry

instance : IsClosedImmersion (subgroupSchemeι I).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : Mono (subgroupSchemeι I) :=
  Over.mono_of_mono_left _

theorem subgroupSchemeι_comp_injective {X : Over (Spec (.of k))} :
    Function.Injective fun φ : X ⟶ subgroupScheme I ↦ φ ≫ subgroupSchemeι I :=
  fun _ _ h ↦ (cancel_mono _).1 h

/-- The `R`-points of the closed subgroup scheme `V(I)` are the invertible matrices over `R`
satisfying the equations in `I`: the identification of `G(R)` with a classical matrix group is a
theorem, not a definition. (blueprint: `sk-d-geometry`) -/
theorem range_homMulEquiv_comp (R : Type u) [CommRing R] [Algebra k R] :
    Set.range (fun φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I ↦
      homMulEquiv n k R (φ ≫ subgroupSchemeι I)) = zeroLocus R I := by
  sorry

end Scheme

end Matrix.GeneralLinearGroup

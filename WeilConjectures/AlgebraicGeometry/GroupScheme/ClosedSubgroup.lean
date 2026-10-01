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
- `Matrix.GeneralLinearGroup.IsConnected`: `V(I)` is its own reduced identity component.
- `Matrix.GeneralLinearGroup.center`: the ideal of the reduced centre `Z(G)`.
- `Matrix.GeneralLinearGroup.zeroLocusMulEquiv`: the `R`-points of `V(I)` as a group of
  morphisms `Spec R ⟶ V(I)` are the group `zeroLocus I R`.

## Main results

- `Matrix.GeneralLinearGroup.range_homMulEquiv_comp`: the `R`-points of `V(I)` are the matrices
  satisfying the equations in `I`.
- `Matrix.GeneralLinearGroup.vanishingIdeal_zeroLocus_eq_radical`: the Nullstellensatz for `GL_n`
  over an algebraically closed field.

## Blueprint

- `sk-d-geometry`: matrix algebraic groups as reduced closed subgroups of `GL(V)`, their identity
  component and centre.
- `sk-i-restriction`: the Zariski closure of a subgroup of `GL n k` is an algebraic group.
- `sk-p-geometry`: the identity component is a closed subgroup scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry WithConv
open scoped MonObj

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

/-- The `R`-points of the closed subgroup scheme `V(I)` of `GL_n` cut out by a Hopf ideal `I`: the
invertible matrices over `R` on which every equation in `I` vanishes.
(blueprint: `sk-d-geometry`) -/
noncomputable def zeroLocus (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] (R : Type*)
    [CommRing R] [Algebra k R] : Subgroup (GL n R) where
  carrier := {g | ∀ a ∈ I, evalAlgHom g a = 0}
  one_mem' _ ha := evalAlgHom_eq_zero_of_mem_one I ha
  mul_mem' hg hh _ ha := evalAlgHom_eq_zero_of_mem_mul I hg hh ha
  inv_mem' hg _ ha := evalAlgHom_eq_zero_of_mem_inv I hg ha

@[simp]
theorem mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {g : GL n R} :
    g ∈ zeroLocus I R ↔ ∀ a ∈ I, evalAlgHom g a = 0 :=
  Iff.rfl

theorem zeroLocus_anti {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]
    (h : I ≤ J) : zeroLocus J R ≤ zeroLocus I R :=
  fun _ hg a ha ↦ hg a (h ha)

variable {S : Type*} [CommRing S] [Algebra k S]

/-- An algebra homomorphism `R → S` maps the `R`-points of `V(I)` to its `S`-points. -/
theorem map_mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] (φ : R →ₐ[k] S)
    {g : GL n R} (hg : g ∈ zeroLocus I R) : map φ.toRingHom g ∈ zeroLocus I S := by
  intro a ha
  rw [evalAlgHom_map, AlgHom.comp_apply, hg a ha, map_zero]

/-- Along an injective algebra homomorphism `R → S`, a matrix over `R` is an `R`-point of `V(I)` if
and only if its image is an `S`-point. -/
theorem map_mem_zeroLocus_iff {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {φ : R →ₐ[k] S}
    (hφ : Function.Injective φ) {g : GL n R} :
    map φ.toRingHom g ∈ zeroLocus I S ↔ g ∈ zeroLocus I R := by
  refine ⟨fun hg a ha ↦ hφ ?_, map_mem_zeroLocus φ⟩
  rw [map_zero, ← AlgHom.comp_apply, ← evalAlgHom_map]
  exact hg a ha

/-- The group homomorphism `V(I)(R) →* V(I)(S)` induced by an algebra homomorphism `R → S`. -/
noncomputable def zeroLocus.map (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    (φ : R →ₐ[k] S) : zeroLocus I R →* zeroLocus I S :=
  ((GeneralLinearGroup.map φ.toRingHom).comp (zeroLocus I R).subtype).codRestrict _
    fun g ↦ map_mem_zeroLocus φ g.2

@[simp]
theorem zeroLocus.coe_map_apply {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] (φ : R →ₐ[k] S)
    (g : zeroLocus I R) : (zeroLocus.map I φ g : GL n S) = GeneralLinearGroup.map φ.toRingHom g :=
  rfl

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
    I ≤ vanishingIdeal (zeroLocus I k : Set (GL n k)) :=
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
    Γ ≤ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k :=
  fun g hg _ ha ↦ mem_vanishingIdeal.1 ha g hg

/-- The `k`-points of the Zariski closure of a subgroup `Γ` lie in `Γ` as soon as `Γ` is cut out by
some set `J` of equations. -/
theorem zeroLocus_vanishingIdeal_le {Γ : Subgroup (GL n k)} (J : Set (CoordinateRing n k))
    (hΓ : ∀ g ∈ Γ, ∀ a ∈ J, evalAlgHom g a = 0)
    (hJ : ∀ g : GL n k, (∀ a ∈ J, evalAlgHom g a = 0) → g ∈ Γ) :
    zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k ≤ Γ :=
  fun g hg ↦ hJ g fun a ha ↦ hg a (mem_vanishingIdeal.2 fun h hh ↦ hΓ h hh a ha)

/-- Over an algebraically closed field, every maximal ideal of the coordinate ring of `GL_n` is the
ideal of a point. -/
theorem exists_ker_evalAlgHom_eq [IsAlgClosed k] (m : Ideal (CoordinateRing n k)) [m.IsMaximal] :
    ∃ g : GL n k, RingHom.ker (evalAlgHom g) = m := by
  let : Field (CoordinateRing n k ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (CoordinateRing n k ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let φ : CoordinateRing n k →ₐ[k] k :=
    (IsAlgClosed.lift : (CoordinateRing n k ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)
  refine ⟨algHomMulEquiv n k k (toConv φ), ?_⟩
  have hφ : evalAlgHom (algHomMulEquiv n k k (toConv φ)) = φ :=
    congrArg ofConv ((algHomMulEquiv n k k).symm_apply_apply (toConv φ))
  rw [hφ]
  ext a
  simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The Nullstellensatz for `GL_n`: over an algebraically closed field, an element vanishing at
every point where the equations `J` vanish lies in the radical of `J`. -/
theorem vanishingIdeal_setOf_le_radical [IsAlgClosed k] (J : Ideal (CoordinateRing n k)) :
    vanishingIdeal {g : GL n k | ∀ a ∈ J, evalAlgHom g a = 0} ≤ J.radical := by
  have : IsJacobsonRing (CoordinateRing n k) := isJacobsonRing_of_finiteType (A := k)
  intro a ha
  rw [J.radical_eq_jacobson, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hJm, hm⟩
  obtain ⟨g, rfl⟩ := exists_ker_evalAlgHom_eq m
  exact mem_vanishingIdeal.1 ha g fun b hb ↦ hJm hb

/-- The Nullstellensatz for closed subgroup schemes of `GL_n`: the ideal of the `k`-points of
`V(I)` is the radical of `I`. (blueprint: `sk-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_eq_radical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : vanishingIdeal (zeroLocus I k : Set (GL n k)) = I.radical :=
  le_antisymm (vanishingIdeal_setOf_le_radical I)
    ((isRadical_vanishingIdeal _).radical_le_iff.2 (le_vanishingIdeal_zeroLocus I))

/-- Over an algebraically closed field, a radical Hopf ideal is the ideal of its `k`-points.
(blueprint: `sk-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_le_of_isRadical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] (hI : I.IsRadical) : vanishingIdeal (zeroLocus I k : Set (GL n k)) ≤ I :=
  ((vanishingIdeal_zeroLocus_eq_radical I).trans hI.radical).le

/-- The point of `Spec k[x_ij, det⁻¹]` given by an invertible matrix `g`: the kernel of evaluation
at `g`. -/
noncomputable def toPrimeSpectrum (g : GL n k) : PrimeSpectrum (CoordinateRing n k) :=
  ⟨RingHom.ker (evalAlgHom (k := k) g), RingHom.ker_isPrime _⟩

theorem toPrimeSpectrum_mem_zeroLocus_iff {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
    {g : GL n k} :
    toPrimeSpectrum g ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) ↔
      g ∈ zeroLocus I k :=
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

/-- The closed subgroup `V(I)` of `GL_n` is connected (and reduced): `I` is the ideal of its own
reduced identity component. -/
def IsConnected (I : Ideal (CoordinateRing n k)) : Prop :=
  identityComponent I = I

theorem IsConnected.isRadical {I : Ideal (CoordinateRing n k)} (h : IsConnected I) :
    I.IsRadical :=
  h ▸ isRadical_identityComponent I

/-- The identity component of an algebraic group over an algebraically closed field is a closed
subgroup scheme. (blueprint: `sk-p-geometry`) -/
instance [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    (identityComponent I).IsHopfIdeal k :=
  sorry

theorem one_mem_zeroLocus_identityComponent [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : (1 : GL n k) ∈ zeroLocus (identityComponent I) k := by
  intro a ha
  have h1 : toPrimeSpectrum (1 : GL n k) ∈ PrimeSpectrum.zeroLocus (I : Set _) :=
    toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus I k).one_mem
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha _ (mem_connectedComponentIn h1)

/-- The ideal of the reduced centre `Z(G)` of the closed subgroup scheme `G = V(I)` of `GL_n`: the
Zariski closure of the matrices of `G(k)` commuting with all of `G(k)`.
(blueprint: `sk-d-geometry`) -/
noncomputable def center (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Ideal (CoordinateRing n k) :=
  vanishingIdeal ((zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
    Subgroup (GL n k)) : Set (GL n k))

instance (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] : (center I).IsHopfIdeal k :=
  instIsHopfIdealVanishingIdeal _

/-- The `k`-points of the centre of `G = V(I)` are the matrices of `G(k)` commuting with all of
`G(k)`. (blueprint: `sk-d-geometry`) -/
theorem mem_zeroLocus_center_iff (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g : GL n k} :
    g ∈ zeroLocus (center I) k ↔ g ∈ zeroLocus I k ∧ ∀ h ∈ zeroLocus I k, g * h = h * g := by
  let J : Set (CoordinateRing n k) :=
    I ∪ {c | ∃ h ∈ zeroLocus I k, ∃ i j, c = commutatorEquation h i j}
  have hΓ : ∀ g ∈ (zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
      Subgroup (GL n k)), ∀ a ∈ J, evalAlgHom g a = 0 := by
    rintro g ⟨hg, hc⟩ a (ha | ⟨h, hh, i, j, rfl⟩)
    · exact hg a ha
    · rw [evalAlgHom_commutatorEquation, ← Units.val_mul, ← Units.val_mul,
        Subgroup.mem_centralizer_iff.1 hc h hh, sub_self]
  have hJ : ∀ g : GL n k, (∀ a ∈ J, evalAlgHom g a = 0) →
      g ∈ (zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
        Subgroup (GL n k)) := by
    refine fun g hg ↦ ⟨fun a ha ↦ hg a (Or.inl ha),
      Subgroup.mem_centralizer_iff.2 fun h hh ↦ ?_⟩
    ext i j
    have := hg _ (Or.inr ⟨h, hh, i, j, rfl⟩)
    rw [evalAlgHom_commutatorEquation, sub_eq_zero] at this
    simpa using this.symm
  constructor
  · intro hg
    obtain ⟨hg, hc⟩ := zeroLocus_vanishingIdeal_le J hΓ hJ hg
    exact ⟨hg, fun h hh ↦ (Subgroup.mem_centralizer_iff.1 hc h hh).symm⟩
  · rintro ⟨hg, hc⟩
    exact subset_zeroLocus_vanishingIdeal _
      ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh ↦ (hc h hh).symm⟩

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
      homMulEquiv n k R (φ ≫ subgroupSchemeι I)) = zeroLocus I R := by
  have key (χ : CoordinateRing n k ⧸ I →ₐ[k] R) :
      homMulEquiv n k R (Spec.mapMulEquiv (toConv χ) ≫ subgroupSchemeι I) =
        algHomMulEquiv n k R (toConv (χ.comp (Ideal.Quotient.mkₐ k I))) := by
    rw [mapMulEquiv_comp_subgroupSchemeι, homMulEquiv, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, ofConv_toConv]
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
      homMulEquiv n k R (φ ≫ subgroupSchemeι I) :=
  (homMulEquiv n k R).injective.comp (subgroupSchemeι_comp_injective I)

/-- The `R`-points of the closed subgroup scheme `V(I)` are the group `zeroLocus I R` of matrices
satisfying the equations in `I`: a point `φ : Spec R ⟶ V(I)` corresponds to the matrix of the
point `φ ≫ ι` of `GL_n`, where `ι : V(I) ⟶ GL_n` is the closed immersion.
(blueprint: `sk-d-geometry`) -/
noncomputable def zeroLocusMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    zeroLocus I R ≃* ((Spec (.of R)).asOver (Spec (.of k)) ⟶ subgroupScheme I) :=
  (MulEquiv.subgroupCongr (SetLike.coe_injective (range_homMulEquiv_comp I R)).symm).trans
    (MonoidHom.ofInjective (f := (homMulEquiv n k R).toMonoidHom.comp
      (IsMonHom.monoidHom (subgroupSchemeι I) _)) (injective_homMulEquiv_comp I R)).symm

variable {I}

@[simp]
theorem homMulEquiv_zeroLocusMulEquiv_comp {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus I R) : homMulEquiv n k R (zeroLocusMulEquiv I R g ≫ subgroupSchemeι I) = g :=
  congrArg Subtype.val ((MonoidHom.ofInjective (f := (homMulEquiv n k R).toMonoidHom.comp
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
    homMulEquiv_specMap_comp]

end Scheme

end Matrix.GeneralLinearGroup

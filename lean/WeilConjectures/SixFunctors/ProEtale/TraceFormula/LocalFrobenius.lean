/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints

/-!
# Local Frobenius operators along a Frobenius orbit

Let `W` be a Weil complex on `a_X : X ⟶ s` with Frobenius `Φ = Φ₁`, iterates `Φ_m` and
coefficient iterates `φ_m : LΦ_m^* K ⟶ K`. For sections `x, y : s ⟶ X` with `x ≫ Φ_n = y`, the
coefficient iterate `φ_n` induces a *transport* `Ly^* K ⟶ Lx^* K`
(`AlgebraicGeometry.ProEtale.WeilComplex.stalkTransport`). Transports compose along the cocycle
of the `φ_m`, and the stalk Frobenius `F_{x,m}` is the transport from `x` to itself. Hence the
transport along `x ≫ Φ_i = y` conjugates `F_{x,d}` into `F_{y,d}` when `x` and `y` are fixed by
`Φ_d`; for a Weil datum (`IsIso W.coeff`) the transports are isomorphisms and `F_{x,d}`, `F_{y,d}`
have the same trace.

For the model Frobenius over a finite field `k` (`WeilComplex.IsModelFrobenius`), the sections
fixed by `Φ_m` lying over a closed point `y` of `X₀` of degree `d ∣ m` form a single orbit
`x₀, x₀ ≫ Φ, …, x₀ ≫ Φ_{d - 1}` of `d` distinct sections. Together with
`WeilComplex.stalkFrobenius_mul_eq_pow` this gives the degree formula
`tr(F_{x,m}) = tr(F_{x₀,d} ^ (m / d))`.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.stalkTransport`: the transport `Ly^* K ⟶ Lx^* K` of
  `φ_n` along `x ≫ Φ_n = y`.
- `AlgebraicGeometry.ProEtale.WeilComplex.frobeniusTransport`: the transport
  `L(x ≫ Φ)^* K ≃ Lx^* LΦ^* K ⟶ Lx^* K` of `φ`.

## Main statements

- `AlgebraicGeometry.ProEtale.WeilComplex.frobeniusTransport_comp_stalkFrobenius`,
  `AlgebraicGeometry.ProEtale.WeilComplex.trace_stalkFrobenius_comp_frobenius`: conjugacy of the
  local Frobenius operators at `x` and `x ≫ Φ`; their iterated versions
  `stalkTransport_comp_stalkFrobenius` and `trace_stalkFrobenius_eq_of_comp_frobeniusIterate`.
- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.bijective_comp_frobeniusIterate`: the
  fixed sections over a closed point of degree `d` are the `d` distinct sections `x₀ ≫ Φ_i`,
  `i < d`.
- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.trace_stalkFrobenius_eq_trace_pow`:
  the degree formula `tr(F_{x,m}) = tr(F_{x₀,d} ^ (m / d))`.

## Blueprint

`lem-trf-local-frobenius-conjugacy` and `lem-trf-frobenius-degree-formula`. The blueprint
formulates them with the Galois Frobenius `g_γ`; here they are stated with the scheme Frobenius
`Φ`, which defines the Lean stalk operator `WeilComplex.stalkFrobenius`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The composition step for transports along endomorphisms: for morphisms `x, y, z : V ⟶ X` with
`x ≫ M = y`, `y ≫ N = z`, an endomorphism `P = M ≫ N` with `x ≫ P = z`, and maps
`ψ_M : LM^* K ⟶ K`, `ψ_N : LN^* K ⟶ K`, the composite of the transports `Lz^* K ⟶ Ly^* K` and
`Ly^* K ⟶ Lx^* K` induced by `ψ_N` and `ψ_M` is the transport `Lz^* K ⟶ Lx^* K` induced by
`ψ_M ∘ LM^* ψ_N`. -/
lemma leftDerivedUpperStarComp_transport_aux {V X : Scheme.{u}} {x y z : V ⟶ X}
    {M N P : X ⟶ X} (eP : P = M ≫ N) (h₁ : x ≫ M = y) (h₂ : y ≫ N = z) (h : x ≫ P = z)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (ψM : ((upperStar A M).leftDerivedFunctor).obj K ⟶ K)
    (ψN : ((upperStar A N).leftDerivedFunctor).obj K ⟶ K) :
    ((leftDerivedUpperStarCongr A h₂).inv.app K ≫ (leftDerivedUpperStarComp A y N).hom.app K ≫
        ((upperStar A y).leftDerivedFunctor).map ψN) ≫
      ((leftDerivedUpperStarCongr A h₁).inv.app K ≫ (leftDerivedUpperStarComp A x M).hom.app K ≫
        ((upperStar A x).leftDerivedFunctor).map ψM) =
    (leftDerivedUpperStarCongr A h).inv.app K ≫ (leftDerivedUpperStarComp A x P).hom.app K ≫
      ((upperStar A x).leftDerivedFunctor).map ((leftDerivedUpperStarCongr A eP).hom.app K ≫
        (leftDerivedUpperStarComp A M N).hom.app K ≫
        ((upperStar A M).leftDerivedFunctor).map ψN ≫ ψM) := by
  subst eP
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.map_comp, Category.assoc, leftDerivedUpperStarCongr_inv_app]
  rw [leftDerivedUpperStarCongr_hom_naturality_assoc h₁.symm,
    leftDerivedUpperStarComp_hom_app_congr_left_assoc,
    leftDerivedUpperStarCongr_hom_app_trans_assoc, leftDerivedUpperStarComp_hom_naturality_assoc,
    leftDerivedUpperStarComp_assoc_app_assoc, leftDerivedUpperStarCongr_hom_app_trans_assoc]

namespace WeilComplex

section Transport

variable {s X : Scheme.{u}} {aX : X ⟶ s} (W : WeilComplex (A := A) aX)

/-- The iterates of the Frobenius commute: `Φ_m ≫ Φ_n = Φ_n ≫ Φ_m`. -/
lemma frobeniusIterate_comm (m n : ℕ) :
    W.frobeniusIterate m ≫ W.frobeniusIterate n = W.frobeniusIterate n ≫ W.frobeniusIterate m := by
  rw [← frobeniusIterate_add, ← frobeniusIterate_add, Nat.add_comm]

/-- If `x` is fixed by `Φ_d`, so is every `x ≫ Φ_i`. -/
lemma comp_frobeniusIterate_comp_frobeniusIterate {x : s ⟶ X} {d : ℕ}
    (hx : x ≫ W.frobeniusIterate d = x) (i : ℕ) :
    (x ≫ W.frobeniusIterate i) ≫ W.frobeniusIterate d = x ≫ W.frobeniusIterate i := by
  rw [Category.assoc, frobeniusIterate_comm, ← Category.assoc, hx]

/-- If `x` is fixed by `Φ_d`, so is `x ≫ Φ`. -/
lemma comp_frobenius_comp_frobeniusIterate {x : s ⟶ X} {d : ℕ}
    (hx : x ≫ W.frobeniusIterate d = x) :
    (x ≫ W.frobenius) ≫ W.frobeniusIterate d = x ≫ W.frobenius := by
  rw [← frobeniusIterate_one]
  exact W.comp_frobeniusIterate_comp_frobeniusIterate hx 1

/-- A section of `a_X` fixed by `Φ_m` is carried by every `Φ_i` to a section of `a_X` fixed by
`Φ_m`. -/
lemma comp_frobeniusIterate_fixed {x : s ⟶ X} {m : ℕ}
    (hx : x ≫ aX = 𝟙 s ∧ x ≫ W.frobeniusIterate m = x) (i : ℕ) :
    (x ≫ W.frobeniusIterate i) ≫ aX = 𝟙 s ∧
      (x ≫ W.frobeniusIterate i) ≫ W.frobeniusIterate m = x ≫ W.frobeniusIterate i :=
  ⟨by rw [Category.assoc, frobeniusIterate_comp, hx.1],
    W.comp_frobeniusIterate_comp_frobeniusIterate hx.2 i⟩

/-- The *transport* `Ly^* K ⟶ Lx^* K` of the coefficient iterate `φ_n` along `x ≫ Φ_n = y`: the
composite

```
  Ly^* K ──(leftDerivedUpperStarCongr h).inv──▶ L(x ≫ Φ_n)^* K
    ──leftDerivedUpperStarComp x Φ_n──▶ Lx^* LΦ_n^* K ──Lx^*.map φ_n──▶ Lx^* K
```

For `y = x` this is the stalk Frobenius `F_{x,n}` (`WeilComplex.stalkTransport_self`). Part of
blueprint `lem-trf-local-frobenius-conjugacy` (2), which formulates the transport with the Galois
Frobenius `g_γ`; here it is defined with the scheme Frobenius `Φ` that defines the Lean stalk
operator `WeilComplex.stalkFrobenius`. -/
noncomputable def stalkTransport (n : ℕ) (x y : s ⟶ X) (h : x ≫ W.frobeniusIterate n = y) :
    ((upperStar A y).leftDerivedFunctor).obj W.obj ⟶
      ((upperStar A x).leftDerivedFunctor).obj W.obj :=
  (leftDerivedUpperStarCongr A h).inv.app W.obj ≫
    (leftDerivedUpperStarComp A x (W.frobeniusIterate n)).hom.app W.obj ≫
    ((upperStar A x).leftDerivedFunctor).map (W.coeffIterate n)

/-- The transport from a fixed point to itself is the stalk Frobenius. -/
lemma stalkTransport_self (m : ℕ) (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) :
    W.stalkTransport m x x hx = W.stalkFrobenius m x hx :=
  rfl

/-- The transport only depends on the number of Frobenius steps, not on how it is written. -/
lemma stalkTransport_congr {n n' : ℕ} (e : n = n') (x y : s ⟶ X)
    (h : x ≫ W.frobeniusIterate n = y) (h' : x ≫ W.frobeniusIterate n' = y) :
    W.stalkTransport n x y h = W.stalkTransport n' x y h' := by
  subst e
  rfl

/-- Transports compose: the transport along `y ≫ Φ_n = z` followed by the transport along
`x ≫ Φ_m = y` is the transport along `x ≫ Φ_{n + m} = z`. This is the cocycle identity
`WeilComplex.coeffIterate_add` read on stalks (part of blueprint
`lem-trf-local-frobenius-conjugacy`, which uses the Galois Frobenius `g_γ` instead of the scheme
Frobenius `Φ`). -/
lemma stalkTransport_comp (m n : ℕ) {x y z : s ⟶ X} (h₁ : x ≫ W.frobeniusIterate m = y)
    (h₂ : y ≫ W.frobeniusIterate n = z) :
    W.stalkTransport n y z h₂ ≫ W.stalkTransport m x y h₁ =
      W.stalkTransport (n + m) x z (by rw [frobeniusIterate_add, ← Category.assoc, h₁, h₂]) := by
  unfold stalkTransport
  rw [coeffIterate_add W n m]
  exact leftDerivedUpperStarComp_transport_aux _ _ _ _ _ _

/-- For a Weil datum the transports are isomorphisms. -/
instance isIso_stalkTransport [IsIso W.coeff] (n : ℕ) (x y : s ⟶ X)
    (h : x ≫ W.frobeniusIterate n = y) : IsIso (W.stalkTransport n x y h) := by
  unfold stalkTransport
  infer_instance

/-- Blueprint `lem-trf-local-frobenius-conjugacy` (3), iterated version: for sections `x`, `y`
fixed by `Φ_d` with `x ≫ Φ_i = y`, the transport `Ly^* K ⟶ Lx^* K` intertwines the local
Frobenius operators, `T ∘ F_{y,d} = F_{x,d} ∘ T`. The blueprint formulates this with the Galois
Frobenius `g_γ`; here it is stated with the scheme Frobenius `Φ` that defines the Lean stalk
operator `WeilComplex.stalkFrobenius`. -/
theorem stalkTransport_comp_stalkFrobenius {d i : ℕ} {x y : s ⟶ X}
    (h : x ≫ W.frobeniusIterate i = y) (hx : x ≫ W.frobeniusIterate d = x)
    (hy : y ≫ W.frobeniusIterate d = y) :
    W.stalkTransport i x y h ≫ W.stalkFrobenius d x hx =
      W.stalkFrobenius d y hy ≫ W.stalkTransport i x y h := by
  rw [← W.stalkTransport_self d x hx, ← W.stalkTransport_self d y hy, stalkTransport_comp,
    stalkTransport_comp]
  exact W.stalkTransport_congr (Nat.add_comm i d) _ _ _ _

/-- The intertwining `T ∘ F_{y,d} = F_{x,d} ∘ T` of `stalkTransport_comp_stalkFrobenius` passes to
the powers: `T ∘ F_{y,d}^n = F_{x,d}^n ∘ T`. Part of blueprint
`lem-trf-local-frobenius-conjugacy`, which formulates it with the Galois Frobenius `g_γ` instead
of the scheme Frobenius `Φ`. -/
theorem stalkTransport_comp_stalkFrobenius_pow {d i : ℕ} {x y : s ⟶ X}
    (h : x ≫ W.frobeniusIterate i = y) (hx : x ≫ W.frobeniusIterate d = x)
    (hy : y ≫ W.frobeniusIterate d = y) (n : ℕ) :
    let F : End (((upperStar A x).leftDerivedFunctor).obj W.obj) := W.stalkFrobenius d x hx
    let F' : End (((upperStar A y).leftDerivedFunctor).obj W.obj) := W.stalkFrobenius d y hy
    W.stalkTransport i x y h ≫ End.asHom (F ^ n) =
      End.asHom (F' ^ n) ≫ W.stalkTransport i x y h := by
  intro F F'
  induction n with
  | zero =>
    simp only [pow_zero, End.one_def, End.asHom]
    rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
    simp only [End.asHom] at ih ⊢
    rw [pow_succ', pow_succ', End.mul_def, End.mul_def, ← Category.assoc, ih, Category.assoc,
      W.stalkTransport_comp_stalkFrobenius h hx hy, Category.assoc]

/-- Blueprint `lem-trf-local-frobenius-conjugacy` (3), trace version, iterated: for a Weil datum
and sections `x`, `y` fixed by `Φ_d` with `x ≫ Φ_i = y`, the local Frobenius operators `F_{x,d}`
and `F_{y,d}` have the same trace. The blueprint formulates this with the Galois Frobenius `g_γ`;
here it is stated with the scheme Frobenius `Φ` that defines the Lean stalk operator
`WeilComplex.stalkFrobenius`. -/
theorem trace_stalkFrobenius_eq_of_comp_frobeniusIterate [DerivedBraiding A] [IsIso W.coeff]
    {d i : ℕ}
    {x y : s ⟶ X} (h : x ≫ W.frobeniusIterate i = y) (hx : x ≫ W.frobeniusIterate d = x)
    (hy : y ≫ W.frobeniusIterate d = y)
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    [HasRightDual (((upperStar A y).leftDerivedFunctor).obj W.obj)] :
    trace (W.stalkFrobenius d y hy) = trace (W.stalkFrobenius d x hx) :=
  trace_eq_of_iso (asIso (W.stalkTransport i x y h)) _ _
    (W.stalkTransport_comp_stalkFrobenius h hx hy).symm

/-- The *Frobenius transport* `T : L(x ≫ Φ)^* K ⟶ Lx^* K` of the Frobenius coefficient morphism
`φ`, the composite

```
  L(x ≫ Φ)^* K ──leftDerivedUpperStarComp x Φ──▶ Lx^* LΦ^* K ──Lx^*.map φ──▶ Lx^* K
```

Blueprint `lem-trf-local-frobenius-conjugacy` (2), which formulates it with the Galois Frobenius
`g_γ`; here it is defined with the scheme Frobenius `Φ` that defines the Lean stalk operator
`WeilComplex.stalkFrobenius`. -/
noncomputable def frobeniusTransport (x : s ⟶ X) :
    ((upperStar A (x ≫ W.frobenius)).leftDerivedFunctor).obj W.obj ⟶
      ((upperStar A x).leftDerivedFunctor).obj W.obj :=
  (leftDerivedUpperStarComp A x W.frobenius).hom.app W.obj ≫
    ((upperStar A x).leftDerivedFunctor).map W.coeff

/-- The Frobenius transport is the transport `WeilComplex.stalkTransport` of `φ_1` along
`x ≫ Φ_1 = x ≫ Φ`. -/
lemma frobeniusTransport_eq (x : s ⟶ X) :
    W.frobeniusTransport x =
      W.stalkTransport 1 x (x ≫ W.frobenius) (by rw [frobeniusIterate_one]) := by
  rw [frobeniusTransport, stalkTransport, coeffIterate_one, Functor.map_comp,
    leftDerivedUpperStarComp_hom_app_congr_right_assoc, leftDerivedUpperStarCongr_inv_app,
    leftDerivedUpperStarCongr_hom_app_trans_assoc, leftDerivedUpperStarCongr_hom_app_self,
    Category.id_comp]

/-- For a Weil datum the Frobenius transport is an isomorphism. -/
instance isIso_frobeniusTransport [IsIso W.coeff] (x : s ⟶ X) :
    IsIso (W.frobeniusTransport x) := by
  rw [frobeniusTransport_eq]
  infer_instance

/-- Blueprint `lem-trf-local-frobenius-conjugacy` (3): for a section `x` fixed by `Φ_d` and
`x' = x ≫ Φ`, the Frobenius transport `T : Lx'^* K ⟶ Lx^* K` intertwines the local Frobenius
operators, `T ∘ F_{x',d} = F_{x,d} ∘ T`. The blueprint formulates this with the Galois Frobenius
`g_γ`; here it is stated with the scheme Frobenius `Φ` that defines the Lean stalk operator
`WeilComplex.stalkFrobenius`. -/
theorem frobeniusTransport_comp_stalkFrobenius {d : ℕ} {x : s ⟶ X}
    (hx : x ≫ W.frobeniusIterate d = x)
    (hx' : (x ≫ W.frobenius) ≫ W.frobeniusIterate d = x ≫ W.frobenius) :
    W.frobeniusTransport x ≫ W.stalkFrobenius d x hx =
      W.stalkFrobenius d (x ≫ W.frobenius) hx' ≫ W.frobeniusTransport x := by
  rw [frobeniusTransport_eq]
  exact W.stalkTransport_comp_stalkFrobenius _ hx hx'

/-- Blueprint `lem-trf-local-frobenius-conjugacy` (3), trace version: for a Weil datum, a section
`x` fixed by `Φ_d` and `x' = x ≫ Φ`, `tr(F_{x',d}) = tr(F_{x,d})`. The blueprint formulates this
with the Galois Frobenius `g_γ`; here it is stated with the scheme Frobenius `Φ` that defines the
Lean stalk operator `WeilComplex.stalkFrobenius`. -/
theorem trace_stalkFrobenius_comp_frobenius [DerivedBraiding A] [IsIso W.coeff] {d : ℕ}
    {x : s ⟶ X}
    (hx : x ≫ W.frobeniusIterate d = x)
    (hx' : (x ≫ W.frobenius) ≫ W.frobeniusIterate d = x ≫ W.frobenius)
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    [HasRightDual (((upperStar A (x ≫ W.frobenius)).leftDerivedFunctor).obj W.obj)] :
    trace (W.stalkFrobenius d (x ≫ W.frobenius) hx') = trace (W.stalkFrobenius d x hx) :=
  trace_eq_of_iso (asIso (W.frobeniusTransport x)) _ _
    (W.frobeniusTransport_comp_stalkFrobenius hx hx').symm

end Transport

section Orbit

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] {aX : X ⟶ Spec (.of Ω)}
  {W : WeilComplex (A := A) aX} {k : Type u} [Field k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k)} {σ : Spec (.of Ω) ⟶ Spec (.of k)} {p : X ⟶ X₀}

/-- Two Frobenius translates `x₀ ≫ Φ_i`, `x₀ ≫ Φ_j` of a section `x₀` of `a_X` agree if and only
if the `i`-th and `j`-th powers of the `#k`-power Frobenius of the residue field `κ(y)` of the
image `y` of `x₀` in `X₀` agree. -/
private lemma IsModelFrobenius.comp_frobeniusIterate_eq_iff [Fintype k] [Algebra k Ω]
    (hΦ : W.IsModelFrobenius f₀ σ p) (x₀ : Spec (.of Ω) ⟶ X) (i j : ℕ) :
    letI := (f₀.residueFieldAlgebraMap ((x₀ ≫ p).base default)).toAlgebra
    x₀ ≫ W.frobeniusIterate i = x₀ ≫ W.frobeniusIterate j ↔
      FiniteField.frobeniusAlgHom k (X₀.residueField ((x₀ ≫ p).base default)) ^ i =
        FiniteField.frobeniusAlgHom k (X₀.residueField ((x₀ ≫ p).base default)) ^ j := by
  let := (f₀.residueFieldAlgebraMap ((x₀ ≫ p).base default)).toAlgebra
  obtain ⟨φ, hφ⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField (x₀ ≫ p)
    (y := (x₀ ≫ p).base default) ⟨default, rfl⟩
  have key (n : ℕ) : x₀ ≫ W.frobeniusIterate n ≫ p = Spec.map (φ ≫ CommRingCat.ofHom
      ((FiniteField.frobeniusAlgHom k Ω ^ n : Ω →ₐ[k] Ω) : Ω →+* Ω)) ≫
      X₀.fromSpecResidueField _ := by
    rw [hΦ.comp_frobeniusIterate_comp, Spec.map_comp, Category.assoc, ← hφ]
  have hext : x₀ ≫ W.frobeniusIterate i = x₀ ≫ W.frobeniusIterate j ↔
      x₀ ≫ W.frobeniusIterate i ≫ p = x₀ ≫ W.frobeniusIterate j ≫ p := by
    refine ⟨fun h ↦ by rw [reassoc_of% h], fun h ↦ hΦ.isPullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, h]
    · rw [Category.assoc, Category.assoc, frobeniusIterate_comp, frobeniusIterate_comp]
  rw [hext, key, key, (Scheme.specMap_comp_fromSpecResidueField_injective _).eq_iff]
  refine ⟨fun h ↦ AlgHom.ext fun a ↦ φ.hom.injective ?_,
    fun h ↦ CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)⟩
  · have := congrArg (fun χ ↦ χ.hom a) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      AlgHom.coe_toRingHom, FiniteField.coe_frobeniusAlgHom_pow] at this
    rw [FiniteField.coe_frobeniusAlgHom_pow, FiniteField.coe_frobeniusAlgHom_pow, map_pow,
      map_pow]
    exact this
  · have := congrArg (fun χ ↦ φ.hom (χ a)) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      AlgHom.coe_toRingHom, FiniteField.coe_frobeniusAlgHom_pow]
    rw [FiniteField.coe_frobeniusAlgHom_pow, FiniteField.coe_frobeniusAlgHom_pow, map_pow,
      map_pow] at this
    exact this

variable [Finite k]

/-- The image in `X₀` of a Frobenius translate `x₀ ≫ Φ_i` of a section `x₀` of `a_X` is the image
of `x₀`. -/
lemma IsModelFrobenius.base_comp_frobeniusIterate (hΦ : W.IsModelFrobenius f₀ σ p)
    (x₀ : Spec (.of Ω) ⟶ X) (i : ℕ) :
    ((x₀ ≫ W.frobeniusIterate i) ≫ p).base default = (x₀ ≫ p).base default := by
  let := Fintype.ofFinite k
  let : Algebra k Ω := (Spec.preimage σ).hom.toAlgebra
  rw [Category.assoc, hΦ.comp_frobeniusIterate_comp, Scheme.Hom.comp_apply]
  exact congrArg _ (Subsingleton.elim _ _)

variable [IsAlgClosed Ω]

/-- A section `x₀` of `a_X` fixed by `Φ_m`, `m ≥ 1`, is fixed by `Φ_d` for the degree `d` of the
closed point of `X₀` under it. Part of blueprint `lem-trf-local-frobenius-conjugacy` (1), which
formulates it with the Galois Frobenius `g_γ`; here it is stated with the scheme Frobenius `Φ`
that defines the Lean stalk operator `WeilComplex.stalkFrobenius`. -/
theorem IsModelFrobenius.comp_frobeniusIterate_degreeOver (hΦ : W.IsModelFrobenius f₀ σ p)
    {m : ℕ} (hm : m ≠ 0) {x₀ : Spec (.of Ω) ⟶ X}
    (hx₀ : x₀ ≫ aX = 𝟙 _ ∧ x₀ ≫ W.frobeniusIterate m = x₀) :
    x₀ ≫ W.frobeniusIterate (f₀.degreeOver ((x₀ ≫ p).base default)) = x₀ := by
  let := Fintype.ofFinite k
  let : Algebra k Ω := (Spec.preimage σ).hom.toAlgebra
  let := (f₀.residueFieldAlgebraMap ((x₀ ≫ p).base default)).toAlgebra
  have : Finite (X₀.residueField ((x₀ ≫ p).base default)) :=
    X₀.mem_finitePoints.1 (hΦ.mem_finitePoints_of_fixedPoint hm hx₀).1
  have hd : f₀.degreeOver ((x₀ ≫ p).base default) =
      Module.finrank k (X₀.residueField ((x₀ ≫ p).base default)) := rfl
  have h := (hΦ.comp_frobeniusIterate_eq_iff x₀ (f₀.degreeOver ((x₀ ≫ p).base default)) 0).2
    (by rw [pow_zero, hd, ← FiniteField.orderOf_frobeniusAlgHom]; exact pow_orderOf_eq_one _)
  rw [h, frobeniusIterate_zero, Category.comp_id]

/-- Blueprint `lem-trf-local-frobenius-conjugacy` (1): let `x₀` be a section of `a_X` fixed by
`Φ_m`, `m ≥ 1`, lying over the closed point `y` of `X₀` of degree `d` (so `d ∣ m`). Then the
sections of `a_X` fixed by `Φ_m` lying over `y` are exactly the `d` distinct sections `x₀ ≫ Φ_i`,
`0 ≤ i < d`: `Φ` acts on them as the `#k`-power Frobenius acts on the `k`-embeddings
`κ(y) ↪ 𝔽_{q^m}`. The blueprint formulates this with the Galois Frobenius `g_γ`; here it is
stated with the scheme Frobenius `Φ` that defines the Lean stalk operator
`WeilComplex.stalkFrobenius`. -/
theorem IsModelFrobenius.bijective_comp_frobeniusIterate (hΦ : W.IsModelFrobenius f₀ σ p)
    {m : ℕ} (hm : m ≠ 0) {x₀ : Spec (.of Ω) ⟶ X}
    (hx₀ : x₀ ≫ aX = 𝟙 _ ∧ x₀ ≫ W.frobeniusIterate m = x₀) :
    Function.Bijective fun i : Fin (f₀.degreeOver ((x₀ ≫ p).base default)) ↦
      (⟨x₀ ≫ W.frobeniusIterate i, W.comp_frobeniusIterate_fixed hx₀ i,
        hΦ.base_comp_frobeniusIterate x₀ i⟩ :
        {x : Spec (.of Ω) ⟶ X // (x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x) ∧
          (x ≫ p).base default = (x₀ ≫ p).base default}) := by
  let := Fintype.ofFinite k
  let : Algebra k Ω := (Spec.preimage σ).hom.toAlgebra
  obtain ⟨hy, hdvd⟩ := hΦ.mem_finitePoints_of_fixedPoint hm hx₀
  let := (f₀.residueFieldAlgebraMap ((x₀ ≫ p).base default)).toAlgebra
  have : Finite (X₀.residueField ((x₀ ≫ p).base default)) := X₀.mem_finitePoints.1 hy
  have hψ (a : Ω) : ((FiniteField.frobeniusAlgHom k Ω ^ m : Ω →ₐ[k] Ω) : Ω →+* Ω) a =
      a ^ (Nat.card k ^ m) := by
    rw [AlgHom.coe_toRingHom, FiniteField.coe_frobeniusAlgHom_pow, Nat.card_eq_fintype_card]
  let e := (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun x ↦ x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x)
    (fun x ↦ (x ≫ p).base default = (x₀ ≫ p).base default)).symm.trans
    ((hΦ.fixedPointsEquiv (Spec.map_preimage σ) m).subtypeEquiv
      (p := fun x ↦ (x.1 ≫ p).base default = (x₀ ≫ p).base default)
      (q := fun g ↦ g.1.base default = (x₀ ≫ p).base default) fun x ↦ Iff.rfl)
  have hcard := (Nat.card_congr e).trans
    (f₀.natCard_fixedFieldPoints_fiber hm _ hψ ((x₀ ≫ p).base default))
  rw [if_pos hdvd] at hcard
  have : Finite {x : Spec (.of Ω) ⟶ X // (x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x) ∧
      (x ≫ p).base default = (x₀ ≫ p).base default} :=
    Nat.finite_of_card_ne_zero (hcard.trans_ne (f₀.degreeOver_ne_zero hy))
  refine Function.Injective.bijective_of_nat_card_le (fun i j hij ↦ ?_) ?_
  · exact (FiniteField.bijective_frobeniusAlgHom_pow k _).1
      ((hΦ.comp_frobeniusIterate_eq_iff x₀ i j).1 (congrArg Subtype.val hij))
  · rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Blueprint `lem-trf-local-frobenius-conjugacy` (1), unbundled: every section `x` of `a_X`
fixed by `Φ_m`, `m ≥ 1`, lying over the same closed point `y` of `X₀` as a section `x₀` fixed by
`Φ_m`, is `x₀ ≫ Φ_i` for some `i < deg y`. The blueprint formulates this with the Galois
Frobenius `g_γ`; here it is stated with the scheme Frobenius `Φ` that defines the Lean stalk
operator `WeilComplex.stalkFrobenius`. -/
theorem IsModelFrobenius.exists_eq_comp_frobeniusIterate (hΦ : W.IsModelFrobenius f₀ σ p)
    {m : ℕ} (hm : m ≠ 0) {x₀ x : Spec (.of Ω) ⟶ X}
    (hx₀ : x₀ ≫ aX = 𝟙 _ ∧ x₀ ≫ W.frobeniusIterate m = x₀)
    (hx : x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x)
    (hy : (x ≫ p).base default = (x₀ ≫ p).base default) :
    ∃ i < f₀.degreeOver ((x₀ ≫ p).base default), x = x₀ ≫ W.frobeniusIterate i := by
  obtain ⟨i, hi⟩ := (hΦ.bijective_comp_frobeniusIterate hm hx₀).2 ⟨x, hx, hy⟩
  exact ⟨i, i.2, (congrArg Subtype.val hi).symm⟩

/-- Blueprint `lem-trf-frobenius-degree-formula`: for a Weil datum, a section `x₀` of `a_X`
lying over a closed point `y` of `X₀` of degree `d`, fixed by `Φ_d`, and a section `x` of `a_X`
fixed by `Φ_m`, `m ≥ 1`, lying over `y` (so `d ∣ m`), the local Frobenius `F_{x,m}` has the trace
of `F_{x₀,d} ^ (m / d)`. The blueprint formulates this with the Galois Frobenius `g_γ`; here it is
stated with the scheme Frobenius `Φ` that defines the Lean stalk operator
`WeilComplex.stalkFrobenius`. -/
theorem IsModelFrobenius.trace_stalkFrobenius_eq_trace_pow [DerivedBraiding A]
    [IsIso W.coeff]
    (hΦ : W.IsModelFrobenius f₀ σ p) {m : ℕ} (hm : m ≠ 0) {x₀ x : Spec (.of Ω) ⟶ X}
    (hx₀a : x₀ ≫ aX = 𝟙 _)
    (hx₀ : x₀ ≫ W.frobeniusIterate (f₀.degreeOver ((x₀ ≫ p).base default)) = x₀)
    (hxa : x ≫ aX = 𝟙 _) (hx : x ≫ W.frobeniusIterate m = x)
    (hy : (x ≫ p).base default = (x₀ ≫ p).base default)
    [HasRightDual (((upperStar A x₀).leftDerivedFunctor).obj W.obj)]
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)] :
    let F : End (((upperStar A x₀).leftDerivedFunctor).obj W.obj) :=
      W.stalkFrobenius (f₀.degreeOver ((x₀ ≫ p).base default)) x₀ hx₀
    trace (W.stalkFrobenius m x hx) =
      trace (End.asHom (F ^ (m / f₀.degreeOver ((x₀ ≫ p).base default)))) := by
  intro F
  have hdvd := (hΦ.mem_finitePoints_of_fixedPoint hm ⟨hxa, hx⟩).2
  rw [hy] at hdvd
  set d := f₀.degreeOver ((x₀ ≫ p).base default)
  obtain ⟨n, rfl⟩ := hdvd
  have hd : d ≠ 0 := left_ne_zero_of_mul hm
  rw [Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hd)]
  obtain ⟨i, -, rfl⟩ := hΦ.exists_eq_comp_frobeniusIterate hm
    ⟨hx₀a, W.comp_frobeniusIterate_mul hx₀ n⟩ ⟨hxa, hx⟩ hy
  have hxd := W.comp_frobeniusIterate_comp_frobeniusIterate hx₀ i
  rw [W.stalkFrobenius_mul_eq_pow hxd n]
  exact trace_eq_of_iso (asIso (W.stalkTransport i x₀ _ rfl)) _ _
    (W.stalkTransport_comp_stalkFrobenius_pow rfl hx₀ hxd n).symm

end Orbit

end WeilComplex

end AlgebraicGeometry.ProEtale

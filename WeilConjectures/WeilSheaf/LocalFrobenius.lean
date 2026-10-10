/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The local Frobenius and the local alternating trace of a Weil complex

Let `K` be a Weil complex on a `k₀`-scheme `X`, with geometric fiber `X̄ = X ×_{k₀} k̄`. A point
`g : Spec K ⟶ X` with values in a finite extension `K` of `k₀` with `qᵐ` elements, together with
an embedding `ι : K ↪ k̄`, gives a geometric point `x̄ : Spec k̄ ⟶ X̄` fixed by the `m`-th power
of the geometric Frobenius up to reparametrisation. The iterated Weil structure then induces the
local Frobenius `F_x^{(m)}` on the stalk `𝓗ʲ(K)_x̄` of every cohomology sheaf of `K`, and the
local alternating trace

`Tr(F_x^{(m)} | K_x̄) = ∑_j (-1)ʲ Tr(F_x^{(m)} | 𝓗ʲ(K)_x̄)`.

The conjugacy class of the local Frobenius does not depend on the embedding `ι`.

## Main definitions

- `AlgebraicGeometry.WeilComplex.stalk` (`def-weil-local-frobenius-trace`): the stalk
  `𝓗ʲ(K)_x̄` at a closed point with its local Frobenius `F_x`.
- `AlgebraicGeometry.WeilComplex.stalkAtGeometricFiberPoint` (`def-weil-local-frobenius-trace`):
  the stalk `𝓗ʲ(K)_x̄` with the local Frobenius `F_x^{(m)}`, at the geometric point attached to
  a point with values in a field with `qᵐ` elements and an embedding of that field into `k̄`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint`
  (`lem-weil-local-frobenius-conjugacy-class`): the local Frobenius operators attached to two
  embeddings are conjugate.

## Implementation notes

The conjugacy of the local Frobenius operators is proved with the transport isomorphisms
`AlgebraicGeometry.WeilSheaf.stalkObjTransport` `F_{s'} ≅ F_s` along `s ≫ Frⁿ = σⁿ ≫ s'`, which
compose additively in `n` (`AlgebraicGeometry.WeilSheaf.stalkObjTransport_trans`); the local
Frobenius is the transport from `s` to itself, and two embeddings differ by a power of `σ`.

The blueprint defines `K_x̄ := L x̄^* For(K)` and its trace as the alternating sum of the traces
on the cohomology sheaves. The local alternating trace `Tr(F_x^{(n)} | K_x̄)` of
`def-weil-local-frobenius-trace` is `AlgebraicGeometry.WeilComplex.traceFunction`
(`WeilConjectures.WeilSheaf.Stalk`), which takes that alternating sum as the definition: the
derived stalk is not used.

The remark `rem-ptr-weil-local-frobenius-trace-1` of the blueprint only points to
`AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime]
variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable (F : WeilSheaf k₀ l X)

open ProEtale

/-- The geometric Galois Frobenius `Fr` of the geometric fiber `X̄`. -/
local notation "𝒢" => Scheme.Hom.geometricGaloisFrobenius (X ↘ Spec (CommRingCat.of k₀))

/-- The stalk `F_x̄` of a Weil sheaf, with the local Frobenius `F_x^{(m)}`, at the geometric point
`x̄ = AlgebraicGeometry.Scheme.Hom.geometricFiberPoint ι g hg` over a point `g : Spec K ⟶ X`
with values in a field `K` with `qᵐ` elements, for an embedding `ι : K ↪ k̄` over `k₀`. -/
noncomputable def stalkAtGeometricFiberPoint {K : Type u} [Field K] [Algebra k₀ K] [Finite K]
    (ι : K →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K) ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    (m : ℕ) (hK : Nat.card K = Nat.card k₀ ^ m) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  F.stalkAt _ m (Scheme.Hom.geometricFiberPoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) ι g hg m hK)

lemma frobeniusPowIso_zero_hom_hom :
    (F.frobeniusPowIso 0).hom.hom =
      eqToHom (by rw [pow_zero]; rfl) ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom.app F.obj.carrier.X := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Mod.comp_hom',
    adicLowerStarCongr_hom_app_hom, lowerStarCongr, eqToIso.hom, eqToHom_app]
  simp only [eqToHom_refl, adicLowerStarId, Iso.trans_hom, NatTrans.comp_app, Functor.id_obj,
    NatIso.ofComponents_hom_app, Mod.comp_hom', Mod.isoMk_hom_hom, Iso.app_hom,
    Mod.comapId_hom_app_hom, Category.id_comp]
  erw [Category.id_comp, Category.comp_id]

lemma frobeniusPowIso_succ_hom_hom (m : ℕ) :
    (F.frobeniusPowIso (m + 1)).hom.hom =
      eqToHom (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]; rfl) ≫
        (lowerStarComp _ (𝒢 ^ m).inv (𝒢).inv).inv.app F.obj.carrier.X ≫
        ((𝒢).inv)_*[WeilCoefficients.{u} l].map (F.frobeniusPowIso m).hom.hom ≫
        F.obj.str.hom.hom := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Mod.comp_hom',
    adicLowerStarCongr_hom_app_hom, lowerStarCongr, eqToIso.hom, eqToHom_app]
  rfl

theorem frobeniusPowIso_add_hom_hom (x y : ℕ) :
    (F.frobeniusPowIso (x + y)).hom.hom =
      eqToHom (by rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]; rfl) ≫
        (lowerStarComp _ (𝒢 ^ x).inv (𝒢 ^ y).inv).inv.app F.obj.carrier.X ≫
        ((𝒢 ^ y).inv)_*[WeilCoefficients.{u} l].map (F.frobeniusPowIso x).hom.hom ≫
        (F.frobeniusPowIso y).hom.hom := by
  induction y with
  | zero =>
    change (F.frobeniusPowIso x).hom.hom = _
    rw [frobeniusPowIso_zero_hom_hom]
    rw [lowerStarComp_inv_app_comp_lowerStarId_hom_app _ _ _ (by rw [pow_zero]; rfl)]
    simp
  | succ y ih =>
    change (F.frobeniusPowIso ((x + y) + 1)).hom.hom = _
    rw [frobeniusPowIso_succ_hom_hom, ih, frobeniusPowIso_succ_hom_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [eqToHom_lowerStarComp_inv_app_assoc_assoc _ _ _ _ ((𝒢) ^ (x + y)).inv
      (by rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]) ((𝒢) ^ (y + 1)).inv
      (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]) ((𝒢) ^ (x + y + 1)).inv
      (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]),
      lowerStar_map_eqToHom_lowerStarComp_inv_app_assoc _ _ _ ((𝒢) ^ (y + 1)).inv
        (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv])]


lemma stalkObjFrobeniusPowIso_add_hom (x y : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (F.stalkObjFrobeniusPowIso (x + y) s).hom =
      eqToHom (congrArg F.stalkObj (by rw [pow_add, Aut.Aut_mul_def, Iso.trans_hom,
        Category.assoc])) ≫
        (F.stalkObjFrobeniusPowIso x (s ≫ ((𝒢) ^ y).hom)).hom ≫
        (F.stalkObjFrobeniusPowIso y s).hom := by
  simp only [stalkObjFrobeniusPowIso, Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  have key := congrArg (Sheaf.Γ _ (WeilCoefficients.{u} l)).map
    (upperStarComp_hom_app_map_comp_of_eq (WeilCoefficients.{u} l) s ((𝒢) ^ x) ((𝒢) ^ y)
      ((𝒢) ^ (x + y)) (by rw [pow_add, Aut.Aut_mul_def]) F.obj.carrier.X
      ((AdicSheaf.forget _).map (F.frobeniusPowIso x).hom)
      ((AdicSheaf.forget _).map (F.frobeniusPowIso y).hom)
      ((AdicSheaf.forget _).map (F.frobeniusPowIso (x + y)).hom)
      (frobeniusPowIso_add_hom_hom F x y))
  simp only [Functor.map_comp, eqToHom_map] at key ⊢
  exact key


lemma stalkObjSpecFrobeniusPowIso_add_hom (x y : ℕ)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (F.stalkObjSpecFrobeniusPowIso (x + y) t).hom =
      eqToHom (congrArg F.stalkObj (by rw [pow_add, Aut.Aut_mul_def, Iso.trans_hom,
        Category.assoc])) ≫
        (F.stalkObjSpecFrobeniusPowIso y ((specGeometricFrobenius k₀ ^ x).hom ≫ t)).hom ≫
        (F.stalkObjSpecFrobeniusPowIso x t).hom := by
  simp only [stalkObjSpecFrobeniusPowIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  exact globalSections_map_upperStarComp_comp_globalSectionsUpperStarIso_of_eq
    _ t (specGeometricFrobenius k₀ ^ x) (specGeometricFrobenius k₀ ^ y)
    (specGeometricFrobenius k₀ ^ (x + y)) (by rw [pow_add, Aut.Aut_mul_def]) _

lemma stalkObjSpecFrobeniusPowIso_hom_comp_stalkObjFrobeniusPowIso_hom (a b : ℕ)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (F.stalkObjSpecFrobeniusPowIso a (t ≫ ((𝒢) ^ b).hom)).hom ≫
        (F.stalkObjFrobeniusPowIso b t).hom =
      eqToHom (congrArg F.stalkObj (Category.assoc _ _ _)) ≫
        (F.stalkObjFrobeniusPowIso b ((specGeometricFrobenius k₀ ^ a).hom ≫ t)).hom ≫
        (F.stalkObjSpecFrobeniusPowIso a t).hom := by
  simp only [stalkObjSpecFrobeniusPowIso, stalkObjFrobeniusPowIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  exact globalSections_map_upperStarComp_comm _ t (specGeometricFrobenius k₀ ^ a) _ _ _

/-- The transport `F_{s'} ≅ F_s` along `s ≫ Frⁿ = σⁿ ≫ s'`. -/
noncomputable def stalkObjTransport (n : ℕ)
    (s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (h : s ≫ ((𝒢) ^ n).hom = (specGeometricFrobenius k₀ ^ n).hom ≫ s') :
    F.stalkObj s' ≅ F.stalkObj s :=
  (F.stalkObjSpecFrobeniusPowIso n s').symm ≪≫ eqToIso (congrArg F.stalkObj h.symm) ≪≫
    F.stalkObjFrobeniusPowIso n s

@[reassoc]
lemma eqToHom_comp_stalkObjSpecFrobeniusPowIso_inv (n : ℕ)
    {p q : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (h : p = q) :
    eqToHom (congrArg F.stalkObj h) ≫ (F.stalkObjSpecFrobeniusPowIso n q).inv =
      (F.stalkObjSpecFrobeniusPowIso n p).inv ≫ eqToHom (by rw [h]) := by
  subst h
  simp

@[reassoc]
lemma stalkObjFrobeniusPowIso_hom_comp_eqToHom (n : ℕ)
    {p q : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (h : p = q) :
    (F.stalkObjFrobeniusPowIso n p).hom ≫ eqToHom (congrArg F.stalkObj h) =
      eqToHom (by rw [h]) ≫ (F.stalkObjFrobeniusPowIso n q).hom := by
  subst h
  simp

lemma stalkObjTransport_trans (a b : ℕ)
    (s s' s'' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (h₁ : s ≫ ((𝒢) ^ a).hom = (specGeometricFrobenius k₀ ^ a).hom ≫ s')
    (h₂ : s' ≫ ((𝒢) ^ b).hom = (specGeometricFrobenius k₀ ^ b).hom ≫ s'')
    (h₃ : s ≫ ((𝒢) ^ (b + a)).hom = (specGeometricFrobenius k₀ ^ (b + a)).hom ≫ s'') :
    F.stalkObjTransport b s' s'' h₂ ≪≫ F.stalkObjTransport a s s' h₁ =
      F.stalkObjTransport (b + a) s s'' h₃ := by
  have rt := F.stalkObjSpecFrobeniusPowIso_hom_comp_stalkObjFrobeniusPowIso_hom a b s'
  rw [← Iso.eq_inv_comp] at rt
  ext : 1
  simp only [stalkObjTransport, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% rt]
  have hR : (F.stalkObjSpecFrobeniusPowIso (b + a) s'').inv =
      (F.stalkObjSpecFrobeniusPowIso b s'').inv ≫
        (F.stalkObjSpecFrobeniusPowIso a ((specGeometricFrobenius k₀ ^ b).hom ≫ s'')).inv ≫
        eqToHom (by rw [pow_add, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc]) := by
    apply Iso.inv_ext
    rw [F.stalkObjSpecFrobeniusPowIso_add_hom b a s'']
    simp only [Category.assoc, Iso.hom_inv_id_assoc, eqToHom_trans, eqToHom_refl]
  rw [Iso.hom_inv_id_assoc, eqToHom_comp_stalkObjSpecFrobeniusPowIso_inv_assoc F a h₂.symm,
    stalkObjFrobeniusPowIso_hom_comp_eqToHom_assoc F b h₁.symm, hR,
    F.stalkObjFrobeniusPowIso_add_hom b a s]
  simp only [Category.assoc, eqToHom_trans_assoc]

lemma stalkAt_frobenius
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((𝒢) ^ m).hom = (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    (F.stalkAt s m hs).frobenius =
      WeilCoefficients.linearEquivOfIso (F.stalkObjTransport m s s hs) :=
  rfl

lemma stalkObjTransport_congr {n n' : ℕ} (hn : n = n')
    (s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (h : s ≫ ((𝒢) ^ n).hom = (specGeometricFrobenius k₀ ^ n).hom ≫ s')
    (h' : s ≫ ((𝒢) ^ n').hom = (specGeometricFrobenius k₀ ^ n').hom ≫ s') :
    F.stalkObjTransport n s s' h = F.stalkObjTransport n' s s' h' := by
  subst hn
  rfl

lemma comp_geometricGaloisFrobenius_pow_add
    {s s' s'' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {a b : ℕ} (h₁ : s ≫ ((𝒢) ^ a).hom = (specGeometricFrobenius k₀ ^ a).hom ≫ s')
    (h₂ : s' ≫ ((𝒢) ^ b).hom = (specGeometricFrobenius k₀ ^ b).hom ≫ s'') :
    s ≫ ((𝒢) ^ (b + a)).hom = (specGeometricFrobenius k₀ ^ (b + a)).hom ≫ s'' := by
  rw [pow_add, Aut.Aut_mul_def, Iso.trans_hom, reassoc_of% h₁, h₂, pow_add, Aut.Aut_mul_def,
    Iso.trans_hom, Category.assoc]

lemma nonempty_equiv_stalkAt_of_iso
    (s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((𝒢) ^ m).hom = (specGeometricFrobenius k₀ ^ m).hom ≫ s)
    (hs' : s' ≫ ((𝒢) ^ m).hom = (specGeometricFrobenius k₀ ^ m).hom ≫ s')
    (E : F.stalkObj s' ≅ F.stalkObj s)
    (hE : F.stalkObjTransport m s s hs ≪≫ E.symm = E.symm ≪≫ F.stalkObjTransport m s' s' hs') :
    Nonempty ((F.stalkAt s m hs).Equiv (F.stalkAt s' m hs')) := by
  let L : (F.stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l] (F.stalkAt s' m hs').carrier :=
    WeilCoefficients.linearEquivOfIso E.symm
  have h : (F.stalkAt s m hs).frobenius.trans L = L.trans (F.stalkAt s' m hs').frobenius := by
    rw [stalkAt_frobenius, stalkAt_frobenius]
    change (WeilCoefficients.linearEquivOfIso _).trans (WeilCoefficients.linearEquivOfIso _) =
      (WeilCoefficients.linearEquivOfIso _).trans (WeilCoefficients.linearEquivOfIso _)
    rw [WeilCoefficients.linearEquivOfIso_trans, WeilCoefficients.linearEquivOfIso_trans, hE]
  exact ⟨FrobeniusModule.Equiv.ofTrans L h⟩



/-- Blueprint `lem-weil-local-frobenius-conjugacy-class`: Independence of the local Frobenius
operator from the embedding.

For a point `g : Spec K ⟶ X` with values in a field `K` with `qᵐ` elements and two embeddings
`ι, ι' : K ↪ k̄` over `k₀`, the local Frobenius operators `F_x^{(m)}` on the stalks of a Weil
sheaf at the two attached geometric points are conjugate. The two embeddings differ by a power
`σʲ` of the Frobenius of `k̄`, so the two geometric points differ by the reparametrisation `σʲ`;
the stalks at a geometric point and at its reparametrisation are identified
(`AlgebraicGeometry.WeilSheaf.stalkObjSpecFrobeniusPowIso`), and this identification
intertwines the iterated Weil structures. -/
theorem nonempty_equiv_stalkAtGeometricFiberPoint {K : Type u} [Field K] [Algebra k₀ K]
    [Finite K] (ι ι' : K →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K) ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    (m : ℕ) (hK : Nat.card K = Nat.card k₀ ^ m) :
    Nonempty ((F.stalkAtGeometricFiberPoint ι g hg m hK).Equiv
      (F.stalkAtGeometricFiberPoint ι' g hg m hK)) := by
  let := Fintype.ofFinite k₀
  obtain ⟨j, hj⟩ := FiniteField.exists_apply_eq_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply
    k₀ (AlgebraicClosure k₀) ι ι'
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint ι g hg
  set s' := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint ι' g hg
  have hss' : s ≫ ((𝒢) ^ j).hom = (specGeometricFrobenius k₀ ^ j).hom ≫ s' := by
    ext
    · simp only [s, s', Category.assoc,
        Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj,
        Scheme.Hom.geometricFiberPoint_comp_geometricFiberProj]
      rw [specGeometricFrobenius_pow_hom, ← Spec.map_comp_assoc]
      congr 2
      ext a
      exact hj a
    · simp [s, s']
  have hs := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint_comp_geometricGaloisFrobenius_pow
    ι g hg m hK
  have hs' := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint_comp_geometricGaloisFrobenius_pow
    ι' g hg m hK
  have key : (F.stalkObjTransport m s' s' hs').hom ≫ (F.stalkObjTransport j s s' hss').hom =
      (F.stalkObjTransport j s s' hss').hom ≫ (F.stalkObjTransport m s s hs).hom := by
    rw [← Iso.trans_hom, ← Iso.trans_hom,
      F.stalkObjTransport_trans j m s s' s' hss' hs'
        (comp_geometricGaloisFrobenius_pow_add hss' hs'),
      F.stalkObjTransport_trans m j s s s' hs hss' (comp_geometricGaloisFrobenius_pow_add hs hss'),
      F.stalkObjTransport_congr (add_comm m j)]
  have key' : (F.stalkObjTransport m s s hs).hom ≫ (F.stalkObjTransport j s s' hss').inv =
      (F.stalkObjTransport j s s' hss').inv ≫ (F.stalkObjTransport m s' s' hs').hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact F.nonempty_equiv_stalkAt_of_iso s s' m hs hs' (F.stalkObjTransport j s s' hss')
    (by ext : 1; exact key')


end WeilSheaf

namespace WeilComplex

variable (K : WeilComplex k₀ l X)

/-- Blueprint `def-weil-local-frobenius-trace`: Local Frobenius and local alternating trace.

The stalk `𝓗ʲ(For K)_x̄` of the `j`-th cohomology sheaf of a Weil complex at the geometric
point over a closed point `x`, with the local Frobenius `F_x`, obtained by iterating the Weil
isomorphism `deg x` times. The geometric point is attached to an embedding `κ(x) ↪ k̄` chosen
by `IsAlgClosed.lift` (`AlgebraicGeometry.WeilSheaf.stalk`). -/
noncomputable def stalk (j : ℤ) (x : X.finitePoints) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((homologySheaf j).obj K).stalk x

/-- Blueprint `def-weil-local-frobenius-trace`: Local Frobenius and local alternating trace.

The stalk `𝓗ʲ(For K)_x̄` of the `j`-th cohomology sheaf of a Weil complex with the local
Frobenius `F_x^{(m)}`, at the geometric point attached to a point `g : Spec K ⟶ X` with values in
a field `K` with `qᵐ` elements and an embedding `ι : K ↪ k̄` over `k₀`. -/
noncomputable def stalkAtGeometricFiberPoint (j : ℤ) {K' : Type u} [Field K'] [Algebra k₀ K']
    [Finite K'] (ι : K' →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K') ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K')))
    (m : ℕ) (hK : Nat.card K' = Nat.card k₀ ^ m) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((homologySheaf j).obj K).stalkAtGeometricFiberPoint ι g hg m hK

/-- Blueprint `lem-weil-local-frobenius-conjugacy-class`: Independence of the local Frobenius
operator from the embedding.

For a point `g : Spec K' ⟶ X` with values in a field `K'` with `qᵐ` elements, two embeddings
`ι, ι' : K' ↪ k̄` over `k₀` and `j ∈ ℤ`, the local Frobenius operators `F_x^{(m)}` on the stalks
of the cohomology sheaf `𝓗ʲ(For K)` at the two attached geometric points are conjugate. For a
closed point `x` take `K' = κ(x)` and `m = deg x`. -/
theorem nonempty_equiv_stalkAtGeometricFiberPoint (j : ℤ) {K' : Type u} [Field K']
    [Algebra k₀ K'] [Finite K'] (ι ι' : K' →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K') ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K')))
    (m : ℕ) (hK : Nat.card K' = Nat.card k₀ ^ m) :
    Nonempty ((K.stalkAtGeometricFiberPoint j ι g hg m hK).Equiv
      (K.stalkAtGeometricFiberPoint j ι' g hg m hK)) :=
  ((homologySheaf j).obj K).nonempty_equiv_stalkAtGeometricFiberPoint ι ι' g hg m hK

end WeilComplex

end AlgebraicGeometry

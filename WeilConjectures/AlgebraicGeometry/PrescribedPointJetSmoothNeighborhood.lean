/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrescribedPointSystemData
import WeilConjectures.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential
import WeilConjectures.PointCount
import WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Smoothness near a closed point with nonzero first jet

Source: Stacks Project, Algebra, Tag 00TR; Tag 00T7.
(blueprint: lem-zl-prescribed-point-jet-smooth-neighborhood).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

/-- A point derivation detects a nonzero value of the sheaf differential.

Source: Stacks Project, Tag 01UR, universal property of differentials. Compose the
point derivation with germs to obtain a derivation into the skyscraper module.
The induced map on differential stalks, paired with the residue field by multiplication,
detects the given differential value. -/
private theorem differentialValue_of_pointDerivation
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (x : X) (d : X.presheaf.stalk x →+ X.residueField x)
    (hmul : ∀ b c, d (b * c) =
      (X.residue x b) * d c + (X.residue x c) * d b)
    (hconst : ∀ a : Γ(Spec (.of k), ⊤),
      d (X.presheaf.germ ⊤ x trivial (p.appTop a)) = 0)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U))
    (ha : d (X.presheaf.germ U x hx a) ≠ 0) :
    p.relativeDifferentialValue U x hx a := by
  classical
  let R := X.presheaf.stalk x
  let F := X.residueField x
  let : Algebra R F := (X.residue x).hom.toAlgebra
  let Q := skyscraper x F
  let D : Q.val.Derivation' p.pullbackPresheafToPresheaf := p.derivationMk
    (fun {V} ↦
      { toFun := fun b h ↦ d (X.presheaf.germ V.unop x h.down b)
        map_zero' := by
          funext h
          change d (X.presheaf.germ V.unop x h.down 0) = 0
          rw [map_zero, map_zero]
        map_add' := by
          intro b c
          funext h
          change d (X.presheaf.germ V.unop x h.down (b + c)) =
            d (X.presheaf.germ V.unop x h.down b) +
              d (X.presheaf.germ V.unop x h.down c)
          rw [map_add, map_add] })
    (fun {V} b c ↦ by
      apply SkyscraperSections.ext
      intro h
      change d (X.presheaf.germ V.unop x h (b * c)) = _
      rw [map_mul, hmul]
      rfl)
    (fun {V W} i b ↦ by
      apply SkyscraperSections.ext
      intro h
      exact congrArg d (X.presheaf.germ_res_apply i.unop x h b))
    (fun V b ↦ by
      apply SkyscraperSections.ext
      intro h
      have hV : V = ⊤ := by
        apply le_antisymm le_top
        intro y _
        exact (Subsingleton.elim (p x) y) ▸ h
      subst V
      change d (X.presheaf.germ ⊤ x trivial (p.appTop b)) = 0
      exact hconst b)
  let f := (p.relativeDifferentialsHomEquiv Q).symm D
  let L : p.relativeDifferentials.presheaf.stalk x →ₗ[R] F :=
    skyscraperStalkEval x F ∘ₗ f.stalkLinearMap x
  have hL : L (p.relativeDifferentials.presheaf.germ U x hx
      (p.relativeDifferentialsDerivation.d (X := op U) a)) =
      d (X.presheaf.germ U x hx a) := by
    dsimp only [L, LinearMap.comp_apply]
    rw [Hom.stalkLinearMap_germ, skyscraperStalkEval_germ]
    change (f.val.app (op U) (p.relativeDifferentialsDerivation.d a)) ⟨hx⟩ = _
    rw [Scheme.Hom.relativeDifferentialsHomEquiv_symm_app_d]
    rfl
  let T := (LinearMap.mul' R F).comp (TensorProduct.map L (LinearMap.id : F →ₗ[R] F))
  intro hzero
  change TensorProduct.tmul R
    (p.relativeDifferentials.presheaf.germ U x hx
      (p.relativeDifferentialsDerivation.d (X := op U) a)) (1 : F) = 0 at hzero
  have ht := congrArg T hzero
  change L (p.relativeDifferentials.presheaf.germ U x hx
    (p.relativeDifferentialsDerivation.d (X := op U) a)) * (1 : F) = 0 at ht
  rw [mul_one, hL] at ht
  exact ha ht

/-- At a rational closed point, a function whose germ is not in m² has nonzero differential.

Source: Stacks Project, Algebra, Tag 00TR. The residue field is the base field.
A linear functional detecting the nonzero cotangent class defines a point derivation
by applying it to b minus its residue. Apply the preceding skyscraper construction. -/
private theorem differentialValue_of_notMem_square
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (x : X) (hclosed : IsClosed ({x} : Set X))
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U))
    (ha : X.presheaf.germ U x hx a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (ha2 : X.presheaf.germ U x hx a ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2) :
    p.relativeDifferentialValue U x hx a := by
  classical
  let R := X.presheaf.stalk x
  let F := X.residueField x
  let c : k →+* R := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
    X.presheaf.germ ⊤ x trivial).hom
  let : Algebra k R := c.toAlgebra
  let : Algebra k F := (p.residueFieldAlgebraMap x).toAlgebra
  have : Module.Finite k F := p.finite_residueField_of_isClosed x hclosed
  let l : F →ₐ[k] k := IsAlgClosed.lift
  have hc (b : k) : X.residue x (c b) = p.residueFieldAlgebraMap x b := by
    have h : CommRingCat.ofHom (p.residueFieldAlgebraMap x) =
        (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
          X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
      unfold Scheme.Hom.residueFieldAlgebraMap
      rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
        Scheme.residue_residueFieldMap, Scheme.Hom.germ_stalkMap_assoc]
      rfl
    exact congrArg (fun f ↦ f.hom b) h.symm
  let ε : R →ₐ[k] k :=
    { toRingHom := l.toRingHom.comp (X.residue x).hom
      commutes' b := by
        change l (X.residue x (c b)) = b
        rw [hc]
        exact l.commutes b }
  have hker : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal R := by
    ext b
    change l (X.residue x b) = 0 ↔ b ∈ IsLocalRing.maximalIdeal R
    rw [map_eq_zero_iff l l.injective]
    exact IsLocalRing.residue_eq_zero_iff b
  have hmem : X.presheaf.germ U x hx a ∈ RingHom.ker ε.toRingHom := by
    rwa [hker]
  have hne : (RingHom.ker ε.toRingHom).toCotangent
      ⟨X.presheaf.germ U x hx a, hmem⟩ ≠ 0 := by
    rw [ne_eq, Ideal.toCotangent_eq_zero]
    change X.presheaf.germ U x hx a ∉ RingHom.ker ε.toRingHom ^ 2
    rwa [hker]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hne
  let d₀ := ε.cotangentDerivation φ
  let d : R →+ F := (p.residueFieldAlgebraMap x).toAddMonoidHom.comp d₀.toAddMonoidHom
  have hinv (b : F) : p.residueFieldAlgebraMap x (l b) = b := by
    apply l.injective
    exact (l.commutes (l b)).trans rfl
  apply differentialValue_of_pointDerivation p x d
  · intro b b'
    change p.residueFieldAlgebraMap x (d₀ (b * b')) = _
    rw [AlgHom.cotangentDerivation_mul, map_add, map_mul, map_mul]
    rw [show ε b = l (X.residue x b) from rfl,
      show ε b' = l (X.residue x b') from rfl, hinv, hinv]
    rfl
  · intro b
    obtain ⟨b, rfl⟩ := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective b
    change p.residueFieldAlgebraMap x (d₀ (c b)) = 0
    have hd : d₀ (c b) = 0 := by
      rw [AlgHom.cotangentDerivation_apply]
      have h : (⟨c b - algebraMap k R (ε (c b)),
          ε.sub_algebraMap_mem_ker (c b)⟩ : RingHom.ker ε.toRingHom) = 0 := by
        apply Subtype.ext
        change c b - c (ε (algebraMap k R b)) = 0
        simp only [ε.commutes, Algebra.algebraMap_self_apply, sub_self]
      rw [h, map_zero, map_zero]
    rw [hd, map_zero]
  · change p.residueFieldAlgebraMap x (d₀ (X.presheaf.germ U x hx a)) ≠ 0
    rw [map_ne_zero_iff _ (p.residueFieldAlgebraMap x).injective,
      AlgHom.cotangentDerivation_of_mem φ hmem]
    exact hφ

/-- A section with nonzero first jet at a closed point of its zero scheme cuts
out a smooth hypersurface near that point.

Source: Stacks Project, Algebra, Tags 00TR (cotangent versus differentials), 00T7
(standard smoothness); blueprint, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-prescribed-point-jet-smooth-neighborhood).

Proof: Put x equal to the image of z in X. Choose an affine neighbourhood of x
with a free generator e of M, and write v = a e there. Its germ lies in the maximal
ideal m, since z belongs to the zero scheme. If the germ of a belonged to m², its
product with the coefficient of e in the chosen stalk frame would also belong to m².
The prescribed jet would be zero. Thus a has a nonzero cotangent class.

The closed-point field theorem makes the residue field finite over k, hence equal
to k. A linear functional on the cotangent space detecting the class of a defines
a point derivation by sending b to the functional applied to b minus its residue.
The already proved AlgHom.cotangentDerivation supplies its Leibniz rule. Extend its
values to the residue field and compose with germs to obtain a derivation into the
skyscraper module at x. The universal property of relative differentials induces
a map on differential stalks. Pairing it with the residue field by multiplication
sends da tensor 1 to the nonzero point derivative. Hence da(x) is nonzero.

Apply Scheme.Hom.smooth_zeroLocus_of_relativeDifferentialValue on this trivializing
neighbourhood, converting homOfGlobalSection M v to compatible sections by unitHomEquiv.
The inverse-equivalence identity keeps the zero scheme exactly the same, and the
criterion supplies the required smooth open neighbourhood of z.
-/
theorem exists_smooth_neighborhood_of_prescribedPointJet
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [Smooth p] [LocallyOfFiniteType p]
    (M : X.Modules) [M.IsInvertible] (v : Γ(M, ⊤))
    (z : (homOfGlobalSection M v).zeroLocus.subscheme)
    (hclosed : IsClosed
      ({(homOfGlobalSection M v).zeroLocus.subschemeι z} : Set X))
    (hjet : prescribedPointJet M ((homOfGlobalSection M v).zeroLocus.subschemeι z) v ≠ 0) :
    ∃ V : (homOfGlobalSection M v).zeroLocus.subscheme.Opens,
      z ∈ V ∧ Smooth (V.ι ≫ (homOfGlobalSection M v).zeroLocus.subschemeι ≫ p) := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    IsInvertible.sheafOfModules_isInvertible M
  let f := homOfGlobalSection M v
  let x := f.zeroLocus.subschemeι z
  obtain ⟨U, hx, _, e, he⟩ := exists_isFreeGenerator M
    (show x ∈ (⊤ : X.Opens) from trivial)
  let a := he.coeff (f.app U.1 (1 : Γ(X, U.1)))
  have ha : f.app U.1 (1 : Γ(X, U.1)) = a • e := (he.coeff_smul _).symm
  have hgs : M.presheaf.germ ⊤ x trivial v =
      X.presheaf.germ U.1 x hx a • M.presheaf.germ U.1 x hx e := by
    rw [← M.presheaf.germ_res_apply (homOfLE le_top) x hx v,
      ← homOfGlobalSection_app_one M v U.1, ha, germ_smul]
  have hsupport : x ∈ f.zeroLocus.support := by
    change x ∈ (f.zeroLocus.support : Set X)
    rw [← f.zeroLocus.range_subschemeι]
    exact Set.mem_range_self z
  have hnotbasic : x ∉ X.basicOpen a := by
    intro h
    have h' : x ∈ U.1 ⊓ f.zeroLocus.support.compl :=
      (basicOpen_coeff_eq f U he) ▸ h
    exact h'.2 hsupport
  have hmem : X.presheaf.germ U.1 x hx a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact fun h ↦ hnotbasic ((X.mem_basicOpen a x hx).mpr h)
  have hnotSquare : X.presheaf.germ U.1 x hx a ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
    intro h
    apply hjet
    change prescribedPointJet M x v = 0
    unfold prescribedPointJet
    dsimp only
    split_ifs with hb
    · have hz : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent
          ⟨_, hb⟩ = 0 := by
        rw [Ideal.toCotangent_eq_zero]
        change (Classical.choice (invertible_stalk_linearEquiv X M x))
          (M.presheaf.germ ⊤ x trivial v) ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2
        rw [hgs, LinearEquiv.map_smul]
        exact Ideal.mul_mem_right _ _ h
      rw [hz, TensorProduct.zero_tmul]
    · rfl
  have hda := differentialValue_of_notMem_square p x hclosed U.1 hx a hmem hnotSquare
  let s := M.unitHomEquiv f
  have hs : M.unitHomEquiv.symm s = f := M.unitHomEquiv.symm_apply_apply f
  have hresult := Scheme.Hom.smooth_zeroLocus_of_relativeDifferentialValue p M s
  rw [hs] at hresult
  exact hresult z U.1 hx e he a ha hda

end

end AlgebraicGeometry

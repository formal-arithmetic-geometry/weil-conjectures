/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.LisseFiltration

import Sheaf.DeligneLaumon.GeometricConstituentOrbit
import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse
import WeilConjectures.WeilSheaf.StalkIso

/-! # Aligning two local eigenvalues in one geometric constituent

This is the constant-extension and geometric-socle step, before choosing any curve.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

private theorem eigenvalue_summand
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    {n : ℕ} (S : Fin n → WeilSheaf k l C) {V : WeilSheaf k l C}
    (v : V ≅ ⨁ S) (z : C.finitePoints) {α : PadicAlgCl l}
    (hα : (V.stalk z).frobeniusEnd.HasEigenvalue α) :
    ∃ a, ((S a).stalk z).frobeniusEnd.HasEigenvalue α := by
  classical
  obtain ⟨w⟩ := nonempty_equiv_stalk_of_iso v z
  obtain ⟨x, hx⟩ := (w.hasEigenvalue hα).exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  let L := stalkFunctor k l ((C ↘ Spec (.of k)).geometricFiberPointOfFinitePoint z) ⋙
    WeilCoefficients.toModuleCat l
  have hproj : ∃ a, stalkAtMap _ _ _ (biproduct.π S a) x ≠ 0 := by
    by_contra! hz
    have ht := congrArg (fun f ↦ (L.map f).hom x) (biproduct.total (f := S))
    have hz' (a : Fin n) : (L.map (biproduct.π S a)).hom x = 0 := hz a
    simp only [Functor.map_sum, Functor.map_comp, ModuleCat.hom_sum,
      ModuleCat.hom_comp, LinearMap.sum_apply, LinearMap.comp_apply] at ht
    simp only [hz', map_zero, Finset.sum_const_zero] at ht
    exact hx.2 (by simpa using ht.symm)
  obtain ⟨a, ha⟩ := hproj
  refine ⟨a, Module.End.hasEigenvalue_of_hasEigenvector
    (x := stalkAtMap _ _ _ (biproduct.π S a) x) ?_⟩
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ha⟩
  change ((S a).stalk z).frobenius _ = _
  exact (stalkAtMap_frobenius _ _ _ (biproduct.π S a) x).symm.trans
    ((congrArg (stalkAtMap _ _ _ (biproduct.π S a)) hx.1).trans
      (map_smul (stalkAtMap _ _ _ (biproduct.π S a)) α x))

private theorem subobject_of_cokernel
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    {A B H S : WeilSheaf k l C} (i : A ⟶ B) (j : B ⟶ H) [Mono i] [Mono j]
    (hA : A.IsLisse) (hB : B.IsLisse) (hS : S.IsLisse)
    (q : S ⟶ cokernel i) [Mono q] :
    ∃ (T : WeilSheaf k l C) (a : A ⟶ T) (b : T ⟶ H),
      Mono a ∧ Mono b ∧ T.IsLisse ∧ Nonempty (cokernel a ≅ S) := by
  let P := pullback (cokernel.π i) q
  let a : A ⟶ P := pullback.lift i 0 (by simp)
  let b : P ⟶ H := pullback.fst _ _ ≫ j
  have ha : Mono a := by
    have : Mono (a ≫ pullback.fst (cokernel.π i) q) := by
      simpa only [a, pullback.lift_fst] using (inferInstance : Mono i)
    exact mono_of_mono a (pullback.fst _ _)
  have hb : Mono b := inferInstance
  have hz : a ≫ pullback.snd (cokernel.π i) q = 0 := pullback.lift_snd _ _ _
  have hk : IsLimit (KernelFork.ofι a hz) := by
    refine KernelFork.IsLimit.ofι' a hz fun {T} t ht ↦ ?_
    have ht' : (t ≫ pullback.fst _ _) ≫ cokernel.π i = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ht, zero_comp]
    refine ⟨Abelian.monoLift i (t ≫ pullback.fst _ _) ht', ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, a, pullback.lift_fst, Abelian.monoLift_comp]
    · simp only [Category.assoc, a, pullback.lift_snd, comp_zero, ht]
  let e : cokernel a ≅ S := IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel a) (Abelian.epiIsCokernelOfKernel _ hk)
  have hP : P.IsLisse :=
    (((hB.biprod hS).kernel_cokernel (hA.kernel_cokernel hB i).2
      (biprod.desc (cokernel.π i) (-q))).1).of_iso
        (IsLimit.conePointUniqueUpToIso
          (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct
            (cokernel.π i) q) (kernelIsKernel _)).symm
  exact ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩

/-- Two local eigenvalues can be aligned on one geometrically simple quotient over a
smooth geometrically connected positive-dimensional affine base.

Source: current blueprint, `sec-deligne-laumon-general/sk-i-dl-general-real/`
`thm-zl-real-mixed-by-curves.proof.md`, paragraph 1 and the geometric-socle
argument of the unit; dimension-zero paragraph 7.
(blueprint: lem-zl-pair-eigenvalue-geometric-constituent).

Proof: The irreducible quotient is supported on one connected clopen component:
its restrictions to clopen components give a direct sum, and simplicity permits
only one nonzero summand. Both eigenvalues force their points onto this support.
Split the geometric components by a finite extension. The geometric socle spans
the quotient under Frobenius, and its simple isotypic components form one orbit;
a proper orbit sum would descend to a proper Weil subobject. On a stabilized
isotypic block the Frobenius return is T tensor B. An eigenline of B exists over
the algebraically closed coefficient field; its orbit would be a proper Weil
subobject unless the multiplicity is one. After increasing the constant field,
the geometric simple summands have Weil structures. Power each local Frobenius
by a common multiple of its permutation cycle lengths. An eigenvector projects
nontrivially onto a block; invertibility transports the powered eigenvalue to
every block in that cycle. Independent Frobenius changes of the geometric lifts
at the two points align them with the same fixed simple summand. These choices
are independent even when the original points coincide. Realize the chosen
summand as a quotient of lisse subsheaves of the actual restricted ambient
object, using inverse images under its quotient map. Exact restriction preserves
both monomorphisms. Local point transport gives the asserted powers, and the
residue tower gives the identical exponents for residue sizes. The ambient
restriction remains real for every embedding: conjugation commutes with powers,
including coincident powered roots. On the chosen smooth geometric component
the relative dimension is constant. If it is zero, the component is a finite-field
point; pull its diagram back to the affine line over that field. The geometric
simple quotient is then a constant line, hence remains geometrically simple.
Use the same rational point twice. This makes the new dimension one and changes
neither local comparison. In positive dimension retain the component itself.
Empty support and the zero quotient cannot have the assumed eigenvalues. -/
theorem exists_pair_eigenvalue_geometric_constituent
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsAffine X]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {G : WeilSheaf k₀ l X} (hG : G.IsLisse) {G₁ G₂ : WeilSheaf k₀ l X}
    (i : G₁ ⟶ G₂) (j : G₂ ⟶ G) [Mono i] [Mono j]
    (h₁ : G₁.IsLisse) (h₂ : G₂.IsLisse)
    (hirr : (cokernel i).IsIrreducibleLisse)
    (x y : X.finitePoints) (α β : PadicAlgCl l)
    (hα : ((cokernel i).stalk x).frobeniusEnd.HasEigenvalue α)
    (hβ : ((cokernel i).stalk y).frobeniusEnd.HasEigenvalue β) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₀ k₁)
      (_ : Fact (ringChar k₁ ≠ l)) (d : ℕ) (C : Scheme.{u})
      (_ : C.Over (Spec (CommRingCat.of k₁))) (_ : IsAffine C)
      (_ : SmoothOfRelativeDimension d (C ↘ Spec (CommRingCat.of k₁)))
      (_ : GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁)))
      (_ : IsSeparated (C ↘ Spec (CommRingCat.of k₁)))
      (_ : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁)))
      (_ : QuasiCompact (C ↘ Spec (CommRingCat.of k₁)))
      (H H₁ H₂ : WeilSheaf k₁ l C) (a : H₁ ⟶ H₂) (b : H₂ ⟶ H)
      (_ : Mono a) (_ : Mono b),
      H.IsLisse ∧ H₁.IsLisse ∧ H₂.IsLisse ∧ (cokernel a).IsGeometricallyIrreducible ∧ 0 < d ∧
      (∀ ι : PadicAlgCl l →+* ℂ, G.IsReal ι → H.IsReal ι) ∧
      ∃ (s t : C.finitePoints) (e f : ℕ), 0 < e ∧ 0 < f ∧
        (C ↘ Spec (CommRingCat.of k₁)).residueCard s.1 =
          (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 ^ e ∧
        (C ↘ Spec (CommRingCat.of k₁)).residueCard t.1 =
          (X ↘ Spec (CommRingCat.of k₀)).residueCard y.1 ^ f ∧
        ((cokernel a).stalk s).frobeniusEnd.HasEigenvalue (α ^ e) ∧
        ((cokernel a).stalk t).frobeniusEnd.HasEigenvalue (β ^ f) ∧
        ∃ c : C ⟶ X,
          c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
            (C ↘ Spec (CommRingCat.of k₁)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) ∧
          c s.1 = x.1 ∧ c t.1 = y.1 := by
  classical
  have hx : Nontrivial ((cokernel i).stalk x).carrier := by
    obtain ⟨z, hz⟩ := hα.exists_hasEigenvector
    exact nontrivial_of_ne z 0 hz.2
  have hy : Nontrivial ((cokernel i).stalk y).carrier := by
    obtain ⟨z, hz⟩ := hβ.exists_hasEigenvector
    exact nontrivial_of_ne z 0 hz.2
  obtain ⟨k₁, hk₁, hfin, halg, hchar, d, C, hover, haff, hsm, hconn, hsep,
    hlft, hqc, R, hlim, hcolim, n, S, v, c, hd, hlisse, hreal, hgeo, hc,
    s, t, e, f, he, hf, hs, ht, hcards, hcardt, hspecs, hspect, horbit⟩ :=
    exists_geometric_constituent_orbit (cokernel i) hirr x y hx hy
  have hα' : ((R.obj (cokernel i)).stalk s).frobeniusEnd.HasEigenvalue (α ^ e) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hspecs,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hα.pow e
  have hβ' : ((R.obj (cokernel i)).stalk t).frobeniusEnd.HasEigenvalue (β ^ f) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hspect,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hβ.pow f
  obtain ⟨a₀, hαS⟩ := eigenvalue_summand S v s hα'
  obtain ⟨b₀, hβS⟩ := eigenvalue_summand S v t hβ'
  obtain ⟨t', ht', hcardt', ⟨w⟩⟩ := horbit a₀ b₀
  let q : S a₀ ⟶ cokernel (R.map i) :=
    biproduct.ι S a₀ ≫ v.inv ≫ (PreservesCokernel.iso R i).hom
  have hq : Mono q := inferInstance
  obtain ⟨T, a, b, ha, hb, hT, ⟨u⟩⟩ := subobject_of_cokernel (R.map i) (R.map j)
    (hlisse G₁ h₁) (hlisse G₂ h₂) (hgeo a₀).1 q
  have hu : (cokernel a).IsGeometricallyIrreducible :=
    (hgeo a₀).of_iso ((carrierFunctor k₁ l C).mapIso u.symm)
  obtain ⟨us⟩ := nonempty_equiv_stalk_of_iso u.symm s
  obtain ⟨ut⟩ := nonempty_equiv_stalk_of_iso u.symm t'
  refine ⟨k₁, hk₁, hfin, halg, hchar, d, C, hover, haff, hsm, hconn,
    hsep, hlft, hqc, R.obj G, R.obj G₁, T, a, b, ha, hb,
    hlisse G hG, hlisse G₁ h₁, hT, hu, hd, hreal G,
    s, t', e, f, he, hf, hcards, hcardt'.trans hcardt,
    us.hasEigenvalue hαS, ut.hasEigenvalue (w.hasEigenvalue hβS), c, hc, hs, ht'⟩

end AlgebraicGeometry.WeilSheaf

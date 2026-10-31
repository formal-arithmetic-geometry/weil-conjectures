/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealCurve
import WeilConjectures.DeligneLaumon.PairEigenvalueGeometricConstituent
import WeilConjectures.DeligneLaumon.GeometricCurveDiagramDescent
import WeilConjectures.DeligneLaumon.ProEtaleIrreducibilityDetector
import WeilConjectures.AlgebraicGeometry.Bertini
import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse

/-! # Simultaneous curve tests for two local eigenvalues

This is the geometric part of the smooth affine constituent argument. It asserts
no weight or purity statement. Frobenius and residue sizes acquire matching powers.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

private theorem geometric_point_over
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (x : X.finitePoints) :
    f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ := by
  dsimp only [Scheme.Hom.geometricFiberPointOfFinitePoint, Scheme.Hom.geometricFiberPoint,
    Scheme.Hom.geometricFiberToAlgebraicClosure]
  exact pullback.lift_snd _ _ _

private theorem exists_geometric_curve_pair
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsAffine X]
    {d : ℕ} (hd : 0 < d)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))]
    (V : WeilSheaf k l X) (hV : V.IsGeometricallyIrreducible)
    (x y : X.finitePoints) :
    ∃ (D : Scheme.{u}) (v : D ⟶ (X ↘ Spec (CommRingCat.of k)).geometricFiber),
      IsClosedImmersion v ∧ IsAffine D ∧
      SmoothOfRelativeDimension 1
        (v ≫ (X ↘ Spec (CommRingCat.of k)).geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace D ∧ ProEtale.IsIrreducibleAdicLocalSystem ((v)^*ᵃ[l].obj V.obj.carrier) ∧
      ∃ sx sy : Spec (.of (AlgebraicClosure k)) ⟶ D,
        sx ≫ v = (X ↘ Spec (CommRingCat.of k)).geometricFiberPointOfFinitePoint x ∧
        sy ≫ v = (X ↘ Spec (CommRingCat.of k)).geometricFiberPointOfFinitePoint y := by
  classical
  let f := X ↘ Spec (CommRingCat.of k)
  have hgeom : SmoothOfRelativeDimension d f.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (SmoothOfRelativeDimension d (pullback.snd f _))
  have : IsAffine f.geometricFiber := isAffine_of_isAffineHom f.geometricFiberProj
  have : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := f)
      (Scheme.specAlgebraicClosure k).hom _ _ (.of_hasPullback _ _)
  have : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
    ⟨by rw [← Algebra.ringChar_eq k (AlgebraicClosure k)]; exact Fact.out⟩
  by_cases hd₂ : 2 ≤ d
  · obtain ⟨T, π, hπ, hπe, hT, hdetect⟩ :=
      ProEtale.exists_connected_finiteEtale_irreducibility_detector (d := d)
        f.geometricFiberToAlgebraicClosure (fun _ : Fin 1 ↦ V.obj.carrier) (fun _ ↦ hV)
    have := hπ
    have := hπe
    have := hT
    let S : Finset (Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber) :=
      {f.geometricFiberPointOfFinitePoint x, f.geometricFiberPointOfFinitePoint y}
    have hS : S.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
    have hS' : ∀ s ∈ S, s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ := by
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact geometric_point_over f x
      · obtain rfl := Finset.mem_singleton.mp hs
        exact geometric_point_over f y
    obtain ⟨D, v, hv, hD, hsm, hconn, hpoints, hpull, _⟩ :=
      Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback f hd₂ π S hS hS'
    have := hD
    have := hsm
    have := hconn
    obtain ⟨sx, hsx⟩ := hpoints _ (Finset.mem_insert_self _ _)
    obtain ⟨sy, hsy⟩ := hpoints _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ⟨D, v, hv, hD, hsm, hconn, hdetect D v hpull 0, sx, sy, hsx, hsy⟩
  · have hd₁ : d = 1 := by omega
    subst d
    have hsmid : SmoothOfRelativeDimension 1
        ((𝟙 f.geometricFiber) ≫ f.geometricFiberToAlgebraicClosure) := by
      simpa only [Category.id_comp] using hgeom
    have hirrid : ProEtale.IsIrreducibleAdicLocalSystem
        ((𝟙 f.geometricFiber)^*ᵃ[l].obj V.obj.carrier) :=
      ProEtale.IsIrreducibleAdicLocalSystem.of_iso
        ((ProEtale.adicUpperStarId l _).app _).symm hV
    exact ⟨f.geometricFiber, 𝟙 _, inferInstance, inferInstance, hsmid, inferInstance,
      hirrid, f.geometricFiberPointOfFinitePoint x, f.geometricFiberPointOfFinitePoint y,
      Category.comp_id _, Category.comp_id _⟩

private theorem eigenvalue_of_charpoly_pow
    {K : Type v} [Field K] [IsAlgClosed K]
    {M N : FrobeniusModule.{w, v} K} {α : K} {e : ℕ}
    (hα : M.frobeniusEnd.HasEigenvalue α)
    (h : N.frobeniusEnd.charpoly = (M.frobeniusEnd ^ e).charpoly) :
    N.frobeniusEnd.HasEigenvalue (α ^ e) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, h,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact hα.pow e

/-- Two eigenvalues of a simple lisse subquotient can be tested in one irreducible
constituent on a smooth geometrically connected curve over a finite extension.

Source: current blueprint, `sec-deligne-laumon-general/sk-i-dl-general-real/`
`thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--3 and 7; geometric socle
and Frobenius permutation argument in the first step of `sk-i-dl-general-real`.
(blueprint: lem-zl-pair-eigenvalue-curve-test).

Proof: The nonzero stalks lie on the unique clopen connected component supporting
the simple quotient. Split its geometric components by a finite constant extension.
The geometric socle of the quotient is the whole quotient: its Frobenius translates
span a nonzero Weil subobject. Its geometric simple summands form a single Frobenius
orbit; otherwise an orbit sum is a proper Weil subobject. The multiplicity action
of the stabilizing Frobenius power has an eigenline over the algebraically closed
coefficient field, and simplicity forces multiplicity one. After a further finite
extension every summand has a Weil structure. A local Frobenius is invertible and
permutes the summands. Raising it to a multiple of their orbit lengths identifies
its eigenvalues with eigenvalues on those summands. Choose geometric lifts of the
two given closed points so that the powers of the two selected eigenvalues belong
to the same fixed geometric summand; Frobenius transitivity permits these choices
independently at the two points. Apply irreducibility-preserving two-point curve
testing to this summand, descend the curve and all its maps to one finite constant
extension, and restrict the actual subquotient diagram. Exactness preserves the
monomorphisms and its cokernel. Geometric irreducibility on the curve implies
irreducibility as a lisse Weil object. The local Frobenius comparison gives the
positive powers alpha^e and beta^f, and the residue field tower gives the same
powers of the residue cardinalities. The ambient restricted sheaf is real for
every embedding for which the original is real, since conjugation-stable spectra
remain conjugation-stable under positive integral powers. In dimension zero the
supporting component is Spec of a finite field, and its simple Weil object is one
Frobenius eigenline. Use the constant diagram on the affine line over a finite
extension of that field; its two rational points (allowed to coincide) provide the
required test. Nontrivial Jordan blocks in the ambient object are harmless, since
only the simple quotient and exact restriction are used. The empty base and zero
quotient cannot supply the two assumed eigenvalues. -/
theorem exists_pair_eigenvalue_curve_test
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
      (_ : Fact (ringChar k₁ ≠ l)) (C : Scheme.{u})
      (_ : C.Over (Spec (CommRingCat.of k₁))) (_ : IsAffine C)
      (_ : SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₁)))
      (_ : GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁)))
      (_ : IsSeparated (C ↘ Spec (CommRingCat.of k₁)))
      (_ : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁)))
      (_ : QuasiCompact (C ↘ Spec (CommRingCat.of k₁)))
      (H H₁ H₂ : WeilSheaf k₁ l C) (a : H₁ ⟶ H₂) (b : H₂ ⟶ H)
      (_ : Mono a) (_ : Mono b),
      H.IsLisse ∧ H₁.IsLisse ∧ H₂.IsLisse ∧ (cokernel a).IsIrreducibleLisse ∧
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
  obtain ⟨k₁, hk₁, hfin₁, halg₁, hchar₁, d, Y, hoverY, haffY, hsmY, hconnY,
    hsepY, hlftY, hqcY, F, F₁, F₂, a₁, b₁, ha₁, hb₁, hF, hF₁, hF₂, hgeo,
    hd, hreal₁, x₁, y₁, e₁, f₁, he₁, hf₁, hcardx₁, hcardy₁, hα₁, hβ₁,
    p, hp, hpx, hpy⟩ :=
    exists_pair_eigenvalue_geometric_constituent hG i j h₁ h₂ hirr x y α β hα hβ
  obtain ⟨D, v, hv, hD, hsmD, hconnD, hgeoD, sx, sy, hsx, hsy⟩ :=
    exists_geometric_curve_pair hd (cokernel a₁) hgeo x₁ y₁
  obtain ⟨k₂, hk₂, hfin₂, halg₂, hchar₂, C, hoverC, haffC, hsmC, hconnC,
    hsepC, hlftC, hqcC, H, H₁, H₂, a, b, ha, hb, hH, hH₁, hH₂, hirrH,
    hreal₂, s, t, e₂, f₂, he₂, hf₂, hcards, hcardt, hspecs, hspect, q, hq, hqs, hqt⟩ :=
    exists_geometric_curve_diagram_descent hF a₁ b₁ hF₁ hF₂ x₁ y₁ D v hgeoD sx sy hsx hsy
  let : Algebra k₀ k₂ := ((algebraMap k₁ k₂).comp (algebraMap k₀ k₁)).toAlgebra
  refine ⟨k₂, hk₂, hfin₂, inferInstance, hchar₂, C, hoverC, haffC, hsmC, hconnC,
    hsepC, hlftC, hqcC, H, H₁, H₂, a, b, ha, hb, hH, hH₁, hH₂, hirrH,
    fun ι hreal ↦ hreal₂ ι (hreal₁ ι hreal), s, t, e₁ * e₂, f₁ * f₂,
    Nat.mul_pos he₁ he₂, Nat.mul_pos hf₁ hf₂, ?_, ?_, ?_, ?_, q ≫ p, ?_, ?_, ?_⟩
  · rw [hcards, hcardx₁, pow_mul]
  · rw [hcardt, hcardy₁, pow_mul]
  · simpa only [pow_mul] using eigenvalue_of_charpoly_pow hα₁ hspecs
  · simpa only [pow_mul] using eigenvalue_of_charpoly_pow hβ₁ hspect
  · calc
      (q ≫ p) ≫ (X ↘ Spec (.of k₀)) = q ≫ (p ≫ (X ↘ Spec (.of k₀))) :=
        Category.assoc _ _ _
      _ = q ≫ ((Y ↘ Spec (.of k₁)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) := by rw [hp]
      _ = (q ≫ (Y ↘ Spec (.of k₁))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) := (Category.assoc _ _ _).symm
      _ = ((C ↘ Spec (.of k₂)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) := by rw [hq]
      _ = (C ↘ Spec (.of k₂)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₂)) := by
        rw [Category.assoc, ← Spec.map_comp]
        rfl
  · simpa only [Scheme.Hom.comp_apply, hqs] using hpx
  · simpa only [Scheme.Hom.comp_apply, hqt] using hpy

end AlgebraicGeometry.WeilSheaf

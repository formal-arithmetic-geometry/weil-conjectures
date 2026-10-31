/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealCurve
import WeilConjectures.DeligneLaumon.MarkedGeometricCurveModel
import WeilConjectures.DeligneLaumon.PoweredGeometricPullbackStalk

/-! # Descending an already chosen geometric curve and its lisse diagram

The input includes the geometric curve, both lifted points, and irreducibility
of the restricted geometric quotient. No Bertini or eigenvalue alignment occurs here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

/-- Descend a given geometric closed curve with a geometrically simple restricted
quotient, retaining the two local characteristic-polynomial power comparisons.

Source: current blueprint, `sec-deligne-laumon-general/sk-i-dl-general-real/`
`thm-zl-real-mixed-by-curves.proof.md`, paragraphs 2--3, exact restriction and
residue extensions. (blueprint: lem-zl-geometric-curve-diagram-descent).

Proof: Descend the finite-presentation closed immersion and smooth affine connected
curve to one finite constant field. Smoothness and relative dimension descend
faithfully flatly; connectedness after extension to the algebraic closure gives
geometric connectedness. An affine curve is separated. Both chosen geometric
points map to closed points of this same model: their residue fields are finite
over a finite field. No separate model for each point is necessary.
On the source pro-etale Weil category use the explicit iterated Weil structure
and the geometric-fibre base-change isomorphism, then inverse image along the
descended immersion. Both operations are exact and preserve lissity. Apply them
to the given diagram, obtaining actual monomorphisms and their actual cokernel.
On geometric fibres this cokernel is the given restricted quotient, so geometric
simplicity implies Weil lisse simplicity. Iterate the normalized stalk point
transports around each closed-point orbit. Their composite is conjugate to the
e-th (respectively f-th) power of the original local Frobenius; hence the stated
characteristic polynomials agree, even with Jordan blocks. Here e and f are the
positive residue extension degrees; the field-cardinality tower gives exactly
the two displayed powers. The same calculation at every closed point of the
ambient pullback proves reality for every embedding, since conjugation commutes
with positive powers and preserves multiplicities even when roots collide.
The descended immersion followed by constant projection is c; the two lifted
point equalities give its images x and y. Its structure square is the base-change
square. Coincident points, including different lifts above one point, are allowed. -/
theorem exists_geometric_curve_diagram_descent
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {G : WeilSheaf k₀ l X} (hG : G.IsLisse) {G₁ G₂ : WeilSheaf k₀ l X}
    (i : G₁ ⟶ G₂) (j : G₂ ⟶ G) [Mono i] [Mono j]
    (h₁ : G₁.IsLisse) (h₂ : G₂.IsLisse)
    (x y : X.finitePoints) (D : Scheme.{u})
    (v : D ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [IsClosedImmersion v] [IsAffine D]
    [SmoothOfRelativeDimension 1
      (v ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)]
    [ConnectedSpace D]
    (hgeo : ProEtale.IsIrreducibleAdicLocalSystem
      ((v)^*ᵃ[l].obj (cokernel i).obj.carrier))
    (sx sy : Spec (.of (AlgebraicClosure k₀)) ⟶ D)
    (hsx : sx ≫ v = (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)
    (hsy : sy ≫ v = (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y) :
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
        ((cokernel a).stalk s).frobeniusEnd.charpoly =
          (((cokernel i).stalk x).frobeniusEnd ^ e).charpoly ∧
        ((cokernel a).stalk t).frobeniusEnd.charpoly =
          (((cokernel i).stalk y).frobeniusEnd ^ f).charpoly ∧
        ∃ c : C ⟶ X,
          c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
            (C ↘ Spec (CommRingCat.of k₁)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) ∧
          c s.1 = x.1 ∧ c t.1 = y.1 := by
  obtain ⟨M⟩ := exists_marked_geometric_curve_model (l := l) x y D v sx sy hsx hsy
  let k₁ := M.k₁
  let hk₁ := M.field₁
  let hfin₁ := M.finite₁
  let halg₁ := M.algebra₁
  let hchar₁ := M.char₁
  let C := M.C
  let hoverC := M.overC
  let haffC := M.affineC
  let hsmC := M.smoothC
  let hconnC := M.connectedC
  let hsepC := M.separatedC
  let hlftC := M.finiteTypeC
  let hqcC := M.quasiCompactC
  let r := M.r
  have hr := M.positive
  have hcard := M.cardinality
  let τ := M.τ
  let c := M.c
  let u := M.u
  let z := M.z
  have hτ := M.τ_comm
  have hc := M.structure_comm
  have hup := M.projection_comm
  have huτ := M.closure_comm
  have hu := M.frobenius_comm
  have hzu := M.immersion_comm
  let s := M.s
  let t := M.t
  have hcs := M.image_s
  have hct := M.image_t
  obtain ⟨P, hlim, hcol, hP⟩ := exists_poweredGeometricPullback (l := l) u r hu
  have : PreservesFiniteLimits P := hlim
  have : PreservesFiniteColimits P := hcol
  have : P.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object (F := P)
  have hcarrier (A : WeilSheaf k₀ l X) :
      (P.obj A).obj.carrier = (u)^*ᵃ[l].obj A.obj.carrier := by
    rw [← hP]
    exact poweredGeometricPullback_obj_carrier u r hu A
  have hlisse {A : WeilSheaf k₀ l X} (hA : A.IsLisse) : (P.obj A).IsLisse := by
    rw [← hP]
    exact poweredGeometricPullback_isLisse u r hu hA
  let H := P.obj G
  let H₁ := P.obj G₁
  let H₂ := P.obj G₂
  let a := P.map i
  let b := P.map j
  have ha : Mono a := inferInstance
  have hb : Mono b := inferInstance
  let Q := cokernel i
  let q := exactFunctorCokernelIso P i
  have hPQ : ProEtale.IsIrreducibleAdicLocalSystem (P.obj Q).obj.carrier := by
    rw [hcarrier]
    exact isIrreducibleAdicLocalSystem_of_iso_composite z u v hzu Q.obj.carrier hgeo
  have hirr : (cokernel a).IsIrreducibleLisse :=
    isIrreducibleLisse_of_geometric_iso q hPQ
  have hreal : ∀ ι : PadicAlgCl l →+* ℂ, G.IsReal ι → H.IsReal ι := by
    intro ι hGreal w
    obtain ⟨xw, ew, _, _, _, hw⟩ :=
      poweredGeometricPullback_stalk (l := l) r hr hcard τ hτ c hc u hup huτ hu w
    apply (hGreal xw).of_charpoly_eq_pow ew
    have h := congrArg (fun F : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C ↦
      ((F.obj G).stalk w).frobeniusEnd.charpoly) hP
    exact h.symm.trans (hw G)
  obtain ⟨xs, e, hxs, he, hcards, hspecs⟩ :=
    poweredGeometricPullback_stalk (l := l) r hr hcard τ hτ c hc u hup huτ hu s
  obtain ⟨xt, f, hxt, hf, hcardt, hspect⟩ :=
    poweredGeometricPullback_stalk (l := l) r hr hcard τ hτ c hc u hup huτ hu t
  have hxs' : xs = x := Subtype.ext (hxs.symm.trans hcs)
  have hxt' : xt = y := Subtype.ext (hxt.symm.trans hct)
  have hcards' := hcards.trans
    (congrArg (fun a : X.finitePoints ↦
      (X ↘ Spec (.of k₀)).residueCard a.1 ^ e) hxs')
  have hcardt' := hcardt.trans
    (congrArg (fun a : X.finitePoints ↦
      (X ↘ Spec (.of k₀)).residueCard a.1 ^ f) hxt')
  refine ⟨k₁, hk₁, hfin₁, halg₁, hchar₁, C, hoverC, haffC, hsmC, hconnC,
    hsepC, hlftC, hqcC, H, H₁, H₂, a, b, ha, hb,
    hlisse hG, hlisse h₁, hlisse h₂,
    hirr, hreal, s, t, e, f, he, hf, hcards', hcardt', ?_, ?_, c, hc, hcs, hct⟩
  · apply ((nonempty_equiv_stalk_of_iso q s).some.charpoly_frobeniusEnd).trans
    have hs : ((P.obj Q).stalk s).frobeniusEnd.charpoly =
        ((Q.stalk xs).frobeniusEnd ^ e).charpoly := by
      have h := congrArg (fun F : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C ↦
        ((F.obj Q).stalk s).frobeniusEnd.charpoly) hP
      exact h.symm.trans (hspecs Q)
    exact hs.trans (congrArg (fun a : X.finitePoints ↦
      ((Q.stalk a).frobeniusEnd ^ e).charpoly) hxs')
  · apply ((nonempty_equiv_stalk_of_iso q t).some.charpoly_frobeniusEnd).trans
    have ht : ((P.obj Q).stalk t).frobeniusEnd.charpoly =
        ((Q.stalk xt).frobeniusEnd ^ f).charpoly := by
      have h := congrArg (fun F : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C ↦
        ((F.obj Q).stalk t).frobeniusEnd.charpoly) hP
      exact h.symm.trans (hspect Q)
    exact ht.trans (congrArg (fun a : X.finitePoints ↦
      ((Q.stalk a).frobeniusEnd ^ f).charpoly) hxt')

end AlgebraicGeometry.WeilSheaf

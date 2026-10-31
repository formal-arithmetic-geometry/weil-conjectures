/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Idempotents
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.Mathlib.RingTheory.TotallySplit
import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting
import WeilConjectures.RingTheory.FiniteInertiaModel
import WeilConjectures.RingTheory.InvariantGeometricOrbit
import WeilConjectures.RingTheory.InertiaIdempotentPrincipalRefinement

/-!
# An inertia component after etale base change

Source: Stacks Project, Tag 0BST, the equivariant idempotent refinement in the proof of
`lemma-inertia-invariants-etale` (blueprint: lem-dl-a1-inertia-orbit-idempotents).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open scoped TensorProduct

namespace Ideal

/-- After an etale base change, one component through the selected geometric point has
stabilizer exactly inertia and its distinct translates partition the whole ring.
Source: Stacks Project, Tag 0BST, middle and final paragraphs.
(blueprint: lem-dl-a1-inertia-orbit-idempotents).

Proof:
1. Choose a finite G-stable C-subalgebra D of R detecting inertia, by adjoining finite
orbits of witnesses to failure of membership in inertia. Its invariant ring is still C.
The contraction qD has exactly the original inertia.
2. The geometric points of D extending the selected base point are transitive under G.
Apply the finite-algebra theorem isolating one geometric point by an idempotent after
an etale base change A0 of C.
3. Apply the principal refinement theorem: products of translates and complements make
an inertia-fixed idempotent whose distinct coset translates are orthogonal. Their
complement vanishes at every geometric point. Shrinking the base once kills that
complement, so the translates become complete. The selected point extends to the
localization A of A0, which remains etale over C.
4. Map the idempotent family from A tensor D into A tensor R. Ring maps preserve all
orthogonality and sum identities, and equivariance preserves the inertia-fixed property.
The tensor-product map to Ω extends the original point and sends the chosen idempotent
to one. No finiteness assumption on R over C has been added. -/
theorem exists_etale_inertia_orbit_idempotents
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G C R] [Algebra.IsInvariant C R G]
    (q : Ideal R) [q.IsPrime]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : R →+* Ω) (hη : RingHom.ker η = q) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra C A) (_ : Algebra.Etale C A),
      ∃ θ : A ⊗[C] R →+* Ω,
        θ.comp (Algebra.TensorProduct.includeRight (R := C) (A := A) (B := R)).toRingHom = η ∧
        ∃ (e : A ⊗[C] R) (n : ℕ) (r : Fin n → G),
          IsIdempotentElem e ∧ θ e = 1 ∧
          (∀ h : q.inertia G,
            AlgHom.baseChangeFamily A (MulSemiringAction.toAlgHom C R) h.val e = e) ∧
          (∀ g : G, ∃ (i : Fin n) (h : q.inertia G), g = r i * h.val) ∧
          CompleteOrthogonalIdempotents
            (fun i ↦ AlgHom.baseChangeFamily A (MulSemiringAction.toAlgHom C R) (r i) e) := by
  classical
  obtain ⟨D, hD, hstable, hdetect⟩ := exists_finite_inertia_model C R G q
  have : Module.Finite C D := hD
  let : MulSemiringAction G D :=
    { smul g x := ⟨g • (x : R), hstable g x x.2⟩
      one_smul x := Subtype.ext (one_smul G (x : R))
      mul_smul g h x := Subtype.ext (mul_smul g h (x : R))
      smul_zero g := Subtype.ext (smul_zero g)
      smul_add g x y := Subtype.ext (smul_add g (x : R) (y : R))
      smul_one g := Subtype.ext (smul_one g)
      smul_mul g x y := Subtype.ext (smul_mul' g (x : R) (y : R)) }
  have : SMulCommClass G C D := ⟨fun g c x ↦ Subtype.ext (smul_comm g c (x : R))⟩
  have : Algebra.IsInvariant C D G := ⟨by
    intro x hx
    obtain ⟨c, hc⟩ := Algebra.IsInvariant.isInvariant (A := C) (x : R)
      (fun g ↦ congrArg Subtype.val (hx g))
    exact ⟨c, Subtype.ext hc⟩⟩
  let qD : Ideal D := q.comap D.val.toRingHom
  have : qD.IsPrime := Ideal.IsPrime.comap D.val.toRingHom
  let ηD : D →+* Ω := η.comp D.val.toRingHom
  have hηD : RingHom.ker ηD = qD := by
    ext x
    exact Iff.of_eq (congrArg (fun J : Ideal R ↦ (x : R) ∈ J) hη)
  have hI : qD.inertia G = q.inertia G := by
    ext g
    constructor
    · intro hg
      exact hdetect g hg
    · intro hg
      change ∀ x : D, g • (x : R) - (x : R) ∈ q
      exact fun x ↦ hg (x : R)
  let φ : C →+* Ω := ηD.comp (algebraMap C D)
  let t : RingHom.PointsOver φ D := ⟨ηD, rfl⟩
  have htrans : ∀ s : RingHom.PointsOver φ D,
      ∃ g : G, ∀ x : D, s x = ηD (g • x) := by
    intro s
    exact RingHom.PointsOver.exists_smul_of_isInvariant C D G Ω φ s t
  obtain ⟨A0, _, _, hA0, α, hα, e0, he0, ht0, huniq0⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_eq φ t
  obtain ⟨a, ha, α', hα', hαA, eD, n, r, heD, htD, hHD, hrD, hcD⟩ :=
    exists_inertia_idempotent_principal_refinement C D G qD Ω ηD hηD htrans
      A0 α hα e0 he0 ht0 huniq0
  let A := Localization.Away a
  have : Algebra.Etale C A := Algebra.Etale.comp C A0 A
  let f : A ⊗[C] D →ₐ[A] A ⊗[C] R :=
    Algebra.TensorProduct.map (AlgHom.id A A) D.val
  let : Algebra C Ω := (η.comp (algebraMap C R)).toAlgebra
  let ηAlg : R →ₐ[C] Ω := { η with commutes' := fun _ ↦ rfl }
  let αAlg : A →ₐ[C] Ω := { α' with commutes' := fun c ↦ RingHom.congr_fun hα' c }
  let θ : A ⊗[C] R →ₐ[C] Ω :=
    Algebra.TensorProduct.lift αAlg ηAlg (fun _ _ ↦ Commute.all _ _)
  have hθ : θ.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := C) (A := A) (B := R)).toRingHom = η := by
    ext x
    simp [θ, ηAlg]
  have hθf (x : A ⊗[C] D) : θ (f x) = (t.tensor hα') x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b d =>
      change α' b * η (d : R) = α' b * ηD d
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hf (g : G) (x : A ⊗[C] D) :
      f (AlgHom.baseChangeFamily A (MulSemiringAction.toAlgHom C D) g x) =
        AlgHom.baseChangeFamily A (MulSemiringAction.toAlgHom C R) g (f x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b d => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨A, inferInstance, inferInstance, inferInstance, θ.toRingHom, hθ,
    f eD, n, r, heD.map f, ?_, ?_, ?_, ?_⟩
  · exact (hθf eD).trans htD
  · intro h
    let hD : qD.inertia G := ⟨h.val, by simpa only [hI] using h.2⟩
    exact (hf h.val eD).symm.trans (congrArg f (hHD hD))
  · intro g
    obtain ⟨i, h, hh⟩ := hrD g
    exact ⟨i, ⟨h.val, by simpa only [hI] using h.2⟩, hh⟩
  · have hh : (fun i ↦ AlgHom.baseChangeFamily A
        (MulSemiringAction.toAlgHom C R) (r i) (f eD)) =
        fun i ↦ f (AlgHom.baseChangeFamily A (MulSemiringAction.toAlgHom C D) (r i) eD) :=
      funext fun i ↦ (hf (r i) eD).symm
    rw [hh]
    exact hcD.map f.toRingHom

end Ideal

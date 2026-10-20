/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.KummerLineGeometry
import Sheaf.AlgebraicGeometry.KummerFiniteFreeComparison
import Sheaf.AlgebraicGeometry.KummerRootLineComputation

/-!
# Kummer computations on the affine and punctured lines

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/thm-pur-kummer-affine-line,
Degrees 0 and 1 and Coefficients; Stacks Project, Tags 03PK, 03PL, 03SC and 01FT
(blueprint: thm-pur-kummer-affine-line).

The Boolean index is false for Spec k[t] and true for Spec k[t,t⁻¹]. The residue ring
is lifted to the coefficient universe; this changes neither its modules nor its scalars.
All cohomology is the existing abelian étale sheaf cohomology, with its unique residue-ring
action. The restriction map is characterized on the coefficient tensors, which generate
by the asserted coefficient comparison. Thus its characterization determines the actual
restriction map uniquely, including for the zero module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.KummerLine

private lemma exponent_isUnit (k : Type u) [Field k] (ℓ N : ℕ)
    (hℓk : IsUnit (ℓ : k)) (b : Bool) :
    IsUnit ((ℓ ^ N : ℕ) : Γ(curve k b, ⊤)) := by
  simpa only [map_pow, map_natCast, Nat.cast_pow] using
    (hℓk.pow N).map (scalar k b)

private def residueLinearMap (m : ℕ) {M P : Type (u + 1)}
    [AddCommGroup M] [AddCommGroup P]
    [Module (ULift.{u + 1} (ZMod m)) M] [Module (ULift.{u + 1} (ZMod m)) P]
    (f : M →+ P) : M →ₗ[ULift.{u + 1} (ZMod m)] P :=
  { f with
    map_smul' := by
      intro r x
      have hr : r = ((ZMod.cast r.down : ℤ) : ULift.{u + 1} (ZMod m)) := by
        apply ULift.ext
        exact (ZMod.intCast_zmod_cast r.down).symm
      change f (r • x) = r • f x
      rw [hr, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul] }

-- Keep the connecting map folded while elaborating coefficient formulas.
attribute [local irreducible] generator

/-- Kummer computations with all finite free module coefficients, their canonical degree-zero
sections and degree-one generator, naturality, and finite free coefficient extension.
Source: blueprint thm-pur-kummer-affine-line; Stacks, Tags 03PK, 03PL, 03SC and 01FT
(blueprint: thm-pur-kummer-affine-line).

Proof: (1) Both schemes are smooth affine connected curves [def-sc-curves]. Apply
 [lem-sc-affine-cohomological-dimension] to the m-torsion roots sheaf to kill degrees above one.
(2) The exact Kummer sequence and its cohomology sequence identify H⁰ with the kernel
 of the power map on units and H¹ with its cokernel, since the Picard groups vanish.
 Use [lem-sc-kummer-exact], [def-sc-kummer-sequence], [def-weil-pbc-sites-and-cohomology],
 [lem-weil-pbc-derived-functor-long-exact], [lem-sc-h1-gm-pic], and
 [lem-pur-affine-punctured-line-algebra].
(3) The units are kˣ on the line and kˣ times t^Z on the punctured line. Both kernels are
 μ_m(k); the primitive root identifies them with R, compatibly with restriction.
 Use [lem-pur-affine-punctured-line-algebra] and [lem-sc-primitive-root].
(4) Divisibility of kˣ kills the first cokernel; the second is Z/m, with inverse sending
 1 to δ(t). The Laurent exponent computes this quotient and fixes the sign of the generator.
 These are the unit quotients of [lem-pur-affine-punctured-line-algebra].
(5) A finite basis of A identifies its twist with a finite sum of μ_m. Finite sums preserve
 injective resolutions, global sections and homology, proving the coefficient comparison.
 Its pure-tensor formula is basis independent and natural because i_a followed by a
 coefficient map f equals i_(f a). This includes the empty basis. Use
 [def-pur-sheaf-tensor-product], [def-weil-pbc-sites-and-cohomology], and
 [def-sp-injective-resolutions].
(6) Tensor the root computation with A. The surviving groups are A and hence finite;
 H¹ on the punctured line is free of the same rank as A. Root restriction and coefficient
 comparison determine restriction on coefficients, so its degree-zero map is the identity.
 Finally apply coefficient comparison to A and A ⊗ S and tensor associativity. Its formula
 on x ⊗ a ⊗ s gives the displayed scalar-extension compatibility and the Kummer formula. -/
theorem kummer_affine_line (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (hN : 1 ≤ N)
    (ζ : kˣ) (hζ : IsPrimitiveRoot ζ (ℓ ^ N)) :
    ∃ (hm : IsUnit ((ℓ ^ N : ℕ) : Γ(curve k true, ⊤)))
      (z : (b : Bool) → Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) 0),
      (∀ b : Bool,
        (kernel.ι (ℓ ^ N • 𝟙 (curve k b).gmSheaf)).hom.app
            (op (Scheme.Etale.mk (𝟙 (curve k b))))
            (Sheaf.H.equiv₀ ((curve k b).rootsOfUnitySheaf (ℓ ^ N))
              (MorphismProperty.Over.mkIdTerminal @Etale (curve k b)) (z b)) =
          ULift.up (Additive.ofMul (Units.map (scalar k b).toMonoidHom ζ))) ∧
      rootRestriction k (ℓ ^ N) 0 (z false) = z true ∧
      (∀ (b : Bool) (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ N)))),
        Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) A →
        Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) A →
        (∃ e : A ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
            Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) 0,
          ∀ a : A, e a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a) 0 (z b)) ∧
        (∀ q : ℕ, (if b then 1 else 0) < q →
          Subsingleton (Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q)) ∧
        (∀ q : ℕ, Finite
          (Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q)) ∧
        (∀ q : ℕ, ∃ e :
            (Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))]
              A) ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
                Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q,
          ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A),
            e (x ⊗ₜ a) = Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a) q x) ∧
        (∀ (B : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ N))))
            [Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) B]
            [Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) B]
            (f : A →ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))] B)
            (q : ℕ) (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A),
          Sheaf.H.map ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).map
              (ModuleCat.ofHom f)) q
              (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a) q x) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) B (f a)) q x) ∧
        (∀ (S : Type (u + 1)) [CommRing S] [Algebra (ULift.{u + 1} (ZMod (ℓ ^ N))) S]
            [Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) S]
            [Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) S] (q : ℕ),
          ∃ e : (Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q
              ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))] S) ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
            Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj
              (ModuleCat.of _ (A ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))] S))) q,
          ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A) (s : S),
            e ((Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a)
              q x) ⊗ₜ s) = Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
                (ModuleCat.of _ (A ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))] S)) (a ⊗ₜ s)) q x)) ∧
      (∀ (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ N))))
          [Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) A]
          [Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) A],
        (∃ e : A ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
            Sheaf.H ((Scheme.kummerAbelianTwist (curve k true) (ℓ ^ N)).obj A) 1,
          ∀ a : A, e a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N) A a) 1
            (generator k (ℓ ^ N) hm)) ∧
        ∃! res : Sheaf.H ((Scheme.kummerAbelianTwist (curve k false) (ℓ ^ N)).obj A) 0
            →ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
              Sheaf.H ((Scheme.kummerAbelianTwist (curve k true) (ℓ ^ N)).obj A) 0,
          (∀ (x : Sheaf.H ((curve k false).rootsOfUnitySheaf (ℓ ^ N)) 0) (a : A),
            res (Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k false) (ℓ ^ N) A a) 0 x) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N) A a) 0
              (rootRestriction k (ℓ ^ N) 0 x)) ∧
          (∀ a : A, res (Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k false) (ℓ ^ N) A a) 0 (z false)) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N) A a)
              0 (z true)))  := by
  classical
  let m := ℓ ^ N
  let R := ULift.{u + 1} (ZMod m)
  have hmpos : 1 ≤ m := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hN
    simpa only [m, hn] using Nat.one_le_pow (1 + n) ℓ hℓ.pos
  let : NeZero m := ⟨by omega⟩
  have hmk : IsUnit (m : k) := by simpa [m] using hℓk.pow N
  let hm := exponent_isUnit k ℓ N hℓk true
  obtain ⟨z, hz, hres, he0, hvan, he1⟩ :=
    kummer_root_line_computation k m hmpos hmk ζ hζ hm
  have cmp (b : Bool) (A : ModuleCat.{u + 1} R)
      [Module.Free R A] [Module.Finite R A] (q : ℕ) :
      ∃ e : (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q ⊗[R] A) ≃ₗ[R]
        Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) m).obj A) q,
        ∀ x a, e (x ⊗ₜ a) = Sheaf.H.map
          (Scheme.kummerCoefficientInsertion (curve k b) m A a) q x := by
    obtain ⟨e, he⟩ := Scheme.kummer_finite_free_comparison (curve k b) m A
    exact ⟨e q, he q⟩
  have gen (b : Bool) (q : ℕ) (w : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
      (ew : R ≃ₗ[R] Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) (hw : ew 1 = w)
      (A : ModuleCat.{u + 1} R) [Module.Free R A] [Module.Finite R A] :
      ∃ e : A ≃ₗ[R] Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) m).obj A) q,
        ∀ a : A, e a = Sheaf.H.map
          (Scheme.kummerCoefficientInsertion (curve k b) m A a) q w := by
    obtain ⟨ec, hc⟩ := cmp b A q
    refine ⟨(TensorProduct.lid R A).symm ≪≫ₗ
      TensorProduct.congr ew (LinearEquiv.refl R A) ≪≫ₗ ec, ?_⟩
    intro a
    simpa only [LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, hw] using hc w a
  have deg0 (b : Bool) (A : ModuleCat.{u + 1} R)
      [Module.Free R A] [Module.Finite R A] :=
    gen b 0 (z b) (he0 b).choose (he0 b).choose_spec A
  refine ⟨hm, z, hz, hres, ?_, ?_⟩
  · intro b A hfree hfinite
    let := hfree
    let := hfinite
    refine ⟨deg0 b A, ?_, ?_, cmp b A, ?_, ?_⟩
    · intro q hq
      let := hvan b q hq
      obtain ⟨ec, _⟩ := cmp b A q
      exact ec.symm.injective.subsingleton
    · intro q
      have rootFinite : Finite (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) := by
        by_cases hq : q = 0
        · subst q
          exact Finite.of_surjective (he0 b).choose (he0 b).choose.surjective
        · cases b
          · let := hvan false q (by simpa using Nat.pos_of_ne_zero hq)
            infer_instance
          · by_cases hq1 : q = 1
            · subst q
              exact Finite.of_surjective he1.choose he1.choose.surjective
            · let := hvan true q (by simp only [↓reduceIte]; omega)
              infer_instance
      let := rootFinite
      let : Module.Finite R (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) :=
        Module.Finite.of_finite
      have : Finite (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q ⊗[R] A) :=
        Module.finite_of_finite R
      obtain ⟨ec, _⟩ := cmp b A q
      exact Finite.of_surjective ec ec.surjective
    · intro B _ _ f q x a
      rw [← Sheaf.H.map_comp_apply]
      apply congrArg (fun g ↦ Sheaf.H.map g q x)
      apply Sheaf.hom_ext
      ext U y
      let η := (curve k b).kummerRootModulePresheaf m ◁
        (Functor.const (curve k b).Etaleᵒᵖ).map (ModuleCat.ofHom f)
      have h := congrArg (fun g ↦ g.app U)
        (toSheafify_naturality (curve k b).smallEtaleTopology η)
      exact (congrArg (fun g ↦ g (y ⊗ₜ[R] a)) h).symm
    · intro S _ _ _ _ q
      obtain ⟨ec, hc⟩ := cmp b A q
      obtain ⟨ed, hd⟩ := cmp b (ModuleCat.of R (A ⊗[R] S)) q
      refine ⟨TensorProduct.congr ec.symm (LinearEquiv.refl R S) ≪≫ₗ
        TensorProduct.assoc R _ A S ≪≫ₗ ed, ?_⟩
      intro x a s
      change ed ((TensorProduct.assoc R _ A S) (ec.symm _ ⊗ₜ s)) = _
      rw [← hc x a, LinearEquiv.symm_apply_apply, TensorProduct.assoc_tmul]
      exact hd x (a ⊗ₜ s)
  · intro A _ _
    refine ⟨gen true 1 _ he1.choose he1.choose_spec A, ?_⟩
    obtain ⟨ef, hf⟩ := cmp false A 0
    obtain ⟨et, ht⟩ := cmp true A 0
    let r := residueLinearMap m (rootRestriction k m 0)
    let res := et.toLinearMap.comp ((TensorProduct.map r LinearMap.id).comp
      ef.symm.toLinearMap)
    have hformula (x : Sheaf.H ((curve k false).rootsOfUnitySheaf m) 0) (a : A) :
        res (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k false) m A a) 0 x) =
          Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) m A a) 0
            (rootRestriction k m 0 x) := by
      change et (TensorProduct.map r LinearMap.id (ef.symm _)) = _
      rw [← hf, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
      exact ht _ _
    refine ⟨res, ⟨hformula, ?_⟩, ?_⟩
    · intro a
      rw [hformula, hres]
    · intro other ho
      apply LinearMap.ext
      intro y
      obtain ⟨t, rfl⟩ := ef.surjective y
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x a => rw [hf, ho.1, hformula]
      | add x y hx hy => simp only [map_add, hx, hy]

end AlgebraicGeometry.KummerLine

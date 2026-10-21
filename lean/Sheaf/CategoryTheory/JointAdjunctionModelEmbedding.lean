module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Joint adjunction model embeddings

Source: blueprint main-20261015, `sk-lem-brown-hypotheses-small.proof.md`,
Essentially small paragraph, global gluing from stratum restrictions;
Stacks Tags 0037, 0106 and 00ZY for the categorical argument.
(blueprint: lem-sfb-joint-adjunction-model-embedding)
-/

set_option autoImplicit false

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

/-- Adjoint maps to prescribed isomorphic local models give a monomorphism into their product.

Source: blueprint main-20261015, `sk-lem-brown-hypotheses-small.proof.md`,
Essentially small paragraph, global gluing; Stacks Tags 0037, 0106 and 00ZY.
(blueprint: lem-sfb-joint-adjunction-model-embedding)

Proof:
1. Take a kernel `k : K ⟶ M` of the displayed product map. The product equations imply
   `k ≫ (adj i).unit.app M ≫ (G i).map (e i).hom = 0` for every `i`.
2. Under the specified adjunction Hom bijection, naturality identifies the adjuncts of
   `(F i).map k ≫ (e i).hom` and `(F i).map (0 : K ⟶ M) ≫ (e i).hom` with zero.
   Injectivity of the bijection, additivity, and cancellation of `e i` give `(F i).map k = 0`.
3. Kernel preservation makes this zero arrow a kernel of the image of the product map.
   Uniqueness of kernel factorization identifies the identity and zero on `(F i).obj K`,
   so `(F i).obj K` is a zero object.
4. Joint zero detection makes `K` zero, and bilinearity gives `k = 0`.
5. If two arrows become equal after the product map, their difference factors through `k`.
   Thus their difference is zero, proving the cancellation property of a monomorphism. -/
theorem mono_pi_lift_adjunction_models
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {I : Type w} {B : I → Type u₂} [∀ i : I, Category.{v₂} (B i)]
    [∀ i : I, Abelian (B i)]
    (F : ∀ i : I, A ⥤ B i) [∀ i : I, (F i).Additive]
    [∀ (i : I) (X Y : A) (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (F i)]
    (G : ∀ i : I, B i ⥤ A) (adj : ∀ i : I, F i ⊣ G i)
    (hzero : ∀ N : A, (∀ i : I, IsZero ((F i).obj N)) → IsZero N)
    (M : A) (models : ∀ i : I, B i) (e : ∀ i : I, (F i).obj M ≅ models i)
    [HasProduct (fun i : I ↦ (G i).obj (models i))] :
    Mono (Pi.lift (fun i : I ↦ (adj i).unit.app M ≫ (G i).map (e i).hom)) := by
  let u := Pi.lift (fun i : I ↦ (adj i).unit.app M ≫ (G i).map (e i).hom)
  apply Preadditive.mono_of_isZero_kernel u
  apply hzero
  intro i
  have hk : kernel.ι u ≫ (adj i).unit.app M ≫ (G i).map (e i).hom = 0 := by
    calc
      _ = (kernel.ι u ≫ u) ≫ Pi.π (fun i : I ↦ (G i).obj (models i)) i := by
        simp only [Category.assoc, u, Pi.lift_π]
      _ = 0 := by simp
  have hmap : (F i).map (kernel.ι u) = 0 := by
    have heq : (F i).map (kernel.ι u) ≫ (e i).hom =
        (F i).map (0 : kernel u ⟶ M) ≫ (e i).hom := by
      apply ((adj i).homEquiv (kernel u) (models i)).injective
      rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
        Adjunction.homEquiv_apply, zero_comp]
      exact hk
    simpa using (cancel_mono (e i).hom).mp heq
  have hlim := isLimitOfHasKernelOfPreservesLimit (F i) u
  have : Mono ((F i).map (kernel.ι u)) := mono_of_isLimit_fork hlim
  exact IsZero.of_mono_eq_zero _ hmap

/-- The map with the adjunction units as components is monic whenever its product exists.

Source: blueprint main-20261015, `sk-lem-brown-hypotheses-small.proof.md`,
Essentially small paragraph, the adjunction-unit embedding.
(blueprint: lem-sfb-joint-adjunction-model-embedding)

Proof (step 6 of the node): apply the local-model assertion with `models i = (F i).obj M`
and `e i` the identity isomorphism. Functors preserve identity arrows, so the components
reduce to `(adj i).unit.app M`. -/
theorem mono_pi_lift_adjunction_units
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {I : Type w} {B : I → Type u₂} [∀ i : I, Category.{v₂} (B i)]
    [∀ i : I, Abelian (B i)]
    (F : ∀ i : I, A ⥤ B i) [∀ i : I, (F i).Additive]
    [∀ (i : I) (X Y : A) (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (F i)]
    (G : ∀ i : I, B i ⥤ A) (adj : ∀ i : I, F i ⊣ G i)
    (hzero : ∀ N : A, (∀ i : I, IsZero ((F i).obj N)) → IsZero N)
    (M : A) [HasProduct (fun i : I ↦ (G i).obj ((F i).obj M))] :
    Mono (Pi.lift (f := fun i : I ↦ (G i).obj ((F i).obj M))
      (fun i : I ↦ (adj i).unit.app M)) := by
  simpa using mono_pi_lift_adjunction_models F G adj hzero M
    (fun i : I ↦ (F i).obj M) (fun i : I ↦ Iso.refl ((F i).obj M))

end CategoryTheory

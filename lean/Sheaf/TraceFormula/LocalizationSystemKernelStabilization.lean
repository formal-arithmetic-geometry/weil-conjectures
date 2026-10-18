import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finitely generated kernels stabilize in a directed system of module localizations

Source: literature/stacks-project/algebra.tex, Algebra Tag 046Y
(blueprint: lem-trf-localization-system-kernel-stabilization).
-/

universe uI uD uP uQ uR

/--
Let `I` be a small nonempty directed set, with a directed system of commutative rings
`D i`, modules `P i`, and semilinear transition maps.  Let `P` be the compatible
module colimit of the underlying abelian groups, and assume every transition is a
localization.  If the kernel at one stage is finitely generated, all sufficiently
late maps to `P` are injective.

Source: Stacks Project, Algebra, Tag 046Y, middle proof paragraph (finite kernel
generators and denominator argument); Tag 00D7 for eventual vanishing; Tag 07JZ
for fractions (blueprint: lem-trf-localization-system-kernel-stabilization).
The proof follows four steps: choose generators and kill each in a later stage;
choose one common upper bound and kill the whole kernel; represent a later kernel
element by a fraction from the initial stage; use the cocone and linearity identities
to put its numerator in the killed kernel and conclude the element is zero.
-/
theorem localization_system_kernel_stabilization
    (I : Type uI) [Preorder I] [Nonempty I]
    (directed : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
    (D : I → Type uD) [∀ i, CommRing (D i)]
    (d : ∀ i j : I, i ≤ j → D i →+* D j)
    (d_id : ∀ i : I, d i i (le_refl i) = RingHom.id (D i))
    (d_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      (d j k hjk).comp (d i j hij) = d i k (hij.trans hjk))
    (P : I → Type uP) [∀ i, AddCommGroup (P i)]
    (moduleP : ∀ i : I, Module (D i) (P i))
    (p : ∀ i j : I, i ≤ j → P i →+ P j)
    (p_id : ∀ i : I, p i i (le_refl i) = AddMonoidHom.id (P i))
    (p_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      (p j k hjk).comp (p i j hij) = p i k (hij.trans hjk))
    (p_semilinear : ∀ i j (hij : i ≤ j) (a : D i) (x : P i),
      p i j hij (a • x) = d i j hij a • p i j hij x)
    (Q : Type uQ) [AddCommGroup Q]
    (moduleQ : ∀ i : I, Module (D i) Q)
    (q_smul_compat : ∀ i j (hij : i ≤ j) (a : D i) (x : Q),
      d i j hij a • x = a • x)
    (psi : ∀ i : I, P i →ₗ[D i] Q)
    (psi_compat : ∀ i j (hij : i ≤ j),
      (psi j).toAddMonoidHom.comp (p i j hij) = (psi i).toAddMonoidHom)
    (cocone : ∀ (R : Type uR) [AddCommGroup R]
      (f : ∀ i : I, P i →+ R)
      (hf : ∀ i j (hij : i ≤ j), (f j).comp (p i j hij) = f i),
      ∃! g : Q →+ R, ∀ i : I, g.comp (psi i).toAddMonoidHom = f i)
    (i₀ : I)
    (finite_kernel : Module.Finite (D i₀) (LinearMap.ker (psi i₀)))
    (W : ∀ i j : I, i ≤ j → Submonoid (D i))
    (W_one : ∀ i j (hij : i ≤ j), (1 : D i) ∈ W i j hij)
    (W_mul : ∀ i j (hij : i ≤ j) (a b : D i), a ∈ W i j hij → b ∈ W i j hij →
      a * b ∈ W i j hij)
    (d_localization : ∀ i j (hij : i ≤ j),
      letI : Algebra (D i) (D j) := (d i j hij).toAlgebra
      IsLocalization (W i j hij) (D j))
    (localization_equiv : ∀ i j (hij : i ≤ j),
      letI : Algebra (D i) (D j) := (d i j hij).toAlgebra
      letI : IsLocalization (W i j hij) (D j) := d_localization i j hij
      letI : Module (D i) (P i) := moduleP i
      letI : Module (D j) (P j) := moduleP j
      letI : Module (D j) (LocalizedModule (W i j hij) (P i)) :=
        LocalizedModule.moduleOfIsLocalization (S := W i j hij) (T := D j)
      ∃ e : LocalizedModule (W i j hij) (P i) ≃ₗ[D j] P j,
        ∀ (m : P i) (s : W i j hij),
          ∃ u : D j, d i j hij (s : D i) * u = 1 ∧
            e (LocalizedModule.mk m s) = u • p i j hij m) :
    ∃ j : I, i₀ ≤ j ∧ ∀ l : I, j ≤ l → Function.Injective (psi l) := by
  sorry

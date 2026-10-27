module

public import Sheaf.AlgebraicGeometry.ArtinRSTangentTensor
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.CategoryTheory.Endomorphism
import Sheaf.CategoryTheory.ProductPreservingVectorFunctorLinearization
import Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Noetherian.Defs

/-! # Infinitesimal automorphisms and reduction kernels

Source: Stacks Project, Formal Deformation Theory, Tags 06JU, 06JV, 06JX and 06JY
(blueprint: lem-sfb-schlessinger-automorphism-kernel).

The vector space is the actual automorphism group of the transported residue
object. Its scalar operation uses square-zero transport and the pseudofunctor's
composition constraint. The torsor is on the kernel of the actual reduction map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {k : Type u} [Field k]

/-- The coefficient-field inclusion into a marked Artinian k-algebra.
Source: Stacks, Tags 06GC and 06JX
(blueprint: lem-sfb-schlessinger-automorphism-kernel). -/
def testFieldInclusion (A : TestCategory k k) : residueTest ⟶ A :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom (Algebra.ofId k (ring A)))
    (CommAlgCat.hom_ext (by
      change (_ : k →ₐ[k] k) = _
      exact Subsingleton.elim _ _)))

/-- Transport of the chosen residue object to a marked test algebra.
Source: Stacks, Tags 06JU and 06JX
(blueprint: lem-sfb-schlessinger-automorphism-kernel). -/
def testBasePoint (D : CofibredGroupoids.{u, v, w} k k)
    (x₀ : fibre D (residueTest (R := k) (k := k))) (A : TestCategory k k) : fibre D A :=
  (push D (testFieldInclusion A)).obj x₀

/-- The group V = Aut(x_ε), before equipping it with its additive vector structure.
Source: Stacks, Tag 06JX
(blueprint: lem-sfb-schlessinger-automorphism-kernel). -/
abbrev infinitesimalAut (D : CofibredGroupoids.{u, v, w} k k)
    (x₀ : fibre D (residueTest (R := k) (k := k))) :=
  Aut (testBasePoint D x₀ (squareZeroTest (R := k) (k := k) k))

/-- The canonical identification f_*x_{0,A} ≅ x_{0,B}. The equality of coefficient
maps is uniqueness of a k-algebra map out of k, not a choice of fibre isomorphism.
Source: Stacks, Tags 06JU and 06JV
(blueprint: lem-sfb-schlessinger-automorphism-kernel). -/
def testBasePointComparison (D : CofibredGroupoids.{u, v, w} k k)
    (x₀ : fibre D (residueTest (R := k) (k := k)))
    {A B : TestCategory k k} (f : A ⟶ B) :
    (push D f).obj (testBasePoint D x₀ A) ≅ testBasePoint D x₀ B :=
  (compIso D (testFieldInclusion A) f).app x₀ ≪≫
    (eqToIso (congrArg (push D)
      (ObjectProperty.hom_ext _ (Over.OverMorphism.ext
        (CommAlgCat.hom_ext (by
          change (_ : k →ₐ[k] ring B) = _
          exact Subsingleton.elim _ _)))))).app x₀

/-- Rescale ε by a and transport automorphisms, identifying the transported point
by the canonical composition comparison.
Source: Stacks, Tags 06JV and 06JX
(blueprint: lem-sfb-schlessinger-automorphism-kernel). -/
def infinitesimalAutScalar (D : CofibredGroupoids.{u, v, w} k k)
    (x₀ : fibre D (residueTest (R := k) (k := k))) (a : k) :
    infinitesimalAut D x₀ → infinitesimalAut D x₀ :=
  fun h ↦ Aut.autMulEquivOfIso
    (testBasePointComparison D x₀ (squareZeroMap (R := k) (a • LinearMap.id)))
    ((push D (squareZeroMap (R := k) (a • LinearMap.id))).mapAut _ h)

/-- Automorphisms of x' whose reduction is the identity on p_*x'.
Source: Stacks, Tag 06JY
(blueprint: lem-sfb-schlessinger-automorphism-kernel). -/
abbrev automorphismReductionKernel (D : CofibredGroupoids.{u, v, w} k k)
    {A' A : TestCategory k k} (p : A' ⟶ A) (x' : fibre D A') :=
  ((push D p).mapAut x').ker

/-- Infinitesimal automorphisms have their natural vector structure, and the
reduction kernel across an extension killed by the maximal ideal is a torsor
under V ⊗ₖ I. The explicit action laws and unique transporter express a free
transitive action of the additive group, including the zero-kernel case.
Source: Stacks, Tags 06JX and 06JY
(blueprint: lem-sfb-schlessinger-automorphism-kernel).

Proof:
1. Define E(B) = Aut(x_{0,B}) with transport along coefficient-field inclusions.
The pseudofunctor constraints give its functor laws. Full faithfulness in (RS)
gives E(B₁ ×_B B₂) = E(B₁) ×_{E(B)} E(B₂). The residue automorphism group is
trivial because D(k) is terminal. This is Tag 06JU.
2. Regard E as a discrete predeformation groupoid. Apply
lem-sfb-product-preserving-vector-functor-linearization and
lem-sfb-artin-rs-tangent-tensor to L(W) = E(k[W]). The product comparison and
composition satisfy the interchange law; hence vector addition is composition
(Eckmann--Hilton), and scaling is induced by ε ↦ aε (Tags 06JV and 06JX).
3. Naturality of the tangent--tensor bijection under projections, addition and
a.id makes it linear. Normalize at k to identify V ⊗ₖ W with L(W), where V's
addition is composition (def-weil-pbc-module-tensor-product).
4. Put I = ker(p). Its containment in the maximal ideal implies I² = 0.
By lem-weil-pbc-artinian-local-noetherian-nilpotent and
def-weil-pbc-noetherian-ring, I is finitely generated; annihilation by the
maximal ideal makes it finite-dimensional over k. The isomorphism
A' ×_A A' ≅ A' ×_k k[I] sends (a,b) to (a,(res(a),b-a)), with inverse
(a,(res(a),i)) ↦ (a,a+i). The hypotheses kill all mixed ideal products.
lem-sfb-artin-local-test-algebra supplies both fibre-product tests.
5. Transport x' along the diagonal into this fibre product. Full faithfulness
in (RS) identifies its automorphisms both with H ×_{H_A} H and with H × L(I),
over the same first projection, where H = Aut(x'). Restrict to first coordinate
1 to obtain ψ : ker(H → H_A) ≃ L(I), as groups (Tags 06JU, 06JI and 06JY).
6. Under Φ : V ⊗ₖ I ≃ L(I), define t ⋅ h = ψ⁻¹(Φ(t) + ψ(h)). Zero and addition
give the action laws. The unique transporter from h to h' is
Φ⁻¹(ψ(h') - ψ(h)). The identity automorphism supplies nonemptiness.
When I=0, both the kernel and L(0) are singletons. No finiteness of V is needed. -/
theorem schlessinger_automorphism_kernel
    (D : CofibredGroupoids.{u, v, w} k k)
    (hpre : IsPredeformation D) (hrs : IsRimSchlessinger D)
    (x₀ : fibre D (residueTest (R := k) (k := k))) :
    ∃ (_ : AddCommGroup (infinitesimalAut D x₀)) (_ : Module k (infinitesimalAut D x₀)),
      (∀ f g : infinitesimalAut D x₀, f + g = f * g) ∧
      (∀ (a : k) (f : infinitesimalAut D x₀), a • f = infinitesimalAutScalar D x₀ a f) ∧
      (∀ (A' A : TestCategory k k) (p : A' ⟶ A)
        (_ : Function.Surjective (map p))
        (_ : ∀ a ∈ IsLocalRing.maximalIdeal (ring A'),
          ∀ i ∈ RingHom.ker (map p).toRingHom, a * i = 0)
        (x' : fibre D A'),
        ∃ act : TensorProduct k (infinitesimalAut D x₀) (RingHom.ker (map p).toRingHom) →
            automorphismReductionKernel D p x' → automorphismReductionKernel D p x',
          (∀ h, act 0 h = h) ∧
          (∀ t s h, act (t + s) h = act t (act s h)) ∧
          (∀ h h', ∃! t, act t h = h')) := by
  sorry

end AlgebraicGeometry.ArtinDeformation

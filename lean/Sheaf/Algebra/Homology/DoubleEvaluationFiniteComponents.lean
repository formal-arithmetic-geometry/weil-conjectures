/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Finite components of double evaluation

Source: Stacks Project, More on Algebra, Tag 0A68,
`lemma-internal-hom-evaluate-isomorphism`, case (2), finite-free specialization.
(blueprint: lem-trf-double-evaluation-finite-components)
-/

@[expose] public section

set_option autoImplicit false

universe r v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace CochainComplex

noncomputable section

variable {R : Type r} [CommRing R]

/-- Shape of the existing linear Hom differential in independent universes.
Source: Stacks Project, Tag 0A8H (blueprint: def-sc-module-total-hom-complex).
Proof: apply ModuleCat.hom_ext and LinearMap.ext to Mathlib HomComplex.δ_shape;
its hypothesis is exactly the negation of the successor relation. -/
theorem moduleHom_shapeOfUniverses (L M : CochainComplex (ModuleCat.{v} R) ℤ)
    (n m : ℤ) (h : ¬ (ComplexShape.up ℤ).Rel n m) :
    ModuleCat.ofHom (HomComplex.δ_hom R L M n m) = 0 := by
  sorry

/-- Square zero of the existing linear Hom differential in independent universes.
Source: Stacks Project, Tag 0A8H (blueprint: def-sc-module-total-hom-complex).
Proof: apply ModuleCat.hom_ext and LinearMap.ext to Mathlib HomComplex.δ_δ.
The two mixed terms cancel and the other two vanish by d squared equals zero. -/
theorem moduleHom_squareOfUniverses (L M : CochainComplex (ModuleCat.{v} R) ℤ)
    (n m k : ℤ) :
    ModuleCat.ofHom (HomComplex.δ_hom R L M n m) ≫
      ModuleCat.ofHom (HomComplex.δ_hom R L M m k) = 0 := by
  sorry

/-- The module-valued product total Hom with independent ring and carrier universes.
It has precisely the existing cochains and differential; at equal universes this
is definitionally the recorded moduleHomComplex, by proof irrelevance.
Source: Stacks Project, Tag 0A8H (blueprint: def-sc-module-total-hom-complex). -/
def moduleHomComplexOfUniverses (L M : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (HomComplex.Cochain L M n)
  d n m := ModuleCat.ofHom (HomComplex.δ_hom R L M n m)
  shape := moduleHom_shapeOfUniverses L M
  d_comp_d' n m k _ _ := moduleHom_squareOfUniverses L M n m k

end

end CochainComplex

namespace CochainComplex.DoubleEvaluation

/-- The triples indexing the potentially nonzero degree-n components.
Source: Stacks Project, Tag 0A68, case (2), finite-support ranges.
(blueprint: lem-trf-double-evaluation-finite-components) -/
def support (u ℓ a b n : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {t | t.1 + t.2.1 + t.2.2 = n ∧ a ≤ t.1 ∧ t.1 ≤ b ∧ t.2.1 ≤ -ℓ ∧ t.2.2 ≤ u}

variable {R : Type r} [CommRing R]

/-- The ordinary module tensor bifunctor in independent coefficient and carrier universes.
This supplies only the bifunctor interface; the tensor and totalization remain the
recorded TensorProduct and mapBifunctor constructions.
Source: Stacks Project, Tag 0A68, tensor totalization of ordinary modules.
(blueprint: lem-trf-double-evaluation-finite-components) -/
def tensor : ModuleCat.{v} R ⥤ ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M :=
    { obj := fun N => ModuleCat.of R (M ⊗[R] N)
      map := fun f => ModuleCat.ofHom (f.hom.lTensor M)
      map_id := fun N => by ext x y; simp
      map_comp := fun f g => by ext x y; simp }
  map f :=
    { app := fun N => ModuleCat.ofHom (f.hom.rTensor N)
      naturality := fun N N' g => by ext x y; rfl }
  map_id := fun M => by ext N x; simp
  map_comp := fun f g => by ext N x; simp

/-- Zero preservation of the ordinary tensor in its first variable.
Source: Stacks Project, Tag 0A68 (blueprint: lem-trf-double-evaluation-finite-components). -/
instance tensor_preservesZeroMorphisms : (tensor (R := R)).PreservesZeroMorphisms where
  map_zero M N := by ext K x; simp [tensor]

/-- Zero preservation of the ordinary tensor in its second variable.
Source: Stacks Project, Tag 0A68 (blueprint: lem-trf-double-evaluation-finite-components). -/
instance tensor_obj_preservesZeroMorphisms (M : ModuleCat.{v} R) :
    ((tensor (R := R)).obj M).PreservesZeroMorphisms where
  map_zero N N' := by ext x; simp [tensor]

/-- The source component Hom(J^{-r}, I^p) tensor P^s.
Source: Stacks Project, Tag 0A68, maps c_{p,r,s}.
(blueprint: lem-trf-double-evaluation-finite-components) -/
abbrev sourceComponent (P J I : CochainComplex (ModuleCat.{v} R) ℤ)
    (t : ℤ × ℤ × ℤ) :=
  (J.X (-t.2.1) →ₗ[R] I.X t.1) ⊗[R] P.X t.2.2

/-- The target component Hom(Hom(P^s, J^{-r}), I^p).
Source: Stacks Project, Tag 0A68, maps c_{p,r,s}.
(blueprint: lem-trf-double-evaluation-finite-components) -/
abbrev targetComponent (P J I : CochainComplex (ModuleCat.{v} R) ℤ)
    (t : ℤ × ℤ × ℤ) :=
  (P.X t.2.2 →ₗ[R] J.X (-t.2.1)) →ₗ[R] I.X t.1

/-- Finite-support identifications and the specified signed evaluation isomorphism.
The isomorphisms are characterized by their canonical coordinate formulas, so no
arbitrary choice of an isomorphism is substituted for the evaluation map.
Source: Stacks Project, Tag 0A68, proof of case (2), finite-free specialization.
(blueprint: lem-trf-double-evaluation-finite-components)

Proof: (1) The equation p+r+s=n puts the support in the finite box
[a,b] times [n-b-u,-ℓ] times [n-b+ℓ,u]. (2) The Hom(P,J) factor at s
vanishes unless ℓ-k ≤ s ≤ u; projection and zero extension identify its
product with the finite product on that interval. A finite product is its
finite direct sum, by summing the coordinate inclusions. (3) In Hom(J,I)
restrict p to [a,b] and r to r ≤ -ℓ. For each tensor degree s the surviving
product is finite. Apply lem-weil-pbc-tensor-finite-product (TensorProduct.piLeft),
then reindex the tensor summands by the triples in the support. The inverse
sends g tensor x to the inclusion of the single cochain g tensor x.
(4) Restrict the outer Hom to p in [a,b]. A functional on the finite product
Hom(P,J) is the sum of its composites with the coordinate inclusions; this
gives the target identification, with coordinates beta composed with single.
(5) Bilinearity defines c(g tensor x)(f)=epsilon*g(f(x)), where
epsilon=(-1)^(s*(r+1)). (6) For a finite basis e_i with coordinates lambda_i,
put iota_i(v)(x)=lambda_i(x)*v. Its values on the basis are delta_ij*v.
The inverse is epsilon times the sum of (beta composed with iota_i) tensor e_i.
(7) Expand f as the sum of iota_i(f(e_i)); epsilon squared is one, so cD=1.
(8) On pure tensors, c(g tensor x) composed with iota_i equals
 epsilon*lambda_i(x)*g. Tensor balancing and basis expansion give Dc=1;
pure tensors generate, so this holds everywhere. (9) Sum the component
isomorphisms and conjugate by the two canonical identifications. This gives
the displayed degreewise isomorphism. Empty intervals, empty bases, and empty
support give zero modules and the same identities. No injectivity or
compatibility with differentials is used. -/
theorem finite_components (P J I : CochainComplex (ModuleCat.{v} R) ℤ)
    (u ℓ a b : ℤ) (hab : a ≤ b)
    (hfree : ∀ s : ℤ, ∃ m : ℕ, Nonempty (Module.Basis (Fin m) R (P.X s)))
    (hP : ∀ s : ℤ, u < s → Subsingleton (P.X s))
    (hJ : ∀ j : ℤ, j < ℓ → Subsingleton (J.X j))
    (hI : ∀ p : ℤ, p < a ∨ b < p → Subsingleton (I.X p)) (n : ℤ) :
    (support u ℓ a b n).Finite ∧
    (∀ t : support u ℓ a b n,
      n - b + ℓ ≤ t.val.2.2 ∧ t.val.2.2 ≤ u ∧
      n - b - u ≤ t.val.2.1 ∧ t.val.2.1 ≤ -ℓ) ∧
    (∀ k s : ℤ, s < ℓ - k ∨ u < s →
      Subsingleton (P.X s →ₗ[R] J.X (s + k))) ∧
    ∃ eT : (mapBifunctor (moduleHomComplexOfUniverses J I) P
        (tensor (R := R))).X n ≃ₗ[R]
        ⨁ t : support u ℓ a b n, sourceComponent P J I t.val,
    ∃ eB : (moduleHomComplexOfUniverses (moduleHomComplexOfUniverses P J) I).X n ≃ₗ[R]
        ⨁ t : support u ℓ a b n, targetComponent P J I t.val,
    ∃ c : ∀ t : support u ℓ a b n,
        sourceComponent P J I t.val ≃ₗ[R] targetComponent P J I t.val,
    ∃ E : (mapBifunctor (moduleHomComplexOfUniverses J I) P
        (tensor (R := R))).X n ≃ₗ[R]
        (moduleHomComplexOfUniverses (moduleHomComplexOfUniverses P J) I).X n,
      (∀ (t : support u ℓ a b n)
        (g : J.X (-t.val.2.1) →ₗ[R] I.X t.val.1) (x : P.X t.val.2.2),
        eT.symm (DirectSum.lof R _ _ t (g ⊗ₜ[R] x)) =
          (ιMapBifunctor (moduleHomComplexOfUniverses J I) P (tensor (R := R))
            (t.val.1 + t.val.2.1) t.val.2.2 n t.property.1).hom
            (HomComplex.Cochain.single (ModuleCat.ofHom g)
              (t.val.1 + t.val.2.1) ⊗ₜ[R] x)) ∧
      (∀ (β : (moduleHomComplexOfUniverses (moduleHomComplexOfUniverses P J) I).X n)
        (t : support u ℓ a b n) (f : P.X t.val.2.2 →ₗ[R] J.X (-t.val.2.1)),
        (eB β t) f =
          (β.v (t.val.1 - n) t.val.1 (by omega)).hom
            (HomComplex.Cochain.single (ModuleCat.ofHom f) (t.val.1 - n))) ∧
      (∀ (t : support u ℓ a b n)
        (g : J.X (-t.val.2.1) →ₗ[R] I.X t.val.1) (x : P.X t.val.2.2)
        (f : P.X t.val.2.2 →ₗ[R] J.X (-t.val.2.1)),
        c t (g ⊗ₜ[R] x) f =
          (t.val.2.2 * (t.val.2.1 + 1)).negOnePow • g (f x)) ∧
      (∀ (t : support u ℓ a b n) (ι : Type w) [Fintype ι]
        (e : Module.Basis ι R (P.X t.val.2.2)),
        ∃ ιe : ι → J.X (-t.val.2.1) →ₗ[R]
            (P.X t.val.2.2 →ₗ[R] J.X (-t.val.2.1)),
          (∀ (i : ι) (v : J.X (-t.val.2.1)) (x : P.X t.val.2.2),
            ιe i v x = e.repr x i • v) ∧
          (∀ β : targetComponent P J I t.val,
            (c t).symm β = (t.val.2.2 * (t.val.2.1 + 1)).negOnePow •
              ∑ i : ι, (β.comp (ιe i)) ⊗ₜ[R] e i)) ∧
      (∀ (z : (mapBifunctor (moduleHomComplexOfUniverses J I) P
          (tensor (R := R))).X n) (t : support u ℓ a b n),
        eB (E z) t = c t (eT z t)) := by
  sorry

end CochainComplex.DoubleEvaluation

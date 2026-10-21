/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy

/-! # Bicosimplicial shuffle and finite cochain totalizations

Source: the current blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), formal homological-algebra
input (blueprint: lem-sfb-bicosimplicial-shuffle-totalization).

All totals below are Mathlib's total complexes with the published nonnegative sign
and finite-coproduct instances. The inner total first combines the two cosimplicial
indices; the remaining total combines their sum with the internal cochain degree.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicTopology
open scoped Simplicial

namespace AlgebraicTopology.BicosimplicialShuffle

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The diagonal alternating-coface bicomplex, before totalization.
Source: current blueprint, direct-images proof (3), diagonal differential.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def diagonalBicomplex (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlternatingCofaceMapComplex.obj (CategoryTheory.Functor.diag SimplexCategory ⋙ X)

/-- The three nonnegative cochain indices, ordered first cosimplicial, second
cosimplicial, internal. Source: current blueprint, direct-images proof (3).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def tripleComplex (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ (CochainComplex C ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlternatingCofaceMapComplex.obj
    (curry.obj X ⋙ alternatingCofaceMapComplex (CochainComplex C ℕ))

/-- First totalize the two cosimplicial indices in the category of internal complexes.
Source: current blueprint, direct-images proof (3); differential δ₁ + (-1)^a δ₂.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def cosimplicialTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (tripleComplex X).total (ComplexShape.up ℕ)

/-- The diagonal total D(X), with differential δ_diag + (-1)^n d_internal.
Source: current blueprint, direct-images proof (3).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def diagonalTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) : CochainComplex C ℕ :=
  (diagonalBicomplex X).total (ComplexShape.up ℕ)

/-- The successive total T(X), with differential
δ₁ + (-1)^a δ₂ + (-1)^(a+b) d_internal.
Source: current blueprint, direct-images proof (3).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def successiveTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) : CochainComplex C ℕ :=
  (cosimplicialTotal X).total (ComplexShape.up ℕ)

/-- Functoriality of D(X), using the existing alternating-coface and total map.
Source: current blueprint, direct-images proof (3), naturality in X.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def diagonalMap
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y) :
    diagonalTotal X ⟶ diagonalTotal Y :=
  HomologicalComplex₂.total.map
    (AlternatingCofaceMapComplex.map
      (whiskerLeft (CategoryTheory.Functor.diag SimplexCategory) f)) (ComplexShape.up ℕ)

/-- Functoriality of T(X), totaling first the two cosimplicial indices and then the
internal index. Source: current blueprint, direct-images proof (3), naturality in X.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def successiveMap
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y) :
    successiveTotal X ⟶ successiveTotal Y :=
  HomologicalComplex₂.total.map
    (HomologicalComplex₂.total.map
      (AlternatingCofaceMapComplex.map
        (whiskerRight (curry.map f) (alternatingCofaceMapComplex (CochainComplex C ℕ))))
      (ComplexShape.up ℕ)) (ComplexShape.up ℕ)

/-- The canonical inclusion X^(n,n,r) into D(X)^(n+r).
Source: current blueprint, direct-images proof (3), finite diagonal sum.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def diagonalInclusion
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (n r m : ℕ) (h : n + r = m) :
    (X.obj (⦋n⦌, ⦋n⦌)).X r ⟶ (diagonalTotal X).X m :=
  (diagonalBicomplex X).ιTotal (ComplexShape.up ℕ) n r m h

/-- The canonical inclusion X^(a,b,r) into T(X)^(a+b+r), with the first direction
first. Source: current blueprint, direct-images proof (3), finite triple sum.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def successiveInclusion
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (a b r m : ℕ) (h : a + b + r = m) :
    (X.obj (⦋a⦌, ⦋b⦌)).X r ⟶ (successiveTotal X).X m :=
  ((tripleComplex X).ιTotal (ComplexShape.up ℕ) a b (a + b) rfl).f r ≫
    (cosimplicialTotal X).ιTotal (ComplexShape.up ℕ) (a + b) r m h

/-- The monotone surjection α_μ(i) = #{j ∈ μ | j < i}. Taking the complement
produces α_ν. Source: current blueprint, direct-images proof (3), shuffle formula.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def shuffleSurjection (n : ℕ) (μ : Finset (Fin n)) : ⦋n⦌ ⟶ ⦋μ.card⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i ↦ ⟨(μ.filter (fun j ↦ j.val < i.val)).card,
        Nat.lt_succ_of_le (Finset.card_filter_le μ _)⟩
      monotone' := fun _i _j hij ↦ Finset.card_le_card
        (Finset.monotone_filter_right μ (fun _k _ hk ↦ lt_of_lt_of_le hk hij)) }

/-- The sign of the permutation with increasing μ followed by increasing μᶜ:
its inversions are pairs (i,j) ∈ μ × μᶜ with j < i.
Source: current blueprint, direct-images proof (3), ε(μ,ν).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def shuffleSign (n : ℕ) (μ : Finset (Fin n)) : ℤ :=
  (-1) ^ ((μ.product μᶜ).filter (fun ij ↦ ij.2 < ij.1)).card

/-- A shuffle summand with its target inclusion. Every subset μ of Fin n gives
exactly one partition (μ,μᶜ); its two cardinalities sum to n.
Source: current blueprint, direct-images proof (3), specified shuffle component.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def shuffleTerm
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (n r m : ℕ) (h : n + r = m) (μ : Finset (Fin n)) :
    (X.obj (⦋n⦌, ⦋n⦌)).X r ⟶ (successiveTotal X).X m :=
  shuffleSign n μ • ((X.map (shuffleSurjection n μ, shuffleSurjection n μᶜ)).f r ≫
    successiveInclusion X μ.card μᶜ.card r m
      ((congrArg (fun k ↦ k + r)
        ((Finset.card_add_card_compl μ).trans (Fintype.card_fin n))).trans h))

/-- The specified shuffle defines natural homotopy equivalences, natural derived
isomorphisms, and strictly preserves augmentations supported in cosimplicial degree zero.
The component equation characterizes S on every coproduct inclusion, so the existential
map is the prescribed finite signed shuffle, with no arbitrary comparison map chosen.

Source: current blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), formal input.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization).

Proof:
1. In Fun(Δ × Δ, Ab), put R_i(j) = ℤ[Hom(i,j)]. Pointwise kernels and cokernels
make this category abelian. Additive Yoneda identifies maps R_i → F with F(i),
so R_i and their finite sums are projective; the sum over all (i,x) surjects onto F.
2. Put P_n = R_(n,n) and Q_n = ⊕_(a+b=n) R_(a,b), with diagonal and signed separate
alternating-deletion boundaries. Cosimplicial identities give square zero; both
augment to the constant ℤ. At (p,q) these are the free pair-string complex and
the total tensor of the two free simplex complexes of
lem-sfb-simplex-lattice-shuffle-boundary.
3. Prepending the minimum vertex gives ∂h+h∂ = 1-eε. On the tensor use
H(u⊗v) = h_p(u)⊗v + (-1)^a E_p(u)⊗h_q(v), with E=eε. Expanding gives
∂H+H∂ = 1-E_p⊗E_q. Thus P,Q are pointwise exact projective resolutions.
4. The cited simplex-lattice shuffle boundary identity assembles the signed sums
into an augmentation-preserving natural chain map σ:Q→P, with distinguished
generator value Σ ε(μ,ν)(α_μ,α_ν).
5. Apply lem-weil-pbc-injective-resolution-lift-exists in the opposite abelian
category, in order Q^op,P^op, obtaining τ:P→Q. The two augmented composites
are homotopic to identities by new-t4-augmented-resolution-lift-homotopy.
6. A map between representables is a finite integral sum of arrows in the reverse
direction. Evaluate it contravariantly on any C-valued diagram, and evaluate
finite sums by transposed matrices of finite biproducts. Bilinearity and
functoriality preserve compositions, hence the chain and homotopy equations.
The evaluated σ is exactly the displayed S, and the evaluated τ is its homotopy inverse.
7. Use the same matrices in every internal degree r. Their entries commute with
the internal differential. Maps preserve n=a+b; homotopies lower n by one, so
the additional internal terms (-1)^(n-1)d_r H + (-1)^n H d_r cancel. This proves
the full total-complex homotopy equivalence. All sums are finite by nonnegativity,
as in def-sp-double-complex-total.
8. Extend by zero to integer cochain degrees and apply localization Q of
def-weil-abstract-derived-category. The homotopy equations give inverse derived
maps; the finite matrix formulas give naturality of the derived isomorphism.
9. If (f₀-f₁)i=(g₀-g₁)i=0, the diagonal difference also kills i by commutation
of the two directions. Thus degree-zero inclusions define j_D,j_T. The sole
empty shuffle has sign 1 and identity surjections, giving j_D ≫ S = j_T strictly.
No step excludes zero objects, constant objects or one constant direction. -/
theorem exists_shuffle [HasDerivedCategory.{w} C] :
    ∃ S : ∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
        diagonalTotal X ⟶ successiveTotal X,
      (∀ (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
        (n r m : ℕ) (h : n + r = m),
        diagonalInclusion X n r m h ≫ (S X).f m =
          ∑ μ : Finset (Fin n), shuffleTerm X n r m h μ) ∧
      (∀ (X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) (f : X ⟶ Y),
        diagonalMap f ≫ S Y = S X ≫ successiveMap f) ∧
      (∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
        ∃ e : HomotopyEquiv (diagonalTotal X) (successiveTotal X), e.hom = S X) ∧
      (∃ e : ∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
          (DerivedCategory.Q.obj ((diagonalTotal X).extend ComplexShape.embeddingUpNat)) ≅
          (DerivedCategory.Q.obj ((successiveTotal X).extend ComplexShape.embeddingUpNat)),
        (∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
          (e X).hom = DerivedCategory.Q.map
            ((ComplexShape.embeddingUpNat.extendFunctor C).map (S X))) ∧
        (∀ (X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) (f : X ⟶ Y),
          DerivedCategory.Q.map
              ((ComplexShape.embeddingUpNat.extendFunctor C).map (diagonalMap f)) ≫
              (e Y).hom =
            (e X).hom ≫ DerivedCategory.Q.map
              ((ComplexShape.embeddingUpNat.extendFunctor C).map (successiveMap f)))) ∧
      (∀ (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
        (M : CochainComplex C ℕ) (i : M ⟶ X.obj (⦋0⦌, ⦋0⦌)),
        i ≫ (X.map ((SimplexCategory.δ (0 : Fin 2), 𝟙 ⦋0⦌) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌)) -
          X.map ((SimplexCategory.δ (1 : Fin 2), 𝟙 ⦋0⦌) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌))) = 0 →
        i ≫ (X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (0 : Fin 2)) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌)) -
          X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (1 : Fin 2)) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌))) = 0 →
        ∃ (jD : M ⟶ diagonalTotal X) (jT : M ⟶ successiveTotal X),
          (∀ m : ℕ, jD.f m = i.f m ≫ diagonalInclusion X 0 m m (Nat.zero_add m)) ∧
          (∀ m : ℕ, jT.f m = i.f m ≫ successiveInclusion X 0 0 m m
            (Nat.zero_add m)) ∧
          jD ≫ S X = jT) := by
  sorry

end AlgebraicTopology.BicosimplicialShuffle

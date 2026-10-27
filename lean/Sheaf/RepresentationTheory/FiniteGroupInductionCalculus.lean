module

public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.GroupTheory.Index
public import Sheaf.RepresentationTheory.FiniteModuleSplitGrothendieck
import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Quotient induction of finite-group representations

Source: the explicit quotient-generator proof in the DAG, with representation context in
ILO, Exposé X, Proposition 1.2, printed p.138
(blueprint: lem-per-finite-group-induction-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory
open scoped MonoidalCategory TensorProduct

namespace Rep.QuotientInduction

variable {F G H : Type u} [Field F] [Group G] [Group H]

/-- Mathlib's quotient induction, bundled as a finite-dimensional representation.
Source: DAG quotient presentation, proof steps 1--3
(blueprint: lem-per-finite-group-induction-calculus). -/
abbrev ind [Finite G] (φ : H →* G) (W : FDRep F H) : FDRep F G :=
  FDRep.of (Representation.ind φ W.ρ)

/-- Restriction keeps the vector space and composes its action with the group homomorphism.
Source: DAG statement (blueprint: lem-per-finite-group-induction-calculus). -/
abbrev res (φ : H →* G) (V : FDRep F G) : FDRep F H := FDRep.of (V.ρ.comp φ)

/-- The quotient generator `[g,w]`. Inversion of the group-algebra index translates Mathlib's
right-inverse action convention into the displayed left-translation convention of the node.
Source: DAG proof step 1 (blueprint: lem-per-finite-group-induction-calculus). -/
abbrev mk [Finite G] (φ : H →* G) (W : FDRep F H) (g : G) :
    W →ₗ[F] ind φ W := Representation.IndV.mk φ W.ρ g⁻¹

/-- The specified finite direct sum with its componentwise representation.
Source: DAG proof step 4 (blueprint: lem-per-finite-group-induction-calculus). -/
abbrev sum {I : Type u} [Finite I] (W : I → FDRep F H) : FDRep F H :=
  FDRep.of (Representation.directSum (fun i ↦ (W i).ρ))

/-- A representation as its finite-dimensional module over the group algebra.
Source: DAG proof step 13 (blueprint: lem-per-finite-group-induction-calculus). -/
def algebraModule (W : FDRep F H) :
    RepresentationTheory.FiniteAlgebraModule.{u, u, u} F (MonoidAlgebra F H) where
  space := ModuleCat.of F W
  finite := inferInstance
  action := Representation.asAlgebraHom W.ρ

/-- The existing presented split representation group specialized to the group algebra.
Source: DAG statement and proof step 13. Isomorphism and direct-sum relations are exactly
those of finite-dimensional representations through their group-algebra actions
(blueprint: lem-per-finite-group-induction-calculus). -/
abbrev group (F J : Type u) [Field F] [Group J] :=
  RepresentationTheory.FiniteModuleSplitGrothendieck.{u, u, u} F (MonoidAlgebra F J)

/-- The generator class of a representation in the existing split presentation.
Source: DAG proof step 13 (blueprint: lem-per-finite-group-induction-calculus). -/
def cls (W : FDRep F H) : group F H :=
  QuotientAddGroup.mk (FreeAbelianGroup.of (algebraModule W))

/-- The underlying bundled representation, without changing its vector space or action.
Source: DAG statement (blueprint: lem-per-finite-group-induction-calculus). -/
abbrev rep (W : FDRep F H) : Rep.{u} F H := Rep.of W.ρ

open Classical in
/-- Quotient induction respects the balancing relations and left action, preserves finite sums,
has the stated dimension, and admits natural transitivity, tensor and Frobenius comparisons.
It also gives multiplication, restriction and induction on the specified presented groups.

Source: the thirteen-step explicit quotient-generator proof in the accepted DAG;
ILO, Exposé X, Proposition 1.2, printed p.138 is representation-theoretic context only.
Serre, Part I, Chapter 7 is WANTED in the DAG, rather than an available proof source
(blueprint: lem-per-finite-group-induction-calculus).

Proof plan:
1. Write `[g,w]` for the quotient generators. Tensor bilinearity and the quotient universal
property let maps descend exactly when they respect `[gh,w]=[g,hw]`. Left translation preserves
these relations and satisfies the action laws.
2. Choose left-coset representatives `s`. The mutually inverse maps from the direct sum of copies
of W send its s-th inclusion to `[s,w]`, and `[sh,w]` to the s-th inclusion of `hw`.
3. Choose a finite basis of W using lem-weil-pbc-vector-space-free. In the coset coordinates the
vectors `[s,b_i]` form a basis. Counting proves finite dimension and the index-times-dimension
formula, using def-weil-vector-space-dimension, including the empty basis when W is zero.
4. The direct-sum map is `[g,(w_i)] ↦ ([g,w_i])_i`. Its inverse sums induced inclusions.
Projection and inclusion identities prove both inverse identities and naturality, also for I empty.
5. The transitivity map sends `[g,[h,u]]` to `[gh,u]`. Both the inner K relation and outer H
relation are respected, so it descends through both quotients.
6. Its inverse sends `[g,u]` to `[g,[1,u]]`. The relations prove the inverse identities;
left translation proves equivariance, and applying an intertwiner to u proves naturality.
7. The tensor map sends `v ⊗ [g,w]` to `[g,g⁻¹v ⊗ w]`. Bilinearity and the target diagonal H
action verify the source balancing relation and give descent.
8. Its inverse sends `[g,v ⊗ w]` to `gv ⊗ [g,w]`. It respects the balancing relation;
expanding pure tensors proves both inverse identities.
9. Applying a in G to each generator proves equivariance. Applying intertwiners to v and w proves
naturality in both variables.
10. Frobenius evaluation is `f ↦ (w ↦ f([1,w]))`. Its inverse sends t to `[g,w] ↦ g t(w)`.
The balancing relations and the intertwining laws prove well-definedness and equivariance.
11. Evaluate the composites on generators to prove they are identities. Pointwise operations
prove F-linearity, and pre/postcomposition proves both naturality identities.
12. Finite tensor bases come from lem-sc-tensor-product-free-basis. Tensor distributivity,
associativity, symmetry and unit maps are equivariant by their pure-tensor formulas; these show
that tensor multiplication respects the direct-sum relations.
13. Restriction and induction preserve sums and isomorphisms, so descend to the presented groups.
Finite-dimensional representations have a set of isomorphism classes by their matrix models.
The tensor and transitivity identities hold on generators and extend by additivity to every
integer linear combination, including negative coefficients.
-/
theorem finiteGroupInductionCalculus (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (G : Type u) [Group G] [Finite G] (H K : Subgroup G) (hKH : K ≤ H) :
    (∀ (W : FDRep F H) (g : G) (h : H) (w : W),
      mk H.subtype W (g * h) w = mk H.subtype W g (W.ρ h w)) ∧
    (∀ (W : FDRep F H) (a g : G) (w : W),
      (ind H.subtype W).ρ a (mk H.subtype W g w) = mk H.subtype W (a * g) w) ∧
    (∀ (I : Type u) [Finite I] (W : I → FDRep F H),
      ∃ e : Rep.ind H.subtype (rep (sum W)) ≅
          rep (sum (fun i ↦ ind H.subtype (W i))),
        ∀ (i : I) (g : G) (w : W i),
          e.hom.hom (mk H.subtype (sum W) g
            (DirectSum.lof F I (fun i ↦ (W i : Type u)) i w)) =
          DirectSum.lof F I (fun i ↦ (ind H.subtype (W i) : Type u)) i
            (mk H.subtype (W i) g w)) ∧
    (∀ W : FDRep F H,
      Module.finrank F (ind H.subtype W) = H.index * Module.finrank F W) ∧
    (∃ t : ∀ U : FDRep F K,
        Rep.ind H.subtype (Rep.ind (Subgroup.inclusion hKH) (rep U)) ≅
          Rep.ind K.subtype (rep U),
      (∀ (U : FDRep F K) (g : G) (h : H) (w : U),
        (t U).hom.hom (mk H.subtype (ind (Subgroup.inclusion hKH) U) g
          (mk (Subgroup.inclusion hKH) U h w)) = mk K.subtype U (g * h) w) ∧
      (∀ (U U' : FDRep F K) (f : rep U ⟶ rep U'),
        Rep.indMap H.subtype (Rep.indMap (Subgroup.inclusion hKH) f) ≫ (t U').hom =
          (t U).hom ≫ Rep.indMap K.subtype f)) ∧
    (∃ p : ∀ (V : FDRep F G) (W : FDRep F H),
        rep V ⊗ Rep.ind H.subtype (rep W) ≅
          Rep.ind H.subtype (Rep.res H.subtype (rep V) ⊗ rep W),
      (∀ (V : FDRep F G) (W : FDRep F H) (v : V) (g : G) (w : W),
        (p V W).hom.hom (v ⊗ₜ[F] mk H.subtype W g w) =
          mk H.subtype (res H.subtype V ⊗ W) g ((V.ρ g⁻¹ v) ⊗ₜ[F] w)) ∧
      (∀ (V V' : FDRep F G) (W W' : FDRep F H)
          (f : rep V ⟶ rep V') (q : rep W ⟶ rep W'),
        (f ⊗ₘ Rep.indMap H.subtype q) ≫ (p V' W').hom =
          (p V W).hom ≫ Rep.indMap H.subtype ((Rep.resFunctor H.subtype).map f ⊗ₘ q))) ∧
    (∃ E : ∀ (W : FDRep F H) (V : FDRep F G),
        (Rep.ind H.subtype (rep W) ⟶ rep V) ≃ₗ[F]
          (rep W ⟶ Rep.res H.subtype (rep V)),
      (∀ (W : FDRep F H) (V : FDRep F G)
          (f : Rep.ind H.subtype (rep W) ⟶ rep V) (w : W),
        (E W V f).hom w = f.hom (mk H.subtype W 1 w)) ∧
      (∀ (W W' : FDRep F H) (V V' : FDRep F G)
          (a : rep W' ⟶ rep W) (b : rep V ⟶ rep V')
          (f : Rep.ind H.subtype (rep W) ⟶ rep V),
        E W' V' (Rep.indMap H.subtype a ≫ f ≫ b) =
          a ≫ E W V f ≫ (Rep.resFunctor H.subtype).map b)) ∧
    (∃ m : ∀ (J : Type u) [Group J] [Finite J],
        group F J →+ group F J →+ group F J,
      (∀ (J : Type u) [Group J] [Finite J] (A B : FDRep F J),
        m J (cls A) (cls B) = cls (A ⊗ B)) ∧
      (∀ (J : Type u) [Group J] [Finite J] (x y z : group F J),
        m J (m J x y) z = m J x (m J y z)) ∧
      (∀ (J : Type u) [Group J] [Finite J] (x y : group F J),
        m J x y = m J y x) ∧
      (∀ (J : Type u) [Group J] [Finite J] (x : group F J),
        m J (cls (FDRep.of (Representation.trivial F J F))) x = x) ∧
      ∃ (r : ∀ (J : Type u) [Group J] [Finite J] (L : Subgroup J),
          group F J →+ group F L)
        (i : ∀ (J : Type u) [Group J] [Finite J] (L : Subgroup J),
          group F L →+ group F J)
        (iKH : group F K →+ group F H),
        (∀ (J : Type u) [Group J] [Finite J] (L : Subgroup J) (A : FDRep F J),
          r J L (cls A) = cls (res L.subtype A)) ∧
        (∀ (J : Type u) [Group J] [Finite J] (L : Subgroup J) (B : FDRep F L),
          i J L (cls B) = cls (ind L.subtype B)) ∧
        (∀ U : FDRep F K, iKH (cls U) = cls (ind (Subgroup.inclusion hKH) U)) ∧
        (∀ (V : FDRep F G) (x : group F H),
          m G (cls V) (i G H x) = i G H (m H (r G H (cls V)) x)) ∧
        (i G H).comp iKH = i G K) := by
  sorry

end Rep.QuotientInduction

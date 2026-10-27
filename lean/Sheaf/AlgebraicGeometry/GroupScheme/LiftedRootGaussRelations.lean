module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Gauss relations for equivariant root lifts

Source: Brian Conrad, Reductive Group Schemes, Lemma 4.3.3 and equation (4.3.1),
printed pp.128--130 (blueprint: lem-sfb-sl2-lifted-root-gauss-relations).

Group-sheaf maps are expressed as families of group homomorphisms natural on all
schemes over the base. The two auxiliary products are the specified Weyl and diagonal
lifts, with no choice of a section of the central extension.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.LiftedRootGauss

/-- The product `g'(t) = y'(-t⁻¹)x'(t)y'(-t⁻¹)` on units.
Source: Conrad, before Lemma 4.3.3, p.128
(blueprint: lem-sfb-sl2-lifted-root-gauss-relations). -/
def weylLift {R : Type u} [CommRing R] {E : Type v} [Group E]
    (X Y : Multiplicative R →* E) (t : Rˣ) : E :=
  Y (Multiplicative.ofAdd (-(↑t⁻¹ : R))) * X (Multiplicative.ofAdd (t : R)) *
    Y (Multiplicative.ofAdd (-(↑t⁻¹ : R)))

/-- The specified diagonal lift `h'(t) = g'(t)g'(1)⁻¹`.
Source: Conrad, before Lemma 4.3.3, p.128
(blueprint: lem-sfb-sl2-lifted-root-gauss-relations). -/
def diagonalLift {R : Type u} [CommRing R] {E : Type v} [Group E]
    (X Y : Multiplicative R →* E) (t : Rˣ) : E :=
  weylLift X Y t * (weylLift X Y 1)⁻¹

/-- Equivariant additive root lifts in a central fppf extension of SL2 give the
multiplicative diagonal lift and both Gauss relations, for arbitrary `u,v` with
`1 + u*v` invertible. Source: Conrad, Lemma 4.3.3 and (4.3.1), pp.128--130
(blueprint: lem-sfb-sl2-lifted-root-gauss-relations).

Proof:
1. Multiply the projected elementary matrices: `p(g'(t))` has rows `(0,t)` and
   `(-t⁻¹,0)`, so `p(h'(t)) = diag(t,t⁻¹)` and `h'(1)=1`. Centrality makes
   conjugation by any lift of `h(s)` the stated diagonal action, hence conjugation
   by `h'(s)` multiplies the upper parameter by `s²` and the lower by `s⁻²`.
2. Apply this to the three factors of `g'(t)` and divide by the case `t=1`.
   Commutativity of the diagonal preimage gives
   `h'(s²*t)=h'(s²)*h'(t)`. By lem-sfb-fppf-local-unit-square-root, every unit
   is an fppf-local square, in every characteristic. The sheaf axiom descends this
   equality, proving multiplicativity of the specified natural family `h'`.
3. Substitute its definition to obtain `h'(s)g'(t)=g'(s*t)`. Expand the Weyl
   products and cancel lower-root factors, obtaining
   `Y((s-1)/(s²*t))*h'(s)*X(t)=X(s*t)*Y((s-1)/(s*t))`.
   For units `u` and `w=1+u*v`, substitute `s=w,t=u/w` to get the first Gauss
   identity in the unit case.
4. For arbitrary `u,v` with unit `w`, use lem-sfb-fppf-local-two-unit-decomposition
   to write `u=a+b` locally with `a,b,q=1+b*v` units. Apply the unit case first
   to `(b,v)` and then to `(a,v/q)`, with parameters `q,w/q`. Move `h'(q)`
   leftward by the conjugation formula, multiply the two diagonal factors, and
   add the upper parameters: `a/(q*w)+b/q=u/w`. Descend the resulting first
   Gauss equality by the sheaf axiom.
5. Apply that equality to `-u,-v` and take inverses, using additivity of both
   root lifts, to obtain the second Gauss equality. Every product and equality
   commutes with restriction on S-schemes, giving a group-sheaf homomorphism
   into the preimage of the diagonal torus. -/
theorem lifted_root_gauss_relations {S : Scheme.{u}}
    (Z : Over S) [GrpObj Z] [IsCommMonObj Z]
    (_hZsep : IsClosedImmersion (pullback.diagonal Z.hom))
    (E : (Over S)ᵒᵖ ⥤ GrpCat.{v})
    (_hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) E)
    (i : ∀ T : Over S, (T ⟶ Z) →* E.obj (op T))
    (_hi_nat : ∀ (T U : Over S) (f : U ⟶ T) (z : T ⟶ Z),
      E.map f.op (i T z) = i U (f ≫ z))
    (p : ∀ T : Over S,
      E.obj (op T) →* Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤))
    (_hp_nat : ∀ (T U : Over S) (f : U ⟶ T) (e : E.obj (op T)),
      p U (E.map f.op e) = Matrix.SpecialLinearGroup.map f.left.appTop.hom (p T e))
    (_hi_inj : ∀ T : Over S, Function.Injective (i T))
    (_hexact : ∀ (T : Over S) (e : E.obj (op T)),
      p T e = 1 ↔ ∃ z : T ⟶ Z, i T z = e)
    (_hp_local : ∀ (T : Over S)
      (g : Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤)),
      ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
        ∀ (U : Over S) (f : U ⟶ T), R f →
          ∃ e : E.obj (op U), p U e = Matrix.SpecialLinearGroup.map f.left.appTop.hom g)
    (_hcentral : ∀ (T : Over S) (z : T ⟶ Z) (e : E.obj (op T)),
      Commute (i T z) e)
    (_hD : ∀ (T : Over S) (a b : E.obj (op T)) (s t : Γ(T.left, ⊤)ˣ),
      (p T a).val = !![(s : Γ(T.left, ⊤)), 0; 0, (↑s⁻¹ : Γ(T.left, ⊤))] →
      (p T b).val = !![(t : Γ(T.left, ⊤)), 0; 0, (↑t⁻¹ : Γ(T.left, ⊤))] →
      Commute a b)
    (X Y : ∀ T : Over S, Multiplicative Γ(T.left, ⊤) →* E.obj (op T))
    (_hX_nat : ∀ (T U : Over S) (f : U ⟶ T) (a : Γ(T.left, ⊤)),
      E.map f.op (X T (Multiplicative.ofAdd a)) =
        X U (Multiplicative.ofAdd (f.left.appTop a)))
    (_hY_nat : ∀ (T U : Over S) (f : U ⟶ T) (a : Γ(T.left, ⊤)),
      E.map f.op (Y T (Multiplicative.ofAdd a)) =
        Y U (Multiplicative.ofAdd (f.left.appTop a)))
    (_hX_lift : ∀ (T : Over S) (a : Γ(T.left, ⊤)),
      p T (X T (Multiplicative.ofAdd a)) =
        Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one a)
    (_hY_lift : ∀ (T : Over S) (a : Γ(T.left, ⊤)),
      p T (Y T (Multiplicative.ofAdd a)) =
        Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a)
    (_hX_equiv : ∀ (T : Over S) (s : Γ(T.left, ⊤)ˣ) (e : E.obj (op T)),
      (p T e).val = !![(s : Γ(T.left, ⊤)), 0; 0, (↑s⁻¹ : Γ(T.left, ⊤))] →
      ∀ a : Γ(T.left, ⊤), e * X T (Multiplicative.ofAdd a) * e⁻¹ =
        X T (Multiplicative.ofAdd ((s : Γ(T.left, ⊤)) ^ 2 * a)))
    (_hY_equiv : ∀ (T : Over S) (s : Γ(T.left, ⊤)ˣ) (e : E.obj (op T)),
      (p T e).val = !![(s : Γ(T.left, ⊤)), 0; 0, (↑s⁻¹ : Γ(T.left, ⊤))] →
      ∀ a : Γ(T.left, ⊤), e * Y T (Multiplicative.ofAdd a) * e⁻¹ =
        Y T (Multiplicative.ofAdd ((↑s⁻¹ : Γ(T.left, ⊤)) ^ 2 * a))) :
    ∃ H : ∀ T : Over S, Γ(T.left, ⊤)ˣ →* E.obj (op T),
      (∀ (T : Over S) (t : Γ(T.left, ⊤)ˣ), H T t = diagonalLift (X T) (Y T) t) ∧
      (∀ (T U : Over S) (f : U ⟶ T) (t : Γ(T.left, ⊤)ˣ),
        E.map f.op (H T t) = H U (Units.map f.left.appTop.hom t)) ∧
      (∀ (T : Over S) (t : Γ(T.left, ⊤)ˣ),
        (p T (H T t)).val = !![(t : Γ(T.left, ⊤)), 0; 0, (↑t⁻¹ : Γ(T.left, ⊤))]) ∧
      (∀ (T : Over S) (s t : Γ(T.left, ⊤)ˣ),
        H T s * weylLift (X T) (Y T) t = weylLift (X T) (Y T) (s * t)) ∧
      (∀ (T : Over S) (a b : Γ(T.left, ⊤)) (w : Γ(T.left, ⊤)ˣ),
        (w : Γ(T.left, ⊤)) = 1 + a * b →
          X T (Multiplicative.ofAdd a) * Y T (Multiplicative.ofAdd b) =
            Y T (Multiplicative.ofAdd (b * (↑w⁻¹ : Γ(T.left, ⊤)))) * H T w *
              X T (Multiplicative.ofAdd (a * (↑w⁻¹ : Γ(T.left, ⊤))))) ∧
      (∀ (T : Over S) (a b : Γ(T.left, ⊤)) (w : Γ(T.left, ⊤)ˣ),
        (w : Γ(T.left, ⊤)) = 1 + a * b →
          Y T (Multiplicative.ofAdd b) * X T (Multiplicative.ofAdd a) =
            X T (Multiplicative.ofAdd (a * (↑w⁻¹ : Γ(T.left, ⊤)))) * (H T w)⁻¹ *
              Y T (Multiplicative.ofAdd (b * (↑w⁻¹ : Γ(T.left, ⊤))))) := by
  sorry

end AlgebraicGeometry.LiftedRootGauss

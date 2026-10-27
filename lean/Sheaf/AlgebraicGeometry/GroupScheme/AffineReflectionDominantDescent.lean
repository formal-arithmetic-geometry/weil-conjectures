module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.Logic.Relation
import Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit

/-! # Dominant representatives of affine-reflection error weights

Source: Andersen, The strong linkage principle (1980), Definition 1, Proposition 1,
Lemma 1, pp.54--55, and Lemma 5, p.58.
(blueprint: lem-sfb-affine-reflection-dominant-descent)

The auxiliary definitions spell out the orders and shifted actions of this statement.
The Weyl group is the actual normalizer quotient; its action is characterized on all
algebra points, and its length is Mathlib's Coxeter length, with the specified simple roots.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

namespace AffineWeight

variable {I : Type v} {X : Type w} {Y : Type t}
variable [AddCommGroup X] [AddCommGroup Y] (P : RootDatum I X Y) (b : P.Base)

/-- The root dominance order: the difference is a nonnegative integral sum of simple roots.
Source: Andersen (1980), p.54 (blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def LE (y x : X) : Prop :=
  x - y ∈ AddSubmonoid.closure (P.root '' (b.support : Set I))

/-- Strict root dominance means dominance and unequal weights.
Source: Andersen (1980), p.54 (blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def LT (y x : X) : Prop := LE P b y x ∧ y ≠ x

/-- The closed shifted dominant chamber, including its walls.
Source: Andersen (1980), p.54 (blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def Dominant (ρ x : X) : Prop :=
  ∀ α ∈ b.support, 0 ≤ P.toLinearMap (x + ρ) (P.coroot α)

/-- The rho-shifted reflection on the integral character lattice.
Source: Andersen (1980), Definition 1
(blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def reflectionDot (ρ : X) (α : I) (x : X) : X := P.reflection α (x + ρ) - ρ

/-- An affine lowering edge, written from its lower to its upper endpoint.
Source: Andersen (1980), Definition 1
(blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def Edge (ρ : X) (p : ℕ) (y x : X) : Prop :=
  ∃ β : I, b.IsPos β ∧ ∃ n : ℤ, 0 ≤ n ∧
    y = reflectionDot P ρ β x + (n * (p : ℤ)) • P.root β ∧ LE P b y x

/-- Strong affine linkage is the finite reflexive transitive closure of lowering edges.
Source: Andersen (1980), Definition 1
(blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def Linked (ρ : X) (p : ℕ) (y x : X) : Prop :=
  Relation.ReflTransGen (Edge P b ρ p) y x

/-- The shifted action of a specified action on a lattice.
Source: Andersen (1980), p.54 (blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def dot {W : Type v} (a : W → X → X) (ρ : X) (g : W) (x : X) : X :=
  a g (x + ρ) - ρ

/-- Pullback of characters by the inverse torus automorphism, the normalizer action on X.
Source: Andersen (1980), p.54; Milne, 21.1--21.2
(blueprint: lem-sfb-affine-reflection-dominant-descent). -/
def characterAction {F : Type u} [Field F]
    {T S : Grp (Over (Spec (.of F)))} (iT : T ⟶ S)
    (a : RankOneRoots.Weyl iT →* Aut T) (g : RankOneRoots.Weyl iT)
    (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) :
    Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :=
  Additive.ofMul ((a g).inv ≫ χ.toMul)

end AffineWeight

/-- Dominant finite-dot-orbit representatives exist uniquely, strict dominance is
well founded on the shifted chamber, and every interior affine-reflection error has
strictly smaller dominant representative strongly linked to the initial weight.
The Coxeter system and longest-element length refer to the actual normalizer quotient.

Source: Andersen (1980), Definition 1, Proposition 1 and Lemma 1, pp.54--55;
reduced words, p.57; Lemma 5, p.58.
(blueprint: lem-sfb-affine-reflection-dominant-descent)

Proof plan:
1. By lem-sfb-semisimple-roots-span and lem-sfb-weyl-reflection-realization the
   roots span the rational character space and W is the finite faithful reflection
   group. By lem-sfb-simple-root-reflection-generation its simple reflections
   generate. Average any positive definite real form over W. The reflection formula
   gives 2 b(v,beta) = <v,beta coroot> b(beta,beta). A simple reflection permutes
   the other positive roots, so lem-sfb-root-sign-word-deletion applies.
2. The prefix roots of a reduced word are positive: otherwise word deletion
   contradicts reducedness. Telescoping gives v-a(v) as the sum of positive prefix
   roots times the nonnegative simple pairings of v. Thus a dot u <= u for u in D.
3. A maximal element of each finite orbit is in D, since a negative simple pairing
   could be reflected upward. Two representatives in D bound one another by step 2,
   hence are equal. Successive negative-simple-pairing folds terminate at this d.
4. By lem-sfb-rho-regular-weyl-orbit the simple pairings of rho are one. The invariant
   form therefore has b(alpha,rho)>0 for every simple root. If u<=x in D, the
   nonnegative simple coordinates of x-u are bounded by b(x+rho,rho). Lower intervals
   are finite; selecting a minimal point in one proves well-foundedness on D.
5. If length(s_alpha w)=length(w)+1, word deletion applied to -w inverse alpha
   rules out w inverse alpha negative. Its positive-root expansion and x in D
   give r>=0 by the invariant form.
6. The equation z=y-(r-kp)alpha gives z linked to y. Apply
   lem-sfb-simple-chamber-fold-affine-step edge by edge while folding y to x, then
   while folding the lower endpoint to d(z). Every fold fixes x. Thus d(z) is linked
   to x and, summing the simple-root differences, d(z)<=x.
7. The invariant norm drops by (r-kp)kp b(alpha,alpha)>0. Consequently z and y
   cannot have the same dominant representative. Step 6 is therefore strict.
8. By lem-sfb-rho-regular-weyl-orbit there is a unique w0 reversing positive roots.
   Each simple reflection changes the inversion count by at most one, giving
   N<=length(w0). The positive prefix roots of a reduced word are distinct, since
   a repeated prefix root deletes two letters. Hence length(w0)<=N.
No irreducibility is used. On walls r may vanish and there is no allowed k. In rank
zero the chamber is the singleton zero and all error assertions are vacuous.
-/
theorem affine_reflection_dominant_descent
    {F : Type u} [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (S T B : Grp (Over (Spec (.of F))))
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B)
    (hTB : IsRhoBorelPair iT iB j)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aS : ModObj T.X S.X) (aB : ModObj T.X B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base) [P.IsReduced]
    (hconjS : aS.smul = (iT.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X)
    (hconjB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T S aS χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ, b.IsPos α ↔
      @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (ρ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hρ : (2 : ℤ) • ρ =
      ∑ β ∈ (@Finset.filter Φ b.IsPos (Classical.decPred _) Finset.univ), P.root β) :
    Finite (RankOneRoots.Weyl iT) ∧
    ∃ (act : RankOneRoots.Weyl iT →* Aut T),
      (∀ (n : RankOneRoots.normalizer iT) (A : CommAlgCat.{u} F)
        (t : StandardGroupSchemes.affine F A ⟶ T.X),
        t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
          (toUnit (StandardGroupSchemes.affine F A) ≫ n.val) * (t ≫ iT.hom.hom) *
            (toUnit (StandardGroupSchemes.affine F A) ≫ n.val)⁻¹) ∧
      ∃ (M : CoxeterMatrix b.support) (cs : CoxeterSystem M (RankOneRoots.Weyl iT)),
        (∀ (α : b.support)
          (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))),
          AffineWeight.characterAction iT act (cs.simple α) χ = P.reflection α.val χ) ∧
        (∃ w₀ : RankOneRoots.Weyl iT,
          Set.image (fun β : Φ ↦ AffineWeight.characterAction iT act w₀ β.val)
              {β : Φ | b.IsPos β} =
            Set.image (fun β : Φ ↦ -β.val) {β : Φ | b.IsPos β} ∧
          cs.length w₀ = (@Finset.filter Φ b.IsPos (Classical.decPred _) Finset.univ).card) ∧
        WellFounded (fun (y x : {x // AffineWeight.Dominant P b ρ x}) ↦
          AffineWeight.LT P b y.val x.val) ∧
        ∃ d : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →
          Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          (∀ y, AffineWeight.Dominant P b ρ (d y) ∧
            (∃ w : RankOneRoots.Weyl iT,
              d y = AffineWeight.dot (AffineWeight.characterAction iT act) ρ w y) ∧
            ∀ z, AffineWeight.Dominant P b ρ z →
              (∃ w : RankOneRoots.Weyl iT,
                z = AffineWeight.dot (AffineWeight.characterAction iT act) ρ w y) → z = d y) ∧
          ∀ (x : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))),
            AffineWeight.Dominant P b ρ x → ∀ (α : b.support) (w : RankOneRoots.Weyl iT),
            cs.length (cs.simple α * w) = cs.length w + 1 →
            0 ≤ P.toLinearMap
              (AffineWeight.dot (AffineWeight.characterAction iT act) ρ w x + ρ)
              (P.coroot α.val) ∧
            ∀ k : ℤ, 0 < k * (p : ℤ) →
              k * (p : ℤ) < P.toLinearMap
                (AffineWeight.dot (AffineWeight.characterAction iT act) ρ w x + ρ)
                (P.coroot α.val) →
              ∀ z : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
                z = AffineWeight.reflectionDot P ρ α.val
                  (AffineWeight.dot (AffineWeight.characterAction iT act) ρ w x) +
                    (k * (p : ℤ)) • P.root α.val →
                AffineWeight.LT P b (d z) x ∧ AffineWeight.Linked P b ρ p (d z) x := by
  sorry

end AlgebraicGeometry

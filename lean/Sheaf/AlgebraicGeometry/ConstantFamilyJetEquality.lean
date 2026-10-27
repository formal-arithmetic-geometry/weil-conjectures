module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Equality of morphisms detected by all jets of a constant rational section

Source: Stacks Project, Algebra, Tag 00IQ, `lemma-intersection-powers-ideal-module`,
part (2), and Tag 00IP. This is the agent-formulated constant-family consequence isolating
Milne, Algebraic Groups, Proposition 8.9, p.150, used for Proposition 8.25.
(blueprint: lem-sfb-constant-family-jet-equality)

The jet maps are constructed from the actual kernel of evaluation on the stalk.
Restriction to an open subscheme is expressed by its inverse image, a scheme pullback.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The canonical map Spec(O_(X,P)/ker(O_(X,P) → k)^(n+1)) → X, obtained from
`Ideal.Quotient.mk` and `Scheme.fromSpecStalk`. Evaluation is the stalk map of the rational
point followed by the canonical identification of the stalk of Spec k with k.
Source: Stacks, Tag 01HV, and the construction in the constant-family consequence of Tag 00IQ.
(blueprint: lem-sfb-constant-family-jet-equality) -/
noncomputable def rationalPointJetInclusion (k : Type u) [Field k] {X : Scheme.{u}}
    (P : Spec (.of k) ⟶ X) (n : ℕ) :
    Spec (.of (X.presheaf.stalk (P (IsLocalRing.closedPoint k)) ⧸
      RingHom.ker (stalkClosedPointTo P).hom ^ (n + 1))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (RingHom.ker (stalkClosedPointTo P).hom ^ (n + 1)))) ≫
      X.fromSpecStalk (P (IsLocalRing.closedPoint k))

/-- The canonical map T ×_k X_n → T ×_k X: the first projection is unchanged and the
second is composed with the actual quotient-stalk spectrum map. The k-structure on X_n
is the composite through X, so this construction requires no chosen comparison map.
Source: the constant-family consequence of Stacks, Tag 00IQ, affine tensor calculation.
(blueprint: lem-sfb-constant-family-jet-equality) -/
noncomputable def constantFamilyJetMap (k : Type u) [Field k] {T X : Scheme.{u}}
    (t : T ⟶ Spec (.of k)) (s : X ⟶ Spec (.of k)) (P : Spec (.of k) ⟶ X) (n : ℕ) :
    pullback t (rationalPointJetInclusion k P n ≫ s) ⟶ pullback t s :=
  pullback.lift (pullback.fst t (rationalPointJetInclusion k P n ≫ s))
    (pullback.snd t (rationalPointJetInclusion k P n ≫ s) ≫ rationalPointJetInclusion k P n)
    (pullback.condition (f := t) (g := rationalPointJetInclusion k P n ≫ s) |>.trans
      (Category.assoc _ _ _).symm)

/-- All positive-order jets of a constant rational section detect equality of k-morphisms
on any open containing that section, including for nonreduced or disconnected T.
Source: agent-formulated geometric consequence of Stacks, Tag 00IQ, part (2), and Tag 00IP;
Milne, Algebraic Groups, Proposition 8.9, p.150, motivates the formal-detection input.
(blueprint: lem-sfb-constant-family-jet-equality)

The condition on E says that the inverse image of P under the second projection lies in E.
Since P is k-rational, this is exactly containment of T ×_k {P}. Every jet family has this
support, so pulling it back along E.ι is its canonical restriction to E and is isomorphic
to the whole jet family. Thus hjet states agreement on every T ×_k X_n, n ≥ 1.

Proof (the eight steps of the node):
1. Pull back the closed diagonal of Z along (f,g), obtaining a closed equalizer Q in E
   (`lem-weil-pbc-closed-immersion-base-change`). Let I be its ideal. Agreement on jets
   says that all jets factor through Q; it suffices to show I = 0.
2. On an affine neighbourhood Spec A of P, A is a finite-type domain and R = A_p
   (`lem-weil-pbc-affine-open-stalk-localization`). It is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian` and `lem-weil-pbc-localization-noetherian`.
   Apply `lem-weil-pbc-krull-intersection-jacobson` to R and its maximal ideal. Injectivity
   of A → A_p then gives intersection p^r = 0 in A.
3. For an affine parameter Spec B put C = B ⊗_k A and J = pC. In a k-basis of B, J^r
   consists precisely of sums with coefficients in p^r. Hence intersection J^r = 0,
   C/J^r = B ⊗_k (A/p^r), and C/J = B.
4. For s outside p, write s = c(1-u), with c in k nonzero and u in p. The finite geometric
   series inverts s modulo p^r, giving A/p^r = R/m^r. Thus the jet families on this chart
   are Spec(C/J^(n+1)); their support is the constant section, so they factor through E.
5. Write the closed complement of E in Spec C as V(K). Its disjointness from V(J) gives
   K+J = C. Choose h in K with 1-h in J, so V(J) lies in D(h) and D(h) lies in E.
   The geometric series makes h invertible modulo every J^r.
6. The maps C_h → C/J^(n+1), n ≥ 1, are jointly injective: for a fraction c/h^e whose
   images vanish, c lies in every J^(n+1), hence is zero. The ideal of Q over D(h) is
   killed by all these maps and is therefore zero.
7. The same injectivity shows h is a non-zero-divisor in C and all C_s, so restrictions
   to D(h) are injective. To pass from this chart to all of T_0 × X, take any nonempty
   affine V = Spec A' of X. Integrality gives a nonempty D(a) inside V ∩ U, with a ≠ 0.
   Multiplication by a is injective on B ⊗_k A', coefficientwise in a k-basis of B;
   localized fraction calculations give injective restrictions on every principal open.
   The sheaf uniqueness axiom then proves injectivity on every open subset.
8. Sections of I vanish on D(h), hence vanish on E ∩ (T_0 × X) by step 7. Affine T_0
   cover T, so I = 0, Q = E and f = g. Empty T is immediate; neither reducedness of B
   nor regularity of R was used. -/
theorem eq_of_constantFamily_jets (k : Type u) [Field k] [IsAlgClosed k]
    {X T Z : Scheme.{u}} (s : X ⟶ Spec (.of k)) (t : T ⟶ Spec (.of k))
    (z : Z ⟶ Spec (.of k)) [IsIntegral X] [IsSeparated s]
    [LocallyOfFiniteType s] [QuasiCompact s] [LocallyOfFiniteType t] [QuasiCompact t]
    [IsSeparated z] (P : Spec (.of k) ⟶ X) (hP : P ≫ s = 𝟙 (Spec (.of k)))
    (E : (pullback t s).Opens)
    (hE : ∀ y : ↥(pullback t s), pullback.snd t s y = P (IsLocalRing.closedPoint k) → y ∈ E)
    (f g : E.toScheme ⟶ Z)
    (hf : f ≫ z = E.ι ≫ pullback.fst t s ≫ t)
    (hg : g ≫ z = E.ι ≫ pullback.fst t s ≫ t)
    (hjet : ∀ n : ℕ, 1 ≤ n →
      pullback.snd (constantFamilyJetMap k t s P n) E.ι ≫ f =
        pullback.snd (constantFamilyJetMap k t s P n) E.ι ≫ g) :
    f = g := by
  sorry

end AlgebraicGeometry.Scheme

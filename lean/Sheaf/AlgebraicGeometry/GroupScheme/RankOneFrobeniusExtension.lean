module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Frobenius-compatible rank-one homomorphisms

Source: Milne, Algebraic Groups (2017), Propositions 23.14 and 23.16, pp.489--490;
formula (146), pp.485--486 (blueprint: lem-sfb-rank-one-frobenius-extension).

Index 1 is the source and index 0 the target. The two Boolean values index the
positive and negative root subgroups. Surjectivity below is surjectivity of schemes.
The normalizer formula pins the coroot to the geometric root datum: the abstract
root-pairing axioms alone do not identify coroots in the presence of a central torus.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A Frobenius-compatible homomorphism of the maximal tori extends to a homomorphism
of rank-one reductive groups, with scalar times qth-power formulas on both roots.
The root data use the actual character and cocharacter groups and composition
pairing of reductive_borel_pair_structure. The normalizer formula expresses the
canonical coroot reflection, including its action on central-torus characters.
Source: Milne, Propositions 23.14 and 23.16, pp.489--490, and formula (146), pp.485--486
(blueprint: lem-sfb-rank-one-frobenius-extension).

Proof:
1. Apply lem-sfb-opposite-root-sl2-parametrizations to each root and then
   lem-sfb-rank-one-semidirect-presentation. This gives SL2 semidirect T presentations
   with faithfully flat quotient maps and coroot kernels isomorphic to Gm.
2. Entrywise qth powers give a polynomial F-group homomorphism on SL2: in positive
   characteristic the binomial identity iterates; for p=1 or e=0 it is the identity.
   This map fixes coefficients in F and raises matrix-coordinate variables to qth powers.
3. The root identity makes (M,t) mapped to (M raised entrywise to q,h(t)) a
   homomorphism of the semidirect presentations. The coroot identity sends the
   kernel element (diag(s,s inverse),coroot(s) inverse) to the target kernel at s^q.
4. By lem-sfb-faithfully-flat-group-quotient-universal descend the composite with
   the target quotient to f. Evaluate on (I,t) and on the upper and lower
   unitriangular matrices to obtain the torus restriction and qth-power formulas.
5. Any two Ga parametrizations of a root subgroup differ by a nonzero scalar:
   a polynomial automorphism with polynomial inverse has degree one and fixes zero.
   If the source and target changes have scalars a and b, take c=b*a^(-q).
   The polynomial inclusion z mapped to c*x^q makes F[x] free over F[z] with basis
   1,x,...,x^(q-1); hence the induced root subgroup map is surjective as a scheme.
   The formulas hold on every algebra, including nonreduced algebras. This covers
   q=1, characteristic two and central tori of arbitrary dimension. -/
theorem rankOne_frobenius_extension
    {F : Type u} [Field F] [IsAlgClosed F] (p e : ℕ) [ExpChar F p]
    (H T : Fin 2 → Grp (Over (Spec (.of F))))
    (iT : ∀ i : Fin 2, T i ⟶ H i)
    (hH : ∀ i, ReductiveTorusCentralizer.IsReductive (H i))
    (hT : ∀ i, ReductiveTorusCentralizer.IsMaximalTorus (iT i))
    (hsplit : ∀ i, ∃ r : ℕ, Nonempty (T i ≅ MultiplicativeType.splitTorus F r))
    [∀ i, IsCommMonObj (T i).X]
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aH : ∀ i, ModObj (T i).X (H i).X)
    (hconj : ∀ i, (aH i).smul =
      ((iT i).hom.hom ⊗ₘ 𝟙 (H i).X) ≫ GrpObj.conj (H i).X)
    (Φ : ∀ i, Finset (Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (D : ∀ i, RootDatum (Φ i)
      (Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T i)))
    (hred : ∀ i, (D i).IsReduced)
    (hroot : ∀ i (χ : Φ i), (D i).root χ = χ.val)
    (hpair : ∀ i (χ : Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T i)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ ((D i).toLinearMap χ ν))
    (hweights : ∀ i (χ : Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))),
      χ ∈ Φ i ↔ χ ≠ 0 ∧
        @TorusCharacterTangent.weightSpace F _ (T i) (H i) (aH i) χ.toMul ≠ ⊥)
    (α : ∀ i, Φ i)
    (hrank : ∀ i (χ : Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))),
      χ ∈ Φ i ↔ χ = (α i).val ∨ χ = -(α i).val)
    (hreflection : ∀ i, ∃ n : 𝟙_ (Over (Spec (.of F))) ⟶ (H i).X,
      ∀ (W : Over (Spec (.of F))) (t : W ⟶ (T i).X),
        (toUnit W ≫ n) * (t ≫ (iT i).hom.hom) * (toUnit W ≫ n)⁻¹ =
          (t ≫ (iT i).hom.hom) *
            (t ≫ (α i).val.toMul.hom.hom ≫ ((D i).coroot (α i)).toMul.hom.hom ≫
              (iT i).hom.hom)⁻¹)
    (U : Fin 2 → Bool → Grp (Over (Spec (.of F))))
    (j : ∀ i ε, U i ε ⟶ H i)
    (hU : ∀ i ε,
      IsClosedSubgroupScheme (j i ε).hom.hom ∧ Smooth (U i ε).X.hom ∧
      ConnectedSpace (U i ε).X.left ∧
      @TorusCharacterTangent.IsStable F _ (T i) (H i) (aH i) _ (j i ε) ∧
      (GrpObj.differential (j i ε).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ (T i) (H i) (aH i)
          (if ε then (α i).val.toMul else (-(α i).val).toMul))
    (hparameter : ∀ i ε, Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ U i ε))
    (h : T 1 ⟶ T 0)
    (hstar : Additive (T 0 ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →+
      Additive (T 1 ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hhstar : ∀ χ, hstar χ = Additive.ofMul (h ≫ χ.toMul))
    (hinj : Function.Injective hstar) (hfinite : Finite (_ ⧸ hstar.range))
    (hα : hstar (α 0).val = (p ^ e) • (α 1).val)
    (hcoroot : ((D 1).coroot (α 1)).toMul.hom.hom ≫ h.hom.hom =
      ((𝟙 (StandardGroupSchemes.multiplicative F)) ^ (p ^ e)) ≫
        ((D 0).coroot (α 0)).toMul.hom.hom) :
    ∃ (f : H 1 ⟶ H 0) (fU : ∀ ε, U 1 ε ⟶ U 0 ε),
      iT 1 ≫ f = h ≫ iT 0 ∧
      (∀ ε, j 1 ε ≫ f = fU ε ≫ j 0 ε) ∧
      (∀ ε, Surjective (fU ε).hom.hom.left) ∧
      ∀ (x : ∀ i ε, Grp.mk (StandardGroupSchemes.additive F) ≅ U i ε),
        ∃ c : Bool → Fˣ, ∀ (ε : Bool) (A : Type u) [CommRing A] [Algebra F A] (a : A),
          TorusCharacterTangent.additiveParameterPoint F a ≫
              (x 1 ε).hom.hom.hom ≫ (j 1 ε).hom.hom ≫ f.hom.hom =
            TorusCharacterTangent.additiveParameterPoint F
                (algebraMap F A (c ε : F) * a ^ (p ^ e)) ≫
              (x 0 ε).hom.hom.hom ≫ (j 0 ε).hom.hom := by
  sorry

end AlgebraicGeometry

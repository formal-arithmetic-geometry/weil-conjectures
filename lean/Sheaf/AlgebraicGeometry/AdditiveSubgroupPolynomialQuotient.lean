/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The additive polynomial quotient of a closed subgroup of the additive group

Source: Milne, Algebraic Groups (2017), Exercise 14-3(a), p.301, Example 14.40,
p.292, and the equivariant exact sequence in Theorem 15.34(d), p.319
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient).

The polynomial map and its points use the existing affine group schemes. The quotient
is the fppf sheafification of the coequalizer of translation and projection. On affine
tests this is precisely the presheaf R / N(R). Lifted Yoneda values put sheafification
in the universe of the big site; this changes no points or quotient equivalence relation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj Opposite

namespace AlgebraicGeometry.StandardGroupSchemes

noncomputable section

variable (k : Type u) [Field k]

/-- Evaluation defines the polynomial endomorphism of the affine line.
Source: Milne, Exercise 14-3(a), p.301
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def additivePolynomialMap (P : Polynomial k) : additive k ⟶ additive k :=
  map k (Polynomial.aeval P)

/-- The R-point of the additive group with coordinate x.
Source: Milne, Example 14.40, p.292
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def additiveCoordinatePoint (R : Type u) [CommRing R] [Algebra k R] (x : R) :
    affine k R ⟶ additive k :=
  map k (Polynomial.aeval x)

/-- Pull back the Laurent coordinate t along an R-point of the multiplicative group.
Its value is a unit since t has inverse t⁻¹ in the coordinate algebra.
Source: Milne, Theorem 15.34(d), p.319
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def multiplicativeCoordinateValue {R : Type u} [CommRing R] [Algebra k R]
    (g : affine k R ⟶ multiplicative k) : R :=
  (algSpec.fullyFaithful (R := .of k) |>.preimage g).unop.hom (LaurentPolynomial.T 1)

/-- The defining ideal of a closed subscheme of the affine line, pulled back along
k[T] ≅ Γ(Spec k[T], O) before taking the kernel of restriction.
Source: Milne, Exercise 14-3(a), p.301
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def additiveSubgroupDefiningIdeal {N : Over (Spec (.of k))} (i : N ⟶ additive k) :
    Ideal (Polynomial k) :=
  RingHom.ker (((Scheme.ΓSpecIso (.of (Polynomial k))).inv ≫ i.left.appTop).hom)

/-- Translation (z,x) ↦ i(z)+x, using the existing additive group law on Hom sets.
Source: Milne, Exercise 14-3(a), p.301
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def additiveSubgroupTranslation {N : Over (Spec (.of k))} (i : N ⟶ additive k) :
    N ⊗ additive k ⟶ additive k :=
  (fst N (additive k) ≫ i) * snd N (additive k)

/-- The pointwise coset presheaf: the coequalizer of translation and projection.
Colimits of presheaves of sets are pointwise; the translation orbit of x is x+N(R).
Source: Milne, Exercise 14-3(a), p.301
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def additiveSubgroupCosetPresheaf {N : Over (Spec (.of k))} (i : N ⟶ additive k) :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1) :=
  coequalizer (uliftYoneda.{u + 1}.map (additiveSubgroupTranslation k i))
    (uliftYoneda.{u + 1}.map (snd N (additive k)))

/-- The actual fppf sheaf quotient, obtained by sheafifying the coset presheaf.
Source: Milne, Exercise 14-3(a), p.301
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def additiveSubgroupFppfQuotient {N : Over (Spec (.of k))} (i : N ⟶ additive k) :
    Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
    (additiveSubgroupCosetPresheaf k i)

/-- The quotient projection before sheafification.
Source: Milne, Exercise 14-3(a), p.301
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient). -/
def additiveSubgroupCosetProjection {N : Over (Spec (.of k))} (i : N ⟶ additive k) :
    uliftYoneda.{u + 1}.obj (additive k) ⟶ additiveSubgroupCosetPresheaf k i :=
  coequalizer.π (uliftYoneda.{u + 1}.map (additiveSubgroupTranslation k i))
    (uliftYoneda.{u + 1}.map (snd N (additive k)))

/-- A proper closed additive subgroup has a unique monic defining polynomial. The
polynomial is additive, gives a faithfully flat finitely presented group morphism with
the specified scheme-theoretic kernel, and identifies its fppf quotient with Gₐ.
Scalar stability through η gives the quotient character η raised to the degree.

Source: Milne, Exercise 14-3(a), p.301; Example 14.40, pp.292-293;
Theorem 15.34(d), p.319
(blueprint: lem-sfb-additive-subgroup-polynomial-quotient).

Proof plan (the seven steps of the DAG node):
1. A closed immersion into Spec k[T] has coordinate quotient k[T]/I. Properness
   gives I ≠ 0; the identity makes every element of I vanish at 0, so I ≠ ⊤.
   The polynomial PID lemma (lem-pur-polynomial-field-pid) gives a generator;
   divide by its leading coefficient. It is monic and has positive degree and zero
   constant term. Two monic generators divide each other; degree additivity and
   comparison of leading coefficients make them equal.
2. In D(X,Y)=P(X+Y)-P(X)-P(Y), each surviving exponent is below n. The two
   universal roots in (k[X]/P)[Y]/P sum to a root by the subgroup property.
   Apply lem-weil-pbc-monic-quotient-free successively over k[X]/P and k to
   make each coefficient of D zero. This proves the polynomial identity.
3. Substitution U ↦ P(T) defines q, and the identity proves IsMonHom q. The
   pullback of the zero section is Spec k[T]/P, so it is precisely N, with its inclusion
   (def-sc-gm-ga, def-sc-group-scheme, def-weil-pbc-algebra-hom-quotient).
4. The k[U]-algebra k[T] is k[U][T]/(P(T)-U): the two substitutions fix T, and
   U=P(T) in the quotient. The relation is monic of degree n>0. Apply
   lem-sfb-monic-quotient-faithful-tensor-coordinates for faithful flatness.
   The one-generator one-relation presentation gives finite presentation.
5. Flatness and surjectivity follow from lem-weil-pbc-flat-ring-map-iff-flat-affine
   and lem-weil-pbc-faithfully-flat-surjective-spectrum. The same finite basis works
   after localization, so q is finite and locally finitely presented, hence finite
   locally free. Its affine source and target give quasi-compactness and separatedness
   by the three affine-scheme lemmas in proof_deps, hence global finite presentation.
6. Translation gives the kernel pair by (z,x) ↦ (x,x+z), with inverse
   (x,y) ↦ (y-x,x). The maps are polynomial and inverse, including scheme structure.
   Apply lem-a1-fppf-kernel-pair-quotient-descent. Thus sheafification of the
   pointwise cosets is Gₐ, with the comparison induced by q. Since q is a group
   homomorphism, this comparison preserves addition.
7. Given any k-algebra R and g in G(R), put a=η(g). In R[T]/P, stability makes
   a times the universal root a root. P(aT)-a^n P(T) has degree below n by monicity,
   and vanishes in that quotient. The monic-quotient basis lemma forces it to be zero,
   also for nonreduced R and the zero ring. Evaluate at x to get the scalar formula;
   through the quotient comparison this is the scalar action by η^n. -/
theorem exists_additiveSubgroup_polynomial_quotient
    (N : Over (Spec (.of k))) [GrpObj N] (i : N ⟶ additive k)
    [IsClosedSubgroupScheme i] (hproper : ¬ IsIso i) :
    ∃ P : Polynomial k,
      P.Monic ∧ 0 < P.natDegree ∧
      Ideal.span ({P} : Set (Polynomial k)) = additiveSubgroupDefiningIdeal k i ∧
      (∀ Q : Polynomial k, Q.Monic →
        Ideal.span ({Q} : Set (Polynomial k)) = additiveSubgroupDefiningIdeal k i → Q = P) ∧
      P.eval 0 = 0 ∧
      P.eval₂ (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k)
          (MvPolynomial.X 0 + MvPolynomial.X 1) =
        P.eval₂ MvPolynomial.C (MvPolynomial.X 0) +
          P.eval₂ MvPolynomial.C (MvPolynomial.X 1) ∧
      IsMonHom (additivePolynomialMap k P) ∧
      (Polynomial.aeval (R := k) P).toRingHom.FaithfullyFlat ∧
      LocallyOfFinitePresentation (additivePolynomialMap k P).left ∧
      QuasiCompact (additivePolynomialMap k P).left ∧
      QuasiSeparated (additivePolynomialMap k P).left ∧
      (∃ e : N ≅ GrpObj.ker (additivePolynomialMap k P), e.hom ≫
        GrpObj.kerι (additivePolynomialMap k P) = i) ∧
      (∃ e : additiveSubgroupFppfQuotient k i ≅
          (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k)))
            (Type (u + 1))).obj (uliftYoneda.{u + 1}.obj (additive k)),
        (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k)))
            (Type (u + 1))).map (additiveSubgroupCosetProjection k i) ≫ e.hom =
          (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k)))
            (Type (u + 1))).map (uliftYoneda.{u + 1}.map (additivePolynomialMap k P))) ∧
      (∀ (G : Over (Spec (.of k))) [GrpObj G] [IsAffine G.left]
          [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
          (eta : G ⟶ multiplicative k) [IsMonHom eta],
        (∀ (R : Type u) [CommRing R] [Algebra k R]
            (g : affine k R ⟶ G) (x : R),
          (∃ z : affine k R ⟶ N, z ≫ i = additiveCoordinatePoint k R x) →
          ∃ z : affine k R ⟶ N, z ≫ i = additiveCoordinatePoint k R
            (multiplicativeCoordinateValue k (g ≫ eta) * x)) →
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (g : affine k R ⟶ G) (x : R),
          Polynomial.aeval (multiplicativeCoordinateValue k (g ≫ eta) * x) P =
            multiplicativeCoordinateValue k (g ≫ eta) ^ P.natDegree * Polynomial.aeval x P) := by
  sorry

end

end AlgebraicGeometry.StandardGroupSchemes

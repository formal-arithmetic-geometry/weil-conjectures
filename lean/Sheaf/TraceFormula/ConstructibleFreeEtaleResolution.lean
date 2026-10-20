module


public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.ConstructibleGeneratorEpimorphism
import Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite étale generators and bounded-above constructible resolutions

Source: literature/lu-zheng-duality-nearby-cycles-general-bases.pdf, Proof of Theorem 5.1,
finite étale generators and Kashiwara--Schapira Lemma 13.2.1(b), p. 42
(blueprint: lem-trf-constructible-free-etale-resolution).

The proof is the descending fibre-product induction of Stacks Tag 05T7, specialized to
finite étale generators.  The degree-zero inclusion and its cokernel give the canonical
brutal-truncation short exact sequence; `DerivedCategory.triangleOfSES` gives its
associated distinguished triangle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Etale

/-- Finite coproduct of a family in a category with finite coproducts.
Source: the finite disjoint-union clause of the node statement
(blueprint: lem-trf-constructible-free-etale-resolution). -/
noncomputable def finiteCoproduct
    {C : Type v} [Category.{w} C] [HasFiniteCoproducts C]
    (m : ℕ) (F : Fin m → C) : C :=
  letI : HasColimit (Discrete.functor F) :=
    (HasFiniteCoproducts.out m).has_colimit (Discrete.functor F)
  colimit (Discrete.functor F)

/-- The canonical inclusion of the degree-zero term as a complex concentrated in degree zero.
Source: Lu--Zheng, Theorem 5.1 proof, p. 42
(blueprint: lem-trf-constructible-free-etale-resolution). -/
noncomputable def degreeZeroInclusion
    {C : Type v} [Category.{w} C] [Preadditive C] [HasZeroObject C]
    (Q : CochainComplex C ℤ) (hQ : Q.IsStrictlyLE 0) :
    (CochainComplex.singleFunctor C 0).obj (Q.X 0) ⟶ Q :=
  HomologicalComplex.mkHomFromSingle (𝟙 (Q.X 0)) (fun k hk => by
    have hk_eq : (1 : ℤ) = k := by simpa only [ComplexShape.up_Rel, zero_add] using hk
    have hk' : 0 < k := by
      rw [← hk_eq]
      norm_num
    exact (Q.isZero_of_isStrictlyLE 0 k hk').eq_of_tgt _ _)

/-- The canonical short complex obtained by inserting the degree-zero subcomplex and taking
its cokernel.  Its third term is the brutal truncation in degrees `≤ -1`.
Source: Lu--Zheng Theorem 5.1 proof, p. 42
(blueprint: lem-trf-constructible-free-etale-resolution). -/
noncomputable def degreeZeroShortComplex
    {C : Type v} [Category.{w} C] [Abelian C]
    (Q : CochainComplex C ℤ) (hQ : Q.IsStrictlyLE 0) :
    ShortComplex (CochainComplex C ℤ) :=
  let f := degreeZeroInclusion Q hQ
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

/-- **Finite étale generators and bounded-above constructible resolutions.**
Let `X` be Noetherian and `Λ` finite commutative.  If `L` has constructible cohomology,
is bounded above, and vanishes in positive degrees, then it is represented by a complex
`Q` concentrated in degrees `≤ 0` whose terms are finite direct sums of extension-by-zero
constant sheaves along separated étale morphisms of finite type.  The kernels and cokernels
of all differentials are constructible.  The canonical degree-zero short exact sequence and
its distinguished derived triangle are included, and the third term has no cohomology in
nonnegative degrees.  No finite projective resolution or finite Tor-dimension assertion is
part of the statement.

Source: literature/lu-zheng-duality-nearby-cycles-general-bases.pdf, Proof of Theorem 5.1,
finite étale generators and Kashiwara--Schapira Lemma 13.2.1(b), p. 42; Stacks Project,
Tag 05T7 (blueprint: lem-trf-constructible-free-etale-resolution).

Proof plan:
1. The degree-zero subcomplex and its brutal quotient give a short exact sequence;
   `DerivedCategory.triangleOfSES` gives the displayed distinguished triangle.
2. Choose a bounded-above representative, shift it to positive-degree vanishing,
   and use constructibility closure and the finite-generator epimorphism on cone
   cohomology.
3. Descending on `n`, lift the epimorphism from the cycle pullback
   `ker (d_Q (n + 1)) ×_{K^(n+1)} K^n` to the cone cohomology, defining the next
   term and the comparison map.
4. The cone becomes acyclic degree by degree; finite étale terms and constructible
   kernel/cokernel closure give the asserted differential clauses.
5. Undo the shift and combine finitely many degree-zero summands as one finite
   disjoint union.  No finite projective resolution or finite Tor-dimension claim
   is used. -/
theorem constructibleFreeEtaleResolution
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (L : DerivedCategoryModule Λ X)
    (hL :
      (∀ n : ℤ,
        Scheme.IsConstructibleEtaleModuleSheaf
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj L)) ∧
      (∃ b : ℤ, ∀ n : ℤ, b < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj L)) ∧
      (∀ n : ℤ, 0 < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj L))) :
    ∃ (Q : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (hQ : Q.IsStrictlyLE 0)
      (e : L ≅
        (DerivedCategory.Q (C := Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} Λ))).obj Q),
      (∀ n : ℤ,
        ∃ (m : ℕ) (U : Fin m → X.Etale),
          (∀ i : Fin m,
            IsSeparated (U i).hom ∧
            LocallyOfFiniteType (U i).hom ∧
            QuasiCompact (U i).hom) ∧
          Nonempty (Q.X n ≅
            finiteCoproduct m (fun i : Fin m ↦
              (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (U i).hom inferInstance).obj
                ((constantSheaf (U i).left.smallEtaleTopology
                  (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))) ∧
      ∃ (U₀ : X.Etale),
        IsSeparated U₀.hom ∧ LocallyOfFiniteType U₀.hom ∧ QuasiCompact U₀.hom ∧
        Nonempty (Q.X 0 ≅
          (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) U₀.hom inferInstance).obj
            ((constantSheaf U₀.left.smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))) ∧
      (∀ n : ℤ,
        Scheme.IsConstructibleEtaleModuleSheaf (kernel (Q.d n (n + 1))) ∧
        Scheme.IsConstructibleEtaleModuleSheaf (cokernel (Q.d n (n + 1)))) ∧
      (Exists fun hS : (degreeZeroShortComplex
          (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) Q hQ).ShortExact =>
        ((∀ n : ℤ, 0 ≤ n →
          IsZero ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj
            ((DerivedCategory.Q (C := Sheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} Λ))).obj
              (degreeZeroShortComplex
                (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) Q hQ).X₃)))) ∧
        Triangle.mk
            ((DerivedCategory.Q (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).map
              (degreeZeroShortComplex
                (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) Q hQ).f ≫ e.inv)
            (e.hom ≫
              (DerivedCategory.Q (C := Sheaf X.smallEtaleTopology
                (ModuleCat.{u + 1} Λ))).map
              (degreeZeroShortComplex
                (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) Q hQ).g)
            (DerivedCategory.triangleOfSES (C :=
              Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) hS).mor₃ ∈
          distTriang (DerivedCategory
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))) := by
  sorry

end AlgebraicGeometry.Etale

end

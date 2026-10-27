/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.TrivialTorusCoherentData
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination

/-! # Projective fixed schemes of split torus representations

Source: Milne, Algebraic Groups (2017), Theorem 7.1, pp.138--139, Theorem 12.12,
pp.234--235, and Lemma 13.51 and its following paragraph, pp.274--275.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes).

An adapted basis identifies P(E) with the existing base-change projective space.
The auxiliary predicates spell out its induced action, its coordinate inclusions,
and representation of the fixed subfunctor. They specify morphisms over all test
algebras, including nonreduced ones. No fixed scheme is chosen by an existence axiom.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.ProjectiveTorusFixedWeights

/-- P(E) in coordinates of the chosen basis, with its actual structure map.
Source: Milne, Lemma 13.51, p.274; polynomial projective space by base change.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def projective (k : Type u) [Field k] (I : Type u) : Over (Spec (.of k)) :=
  Over.mk (ProjectiveSpace I (Spec (.of k)) ↘ Spec (.of k))

/-- The coordinate projections of the recorded product torus, including rank zero.
Source: Milne, Definition 12.14 and Lemma 13.51, pp.236, 274.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def torusCoordinate (k : Type u) [Field k] :
    (r : ℕ) → Fin r → ((MultiplicativeType.splitTorus k r).X ⟶
      StandardGroupSchemes.multiplicative k)
  | 0, i => Fin.elim0 i
  | r + 1, i => Fin.cases
      (fst (StandardGroupSchemes.multiplicative k) (MultiplicativeType.splitTorus k r).X)
      (fun j ↦ snd (StandardGroupSchemes.multiplicative k)
        (MultiplicativeType.splitTorus k r).X ≫ torusCoordinate k r j) i

/-- The projective point given by generating sections of a trivial line bundle.
Source: Milne, Example 13.50 and Lemma 13.51, p.274.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def ofSections {k : Type u} [Field k] {I : Type u}
    (A : CommAlgCat.{u} k) (s : I → Γ(Spec (.of A), ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) :
    StandardGroupSchemes.affine k A ⟶ projective k I :=
  Over.homMk (ProjectiveSpace.homOfSections (StandardGroupSchemes.affine k A).hom s hs)
    (ProjectiveSpace.homOfSections_over _ _ _)

/-- Matrix action on homogeneous coordinates, with the actual Spec global-section map.
Source: Milne, Chapter 4(a), pp.83--84, and Example 13.50, p.274.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def transformedSections {k : Type u} [Field k] {I : Type u} [Fintype I] [DecidableEq I]
    {T : Grp (Over (Spec (.of k)))} (ρ : T ⟶ Grp.mk (GeneralLinearGroup I k))
    (A : CommAlgCat.{u} k) (t : StandardGroupSchemes.affine k A ⟶ T.X)
    (s : I → Γ(Spec (.of A), ⊤)) : I → Γ(Spec (.of A), ⊤) :=
  fun i ↦ ∑ j, (Scheme.ΓSpecIso (.of A)).inv
    ((GeneralLinearGroup.homMulEquiv I k A (t ≫ ρ.hom.hom)).val i j) * s j

/-- The induced projective action, characterized on all generating homogeneous tuples.
Local triviality of line bundles makes this a characterization on every scheme point.
Source: Milne, Chapter 4(a), pp.83--84, and Example 13.50, p.274.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def IsInducedAction {k : Type u} [Field k] {I : Type u} [Fintype I] [DecidableEq I]
    {T : Grp (Over (Spec (.of k)))} (ρ : T ⟶ Grp.mk (GeneralLinearGroup I k))
    (a : ModObj T.X (projective k I)) : Prop :=
  ∀ (A : CommAlgCat.{u} k)
      (t : StandardGroupSchemes.affine k A ⟶ T.X)
      (s : I → Γ(Spec (.of A), ⊤)) (hs : Ideal.span (Set.range s) = ⊤),
      ∃ ht : Ideal.span (Set.range (transformedSections ρ A t s)) = ⊤,
        lift t (ofSections A s hs) ≫ a.smul =
          ofSections A (transformedSections ρ A t s) ht

/-- Fixedness under a homomorphism is tested after every algebra extension.
The torus case takes f = identity; the cocharacter case takes f = lambda.
Source: Milne, Theorem 7.1, pp.138--139.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def IsFixed {k : Type u} [Field k] {G : Grp (Over (Spec (.of k)))}
    {H X : Over (Spec (.of k))} (a : ModObj G.X X) (f : H ⟶ G.X)
    (A : CommAlgCat.{u} k) (x : StandardGroupSchemes.affine k A ⟶ X) : Prop :=
  ∀ (B : CommAlgCat.{u} k) (g : A ⟶ B)
    (t : StandardGroupSchemes.affine k B ⟶ H),
    lift (t ≫ f) ((algSpec (.of k)).map g.op ≫ x) ≫ a.smul =
      (algSpec (.of k)).map g.op ≫ x

/-- The specified inclusion represents the fixed subfunctor, with unique lifts.
Source: Milne, Theorem 7.1 and Lemma 13.51, pp.138--139, 274.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def RepresentsFixed {k : Type u} [Field k] {G : Grp (Over (Spec (.of k)))}
    {H X Z : Over (Spec (.of k))} (a : ModObj G.X X) (f : H ⟶ G.X) (j : Z ⟶ X) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (x : StandardGroupSchemes.affine k A ⟶ X),
    (∃! z : StandardGroupSchemes.affine k A ⟶ Z, z ≫ j = x) ↔ IsFixed a f A x

/-- The actual generators of the chart fixed ideal, rather than a radical or support.
Source: Milne, Example 13.50 and Lemma 13.51, p.274, chart calculation.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def chartIdeal {k : Type u} [Field k] {I Ω : Type u} (c : I → Ω) (i : I) :
    Ideal Γ(ProjectiveSpace I (Spec (.of k)),
      ProjectiveSpace.standardOpen I (Spec (.of k)) i) :=
  Ideal.span {z | ∃ j : I, c j ≠ c i ∧
    z = ProjectiveSpace.coordRatio I (Spec (.of k)) i j}

/-- A weight-block coordinate tuple extended by zero in all other blocks.
Source: Milne, Lemma 13.51, p.274.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def extendSections {I Ω : Type u} (c : I → Ω) (ω : Ω) {R : Type u} [Zero R]
    (s : {i : I // c i = ω} → R) : I → R := by
  classical
  exact fun i ↦ if h : c i = ω then s ⟨i, h⟩ else 0

/-- The canonical projective coordinate inclusion of a weight subspace.
Its normalization on generating coordinates determines the entire scheme morphism.
Source: Milne, Lemma 13.51, p.274.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def IsBlockInclusion {k : Type u} [Field k] {I Ω : Type u} (c : I → Ω) (ω : Ω)
    (j : projective k {i : I // c i = ω} ⟶ projective k I) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (s : {i : I // c i = ω} → Γ(Spec (.of A), ⊤))
    (hs : Ideal.span (Set.range s) = ⊤),
    ∃ he : Ideal.span (Set.range (extendSections c ω s)) = ⊤,
      ofSections A s hs ≫ j = ofSections A (extendSections c ω s) he

/-- The inverse-image chart as an object over the field.
Source: Milne, Lemma 13.51 and following paragraph, pp.274--275.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def chart {k : Type u} [Field k] {I : Type u}
    {X : Over (Spec (.of k))} (i : X ⟶ projective k I) (q : I) :
    Over (Spec (.of k)) :=
  Over.mk ((i.left ⁻¹ᵁ ProjectiveSpace.standardOpen I (Spec (.of k)) q).ι ≫ X.hom)

/-- The inclusion of an inverse-image chart, with its prescribed structure map.
Source: Milne, Lemma 13.51 and following paragraph, pp.274--275.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes). -/
def chartInclusion {k : Type u} [Field k] {I : Type u}
    {X : Over (Spec (.of k))} (i : X ⟶ projective k I) (q : I) : chart i q ⟶ X :=
  Over.homMk (i.left ⁻¹ᵁ ProjectiveSpace.standardOpen I (Spec (.of k)) q).ι

/-- Projective torus fixed schemes are the disjoint union of projective weight spaces,
with the same scheme for every separating cocharacter, on all charts and on every
closed equivariant subscheme.

Source: Milne, Theorem 7.1, pp.138--139; Theorem 12.12, pp.234--235;
Lemma 13.51 and following paragraph, pp.274--275.
(blueprint: lem-sfb-projective-torus-fixed-weight-schemes).

Proof:
1. Bound all coordinates of all weight differences by M and take N > M+1. The
   vector (1,N,...,N^(r-1)) separates them: its highest nonzero difference term
   dominates the sum of lower terms. The monomial map is a group homomorphism
   by lem-sfb-split-torus-hom-matrices. Rank zero and a single weight allow zero.
2. The standard charts cover by lem-weil-pbc-projective-space-standard-charts.
   The diagonal action preserves each chart and multiplies z_j/z_i by chi_j/chi_i.
   The ratio-extensionality lemma identifies these formulas as scheme morphisms.
3. Test fixedness on A[v_1^+-1,...,v_r^+-1] at its universal torus point. A nonzero
   weight difference gives b_j(v^d-1)=0. Laurent coefficient independence forces
   b_j=0, even over nonreduced A. For lambda the same argument uses one variable;
   separation makes exactly the same differences nonzero. The converse is direct.
4. The affine quotient by the displayed chartIdeal therefore represents each chart
   fixed functor, using affine Spec and the algebra quotient universal property.
5. Globally use the homogeneous ideal (z_i*z_j : c i != c j). Relative-Proj
   functoriality and the free-projective comparison give a closed embedding.
   lem-sfb-homogeneous-quotient-chart-kernel identifies its chart ideals with step 4.
6. Same-weight charts glue to P(E_chi); charts of distinct weights have empty
   intersection, since a zero coordinate would have to be invertible. Scheme
   morphism gluing identifies their disjoint union, with its coordinate inclusions.
7. A general affine-valued point is locally in standard charts. Its unique lifts
   through the closed subscheme agree and glue. Fixedness descends and ascends on
   this cover after every algebra extension, so the representation is functorial.
8. For X closed equivariant, a point is fixed exactly when its ambient point is
   fixed: a closed immersion is a monomorphism on all test schemes. The fibre
   product thus represents both fixed functors. The same calculation on the
   inverse-image affine charts gives the final assertion, including empty X.
-/
theorem projective_torus_fixed_weight_schemes
    {k : Type u} [Field k] {E : Type v} [AddCommGroup E] [Module k E]
    [FiniteDimensional k E] [Nontrivial E]
    {I Ω : Type u} [Fintype I] [DecidableEq I] [Nonempty I] [Finite Ω] [DecidableEq Ω]
    (b : Module.Basis I k E) (V : Ω → Submodule k E)
    (hV : DirectSum.IsInternal V) (hne : ∀ ω, V ω ≠ ⊥)
    (c : I → Ω) (hc : ∀ ω, Submodule.span k (b '' {i : I | c i = ω}) = V ω)
    (r : ℕ)
    (ρ : MultiplicativeType.splitTorus k r ⟶ Grp.mk (GeneralLinearGroup I k))
    (χ : Ω → (MultiplicativeType.splitTorus k r ⟶
      Grp.mk (StandardGroupSchemes.multiplicative k)))
    (hχ : Function.Injective χ) (n : Ω → Fin r → ℤ)
    (hn : ∀ (W : Over (Spec (.of k))) (t : W ⟶ (MultiplicativeType.splitTorus k r).X)
      (ω : Ω), t ≫ (χ ω).hom.hom =
        (List.ofFn (fun q : Fin r ↦ (t ≫ torusCoordinate k r q) ^ n ω q)).prod)
    (hρ : ∀ (A : CommAlgCat.{u} k)
      (t : StandardGroupSchemes.affine k A ⟶ (MultiplicativeType.splitTorus k r).X)
      (i : I),
      (Matrix.GeneralLinearGroup.toLin' (b.baseChange A)
        (GeneralLinearGroup.homMulEquiv I k A (t ≫ ρ.hom.hom))).toLinearEquiv
          (1 ⊗ₜ[k] b i) = (Scheme.ΓSpecIso (.of A)).hom
            (TrivialTorusCoherent.characterValue (MultiplicativeType.splitTorus k r)
              (Additive.ofMul (χ (c i))) (StandardGroupSchemes.affine k A) t) •
            (1 ⊗ₜ[k] b i))
    : (∃! a : ModObj (MultiplicativeType.splitTorus k r).X (projective k I),
        IsInducedAction ρ a) ∧
    ∀ a : ModObj (MultiplicativeType.splitTorus k r).X (projective k I),
      IsInducedAction ρ a →
    (∃ (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶
        MultiplicativeType.splitTorus k r) (m : Ω → ℤ),
      Function.Injective m ∧ ∀ ω, lam.hom.hom ≫ (χ ω).hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative k)) ^ m ω) ∧
    ∀ (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶
        MultiplicativeType.splitTorus k r) (m : Ω → ℤ),
      Function.Injective m →
      (∀ ω, lam.hom.hom ≫ (χ ω).hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative k)) ^ m ω) →
      ∃ (jω : ∀ ω : Ω, projective k {i : I // c i = ω} ⟶ projective k I)
        (j : (∐ fun ω : Ω ↦ projective k {i : I // c i = ω}) ⟶ projective k I),
        (∀ ω, IsBlockInclusion c ω (jω ω) ∧ Sigma.ι _ ω ≫ j = jω ω) ∧
        IsClosedImmersion j.left ∧
        RepresentsFixed a (𝟙 _) j ∧ RepresentsFixed a lam.hom.hom j ∧
        (∀ i : I,
          a.smul.left ⁻¹ᵁ ProjectiveSpace.standardOpen I (Spec (.of k)) i =
            (snd (MultiplicativeType.splitTorus k r).X (projective k I)).left ⁻¹ᵁ
              ProjectiveSpace.standardOpen I (Spec (.of k)) i) ∧
        (∀ i : I, RingHom.ker (j.left.app
          (ProjectiveSpace.standardOpen I (Spec (.of k)) i)).hom = chartIdeal c i) ∧
        ∀ (X : Over (Spec (.of k))) (aX : ModObj (MultiplicativeType.splitTorus k r).X X)
          (i : X ⟶ projective k I), IsClosedImmersion i.left →
          aX.smul ≫ i = ((MultiplicativeType.splitTorus k r).X ◁ i) ≫ a.smul →
          IsClosedImmersion (pullback.fst i j).left ∧
          RepresentsFixed aX (𝟙 _) (pullback.fst i j) ∧
          RepresentsFixed aX lam.hom.hom (pullback.fst i j) ∧
          ∀ q : I, IsAffine (chart i q).left ∧
            ∃ aU : ModObj (MultiplicativeType.splitTorus k r).X (chart i q),
              aU.smul ≫ chartInclusion i q =
                ((MultiplicativeType.splitTorus k r).X ◁ chartInclusion i q) ≫ aX.smul ∧
              IsClosedImmersion
                (pullback.fst (chartInclusion i q) (pullback.fst i j)).left ∧
              RepresentsFixed aU (𝟙 _)
                (pullback.fst (chartInclusion i q) (pullback.fst i j)) ∧
              RepresentsFixed aU lam.hom.hom
                (pullback.fst (chartInclusion i q) (pullback.fst i j)) := by
  sorry

end AlgebraicGeometry.ProjectiveTorusFixedWeights

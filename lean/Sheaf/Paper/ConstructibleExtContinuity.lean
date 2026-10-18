/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Continuity of Ext from constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/
sk-lem-constructible-ext-continuity/_section.md, statement and proof
(blueprint: sk-lem-constructible-ext-continuity).

All derived categories below are ordinary derived categories of internal module objects.
The comparison is induced by a colimit cocone of complexes, hence by the termwise
colimit cocone. Field coefficients use the finite constant-model constructibility
recorded by sk-def-sfb-constructible.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The additive functor `K ↦ Hom(C, Q(K)[q])`.
Source: blueprint sk-lem-constructible-ext-continuity, displayed Hom groups
(blueprint: sk-lem-constructible-ext-continuity). -/
def extContinuityTestFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : DerivedCategory A) (q : ℤ) : CochainComplex A ℤ ⥤ AddCommGrpCat.{w} :=
  DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory A) q ⋙ preadditiveCoyoneda.obj (op C)

/-- The canonical comparison induced by the arrows of the given colimit cocone.
On the i-th Hom group it sends f to f followed by Q(c.ι_i)[q].
Source: blueprint sk-lem-constructible-ext-continuity, displayed natural map
(blueprint: sk-lem-constructible-ext-continuity). -/
def extContinuityComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type w} [SmallCategory I]
    (C : DerivedCategory A) (K : I ⥤ CochainComplex A ℤ) (c : Cocone K) (q : ℤ) :
    colimit (K ⋙ extContinuityTestFunctor C q) ⟶
      (extContinuityTestFunctor C q).obj c.pt :=
  colimit.desc _ ((extContinuityTestFunctor C q).mapCocone c)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The sheaves a_!L, expressed by an open immersion into a closed subscheme and
finite locally free pro-etale coefficient modules. All such factorizations are allowed.
Source: blueprint sk-lem-constructible-ext-continuity, generator paragraph
(blueprint: sk-lem-constructible-ext-continuity). -/
def IsExtContinuityStratum (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
    (_ : IsOpenImmersion j) (_ : IsClosedImmersion i)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
    IsLisseCoefficientModule Λ L ∧
      Nonempty (M ≅ (CondensedRing.lowerStar Λ i).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj L))

/-- Generators with allowed integer shifts N. Taking N = univ allows every shift;
N = {0} describes the unshifted generators used in the integral sheaf clause.
Source: blueprint sk-lem-constructible-ext-continuity, finite extension hypothesis
(blueprint: sk-lem-constructible-ext-continuity). -/
def extContinuityShiftedStrata (X : Scheme.{u}) (N : Set ℤ) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  fun C ↦ ∃ M, IsExtContinuityStratum Λ X M ∧ ∃ n ∈ N,
    Nonempty (C ≅ ((DerivedCategory.singleFunctor _ 0).obj M)⟦n⟧)

/-- Finite iterated extensions of the indicated generators, up to isomorphism.
Mathlib's extensionProductIter counts n extensions from n+1 factors. Zero is included
because the zero module is locally free of rank zero and is a stratum generator.
Source: blueprint sk-lem-constructible-ext-continuity, finite extension hypothesis
(blueprint: sk-lem-constructible-ext-continuity). -/
def IsExtContinuityGenerated (X : Scheme.{u}) (N : Set ℤ)
    (C : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) : Prop :=
  ∃ n : ℕ, (extContinuityShiftedStrata Λ X N).extensionProductIter n C

/-- Continuity for finite extensions and shifts of locally closed lisse generators.
Source: blueprint sk-lem-constructible-ext-continuity, displayed comparison
(blueprint: sk-lem-constructible-ext-continuity).

Proof:
1. For the fixed diagram, consider objects whose comparisons are isomorphisms in
all degrees. Hom out of a distinguished triangle gives the five-term exact segment
in the node, also after rotating the triangle. Filtered colimits of abelian groups
are exact. The five lemma therefore gives extension closure. Shift identities replace
q by q-n, and precomposition gives invariance under isomorphisms. Zero also belongs.
Rotating a cone triangle gives closure under cones.
2. Noetherianity makes X qcqs and every open quasi-compact. A locally closed
immersion is quasi-compact and factors as an open immersion j followed by a closed
i. Their complementary opens are quasi-compact as well. The stratum continuity
lemma det-lem-constructible-ext-continuity-stratum applies to the finite locally
free L, each of the three coefficient rings, and the common lower bound b. Its
comparison is the map below, since its arrows are the same cocone arrows.
3. Induct on the finite extension expression, applying step 2 to the factors and
step 1 to every shift, isomorphism and extension. -/
theorem constructible_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ ∨ R = Profinite.padicIntegersCondensedRing ℓ E)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)))
    (hC : IsExtContinuityGenerated (coefficientHeartRingObj R) X Set.univ C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)) ℤ)
    (b : ℤ) (hb : ∀ (i : I) (r : ℤ), r < b → IsZero ((K.obj i).X r))
    (c : Cocone K) (hc : IsColimit c) (q : ℤ) :
    IsIso (extContinuityComparison C K c q) := by
  sorry

/-- Every bounded constructible complex with field coefficients has the generator
hypothesis of continuity. Constructibility here means finite constant scalar models.
Source: blueprint sk-lem-constructible-ext-continuity, clause 1
(blueprint: sk-lem-constructible-ext-continuity).

Proof: det-cor-coefficient-heart-ii-generation expresses every such C by finitely many
cones of shifted a_!L with L lisse, under precisely the Noetherian hypothesis here.
Rotate each cone triangle A → B → Cone → A[1] to B → Cone → A[1] → B[1]. This rewrites
the finite cone expression using extensions, shifts and isomorphisms as required. -/
theorem bounded_constructible_ext_generated
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)))
    (hC : constantModelBoundedConstructible (coefficientHeartRingObj R) X C) :
    IsExtContinuityGenerated (coefficientHeartRingObj R) X Set.univ C := by
  sorry

/-- In particular all integer Ext functors from a constructible field-coefficient
sheaf commute with filtered colimits of module objects.
Source: blueprint sk-lem-constructible-ext-continuity, clause 1, in particular
(blueprint: sk-lem-constructible-ext-continuity).

Proof: a constructible sheaf in degree zero is bounded constructible. Apply
bounded_constructible_ext_generated, then constructible_ext_continuity to its
degree-zero diagram. This diagram has common lower bound zero, and its termwise
colimit is the degree-zero embedding of the module colimit. The induced cocone is
therefore exactly the Ext comparison of the source. -/
theorem constructible_sheaf_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (c : Cocone M) (hc : IsColimit c) (q : ℤ) :
    IsIso (colimit.desc _
      (((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor _ 0).obj C))).mapCocone c))) := by
  sorry

/-- Integral finite extensions of the unshifted a_!L satisfy the main hypothesis.
Requiring the degree-zero C to be an iterated triangle extension of degree-zero
sheaves is precisely a finite extension by short exact sequences in the heart.
Source: blueprint sk-lem-constructible-ext-continuity, clause 2
(blueprint: sk-lem-constructible-ext-continuity).

Proof: take a finite extension filtration starting at zero with lisse stratum
quotients. The zero object and every quotient satisfy the generator hypothesis.
The derived short-exact-sequence triangle turns each filtration step into an
extension. Induct over the filtration; allowing every shift includes shift zero. -/
theorem integral_finite_extension_ext_generated
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    (hC : IsExtContinuityGenerated (Profinite.padicIntegersRingObj ℓ E) X {0}
      ((DerivedCategory.singleFunctor _ 0).obj C)) :
    IsExtContinuityGenerated (Profinite.padicIntegersRingObj ℓ E) X Set.univ
      ((DerivedCategory.singleFunctor _ 0).obj C) := by
  sorry

end AlgebraicGeometry.ProEtale

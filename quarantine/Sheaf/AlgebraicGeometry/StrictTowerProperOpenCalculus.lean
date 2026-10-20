/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Normalized proper/open calculus on strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: lem-cbc-strict-tower-proper-open-calculus).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The clopen projection is identity on the image and zero on the complementary open.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: split each test object into the inverse image of the two open components.
The sheaf condition is the product decomposition. The direct-image adjunction unit
is projection to the image component, and the inverse open-to-direct comparison
identifies that component with extension by zero. This is natural in modules,
transitions and differentials; exact localization preserves both equations. -/
theorem pi_components {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Derived B X) :
    (G B s).map ((pi B s).app M) = (jAdj B s).unit.app ((G B s).obj M) ∧
      (G B c).map ((pi B s).app M) = 0 := by
  sorry

/-- Cartesian squares recover beta from the intrinsic clopen construction.
Source: Stacks, Tag 0F7B and blueprint, fourth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: the fibre-product lift is the canonical isomorphism of the cartesian square.
Its complementary open is empty, so its component projection is identity. The
normalized compositors and the open-unit transpose identify the remaining map with beta. -/
theorem alpha_cartesian {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    alpha B k r p i h = (beta B r k i p h.symm hsq.flip).hom := by
  sorry

/-- Beta is normalized to identity on an identity base change.
Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: transpose the two maps under the open adjunction. The unit equation of the
identity inverse-image compositor makes both transposes the open unit. -/
theorem beta_id {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (hsq : IsPullback (𝟙 U) j j (𝟙 X))
    (M : Derived B U) :
    (beta B (𝟙 U) j j (𝟙 X) h hsq).hom.app M ≫
        (J B j).map ((gId B U).hom.app M) = (gId B X).hom.app ((J B j).obj M) := by
  sorry

/-- Successive base changes of beta agree with the composite, before evaluation.
Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: transpose both inverse comparisons under the final open adjunction. Both are
the same iterated pullback of the original open unit; unit naturality identifies the
successive transpose. Injectivity of the adjunction Hom equivalence gives equality. -/
theorem beta_comp {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    [IsOpenImmersion j] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g))
    (s₁ : IsPullback a j₁ j g) (s₂ : IsPullback b j₂ j₁ h)
    (s : IsPullback (b ≫ a) j₂ j (h ≫ g)) (M : Derived B U) :
    (gComp B h g).hom.app ((J B j).obj M) ≫
        (G B h).map ((beta B a j₁ j g w₁ s₁).hom.app M) ≫
        (beta B b j₂ j₁ h w₂ s₂).hom.app ((G B a).obj M) =
      (beta B (b ≫ a) j₂ j (h ≫ g) w s).hom.app M ≫
        (J B j₂).map ((gComp B b a).hom.app M) := by
  sorry

/-- Beta commutes with composition of open immersions, before evaluation.
Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: transpose under the composite open adjunction. Its unit is the composite of
the two open units, so naturality and the normalized pullback compositors identify
the two transposes. Injectivity of the Hom equivalence gives the stated equality. -/
theorem beta_open_comp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (sk : IsPullback b k₁ k a) (sj : IsPullback a j₁ j g)
    (s : IsPullback b (k₁ ≫ j₁) (k ≫ j) g) (M : Derived B V) :
    (G B g).map ((jComp B k j).inv.app M) ≫
        (beta B a j₁ j g wj sj).hom.app ((J B k).obj M) ≫
        (J B j₁).map ((beta B b k₁ k a wk sk).hom.app M) ≫
        (jComp B k₁ j₁).hom.app ((G B b).obj M) =
      (beta B b (k₁ ≫ j₁) (k ≫ j) g w s).hom.app M := by
  sorry

/-- Intrinsic alpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: after beta, the two clopen projections select nested open components.
On every test object's intersections of the two clopen decompositions the two
composites are both identity or both zero. Sheaf uniqueness proves equality,
termwise extension preserves it, and exact localization descends it. -/
theorem alpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Derived B E) :
    (gComp B p₁ p₂).hom.app ((J B j).obj N) ≫
        (G B p₁).map ((alpha B i r₂ p₂ j h₂).app N) ≫
        (alpha B k r₁ p₁ i h₁).app ((G B r₂).obj N) =
      (alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (J B k).map ((gComp B r₁ r₂).hom.app N) := by
  sorry

/-- Intrinsic alpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: the first clopen projection selects l(W), and the second selects lk(V)
inside it. Their composite selects lk(V) and vanishes on its complement. Use the
open-composition beta equation and exact localization to identify the displayed maps. -/
theorem alpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Derived B C) :
    (G B q).map ((jComp B i j).hom.app N) ≫
        (alpha B (k ≫ l) r q (i ≫ j) h).app N =
      (alpha B l p q j h₂).app ((J B i).obj N) ≫
        (J B l).map ((alpha B k r p i h₁).app N) ≫
        (jComp B k l).hom.app ((G B r).obj N) := by
  sorry

/-- Intrinsic alpha commutes with the canonical pullback cube.
Source: Stacks, Tag 0F7F and blueprint, fifth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: base change takes the selected clopen image and its complementary open to
the corresponding two components. Exact inverse image preserves the split
identity/zero projection. The beta comparison identifies open extension on these
components. Sheaf uniqueness and localization give equality before evaluation. -/
theorem alpha_baseChange {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) (N : Derived B S) :
    (squareG B a p₁ p b wp).hom.app ((J B i).obj N) ≫
        (G B a).map ((alpha B k r p i h).app N) ≫
        (beta B d k₁ k a wk sk).hom.app ((G B r).obj N) ≫
        (J B k₁).map ((squareG B d r₁ r c wr).inv.app N) =
      (G B p₁).map ((beta B c i₁ i b wi si).hom.app N) ≫
        (alpha B k₁ r₁ p₁ i₁ h₁).app ((G B c).obj N) := by
  sorry

/-- Select the second witness without repeatedly expanding a large normalization
predicate in the kernel. This is precisely the nested choice used by the finite
proper/open coherence theorem, not a new choice of unnormalized comparison.
Source: Stacks, Tag 0F7B and the finite coherence interface
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
noncomputable def secondWitness {A : Sort v} {C : Sort w} {P : A → C → Prop}
    (h : ∃ a c, P a c) : C :=
  h.choose_spec.choose

/-- The finite etale comparison furnished by the dependency's section and derived-unit
normalizations; these determine its arrow, including the refinement case.
Source: Stacks, Tag 0F7B
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
@[no_expose] noncomputable def finiteGamma (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p :=
  secondWitness (Etale.properOpenInterchangeCoherence Λ) k i r p h

/-- The finite comparison retains the specified witness of the normalization theorem. -/
theorem finiteGamma_eq_secondWitness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    finiteGamma Λ k r p i h =
      secondWitness (Etale.properOpenInterchangeCoherence Λ) k i r p h := by
  unfold finiteGamma
  rfl

/-- The canonical identification of the evaluated source with the finite etale
source, retaining the evaluation mates and the specified origin isomorphism.
Source: blueprint, seventh and eighth proof steps
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
noncomputable def finiteSource {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsProper r] [IsOpenImmersion i] (M : Derived B V) (n : ℕ)
    (w : ScalarEtaleOrigin B V ((ev B V n).obj M)) :
    (HD B T w.Λ w.φ).obj
        (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} w.Λ) i).mapDerivedCategoryPlus).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} w.Λ) r).obj w.origin.L)) ≅
      (ev B T n).obj ((J B i).obj ((R B r).obj M)) :=
  (hJ B i w.Λ w.φ).app _ ≪≫
  (moduleJ B i).mapDerivedCategory.mapIso
    ((@asIso _ _ _ _ (hR B r w.Λ w.φ) (hR_isIso B r w.Λ w.φ)).app w.origin.L) ≪≫
  (moduleJ B i).mapDerivedCategory.mapIso
    ((moduleDirectImage B r).rightDerivedFunctor.mapIso (originIso B w)) ≪≫
  (moduleJ B i).mapDerivedCategory.mapIso
    ((@asIso _ _ _ _ (evalR B r n) (evalR_isIso B r n)).app M).symm ≪≫
  (evalJ B i n).symm.app ((R B r).obj M)

/-- The canonical identification of the evaluated target with the finite etale
target, using the same comparisons and origin. Source: blueprint, steps 7--8
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
noncomputable def finiteTarget {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k] [IsProper p] (M : Derived B V) (n : ℕ)
    (w : ScalarEtaleOrigin B V ((ev B V n).obj M)) :
    (HD B T w.Λ w.φ).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} w.Λ) p).obj
          (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} w.Λ) k).mapDerivedCategoryPlus).obj
            w.origin.L)) ≅
      (ev B T n).obj ((R B p).obj ((J B k).obj M)) :=
  (@asIso _ _ _ _ (hR B p w.Λ w.φ) (hR_isIso B p w.Λ w.φ)).app _ ≪≫
  (moduleDirectImage B p).rightDerivedFunctor.mapIso ((hJ B k w.Λ w.φ).app w.origin.L) ≪≫
  (moduleDirectImage B p).rightDerivedFunctor.mapIso
    ((moduleJ B k).mapDerivedCategory.mapIso (originIso B w)) ≪≫
  (moduleDirectImage B p).rightDerivedFunctor.mapIso ((evalJ B k n).symm.app M) ≪≫
  ((@asIso _ _ _ _ (evalR B p n) (evalR_isIso B p n)).app ((J B k).obj M)).symm

/-- The n-th evaluation is this particular normalized finite comparison, including
refinements, and not just some isomorphism between the same objects.
Source: Stacks, Tag 0F7B and blueprint, seventh and eighth proof steps
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: evaluation preserves the exact functors, and its R comparison is the mate
preserving their units and counits. Scalar restriction preserves the identity/zero
clopen projector. The site comparison carries the two clopen components to the
same components. Transpose under the proper adjunction: the direct-image unit
normalization cancels its counit, leaving the same compared clopen alpha on both
sides. The finite etale node has precisely this transpose, by its section and
K-injective unit normalization. Injectivity of the adjunction Hom equivalence
proves the equation, including when r is identity and the lift is a clopen section. -/
theorem gamma_evaluation {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived B V) (n : ℕ)
    (w : ScalarEtaleOrigin B V ((ev B V n).obj M)) :
    (finiteSource B r i M n w).hom ≫ (ev B T n).map ((gamma B k r p i h).app M) =
      (HD B T w.Λ w.φ).map ((finiteGamma w.Λ k r p i h).hom.app w.origin.L) ≫
        (finiteTarget B k p M n w).hom := by
  sorry

/-- Proper/open interchange is invertible for independently bounded finite etale
origins at every positive level, with no uniform bound on those origins.
Source: Stacks, Tag 0F7B and blueprint, steps 7--9
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: evaluation of a K-injective strict tower is K-injective, so evaluation
commutes with R and its adjunction units and counits. Scalar restriction commutes
with G, J and R by the normalized change-of-ring adjunction, not by any claim that
it preserves K-injectives. The identity/zero clopen projector is unchanged by
scalar restriction. At an etale origin the canonical direct-image comparisons for
proper (hence qcqs) maps and open comparisons identify this mate with the normalized
finite etale comparison of properOpenInterchangeCoherence. It is an isomorphism.
Thus every evaluated map is invertible. Tower cohomology is levelwise, so the map
induces an isomorphism in every degree, and the unbounded-derived cohomology
criterion proves invertibility. This detects isomorphisms, not equality of maps. -/
theorem gamma_isIso {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived B V)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B V ((ev B V n).obj M))) :
    IsIso ((gamma B k r p i h).app M) := by
  have heval (n : ℕ) : IsIso ((ev B T n).map ((gamma B k r p i h).app M)) := by
    let w := Classical.choice (hM n)
    have heq := gamma_evaluation B k r p i h M n w
    have : IsIso ((finiteSource B r i M n w).hom ≫
        (ev B T n).map ((gamma B k r p i h).app M)) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_left (finiteSource B r i M n w).hom _
  apply (DerivedCategory.isIso_iff _ _).2
  intro q
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  have := heval n.unop
  exact (NatIso.isIso_map_iff
    (((evaluation ℕᵒᵖ (Modules B T)).obj n).mapDerivedCategoryHomologyFunctorIso q)
    ((gamma B k r p i h).app M)).2 (by
      change IsIso ((DerivedCategory.homologyFunctor (Modules B T) q).map
        ((ev B T n.unop).map ((gamma B k r p i h).app M)))
      infer_instance)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Vertical, horizontal and base-change coherence for every commutative proper/open
square, as equalities in derived strict-tower categories, without assuming evaluation
faithful. Source: Stacks, Tags 0F7C, 0F7D and 0F7F, and blueprint, steps 5, 6, 10, 11
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: for alpha, pull the clopen decompositions to each test object. In a vertical
or horizontal pasting the selected opens are nested, so successive component
projections equal the outer component projection. Base change pulls both clopen
components and the identity/zero projector to the corresponding components. Verify
these equations on their intersections using sheaf uniqueness. Apply the exact
functors termwise to towers and complexes, then use localization uniqueness to
descend the equations. Take proper-adjunction mates with composition adjunctions.
Mate pasting gives the two composition laws; the pullback cube gives the base-change
law. Associativity of normalized compositors makes all parenthesizations agree. -/
theorem normalizedProperOpenCalculus :
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived B A),
      (J B j).map ((rComp B r₁ r₂).hom.app M) ≫
          (gamma B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (rComp B p₁ p₂).inv.app ((J B k).obj M) =
        (gamma B i r₂ p₂ j h₂).app ((R B r₁).obj M) ≫
          (R B p₂).map ((gamma B k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived B A),
      (jComp B i j).hom.app ((R B r).obj M) ≫
          (gamma B (k ≫ l) r q (i ≫ j) h).app M ≫
          (R B q).map ((jComp B k l).inv.app M) =
        (J B j).map ((gamma B k r p i h₁).app M) ≫
          (gamma B l p q j h₂).app ((J B k).obj M)) ∧
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) (M : Derived B V),
      (G B b).map ((gamma B k r p i h).app M) ≫
          (exchange B a p₁ p b wp).app ((J B k).obj M) ≫
          (R B p₁).map ((beta B d k₁ k a wk sk).hom.app M) =
        (beta B c i₁ i b wi si).hom.app ((R B r).obj M) ≫
          (J B i₁).map ((exchange B d r₁ r c wr).app M) ≫
          (gamma B k₁ r₁ p₁ i₁ h₁).app ((G B d).obj M)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A C E B₀ D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    have hs : alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h =
        (((TwoSquare.mk _ _ _ _ (alpha B i r₂ p₂ j h₂)).vComp
          (TwoSquare.mk _ _ _ _ (alpha B k r₁ p₁ i h₁))).whiskerRight
            (gComp B p₁ p₂).hom).whiskerLeft (gComp B r₁ r₂).inv := by
      ext N
      simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
        TwoSquare.vComp_app]
      apply (cancel_mono ((J B k).map ((gComp B r₁ r₂).hom.app N))).1
      simpa [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
        Iso.hom_inv_id_app, Functor.map_id, Category.comp_id,
        TwoSquare.mk, TwoSquare.natTrans] using
        (alpha_vertical B k i j r₁ r₂ p₁ p₂ h₁ h₂ h N).symm
    have hm := congrArg (fun α ↦ (mateEquiv (adj B (r₁ ≫ r₂))
      (adj B (p₁ ≫ p₂)) α).app M) hs
    rw [conjugateEquiv_mateEquiv_vcomp _ ((adj B r₂).comp (adj B r₁)),
      mateEquiv_conjugateEquiv_vcomp _ ((adj B p₂).comp (adj B p₁)),
      mateEquiv_hcomp] at hm
    simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.hComp_app] at hm
    change (gamma B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M =
      (J B j).map ((rComp B r₁ r₂).inv.app M) ≫
        ((gamma B i r₂ p₂ j h₂).app ((R B r₁).obj M) ≫
          (R B p₂).map ((gamma B k r₁ p₁ i h₁).app M)) ≫
            (rComp B p₁ p₂).hom.app ((J B k).obj M) at hm
    rw [hm]
    simp [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.id_comp]
  · intro A C E B₀ D F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    have hs : alpha B (k ≫ l) r q (i ≫ j) h =
        (((TwoSquare.mk _ _ _ _ (alpha B k r p i h₁)).hComp
          (TwoSquare.mk _ _ _ _ (alpha B l p q j h₂))).whiskerTop
            (jComp B i j).inv).whiskerBottom (jComp B k l).hom := by
      ext N
      simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
        TwoSquare.hComp_app]
      apply (cancel_epi ((G B q).map ((jComp B i j).hom.app N))).1
      simpa [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
        Functor.map_id, Category.id_comp, TwoSquare.mk, TwoSquare.natTrans] using
        alpha_horizontal B k l i j r p q h₁ h₂ h N
    have hm := congrArg (fun α ↦ (mateEquiv (adj B r) (adj B q) α).app M) hs
    rw [mateEquiv_whiskerTop_whiskerBottom,
      mateEquiv_vcomp (adj B r) (adj B p) (adj B q)] at hm
    simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.vComp_app] at hm
    simp only [Category.assoc] at hm
    change (gamma B (k ≫ l) r q (i ≫ j) h).app M =
      (jComp B i j).inv.app ((R B r).obj M) ≫
        (J B j).map ((gamma B k r p i h₁).app M) ≫
        (gamma B l p q j h₂).app ((J B k).obj M) ≫
        (R B q).map ((jComp B k l).hom.app M) at hm
    rw [hm]
    simp [Category.assoc, ← Functor.map_comp]
  · intro V W S T V₁ W₁ S₁ T₁ k i r p k₁ i₁ r₁ p₁ a b c d
      _ _ _ _ _ _ _ _ _ _ _ _ h h₁ wk wi wp wr sk si sp sr M
    let α := TwoSquare.mk _ _ _ _ (alpha B k r p i h)
    let α₁ := TwoSquare.mk _ _ _ _ (alpha B k₁ r₁ p₁ i₁ h₁)
    let δp := TwoSquare.mk _ _ _ _ (squareG B a p₁ p b wp).hom
    let δr := TwoSquare.mk _ _ _ _ (squareG B d r₁ r c wr).hom
    have hs : (α.hComp δp).whiskerBottom (beta B d k₁ k a wk sk).hom =
        (δr.hComp α₁).whiskerTop (beta B c i₁ i b wi si).hom := by
      ext N
      simp only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app,
        TwoSquare.hComp_app, α, α₁, δp, δr, TwoSquare.mk, TwoSquare.natTrans]
      apply (cancel_mono
        ((J B k₁).map ((squareG B d r₁ r c wr).inv.app N))).1
      simpa [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
        Functor.map_id, Category.comp_id] using
        alpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si sp sr N
    have hm := congrArg (fun σ ↦ (mateEquiv (adj B r) (adj B p₁) σ).app M) hs
    rw [mateEquiv_whiskerBottom, mateEquiv_vcomp (adj B r) (adj B p) (adj B p₁)] at hm
    have ht : mateEquiv (adj B r) (adj B p₁)
        ((δr.hComp α₁).whiskerTop (beta B c i₁ i b wi si).hom) =
        (mateEquiv (adj B r) (adj B p₁) (δr.hComp α₁)).whiskerRight
          (beta B c i₁ i b wi si).hom := by
      ext N
      simp [mateEquiv, TwoSquare.whiskerTop, TwoSquare.whiskerRight]
    rw [ht, mateEquiv_vcomp (adj B r) (adj B r₁) (adj B p₁)] at hm
    simpa [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.vComp_app, α, α₁, δp, δr, gamma, exchange,
      TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using hm

/-- Identity normalizations of gamma in both directions.
Source: Stacks, Tags 0F7B and 07A7, blueprint, steps 6 and 10
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: the clopen projection is identity for either identity square. Its alpha is the
canonical inverse-image/open-extension identity; taking the mate and using the
triangle identities gives the corresponding identity on direct image or extension. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived B U),
      (gamma B j (𝟙 U) (𝟙 X) j h).app M ≫
          (rId B X).hom.app ((J B j).obj M) =
        (J B j).map ((rId B U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived B U),
      (gamma B (𝟙 U) p p (𝟙 X) h).app M ≫
          (R B p).map ((jId B U).hom.app M) =
        (jId B X).hom.app ((R B p).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower

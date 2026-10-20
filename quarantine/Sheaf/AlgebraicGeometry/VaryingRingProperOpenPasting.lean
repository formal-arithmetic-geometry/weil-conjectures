/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.SemilinearDerivedSections
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

/-!
# Proper/open projection and pasting for varying coefficient rings

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D, open-immersion cases; the
agent-formulated varying-ring extension extracted from the blueprint's local-pairs
construction (blueprint: lem-sp-varying-ring-proper-open-pasting).

Every map below lives on the ordinary derived category of strict semilinear systems.
The ordinary system maps and their two pasting equations are stated separately, so
these equalities precede evaluation. No invertibility of gamma on arbitrary inputs
is asserted.

## Main statements

- `modulePi_components`: identity on the image and zero on the complement.
- `moduleAlpha_vertical`, `moduleAlpha_horizontal`: intrinsic system pasting.
- `alpha_vertical`, `alpha_horizontal`, `properOpenPasting`: derived pasting laws.
- `alpha_identities`, `gamma_identities`, `gamma_evaluation`: normalization and evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

private theorem mate_whisker
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : G ⋙ L₂ ⟶ L₁ ⋙ H) (t : G' ⟶ G) (b : H ⟶ H') :
    mateEquiv adj₁ adj₂
        (Functor.whiskerRight t L₂ ≫ a ≫ Functor.whiskerLeft L₁ b) =
      Functor.whiskerLeft R₁ t ≫ mateEquiv adj₁ adj₂ a ≫
        Functor.whiskerRight b R₂ := by
  apply TwoSquare.ext
  intro X
  dsimp [mateEquiv, TwoSquare.natTrans]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have ht := adj₂.unit.naturality (t.app (R₁.obj X))
  dsimp at ht
  rw [← reassoc_of% ht]
  slice_lhs 4 5 => rw [← R₂.map_comp, ← b.naturality, R₂.map_comp]

/-- The system clopen projection is identity on its image and zero on the complement.
Source: Stacks 09AE; node proof Step 4
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: split every test object into its pullbacks of the clopen image and its
complement. The sheaf axiom identifies its sections with the product of the two
section modules. The unit followed by inverse open-to-direct comparison is (x,y) ↦
(x,0). The horizontal restrictions are semilinear componentwise maps, so they
commute with this projection, as do module maps and differentials. -/
theorem modulePi_components {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Modules R φ X) :
    (pull R φ s).map ((modulePi R φ s).app M) =
        (moduleJAdj R φ s).unit.app ((pull R φ s).obj M) ∧
      (pull R φ c).map ((modulePi R φ s).app M) = 0 := by
  sorry

/-- Intrinsic moduleAlpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: after beta, the two clopen projections select nested open components.
On every test object's intersections of the two clopen decompositions the two
composites are both identity or both zero. Sheaf uniqueness proves equality,
each map already commutes with the semilinear transitions, so this is an equality of system maps. -/
theorem moduleAlpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Modules R φ E) :
    (moduleGComp R φ p₁ p₂).hom.app ((extension R φ j).obj N) ≫
        (pull R φ p₁).map ((moduleAlpha R φ i r₂ p₂ j h₂).app N) ≫
        (moduleAlpha R φ k r₁ p₁ i h₁).app ((pull R φ r₂).obj N) =
      (moduleAlpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (extension R φ k).map ((moduleGComp R φ r₁ r₂).hom.app N) := by
  sorry

/-- Intrinsic moduleAlpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the first clopen projection selects l(W), and the second selects lk(V)
inside it. Their composite selects lk(V) and vanishes on its complement. Use the
open-composition beta equation and exact localization to identify the displayed maps. -/
theorem moduleAlpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Modules R φ C) :
    (pull R φ q).map ((moduleJComp R φ i j).hom.app N) ≫
        (moduleAlpha R φ (k ≫ l) r q (i ≫ j) h).app N =
      (moduleAlpha R φ l p q j h₂).app ((extension R φ i).obj N) ≫
        (extension R φ l).map ((moduleAlpha R φ k r p i h₁).app N) ≫
        (moduleJComp R φ k l).hom.app ((pull R φ r).obj N) := by
  sorry

/-- Intrinsic alpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
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
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Derived R φ E) :
    (gComp R φ p₁ p₂).hom.app ((J R φ j).obj N) ≫
        (G R φ p₁).map ((alpha R φ i r₂ p₂ j h₂).app N) ≫
        (alpha R φ k r₁ p₁ i h₁).app ((G R φ r₂).obj N) =
      (alpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (J R φ k).map ((gComp R φ r₁ r₂).hom.app N) := by
  sorry

/-- Intrinsic alpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
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
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Derived R φ C) :
    (G R φ q).map ((jComp R φ i j).hom.app N) ≫
        (alpha R φ (k ≫ l) r q (i ≫ j) h).app N =
      (alpha R φ l p q j h₂).app ((J R φ i).obj N) ≫
        (J R φ l).map ((alpha R φ k r p i h₁).app N) ≫
        (jComp R φ k l).hom.app ((G R φ r).obj N) := by
  sorry

/-- Both normalized proper/open mate-pasting laws, as system transformations.
Source: Stacks 0F7C, 0F7D and the varying-ring extension of the local-pairs argument
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof (the node's eleven steps):
1. Apply the constant-ring geometric calculus, with ring Z, to obtain the clopen
   lift s=(k,r) into W ×_T S and its complementary open, without cartesianness.
2. Inverse image and direct-sum extension act on the same underlying abelian
   sheaves after restriction along φ. A semilinear transition sends [a,x] to
   [a,t(x)], with t(cx)=φ(c)t(x); exactness is componentwise.
3. Cartesian open comparison preserves the lift label under the fibre-product
   bijection. It is the inverse open-unit transpose moduleBeta. Both routes past
   a transition therefore send a generator to [a',t(x)]. Sheafify this equality.
4. On the two clopen components the projection is (x,y) ↦ (x,0). It commutes with
   every semilinear transition, restriction and differential. This is modulePi;
   composition with moduleBeta and the compositors gives moduleAlpha.
5. Inverse-image composition identifies iterated pullbacks, and open composition
   combines lift labels without changing sections. The section-normalized
   direct-image compositor and its conjugate fix these comparisons and units.
6. Vertically, the projections retain nested components. On the final retained
   component both composites are identity, and on every other component one
   projection is zero. Sheaf uniqueness proves moduleAlpha_vertical.
7. Horizontally the projections select l(W) and then lk(V) inside it. The same
   identity/zero calculation and the open compositor give moduleAlpha_horizontal.
8. Apply the simultaneous ordinary-derived section model. Localize these actual
   degreewise maps of systems, obtaining alpha and its two pasting equations.
   Equalities are not inferred from evaluation of arbitrary derived morphisms.
9. Take the proper-adjunction mate. Its definition is precisely eta_p, alpha
   whiskered by Rr, and Rp(k! epsilon_r), with the specified order.
10. mateEquiv_hcomp applied to Step 6 proves the first displayed law, and
    mateEquiv_vcomp applied to Step 7 proves the second. Conjugate comparisons
    transport from composite adjunctions to the intrinsic proper compositors.
11. Identity lift labels and projections give the identity mate via the triangle
    laws. Evaluation preserves the constructed maps, units and counits, so the
    evaluated mate is the arbitrary constant-R_n clopen-projection mate. This
    uses neither finite-coefficient invertibility nor faithfulness of evaluation. -/
theorem properOpenPasting :
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived R φ A),
      (J R φ j).map ((pComp R φ r₁ r₂).hom.app M) ≫
          (gamma R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (pComp R φ p₁ p₂).inv.app ((J R φ k).obj M) =
        (gamma R φ i r₂ p₂ j h₂).app ((P R φ r₁).obj M) ≫
          (P R φ p₂).map ((gamma R φ k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived R φ A),
      (jComp R φ i j).hom.app ((P R φ r).obj M) ≫
          (gamma R φ (k ≫ l) r q (i ≫ j) h).app M ≫
          (P R φ q).map ((jComp R φ k l).inv.app M) =
        (J R φ j).map ((gamma R φ k r p i h₁).app M) ≫
          (gamma R φ l p q j h₂).app ((J R φ k).obj M)) := by
  constructor
  · intro A C E B₀ D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    let a₁ := TwoSquare.mk _ _ _ _ (alpha R φ k r₁ p₁ i h₁)
    let a₂ := TwoSquare.mk _ _ _ _ (alpha R φ i r₂ p₂ j h₂)
    let a := TwoSquare.mk _ _ _ _ (alpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    have ha : TwoSquare.vComp a₂ a₁ =
        (a.whiskerLeft (gComp R φ r₁ r₂).hom).whiskerRight
          (gComp R φ p₁ p₂).inv := by
      apply TwoSquare.ext
      intro N
      dsimp [a₁, a₂, a, TwoSquare.vComp, TwoSquare.whiskerLeft,
        TwoSquare.whiskerRight]
      simpa [TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using
        (congrArg (fun f ↦ (gComp R φ p₁ p₂).inv.app ((J R φ j).obj N) ≫ f)
          (alpha_vertical R φ k i j r₁ r₂ p₁ p₂ h₁ h₂ h N))
    have hm := congrArg
      (mateEquiv ((adj R φ r₂).comp (adj R φ r₁))
        ((adj R φ p₂).comp (adj R φ p₁))) ha
    rw [mateEquiv_hcomp,
      mateEquiv_conjugateEquiv_vcomp _ (adj R φ (p₁ ≫ p₂)),
      conjugateEquiv_mateEquiv_vcomp _ (adj R φ (r₁ ≫ r₂))] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    simpa only [a₁, a₂, a, gamma, pComp, conjugateIsoEquiv_apply_hom,
      conjugateIsoEquiv_apply_inv, TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hmM.symm
  · intro A C E B₀ D F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    let a₁ := TwoSquare.mk _ _ _ _ (alpha R φ k r p i h₁)
    let a₂ := TwoSquare.mk _ _ _ _ (alpha R φ l p q j h₂)
    let a := TwoSquare.mk _ _ _ _ (alpha R φ (k ≫ l) r q (i ≫ j) h)
    have ha : TwoSquare.hComp a₁ a₂ =
        (a.whiskerTop (jComp R φ i j).hom).whiskerBottom
          (jComp R φ k l).inv := by
      apply TwoSquare.ext
      intro N
      dsimp [a₁, a₂, a, TwoSquare.hComp, TwoSquare.whiskerTop,
        TwoSquare.whiskerBottom]
      have hh := alpha_horizontal R φ k l i j r p q h₁ h₂ h N
      have hh' := congrArg
        (fun f ↦ f ≫ (jComp R φ k l).inv.app ((G R φ r).obj N)) hh
      simpa [TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using hh'.symm
    have hm := congrArg (mateEquiv (adj R φ r) (adj R φ q)) ha
    rw [mateEquiv_vcomp (adj R φ r) (adj R φ p) (adj R φ q)] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    rw [show (a.whiskerTop (jComp R φ i j).hom).whiskerBottom
        (jComp R φ k l).inv =
        Functor.whiskerRight (jComp R φ i j).hom (G R φ q) ≫ a ≫
          Functor.whiskerLeft (G R φ r) (jComp R φ k l).inv from by
          simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, Category.assoc],
      mate_whisker] at hmM
    simpa only [a₁, a₂, a, gamma, TwoSquare.vComp, TwoSquare.mk,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hmM.symm

/-- Identity normalizations of the intrinsic inverse-image/open-extension arrow.
Source: Stacks 07A7, 0F7B; node proof Steps 5 and 11
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the identity square has the identity lift and its projection retains the
entire component. The unit normalization of beta and the identity compositors
therefore gives these equalities already on system complexes; localize them. -/
theorem alpha_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (alpha R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (J R φ j).map ((gId R φ U).hom.app M) =
        (gId R φ X).hom.app ((J R φ j).obj M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ X),
      (alpha R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (jId R φ U).hom.app ((G R φ p).obj M) =
        (G R φ p).map ((jId R φ X).hom.app M)) := by
  sorry

/-- Identity normalizations of gamma in both directions.
Source: Stacks, Tags 0F7B and 07A7, blueprint, steps 6 and 10
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the clopen projection is identity for either identity square. Its alpha is the
canonical inverse-image/open-extension identity; taking the mate and using the
triangle identities gives the corresponding identity on direct image or extension. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (gamma R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (pId R φ X).hom.app ((J R φ j).obj M) =
        (J R φ j).map ((pId R φ U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ U),
      (gamma R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (P R φ p).map ((jId R φ U).hom.app M) =
        (jId R φ X).hom.app ((P R φ p).obj M)) := by
  constructor
  · intro U X j _ _ h M
    let a := TwoSquare.mk _ _ _ _ (alpha R φ j (𝟙 U) (𝟙 X) j h)
    have ha : (a.whiskerLeft (gId R φ U).hom).whiskerRight
        (gId R φ X).inv = TwoSquare.vId (J R φ j) := by
      apply TwoSquare.ext
      intro N
      dsimp [a, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vId]
      simpa [TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using
        (congrArg (fun f ↦ (gId R φ X).inv.app ((J R φ j).obj N) ≫ f)
          ((alpha_identities R φ).1 j h N))
    have hm := congrArg (mateEquiv Adjunction.id Adjunction.id) ha
    rw [mateEquiv_conjugateEquiv_vcomp _ (adj R φ (𝟙 X)),
      conjugateEquiv_mateEquiv_vcomp _ (adj R φ (𝟙 U))] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    have hh : (J R φ j).map ((pId R φ U).inv.app M) ≫
        (gamma R φ j (𝟙 U) (𝟙 X) j h).app M ≫
        (pId R φ X).hom.app ((J R φ j).obj M) = 𝟙 _ := by
      simpa [a, gamma, pId, conjugateIsoEquiv, TwoSquare.whiskerTop,
        TwoSquare.whiskerBottom, TwoSquare.vId, mateEquiv, Adjunction.id] using hmM
    have hh' := congrArg (fun f ↦ (J R φ j).map ((pId R φ U).hom.app M) ≫ f) hh
    simpa [← Category.assoc, ← Functor.map_comp] using hh'
  · intro U X p _ h M
    let a := TwoSquare.mk _ _ _ _ (alpha R φ (𝟙 U) p p (𝟙 X) h)
    have ha : (a.whiskerTop (jId R φ X).inv).whiskerBottom
        (jId R φ U).hom = TwoSquare.hId (G R φ p) := by
      apply TwoSquare.ext
      intro N
      dsimp [a, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hId]
      have hh := (alpha_identities R φ).2 p h N
      have hh' := congrArg
        (fun f ↦ (G R φ p).map ((jId R φ X).inv.app N) ≫ f) hh
      simpa [TwoSquare.mk, TwoSquare.natTrans, ← Functor.map_comp,
        Category.assoc] using hh'
    have hm := congrArg (mateEquiv (adj R φ p) (adj R φ p)) ha
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.natTrans, TwoSquare.mk, Category.assoc] at hm
    rw [mate_whisker] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    have hh : (jId R φ X).inv.app ((P R φ p).obj M) ≫
        (gamma R φ (𝟙 U) p p (𝟙 X) h).app M ≫
        (P R φ p).map ((jId R φ U).hom.app M) = 𝟙 _ := by
      simpa [a, gamma, TwoSquare.hId, mateEquiv] using hmM
    have hh' := congrArg
      (fun f ↦ (jId R φ X).hom.app ((P R φ p).obj M) ≫ f) hh
    simpa only [← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp, Category.comp_id] using hh'


/-- Evaluation gives exactly the arbitrary constant-R_n clopen-projection mate.
Source: node proof Step 11, Stacks 0F7B
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: ordinary evaluations preserve the lift comparison and the clopen
identity/zero projection. Thus they carry moduleAlpha to the constant-ring alpha.
Localization preserves these actual comparisons. The normalized mate-evaluation
identity from lem-coef-semilinear-derived-sections, using both unit and counit
equations, identifies gamma with the evaluated constant-ring mate. Constant
embedding followed by evaluation is identity, which is exactly constantGamma.
This works for arbitrary, including infinite, R_n. -/
theorem gamma_evaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived R φ V) (n : ℕ) :
    (ev R φ T n).map ((gamma R φ k r p i h).app M) ≫
        (evalP R φ p n).hom.app ((J R φ k).obj M) ≫
        (StrictTower.moduleDirectImage (R n) p).rightDerivedFunctor.map
          ((evalJ R φ k n).hom.app M) =
      (evalJ R φ i n).hom.app ((P R φ r).obj M) ≫
        (StrictTower.moduleJ (R n) i).mapDerivedCategory.map
          ((evalP R φ r n).hom.app M) ≫
        constantGamma (R n) k r p i h ((ev R φ V n).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing

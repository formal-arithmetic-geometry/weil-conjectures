/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportLinePull
import all WeilConjectures.SecSmoothPurity.TransportPull
import all WeilConjectures.AlgebraicGeometry.RationalTateLineComposition
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit

/-! # Uniqueness of normalized Tate pullback coordinates

Source: projection and tensor normalization in smooth purity transport.
(blueprint: lem-per-condensed-line-pull-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- Projection normalization determines all the Tate pullback coordinates.
Source: `LinePullCoordinates.integral_normalized`, `first_normalized`, and
`power_normalized` (blueprint: lem-per-condensed-line-pull-coherence).

Proof: compare the integral maps after every finite projection. At a finite
level, undoing the coefficient normalization is faithful, so the common raw
root-pullback map determines the level comparison uniquely. Limit extensionality
then identifies the integral comparisons. Scalar normalization identifies the
first lines, and tensor-power normalization identifies every power. All remaining
fields are propositions and hence proof irrelevant. No nonempty-scheme or
positive-rank assumption is used.
-/
theorem linePullCoordinates_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Subsingleton (LinePullCoordinates ell c f) := by
  refine ⟨fun p q ↦ ?_⟩
  have hi : p.integral = q.integral := by
    apply Iso.ext
    apply limit.hom_ext
    intro n
    obtain ⟨ep, hep, hp⟩ := p.integral_normalized n.unop
    obtain ⟨eq, heq, hq⟩ := q.integral_normalized n.unop
    have he : ep = eq := pullNormalized_unique _ f ep eq _ hep heq
    rw [hp, hq, he]
  have hf : p.first = q.first := by
    apply eq_of_heq
    exact p.first_normalized.trans ((heq_of_eq (congrArg
      (scalarPull (c.integralMap ell) f) hi)).trans q.first_normalized.symm)
  have hp : p.power = q.power := by
    funext d
    apply eq_of_heq
    exact (p.power_normalized d).trans ((heq_of_eq (congrArg
      (fun e ↦ powerPull (CondensedRing.upperStar (c.obj ell) f)
        (c.firstLine ell Y) (c.firstLine ell X) e d) hf)).trans
          (q.power_normalized d).symm)
  cases p
  cases q
  dsimp only at hi hf hp
  subst_vars
  rfl

private theorem conjugate_comp {C B A : Type (u + 2)}
    [Category C] [Category B] [Category A]
    (F : C ⥤ B) (G : B ⥤ A) (H : C ⥤ A) (alpha : H ≅ F ⋙ G)
    {LZ KZ : C} {LY KY : B} {LX KX : A}
    (ez : LZ ≅ KZ) (ey : LY ≅ KY) (ex : LX ≅ KX)
    (ag : F.obj KZ ⟶ KY) (af : G.obj KY ⟶ KX) (afg : H.obj KZ ⟶ KX)
    (hc : alpha.hom.app KZ ≫ G.map ag ≫ af = afg) :
    alpha.hom.app LZ ≫ G.map (F.map ez.hom ≫ ag ≫ ey.inv) ≫
        (G.map ey.hom ≫ af ≫ ex.inv) = H.map ez.hom ≫ afg ≫ ex.inv := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc ey.inv ey.hom, Iso.inv_hom_id, G.map_id, Category.id_comp]
  have hn := alpha.hom.naturality ez.hom
  dsimp only [Functor.comp_map] at hn
  calc
    _ = H.map ez.hom ≫ (alpha.hom.app KZ ≫ G.map ag ≫ af) ≫ ex.inv := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ G.map ag ≫ af ≫ ex.inv) hn.symm
    _ = _ := by rw [hc]

/-- Composition of the abelian root pullbacks in these generator coordinates.
Source: restriction of roots in the smooth-orientation compatibility of Step 2
(blueprint: lem-per-condensed-line-pull-coherence).

Proof: expand the two conjugations by rootComparison. Functoriality cancels the
middle comparison and its inverse. Naturality moves the remaining target
comparison across the inverse-image compositor. The existing composition theorem
for inverse image of roots then gives the composite root restriction. No prime
invertibility hypothesis is needed for this equality of maps.
-/
theorem rootPull_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : ℕ) :
    (upperStarComp Ab.{u + 1} f g).hom.app (rootsOfUnitySheaf Z N) ≫
        (upperStar Ab.{u + 1} f).map (rootPull g N) ≫ rootPull f N =
      rootPull (f ≫ g) N := by
  simpa only [rootPull, Category.assoc] using conjugate_comp
    (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1} f)
    (upperStar Ab.{u + 1} (f ≫ g)) (upperStarComp Ab.{u + 1} f g)
    (rootComparison Z N) (rootComparison Y N) (rootComparison X N)
    (Scheme.proEtaleRootsOfUnityInverseImageMap g N)
    (Scheme.proEtaleRootsOfUnityInverseImageMap f N)
    (Scheme.proEtaleRootsOfUnityInverseImageMap (f ≫ g) N)
    (RationalP1.roots_comp f g N)

private theorem normalized_adjunct
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (e : (CondensedRing.upperStar R f).obj M ≅ N)
    (a : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X) (h : PullNormalized R f e a) :
    ((CondensedRing.upperStarLowerStarAdjunction R f).homEquiv M N e.hom).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv M.X N.X a := by
  have he := eq_of_heq h
  change ((Mod.extendScalarsIsoComapInv (condensedPullbackHom R f)).inv.app
      (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj R Y)).obj M)).hom ≫
        e.hom.hom = a at he
  rw [Mod.extendScalarsIsoComapInv_inv_app_hom,
    Mod.extendRestrictAdjunction_unit_app_hom] at he
  rw [CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom,
    Adjunction.homEquiv_unit, he]

/-- Coherent raw comparisons give coherent normalized module comparisons.
Source: finite root projection argument in Step 2, scalar normalization
(blueprint: lem-per-condensed-line-pull-coherence).

Proof: rewrite normalization using the unit of scalar extension. Under the native
module inverse-image adjunction this is exactly the ordinary sheaf adjunct of
the prescribed raw map. The existing module-comparison composition theorem then
transports the raw composition equation through the two adjunction bijections.
-/
theorem normalized_comparison_comp
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z))
    (MY : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))
    (MX : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (ag : (upperStar Ab.{u + 1} g).obj MZ.X ⟶ MY.X)
    (af : (upperStar Ab.{u + 1} f).obj MY.X ⟶ MX.X)
    (afg : (upperStar Ab.{u + 1} (f ≫ g)).obj MZ.X ⟶ MX.X)
    (eg : (CondensedRing.upperStar R g).obj MZ ≅ MY)
    (ef : (CondensedRing.upperStar R f).obj MY ≅ MX)
    (efg : (CondensedRing.upperStar R (f ≫ g)).obj MZ ≅ MX)
    (hg : PullNormalized R g eg ag) (hf : PullNormalized R f ef af)
    (hfg : PullNormalized R (f ≫ g) efg afg)
    (hcomp : (upperStarComp Ab.{u + 1} f g).hom.app MZ.X ≫
      (upperStar Ab.{u + 1} f).map ag ≫ af = afg) :
    (CondensedRing.upperStarComp R f g).hom.app MZ ≫
      (CondensedRing.upperStar R f).map eg.hom ≫ ef.hom = efg.hom := by
  exact RationalP1.module_comparison_comp R f g MZ MY MX ag af afg
    eg.hom ef.hom efg.hom (normalized_adjunct R g MZ MY eg ag hg)
    (normalized_adjunct R f MY MX ef af hf) (normalized_adjunct R (f ≫ g) MZ MX efg afg hfg)
    hcomp

/-- Tensor-power transport preserves a given composition equation for the first line.
Source: tensor-power step of smooth-orientation compatibility in Step 2
(blueprint: lem-per-condensed-line-pull-coherence).

Proof: induct on the power. At zero, monoidality of the compositor identifies the
inverse unit comparisons. At the successor, naturality of the inverse tensor
comparison moves the preceding power and first-line maps through it. Monoidality
of the compositor changes its tensor comparison into the tensor of its two
components. Functoriality of tensor products reduces the equation to the
inductive hypothesis and the given first-line equation.
-/
theorem powerPull_comp {C B A : Type (u + 2)}
    [Category C] [Category B] [Category A]
    [MonoidalCategory C] [MonoidalCategory B] [MonoidalCategory A]
    (F : C ⥤ B) (G : B ⥤ A) (H : C ⥤ A)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (alpha : H ≅ F ⋙ G) [NatTrans.IsMonoidal alpha.hom]
    (L : C) (M : B) (N : A)
    (eg : F.obj L ≅ M) (ef : G.obj M ≅ N) (efg : H.obj L ≅ N)
    (hfirst : alpha.hom.app L ≫ G.map eg.hom ≫ ef.hom = efg.hom) (d : ℕ) :
    alpha.hom.app (Nat.rec (𝟙_ C) (fun _ P ↦ P ⊗ L) d) ≫
      G.map (powerPull F L M eg d).hom ≫ (powerPull G M N ef d).hom =
        (powerPull H L N efg d).hom := by
  induction d with
  | zero =>
    change alpha.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η (F ⋙ G) =
      Functor.OplaxMonoidal.η H
    apply (cancel_epi (Functor.LaxMonoidal.ε H)).mp
    simp only [NatTrans.IsMonoidal.unit_assoc, Functor.Monoidal.ε_η]
  | succ d ih =>
    simp only [powerPull, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Functor.Monoidal.μIso_inv, Functor.map_comp, Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc]
    rw [← Category.assoc
      (G.map (Functor.OplaxMonoidal.δ F (Nat.rec (𝟙_ C) (fun _ P ↦ P ⊗ L) d) L))
      (Functor.OplaxMonoidal.δ G _ _)]
    change alpha.hom.app (Nat.rec (𝟙_ C) (fun _ P ↦ P ⊗ L) d ⊗ L) ≫
      Functor.OplaxMonoidal.δ (F ⋙ G) _ _ ≫
        (G.map (powerPull F L M eg d).hom ⊗ₘ G.map eg.hom) ≫
        ((powerPull G M N ef d).hom ⊗ₘ ef.hom) = _
    rw [← NatTrans.IsMonoidal.δ_comp_tensorHom_assoc]
    simp only [tensorHom_comp_tensorHom, ih, hfirst]

end AlgebraicGeometry.ProEtale.PurityTransport

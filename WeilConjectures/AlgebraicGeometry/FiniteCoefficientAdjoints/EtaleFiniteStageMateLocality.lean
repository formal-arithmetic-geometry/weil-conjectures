/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateProperty
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactTowerScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumNormalization
import all WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineProjectionCoefficientMate
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteAdjointMateCompatibility
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartExceptionalScalar
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.AlgebraicGeometry.Sf.SfAffineChartFactorizationGluing
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality

/-! # Finite affine chart reduction of the finite-stage mate

Source: ordinary etale reduction-exceptional argument and the parent mate proof.
(blueprint: lem-pur-etale-finite-stage-mate-locality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option linter.auxLemma false in
attribute [local instance 100000] AlgebraicGeometry.Etale.DerivedCategoryModule._proof_1
  AlgebraicGeometry.Etale.DerivedCategoryModule._proof_2

namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- Transport the coefficient mate through two compatible left-adjoint isomorphisms.
The right-adjoint uniqueness isomorphisms preserve the counit, so the given scalar
square identifies the mates. -/
private theorem mate_isIso_of_left_iso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F H : C ⥤ D} {G J : D ⥤ C} {F' H' : C' ⥤ D'} {G' J' : D' ⥤ C'}
    (g : F ⊣ G) (h : H ⊣ J) (g' : F' ⊣ G') (h' : H' ⊣ J')
    (e : H ≅ F) (e' : H' ≅ F') (S : C ⥤ C') (T : D ⥤ D')
    (β : F ⋙ T ≅ S ⋙ F') (γ : H ⋙ T ≅ S ⋙ H')
    (hs : ∀ X, T.map (e.hom.app X) ≫ β.hom.app X =
      γ.hom.app X ≫ e'.hom.app (S.obj X))
    (K : D) (q : S.obj (G.obj K) ⟶ G'.obj (T.obj K))
    (r : S.obj (J.obj K) ⟶ J'.obj (T.obj K))
    (hq : β.hom.app (G.obj K) ≫ F'.map q ≫ g'.counit.app (T.obj K) =
      T.map (g.counit.app K))
    (hr : γ.hom.app (J.obj K) ≫ H'.map r ≫ h'.counit.app (T.obj K) =
      T.map (h.counit.app K)) [IsIso r] : IsIso q := by
  have ht := Etale.transported_counit_scalar h h' e e' S T β.hom γ.hom K r hs hr
  have he := Etale.rightAdjointUniq_scalar_of_counits g (h.ofNatIsoLeft e)
    g' (h'.ofNatIsoLeft e') S T β.hom K q r hq inferInstance ht
  have : IsIso (q ≫ (g'.rightAdjointUniq (h'.ofNatIsoLeft e')).hom.app (T.obj K)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right q
    ((g'.rightAdjointUniq (h'.ofNatIsoLeft e')).hom.app (T.obj K))

/-- The unbounded compactification scalar squares give the chosen compositor square.
No boundedness assumption is needed here. -/
private theorem scalar_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : Etale.DerivedCategoryModule A X) :
    (Etale.scalarExtension φ Z).map
        ((Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
      (Etale.compactScalarChosenMap φ (f ≫ g)).app M =
    (Etale.compactScalarChosenMap φ g).app
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
        ((Etale.compactScalarChosenMap φ f).app M) ≫
      (Etale.unboundedEtaleLowerShriekCompIso B f g).hom.app
        ((Etale.scalarExtension φ X).obj M) := by
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    e.restrict
  apply Etale.composition_scalar_transport
    (Etale.scalarExtension φ X) (Etale.scalarExtension φ Y) (Etale.scalarExtension φ Z)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) F
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e))
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) e.restrict)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) (d.comp e))
    (Etale.rightDerivedLowerShriekIso A e.restrict) (Etale.rightDerivedLowerShriekIso A d)
    (Etale.rightDerivedLowerShriekIso A (d.comp e))
    (Etale.rightDerivedLowerShriekIso B e.restrict) (Etale.rightDerivedLowerShriekIso B d)
    (Etale.rightDerivedLowerShriekIso B (d.comp e))
    (Etale.unboundedEtaleLowerShriekCompIso A f g)
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso A d e)
    (Etale.unboundedEtaleLowerShriekCompIso B f g)
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso B d e)
    (Etale.unboundedEtaleLowerShriekCompIso_tower A f g d e)
    (Etale.unboundedEtaleLowerShriekCompIso_tower B f g d e)
    (Etale.compactScalarChosenMap φ f) (Etale.compactScalarMap φ e.restrict)
    (Etale.compactScalarChosenMap φ g) (Etale.compactScalarMap φ d)
    (Etale.compactScalarChosenMap φ (f ≫ g))
    (Etale.compactScalarMap φ (d.comp e)) M
  · exact Etale.ordinaryChartCompactificationScalar φ e.restrict
      (HasCompactification.compactification f) M
  · exact Etale.ordinaryChartCompactificationScalar φ d
      (HasCompactification.compactification g) (F.obj M)
  · exact Etale.ordinaryChartCompactificationScalar φ (d.comp e)
      (HasCompactification.compactification (f ≫ g)) M
  · exact Etale.ordinaryChartCompactTowerScalar φ f g d e M

/-- The component of coefficient exchange for specified compact-support adjunctions. -/
private def localityMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {G : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X}
    {G' : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X}
    (g : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (g' : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ G')
    (K : Etale.DerivedCategoryModule A Y) :
    (Etale.scalarExtension φ X).obj (G.obj K) ⟶
      G'.obj ((Etale.scalarExtension φ Y).obj K) :=
  g'.homEquiv _ _ (Etale.ExceptionalCoefficients.comparisonInverse φ c (G.obj K) ≫
    (Etale.scalarExtension φ Y).map (g.counit.app K))

private theorem localityMate_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f)
    {G : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X}
    {G' : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X}
    (g : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (g' : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ G')
    (K : Etale.DerivedCategoryModule A Y) :
    (Etale.compactScalarMap φ c).app (G.obj K) ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        (localityMate φ c g g' K) ≫
      g'.counit.app ((Etale.scalarExtension φ Y).obj K) =
    (Etale.scalarExtension φ Y).map (g.counit.app K) := by
  have h := (g'.homEquiv ((Etale.scalarExtension φ X).obj (G.obj K))
      ((Etale.scalarExtension φ Y).obj K)).symm_apply_apply
    (Etale.ExceptionalCoefficients.comparisonInverse φ c (G.obj K) ≫
      (Etale.scalarExtension φ Y).map (g.counit.app K))
  change (Etale.compactScalarMap φ c).app (G.obj K) ≫
    (g'.homEquiv ((Etale.scalarExtension φ X).obj (G.obj K))
      ((Etale.scalarExtension φ Y).obj K)).symm
      ((g'.homEquiv ((Etale.scalarExtension φ X).obj (G.obj K))
        ((Etale.scalarExtension φ Y).obj K))
        (Etale.ExceptionalCoefficients.comparisonInverse φ c (G.obj K) ≫
          (Etale.scalarExtension φ Y).map (g.counit.app K))) = _
  rw [h, Etale.ExceptionalCoefficients.comparisonInverse_eq,
    ← Etale.ExceptionalCoefficients.compactSupportIso_hom φ c]
  simp only [Iso.hom_inv_id_app_assoc]

/-- Neither the choice of compactification nor the chosen right adjoint affects
invertibility of the normalized mate. The coefficient square is unbounded. -/
private theorem localityMate_transfer
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    {G : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X}
    {J : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X}
    {G' : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X}
    {J' : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X}
    (g : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (j : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ J)
    (g' : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ G')
    (j' : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d ⊣ J')
    (K : Etale.DerivedCategoryModule A Y)
    (h : IsIso (localityMate φ d j j' K)) : IsIso (localityMate φ c g g' K) := by
  let := h
  exact mate_isIso_of_left_iso g j g' j'
    (Etale.rightDerivedLowerShriekOfCompactificationIso A d c)
    (Etale.rightDerivedLowerShriekOfCompactificationIso B d c)
    (Etale.scalarExtension φ X) (Etale.scalarExtension φ Y)
    (Etale.ExceptionalCoefficients.compactSupportIso φ c)
    (Etale.ExceptionalCoefficients.compactSupportIso φ d)
    (fun M ↦ by
      simpa only [Etale.ExceptionalCoefficients.compactSupportIso_hom] using
        Etale.ordinaryChartCompactificationScalar φ d c M)
    K _ _
    (by simpa only [Etale.ExceptionalCoefficients.compactSupportIso_hom] using
      localityMate_counit φ c g g' K)
    (by simpa only [Etale.ExceptionalCoefficients.compactSupportIso_hom] using
      localityMate_counit φ d j j' K)

private theorem mate_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : Etale.DerivedCategoryModule A Z) :
    (Etale.scalarExtension φ X).map
        ((conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
          ((Etale.rightDerivedUpperShriekAdjunction A f).comp
            (Etale.rightDerivedUpperShriekAdjunction A g))
          (Etale.unboundedEtaleLowerShriekCompIso A f g)).hom.app K) ≫
      Etale.ExceptionalCoefficients.mateMap φ f
        ((Etale.rightDerivedUpperShriek A g).obj K) ≫
      (Etale.rightDerivedUpperShriek B f).map
        (Etale.ExceptionalCoefficients.mateMap φ g K) =
    Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K ≫
      (conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction B (f ≫ g))
        ((Etale.rightDerivedUpperShriekAdjunction B f).comp
          (Etale.rightDerivedUpperShriekAdjunction B g))
        (Etale.unboundedEtaleLowerShriekCompIso B f g)).hom.app
          ((Etale.scalarExtension φ Z).obj K) := by
  have hc := scalar_composition φ f g
    ((Etale.rightDerivedUpperShriek A (f ≫ g)).obj K)
  rw [← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ f,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ g,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ (f ≫ g)] at hc
  exact finiteMate_composition
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A g)
    (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction B f)
    (Etale.rightDerivedUpperShriekAdjunction B g)
    (Etale.rightDerivedUpperShriekAdjunction B (f ≫ g))
    (Etale.unboundedEtaleLowerShriekCompIso A f g)
    (Etale.unboundedEtaleLowerShriekCompIso B f g)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ f)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ g)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ (f ≫ g)) K _ _ _
    (Etale.ExceptionalCoefficients.mateMap_counit φ f _)
    (Etale.ExceptionalCoefficients.mateMap_counit φ g K)
    (Etale.ExceptionalCoefficients.mateMap_counit φ (f ≫ g) K) hc

private theorem mate_isIso_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : Etale.DerivedCategoryModule A Z)
    (hf : IsIso (Etale.ExceptionalCoefficients.mateMap φ f
      ((Etale.rightDerivedUpperShriek A g).obj K)))
    (hg : IsIso (Etale.ExceptionalCoefficients.mateMap φ g K)) :
    IsIso (Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K) := by
  let := hf
  let := hg
  have he := mate_composition φ f g K
  have hi : IsIso (Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K ≫
      (conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction B (f ≫ g))
        ((Etale.rightDerivedUpperShriekAdjunction B f).comp
          (Etale.rightDerivedUpperShriekAdjunction B g))
        (Etale.unboundedEtaleLowerShriekCompIso B f g)).hom.app
          ((Etale.scalarExtension φ Z).obj K)) := by
    rw [← he]
    infer_instance
  let := hi
  exact IsIso.of_isIso_comp_right (Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K)
    ((conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction B (f ≫ g))
      ((Etale.rightDerivedUpperShriekAdjunction B f).comp
        (Etale.rightDerivedUpperShriekAdjunction B g))
      (Etale.unboundedEtaleLowerShriekCompIso B f g)).hom.app
        ((Etale.scalarExtension φ Z).obj K))

/-- For etale morphisms the coefficient mate is scalar/pullback balancing,
transported through the graph-normalized sum adjunction. -/
private theorem mate_isIso_etale
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (K : Etale.DerivedCategoryModule A Y) :
    IsIso (Etale.ExceptionalCoefficients.mateMap φ f K) := by
  obtain ⟨NA⟩ := Etale.nonempty_etaleCompactSupportNormalization A
  obtain ⟨NB⟩ := Etale.nonempty_etaleCompactSupportNormalization B
  let c := HasCompactification.compactification f
  let a := (Etale.derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) f inferInstance).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm
  let b := (Etale.derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) f inferInstance).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm
  have hs (M : Etale.DerivedCategoryModule A X) :
      (Etale.scalarExtension φ Y).map ((NA.comparison f c).inv.app M) ≫
        (Etale.compactScalarMap φ c).app M =
      (ProEtale.CoefficientCompatibility.sumCoefficientIso φ f).hom.app M ≫
        (NB.comparison f c).inv.app ((Etale.scalarExtension φ X).obj M) := by
    apply (cancel_mono ((NB.comparison f c).hom.app
      ((Etale.scalarExtension φ X).obj M))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [Etale.ordinaryChartSumNormalization φ f c NA NB M]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      _root_.CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id
      ((ProEtale.CoefficientCompatibility.sumCoefficientIso φ f).hom.app M)).symm
  exact mate_isIso_of_left_iso
    (Etale.rightDerivedUpperShriekAdjunction A f) a
    (Etale.rightDerivedUpperShriekAdjunction B f) b
    (NA.comparison f c).symm (NB.comparison f c).symm
    (Etale.scalarExtension φ X) (Etale.scalarExtension φ Y)
    (Etale.ExceptionalCoefficients.compactSupportIso φ c)
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ f)
    (fun M ↦ by
      simpa only [Etale.ExceptionalCoefficients.compactSupportIso_hom, Iso.symm_hom]
        using hs M) K _
    ((Etale.scalarPullbackIso φ f).inv.app K)
    (by
      have hh := localityMate_counit φ c
        (Etale.rightDerivedUpperShriekAdjunction A f)
        (Etale.rightDerivedUpperShriekAdjunction B f) K
      simpa only [Etale.rightDerivedLowerShriek, Etale.rightDerivedUpperShriek, c,
        localityMate, Etale.ExceptionalCoefficients.mateMap,
        Etale.ExceptionalCoefficients.compactSupportIso_hom] using hh)
    (Etale.sum_scalar_counit φ f K)

private theorem stage_annihilator
    {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (s : Stage l E) :
    ∃ n : ℕ, (l : s.ring) ^ n = 0 := by
  obtain ⟨e, z, hz, hideal, _⟩ := stage_ramification s
  let n : ℕ := (e : ℕ) * (s.exponent : ℕ)
  have hF := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have hlmem : (l : s.integers) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) := by
    have hgen : Ideal.span
        ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) =
        Padic.coefficientExtensionMaximalIdeal l s.field :=
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    rw [hgen]
    apply (hF.2.1 _).mpr
    change spectralNorm (Padic l) s.field (l : s.field) < 1
    rw [← map_natCast (algebraMap (Padic l) s.field) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  refine ⟨n, ?_⟩
  have hm : (l : s.integers) ^ n ∈ s.ideal := by
    change _ ∈ Ideal.span ({s.parameter} : Set s.integers) ^ (s.exponent : ℕ)
    rw [hideal]
    exact Ideal.pow_mem_pow hlmem n
  simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

private theorem coefficient_exponent_unit
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] [Fact l.Prime] (hlp : l ≠ p)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] (n : ℕ) :
    IsUnit ((l ^ n : ℕ) : Γ(T, ⊤)) := by
  have hnonzero : (l : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : l.Prime) hlp.symm
  have hu : IsUnit ((l ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hnonzero)
  let r : k →+* Γ(T, ⊤) :=
    (T ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  simpa only [map_natCast] using hu.map r

private theorem stage_invertible_exponent
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] [Fact l.Prime] (hlp : l ≠ p)
    {E : Type (u + 1)} [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (s : Stage l E)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] : HasInvertibleExponent s.ring T := by
  obtain ⟨n, hn⟩ := stage_annihilator s
  exact ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, by simpa using hn,
    coefficient_exponent_unit k p l hlp T n⟩

private def StandardMateProperty {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : Prop :=
  ∀ K : Etale.DerivedCategoryModule s.ring Y,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} s.ring) Y K →
    IsIso (Etale.ExceptionalCoefficients.mateMap a.ringMap f K)

private theorem standard_of_property
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [QuasiCompact f] [HasCompactification f]
    (hf : EtaleFiniteStageMateProperty a f) : StandardMateProperty a f := by
  intro K hK
  let c := HasCompactification.compactification f
  exact localityMate_transfer a.ringMap c c
    (Etale.rightDerivedUpperShriekAdjunction s.ring f) (etaleAdjunction s.ring c)
    (Etale.rightDerivedUpperShriekAdjunction t.ring f) (etaleAdjunction t.ring c)
    K (hf c K hK)

private theorem property_of_standard
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [QuasiCompact f] [HasCompactification f]
    (hf : StandardMateProperty a f) : EtaleFiniteStageMateProperty a f := by
  intro c K hK
  exact localityMate_transfer a.ringMap c (HasCompactification.compactification f)
    (etaleAdjunction s.ring c) (Etale.rightDerivedUpperShriekAdjunction s.ring f)
    (etaleAdjunction t.ring c) (Etale.rightDerivedUpperShriekAdjunction t.ring f)
    K (hf K hK)

private theorem standard_comp
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [Z.Over (Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))] [HasInvertibleExponent s.ring Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : StandardMateProperty a f) (hg : StandardMateProperty a g) :
    StandardMateProperty a (f ≫ g) := by
  intro K hK
  exact mate_isIso_comp a.ringMap f g K
    (hf _ (Etale.constructibleFiniteTor_rightDerivedUpperShriek s.ring
      (Z ↘ Spec (.of k)) g hK)) (hg K hK)

private theorem standard_etale
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] : StandardMateProperty a f := by
  intro K _
  exact mate_isIso_etale a.ringMap f K

private theorem standard_affine
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hk : Finite k ∨ IsAlgClosed k)
    (hp : 0 < p) (hlp : l ≠ p)
    (V : Scheme.{u}) [IsNoetherian V] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (d : ℕ) :
    StandardMateProperty a (affineTraceProjection V d) := by
  obtain ⟨n, hn⟩ := stage_annihilator s
  have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos _
  have hA : ((l ^ n : ℕ) : s.ring) = 0 := by simpa only [Nat.cast_pow] using hn
  have hB : ((l ^ n : ℕ) : t.ring) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg a.ringMap hA
  obtain ⟨tA, DA, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (l ^ n) hN s.ring hA
  obtain ⟨tB, DB, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (l ^ n) hN t.ring hB
  intro K hK
  have hL : Etale.DerivedCategory.isBoundedConstructible s.ring V K :=
    (ProEtale.AdjunctionTransfer.boundedConstructible_iff s.ring V K).2 hK.1
  have hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn s.ring V a b K := by
    obtain ⟨a, b, ht⟩ := hK.2
    exact ⟨a, b, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 ht⟩
  exact (Etale.ordinaryAffineProjectionAssertion l p hp hlp k hk s.ring t.ring
    a.ringMap n hA hB V (coefficient_exponent_unit k p l hlp V n) d
    tA DA tB DB K hL hTor).2.1

/-- Pullbacks along a source open cover detect the mate. The composition square
expresses each pullback as the composite mate with the invertible open mate removed. -/
private theorem standard_source_cover
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f]
    {ι : Type u} (U : ι → X.Opens)
    [∀ i, IsNoetherian (U i).toScheme]
    [∀ i, QuasiCompact (U i).ι]
    [∀ i, HasCompactification (U i).ι]
    [∀ i, HasCompactification ((U i).ι ≫ f)]
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hlocal : ∀ i, StandardMateProperty a ((U i).ι ≫ f)) :
    StandardMateProperty a f := by
  intro K hK
  let w := Etale.ExceptionalCoefficients.mateMap a.ringMap f K
  have hsurj : ∀ x : X, ∃ (i : ι) (y : (U i).toScheme), (U i).ι y = x := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  refine Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective
    t.ring (fun i ↦ (U i).ι) hsurj w ?_
  intro i
  have hcomp := hlocal i K hK
  have hopen := mate_isIso_etale a.ringMap (U i).ι
    ((Etale.rightDerivedUpperShriek s.ring f).obj K)
  let := hcomp
  let := hopen
  have he := mate_composition a.ringMap (U i).ι f K
  have hi : IsIso ((Etale.scalarExtension a.ringMap (U i).toScheme).map
        ((conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction s.ring ((U i).ι ≫ f))
          ((Etale.rightDerivedUpperShriekAdjunction s.ring (U i).ι).comp
            (Etale.rightDerivedUpperShriekAdjunction s.ring f))
          (Etale.unboundedEtaleLowerShriekCompIso s.ring (U i).ι f)).hom.app K) ≫
      Etale.ExceptionalCoefficients.mateMap a.ringMap (U i).ι
        ((Etale.rightDerivedUpperShriek s.ring f).obj K) ≫
      (Etale.rightDerivedUpperShriek t.ring (U i).ι).map w) := by
    rw [he]
    infer_instance
  have hmap : IsIso ((Etale.rightDerivedUpperShriek t.ring (U i).ι).map w) := by
    exact (isIso_comp_left_iff _ _).1 ((isIso_comp_left_iff _ _).1 hi)
  exact (NatIso.isIso_map_iff
    (Etale.rightDerivedUpperShriekOpenImmersionIso t.ring (U i).ι) w).1 hmap

/-- Finite affine charts reduce ordinary etale coefficient change to closed immersions.
The hypothesis concerns only closed immersions; the conclusion is for any separated
finite-type morphism. Source: reduction-exceptional, Charts and Locality, and parent
mate-invertibility steps 1 and 4
(blueprint: lem-pur-etale-finite-stage-mate-locality).

Proof: stage_ramification gives a power of l annihilating the actual stage ring.
The affine projection coefficient theorem therefore applies directly to both stage
rings and to their actual ring map. Graph-normalized etale sum adjunctions identify
etale coefficient mates with invertible scalar/pullback balancing. The unbounded
compactification and composition scalar squares transport invertibility between
chosen right adjoints and identify the mate of a composite with the composite mates.
Choose finite affine charts and factor each restricted map as a closed immersion
followed by an affine projection, using the canonical coordinate-tower isomorphism.
The closed factor uses hclosed; the projection uses the normalized affine theorem.
Exceptional pullback preserves the constructible finite-Tor domain, so composition
applies. Compose with the target open inclusion. On the source open cover the
composition equation and invertibility of the open mate show that pullbacks of the
original mate are invertible. Derived open-cover conservativity concludes, including
an empty source. No flatness of the coefficient arrow is used. -/
theorem etale_finite_stage_mate_locality
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hk : Finite k ∨ IsAlgClosed k)
    (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {s t : Stage l E} (a : Arrow s t)
    (hclosed : ∀
      {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
      [IsSeparated (U ↘ Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
      [IsSeparated (V ↘ Spec (.of k))]
      (g : U ⟶ V) [g.IsOver (Spec (.of k))]
      [IsClosedImmersion g],
      letI := finiteTypeNoetherian k U
      letI := finiteTypeNoetherian k V
      EtaleFiniteStageMateProperty a g)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    EtaleFiniteStageMateProperty a f := by
  classical
  let := finiteTypeNoetherian k X
  let := finiteTypeNoetherian k Y
  let := (finiteTypeMorphismProperties k f).1
  let := (finiteTypeMorphismProperties k f).2.1
  let := (finiteTypeMorphismProperties k f).2.2
  let := stage_invertible_exponent k p l hlp s Y
  apply property_of_standard a f
  obtain ⟨n, V, N, U, hUV, m, c, hV, hcovV, hU, hcovU, hfactor, hVk, hUk, _⟩ :=
    exists_sf_affine_chart_factorization_gluing k X Y f
  let (i : Fin n) : IsAffine (V i).toScheme := hV i
  let (i : Fin n) (j : Fin (N i)) : IsAffine (U i j).toScheme := hU i j
  let (i : Fin n) : IsSeparated ((V i).toScheme ↘ Spec (.of k)) := (hVk i).1
  let (i : Fin n) : LocallyOfFiniteType ((V i).toScheme ↘ Spec (.of k)) := (hVk i).2.1
  let (i : Fin n) : QuasiCompact ((V i).toScheme ↘ Spec (.of k)) := (hVk i).2.2
  let (i : Fin n) (j : Fin (N i)) :
      IsSeparated ((U i j).toScheme ↘ Spec (.of k)) := (hUk i j).1
  let (i : Fin n) (j : Fin (N i)) :
      LocallyOfFiniteType ((U i j).toScheme ↘ Spec (.of k)) := (hUk i j).2.1
  let (i : Fin n) (j : Fin (N i)) :
      QuasiCompact ((U i j).toScheme ↘ Spec (.of k)) := (hUk i j).2.2.1
  let (i : Fin n) : IsNoetherian (V i).toScheme := finiteTypeNoetherian k _
  let (i : Fin n) (j : Fin (N i)) : IsNoetherian (U i j).toScheme :=
    finiteTypeNoetherian k _
  let W : ULift.{u} (Σ i : Fin n, Fin (N i)) → X.Opens :=
    fun ij ↦ U ij.down.1 ij.down.2
  apply standard_source_cover a f W
  · intro x
    obtain ⟨i, hi⟩ := hcovV (f x)
    obtain ⟨j, hj⟩ := hcovU i x hi
    exact ⟨ULift.up ⟨i, j⟩, hj⟩
  · rintro ⟨⟨i, j⟩⟩
    change StandardMateProperty a ((U i j).ι ≫ f)
    let T := affineTraceTower (V i).toScheme (m i j)
    let q : T ⟶ (V i).toScheme := affineTraceProjection (V i).toScheme (m i j)
    let : T.Over (Spec (.of k)) := ⟨q ≫ ((V i).toScheme ↘ Spec (.of k))⟩
    let : IsNoetherian T := affineTraceNoetherian _ _
    let : IsSeparated (T ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated (q ≫ ((V i).toScheme ↘ Spec (.of k))))
    let : LocallyOfFiniteType (T ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (q ≫ ((V i).toScheme ↘ Spec (.of k))))
    let : QuasiCompact (T ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (q ≫ ((V i).toScheme ↘ Spec (.of k))))
    let : HasInvertibleExponent s.ring (V i).toScheme :=
      stage_invertible_exponent k p l hlp s (V i).toScheme
    let z : (U i j).toScheme ⟶ T := c i j ≫
      (affineTraceAffineSpaceIso (V i).toScheme (m i j)).inv
    let : IsClosedImmersion (c i j) := (hfactor i j).1
    let : IsClosedImmersion z := inferInstance
    have hz : z ≫ q = f.resLE (V i) (U i j) (hUV i j) := by
      dsimp only [z, q, T]
      have hproj : (affineTraceAffineSpaceIso (V i).toScheme (m i j)).inv ≫
          affineTraceProjection (V i).toScheme (m i j) =
          (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘ (V i).toScheme) := by
        apply (cancel_epi (affineTraceAffineSpaceIso (V i).toScheme (m i j)).hom).mp
        simp only [Iso.hom_inv_id_assoc]
        exact (AffineSpace.homOfVector_over _ _).symm
      rw [Category.assoc, hproj]
      exact (hfactor i j).2.1
    let : z.IsOver (Spec (.of k)) := ⟨by
      change z ≫ (q ≫ ((V i).toScheme ↘ Spec (.of k))) =
        (U i j).toScheme ↘ Spec (.of k)
      rw [← Category.assoc, hz]
      change f.resLE (V i) (U i j) (hUV i j) ≫
          ((V i).ι ≫ (Y ↘ Spec (.of k))) =
        (U i j).ι ≫ (X ↘ Spec (.of k))
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, comp_over]⟩
    have hclosed' := standard_of_property a z (hclosed z)
    have haffine := standard_affine a k p hk hp hlp (V i).toScheme (m i j)
    have hrestricted : StandardMateProperty a
        (f.resLE (V i) (U i j) (hUV i j)) := by
      have hcomp := standard_comp a k z q hclosed' haffine
      simpa only [hz] using hcomp
    have h := standard_comp a k (f.resLE (V i) (U i j) (hUV i j)) (V i).ι
      hrestricted (standard_etale a (V i).ι)
    simpa only [Scheme.Hom.resLE_comp_ι] using h

section StageProperty
variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {s t : Stage l E} (a : Arrow s t)

end StageProperty

end AlgebraicGeometry.FiniteCoefficientAdjoints

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceRestriction
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactScalar
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactTowerScalar
public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaFiniteTrace

/-! # Compositor form of the finite étale trace restriction square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

private theorem scalar_composition_unbounded
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
        (compactScalarChosenMap φ (f ≫ g)).app M =
      (compactScalarChosenMap φ g).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
          ((compactScalarChosenMap φ f).app M) ≫
        (unboundedEtaleLowerShriekCompIso B f g).hom.app
          ((scalarExtension φ X).obj M) := by
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict
  apply composition_scalar_transport (scalarExtension φ X) (scalarExtension φ Y)
    (scalarExtension φ Z)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) F
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) e.restrict)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) (d.comp e))
    (rightDerivedLowerShriekIso A e.restrict) (rightDerivedLowerShriekIso A d)
    (rightDerivedLowerShriekIso A (d.comp e))
    (rightDerivedLowerShriekIso B e.restrict) (rightDerivedLowerShriekIso B d)
    (rightDerivedLowerShriekIso B (d.comp e))
    (unboundedEtaleLowerShriekCompIso A f g)
    (rightDerivedLowerShriekOfCompactificationCompIso A d e)
    (unboundedEtaleLowerShriekCompIso B f g)
    (rightDerivedLowerShriekOfCompactificationCompIso B d e)
    (unboundedEtaleLowerShriekCompIso_tower A f g d e)
    (unboundedEtaleLowerShriekCompIso_tower B f g d e)
    (compactScalarChosenMap φ f) (compactScalarMap φ e.restrict)
    (compactScalarChosenMap φ g) (compactScalarMap φ d)
    (compactScalarChosenMap φ (f ≫ g)) (compactScalarMap φ (d.comp e)) M
  · exact ordinaryChartCompactificationScalar φ e.restrict
      (HasCompactification.compactification f) M
  · exact ordinaryChartCompactificationScalar φ d
      (HasCompactification.compactification g) (F.obj M)
  · exact ordinaryChartCompactificationScalar φ (d.comp e)
      (HasCompactification.compactification (f ≫ g)) M
  · exact ordinaryChartCompactTowerScalar φ f g d e M

private theorem inverse_scalar_square
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {X Y : C} {X' Y' : D} (a : X ≅ Y) (b : X' ≅ Y')
    (s : Q.obj X ⟶ X') (t : Q.obj Y ⟶ Y')
    (h : Q.map a.hom ≫ t = s ≫ b.hom) :
    Q.map a.inv ≫ s = t ≫ b.inv := by
  apply (cancel_mono b.hom).1
  rw [Category.assoc, ← h]
  simp only [← Q.map_comp_assoc, Iso.inv_hom_id,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- Invert the refinement square without assuming any bound on scalar extension.

private theorem scalar_comparison_inverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [QuasiCompact f] [HasCompactification f]
    (c : Compactification f) (K : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map ((rightDerivedLowerShriekIso A c).inv.app K) ≫
        (compactScalarMap φ c).app K =
      (compactScalarChosenMap φ f).app K ≫
        (rightDerivedLowerShriekIso B c).inv.app ((scalarExtension φ X).obj K) := by
  have h : (scalarExtension φ Y).map ((rightDerivedLowerShriekIso A c).hom.app K) ≫
      (compactScalarChosenMap φ f).app K =
      (compactScalarMap φ c).app K ≫
        (rightDerivedLowerShriekIso B c).hom.app ((scalarExtension φ X).obj K) :=
    ordinaryChartCompactificationScalar φ c (HasCompactification.compactification f) K
  exact inverse_scalar_square (scalarExtension φ Y)
    ((rightDerivedLowerShriekIso A c).app K)
    ((rightDerivedLowerShriekIso B c).app ((scalarExtension φ X).obj K))
    ((compactScalarMap φ c).app K) ((compactScalarChosenMap φ f).app K) h


-- Transfer the canonical equation to each of the three supplied compactifications.

private theorem scalar_supplied_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hf : f ≫ g = h)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [QuasiCompact h]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h)
    (K : DerivedCategoryModule A X) :
    (compactScalarMap φ d).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d).map
        ((compactScalarMap φ c).app K) ≫
      (finiteSupportComposition B f g h hf c d e).hom.app ((scalarExtension φ X).obj K) =
    (scalarExtension φ Z).map ((finiteSupportComposition A f g h hf c d e).hom.app K) ≫
      (compactScalarMap φ e).app K := by
  subst h
  symm
  apply composition_scalar_transport (scalarExtension φ X) (scalarExtension φ Y)
    (scalarExtension φ Z)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) e)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (rightDerivedLowerShriekIso A c).symm (rightDerivedLowerShriekIso A d).symm
    (rightDerivedLowerShriekIso A e).symm
    (rightDerivedLowerShriekIso B c).symm (rightDerivedLowerShriekIso B d).symm
    (rightDerivedLowerShriekIso B e).symm
    (finiteSupportComposition A f g (f ≫ g) rfl c d e)
    (unboundedEtaleLowerShriekCompIso A f g)
    (finiteSupportComposition B f g (f ≫ g) rfl c d e)
    (unboundedEtaleLowerShriekCompIso B f g)
    (by
      ext M
      simp only [finiteSupportComposition, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Iso.symm_inv,
        NatTrans.hcomp_app, Category.assoc]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ (unboundedEtaleLowerShriekCompIso A f g).hom.app M ≫
          (rightDerivedLowerShriekIso A e).inv.app M)
        ((rightDerivedLowerShriekIso A d).hom.naturality
          ((rightDerivedLowerShriekIso A c).hom.app M)))
    (by
      ext M
      simp only [finiteSupportComposition, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Iso.symm_inv,
        NatTrans.hcomp_app, Category.assoc]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ (unboundedEtaleLowerShriekCompIso B f g).hom.app M ≫
          (rightDerivedLowerShriekIso B e).inv.app M)
        ((rightDerivedLowerShriekIso B d).hom.naturality
          ((rightDerivedLowerShriekIso B c).hom.app M)))
    (compactScalarMap φ c) (compactScalarChosenMap φ f)
    (compactScalarMap φ d) (compactScalarChosenMap φ g)
    (compactScalarMap φ e) (compactScalarChosenMap φ (f ≫ g)) K
  · exact scalar_comparison_inverse φ c K
  · exact scalar_comparison_inverse φ d _
  · exact scalar_comparison_inverse φ e K
  · exact scalar_composition_unbounded φ f g K

/-- The compact-support coefficient map respects composition with the structure map,
evaluated at the upper dualizing object.
Source: Step 3 of lem-coef-etale-relative-trace-restriction, using
lem-sf-etale-restriction-compositor and lem-amb-unbounded-compact-support-comparisons
(blueprint: lem-coef-etale-relative-trace-restriction-compositor).
Proof: apply the unbounded proper/open tower scalar equation, then transfer it
through the three canonical compactification comparisons by composition_scalar_transport.
Invert the refinement scalar squares by cancellation and use the same transport lemma
to pass from the canonical compositor to the supplied compactifications. Naturality
identifies their horizontal composition with finiteSupportComposition. Finally use
Noetherianity of the finite-type schemes over the finite field and specialize to the
adjacent coefficient quotient and the upper dualizing object. The existing unbounded
scalar equations retain the proper/open normalization without a lower-bound assumption
on scalar extension. No trace or dualizing transition equation is assumed. -/
theorem finiteEtaleTrace_restriction_compositor (n : ℕ) :
    letI := c.hasCompactification
    letI := (finiteDualizingCompactification D X).hasCompactification
    letI := (finiteDualizingCompactification D Y).hasCompactification
    let q := finiteDualizingQuotient l E n.le_succ
    let K := finiteDualizingEtaleTerm l E D X (n + 1)
    let FA := Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c
    let GB := finiteDualizingEtaleSupport l E D Y n
    let aA := finiteSupportComposition (finiteDualizingCoeff l E (n + 1)) f
      (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
      (CategoryTheory.comp_over f (Spec (.of D.k))) c
      (finiteDualizingCompactification D Y) (finiteDualizingCompactification D X)
    let aB := finiteSupportComposition (finiteDualizingCoeff l E n) f
      (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
      (CategoryTheory.comp_over f (Spec (.of D.k))) c
      (finiteDualizingCompactification D Y) (finiteDualizingCompactification D X)
    Etale.ExceptionalCoefficients.compactSupportMap q
        (finiteDualizingCompactification D Y) (FA.obj K) ≫
      GB.map (Etale.ExceptionalCoefficients.compactSupportMap q c K) ≫
      aB.hom.app ((Etale.scalarExtension q X).obj K) =
    (Etale.scalarExtension q (Spec (.of D.k))).map (aA.hom.app K) ≫
      Etale.ExceptionalCoefficients.compactSupportMap q
        (finiteDualizingCompactification D X) K := by
  let := c.hasCompactification
  let := (finiteDualizingCompactification D X).hasCompactification
  let := (finiteDualizingCompactification D Y).hasCompactification
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of D.k))
  have : IsNoetherian Y := ⟨⟩
  exact scalar_supplied_composition (finiteDualizingQuotient l E n.le_succ)
    f (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
    (CategoryTheory.comp_over f (Spec (.of D.k))) c
    (finiteDualizingCompactification D Y) (finiteDualizingCompactification D X)
    (finiteDualizingEtaleTerm l E D X (n + 1))

end WeilConjectures.CoefDualFormulaScalarTranspose

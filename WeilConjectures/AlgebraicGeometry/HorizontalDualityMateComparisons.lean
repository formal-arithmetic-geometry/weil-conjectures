/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap

/-! # Fixed endpoint comparisons for horizontal duality mates

## References

* Stacks Project, Tags 0D5S, 0D5T and 0ATR
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

noncomputable section
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Restriction of derived pullback to quasi-coherent complexes.
-/
def horizontalMatePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X :=
  (schemeDerivedQCohProperty X).lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh f).1 E.obj E.property)

/-- Restriction of derived direct image to quasi-coherent complexes.
-/
def horizontalMatePushforward {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y :=
  (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property)

/-- The composition isomorphism determined by the left-derived universal property.
-/
def horizontalMateAmbientComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) f g

/-- The identity isomorphism from the same coherent comparison family.
-/
def horizontalMateAmbientId (X : Scheme.{u}) : derivedPullback (𝟙 X) ≅ 𝟭 _ :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))).2) X

/-- Coherent composition comparison on quasi-coherent complexes.
-/
def horizontalMateComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    horizontalMatePullback g ⋙ horizontalMatePullback f ≅
      horizontalMatePullback (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (schemeDerivedQCohProperty X).ι
    (Functor.isoWhiskerLeft (schemeDerivedQCohProperty Z).ι
      (horizontalMateAmbientComp f g))

/-- Coherent identity comparison on quasi-coherent complexes.
-/
def horizontalMateId (X : Scheme.{u}) : horizontalMatePullback (𝟙 X) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (schemeDerivedQCohProperty X).ι
    (Functor.isoWhiskerLeft (schemeDerivedQCohProperty X).ι
      (horizontalMateAmbientId X))

/-- Pullback along a scheme isomorphism, with inverse the pullback along its inverse.
-/
def horizontalMateEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    schemeDerivedQCohCategory Y ≌ schemeDerivedQCohCategory X :=
  CategoryTheory.Equivalence.mk (horizontalMatePullback e.hom) (horizontalMatePullback e.inv)
    (horizontalMateComp e.inv e.hom ≪≫
      eqToIso (congrArg horizontalMatePullback e.inv_hom_id) ≪≫ horizontalMateId Y).symm
    (horizontalMateComp e.hom e.inv ≪≫
      eqToIso (congrArg horizontalMatePullback e.hom_inv_id) ≪≫ horizontalMateId X)

/-- The pinned derived pullback/direct-image adjunction restricted to QCoh.
-/
def horizontalMateAdjunction {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    horizontalMatePullback f ⊣ horizontalMatePushforward f :=
  Adjunction.restrictFullyFaithful
    (Classical.choose (exists_schemeDerivedAdjunction f
      (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f)))
    (schemeDerivedQCohProperty Y).fullyFaithfulι
    (schemeDerivedQCohProperty X).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- Direct-image composition is the conjugate of the fixed pullback comparison.
-/
def horizontalMatePushComp {X Y Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] :
    horizontalMatePushforward (f ≫ g) ≅
      horizontalMatePushforward f ⋙ horizontalMatePushforward g :=
  conjugateIsoEquiv (horizontalMateAdjunction (f ≫ g))
    ((horizontalMateAdjunction g).comp (horizontalMateAdjunction f))
    (horizontalMateComp f g)

/-- Transport of the right adjoint across an isomorphism of the source schemes.
(Stacks, Tags 0D5S, 0D5T and 0ATR) -/
def horizontalMateRightAdjointIso {P Q Z : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (e : P ≅ Q) (q : Q ⟶ Z) (p : P ⟶ Z) [QuasiCompact q] [QuasiSeparated q]
    [QuasiCompact p] [QuasiSeparated p] (hp : e.hom ≫ q = p)
    (c : schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory Q)
    (d : schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory P)
    (adjc : horizontalMatePushforward q ⊣ c)
    (adjd : horizontalMatePushforward p ⊣ d) :
    d ≅ c ⋙ horizontalMatePullback e.hom := by
    subst p
    let ev := horizontalMateEquivalence e
    let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
    let li : horizontalMatePushforward (e.hom ≫ q) ≅
        horizontalMatePullback e.inv ⋙ horizontalMatePushforward q :=
      horizontalMatePushComp e.hom q ≪≫
        Functor.isoWhiskerRight ri (horizontalMatePushforward q)
    exact adjd.rightAdjointUniq
      ((ev.symm.toAdjunction.comp adjc).ofNatIsoLeft li.symm)

/-- Source endpoint comparison for the two successive pullbacks.
(Stacks, Tags 0D5S and 0ATR) -/
def horizontalMateSourceIso {X Y Y' Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : Z ⟶ Y') (E : schemeDerivedCategory X) :
    (derivedPullback (pullback.fst (pullback.snd f g) h)).obj
        ((derivedPullback (pullback.fst f g)).obj E) ≅
      (derivedPullback (pullbackLeftPullbackSndIso f g h).hom).obj
        ((derivedPullback (pullback.fst f (h ≫ g))).obj E) :=
  (horizontalMateAmbientComp (pullback.fst (pullback.snd f g) h)
    (pullback.fst f g)).app E ≪≫
    eqToIso (congrArg (fun s ↦ (derivedPullback s).obj E)
      (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
    ((horizontalMateAmbientComp (pullbackLeftPullbackSndIso f g h).hom
      (pullback.fst f (h ≫ g))).app E).symm

/-- Target endpoint comparison, first composing the pullbacks on the input,
then transporting the supplied right adjoints across the pullback associativity iso.
(Stacks, Tag 0ATR) -/
def horizontalMateTargetIso {X Y Y' Z : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : Y' ⟶ Y) (h : Z ⟶ Y')
    (c : schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (d : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adjc : @horizontalMatePushforward _ (pullback f (h ≫ g)) Z _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _
      (pullback.snd f (h ≫ g)) _ _ ⊣ c)
    (adjd : @horizontalMatePushforward _ (pullback (pullback.snd f g) h) Z _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _
      (pullback.snd (pullback.snd f g) h) _ _ ⊣ d)
    (K : schemeDerivedQCohCategory Y) :
    (d.obj ((horizontalMatePullback h).obj ((horizontalMatePullback g).obj K))).obj ≅
      (derivedPullback (pullbackLeftPullbackSndIso f g h).hom).obj
        (c.obj ((horizontalMatePullback (h ≫ g)).obj K)).obj := by
    have : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    have : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    exact (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.mapIso
      (d.mapIso ((horizontalMateComp h g).app K) ≪≫
        (horizontalMateRightAdjointIso (pullbackLeftPullbackSndIso f g h)
          (pullback.snd f (h ≫ g)) (pullback.snd (pullback.snd f g) h)
          (pullbackLeftPullbackSndIso_hom_snd f g h) c d adjc adjd).app
            ((horizontalMatePullback (h ≫ g)).obj K))

end
end AlgebraicGeometry

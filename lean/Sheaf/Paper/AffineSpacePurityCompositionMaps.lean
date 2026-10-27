module

public import Sheaf.Paper.AffineSpacePurityComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import Mathlib.Logic.Equiv.Fin.Basic


/-! # Composition and coordinate interchange for affine-space purity

Source: blueprint sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md
(blueprint: def-pur-affine-comparison-coordinate-maps).
All transports below are constructed from the specified pullback, tensor and adjunction
comparisons. In particular coordinate interchange uses its actual polynomial map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpacePurity
open AffineLinePurity VectorIntegrationSite

/-- Rebracketing an ordered tensor iteration into two consecutive blocks.
Source: twist and shift reassociation (blueprint: def-pur-affine-comparison-coordinate-maps). -/
def actionAddIso {B : Type v} [Category.{w} B] (F : B ⥤ B) (e : ℕ) :
    (d : ℕ) → action F (e + d) ≅ action F e ⋙ action F d
  | 0 => (Functor.rightUnitor _).symm
  | d + 1 => Functor.isoWhiskerRight (actionAddIso F e d) F ≪≫
      Functor.associator _ _ _


/-- Twisted pullback along an explicitly given projection. The positive-dimensional
orderedSource is this functor. Source: F_f in proof Step 4
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def projectionSource (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : D P Y ⥤ D P X :=
  inverseImage (Ring P) f ⋙ twistAction P X d


/-- Pullback of an ordered twist, using the canonical tensor comparison in every factor.
Source: canonical reassociation paragraph
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def twistPullbackIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X T : Scheme.{u}} (f : X ⟶ T) (aT : T ⟶ Spec (.of P.field.k))
    (K : D P T) (d : ℕ) :
    (inverseImage (Ring P) f).obj ((twistAction P T d).obj K) ≅
      (twistAction P X d).obj ((inverseImage (Ring P) f).obj K) := by
  unfold twistAction
  exact actionPullbackIso
    ((tensor (Ring P) T).flip.obj (shiftedLine P T))
    ((tensor (Ring P) X).flip.obj (shiftedLine P X)) (inverseImage (Ring P) f)
    (fun M => inverseImageTensorIso (Ring P) f M (shiftedLine P T) ≪≫
      tensorIso (Ring P) X (Iso.refl _) (shiftedLinePullback P f aT)) K d


/-- Reassociate the total twist into the e-block followed by the d-block.
Source: the displayed composition formula, including pullback and shift reassociation
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def blockSourceIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    (aT : T ⟶ Spec (.of P.field.k)) (K : D P Y) (d e : ℕ) :
    (projectionSource P (f ≫ g) (e + d)).obj K ≅
      (projectionSource P f d).obj ((projectionSource P g e).obj K) :=
  (twistAction P X (e + d)).mapIso ((inverseImageComp (Ring P) f g).app K) ≪≫
    (by
      unfold twistAction
      exact (actionAddIso ((tensor (Ring P) X).flip.obj (shiftedLine P X)) e d).app
        ((inverseImage (Ring P) f).obj ((inverseImage (Ring P) g).obj K))) ≪≫
    (twistAction P X d).mapIso
      (twistPullbackIso P f aT ((inverseImage (Ring P) g).obj K) e).symm


/-- Canonical comparison of extraordinary and ordinary pullback along a scheme
isomorphism, evaluated on a specified bounded-below etale representative.
Source: adjunction-preserving coordinate transport, proof Steps 1 and 3
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def isoExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} (i : X ≅ T)
    (M : C A T) (Me : Etale.DerivedCategoryModule A T)
    (hMe : DerivedCategory.TStructure.t.plus Me) (eM : (comparison A T).obj Me ≅ M) :
    (inverseImage A i.hom).obj M ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) i.hom).obj M :=
  (inverseImage A i.hom).mapIso eM.symm ≪≫
    ((pullback A i.hom).app Me).symm ≪≫
    (comparison A X).mapIso
      ((Etale.rightDerivedUpperShriekIsoOfIso (ModuleCat.{u + 1} A) i).symm.app Me) ≪≫
    (rightDerivedUpperShriekComparisonIso A i.hom Me hMe).symm ≪≫
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) i.hom).mapIso eM


set_option linter.defProp false in
/-- The canonical regrouping of the iterated-affine-line model; it changes parentheses
and keeps every coordinate in place. Source: the canonical affine-space identification
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def blockSchemeEq (Y : Scheme.{u}) (e : ℕ) :
    (d : ℕ) → iteratedAffineLine (iteratedAffineLine Y e) d = iteratedAffineLine Y (e + d)
  | 0 => rfl
  | d + 1 => congrArg (AffineSpace PUnit.{u + 1}) (blockSchemeEq Y e d)


/-- The regrouping identification respects the actual projections.
Source: the affine-space identification in the proposition
(blueprint: def-pur-affine-comparison-coordinate-maps).
Proof: induct on d. At zero both maps are p_e after its identity unitor. At a successor,
the affine-line projection is natural with respect to the equality at the preceding
stage; substitute the induction hypothesis and reassociate the three scheme maps. -/
theorem blockProjection (Y : Scheme.{u}) (d e : ℕ) :
    (eqToIso (blockSchemeEq Y e d)).hom ≫ iteratedAffineLineProj Y (e + d) =
      iteratedAffineLineProj (iteratedAffineLine Y e) d ≫ iteratedAffineLineProj Y e := by
  have hproj {S T : Scheme.{u}} (h : S = T) :
      (eqToIso (congrArg (AffineSpace PUnit.{u + 1}) h)).hom ≫
          (AffineSpace PUnit.{u + 1} T ↘ T) =
        (AffineSpace PUnit.{u + 1} S ↘ S) ≫ (eqToIso h).hom := by
    subst T
    simp
  induction d with
  | zero =>
    change (𝟙 _) ≫ _ = (𝟙 _) ≫ _
    rfl
  | succ d ih =>
    change (eqToIso (congrArg (AffineSpace PUnit.{u + 1})
      (blockSchemeEq Y e d))).hom ≫
        ((AffineSpace PUnit.{u + 1} (iteratedAffineLine Y (e + d)) ↘ _) ≫
          iteratedAffineLineProj Y (e + d)) =
      ((AffineSpace PUnit.{u + 1} (iteratedAffineLine (iteratedAffineLine Y e) d) ↘ _) ≫
        iteratedAffineLineProj (iteratedAffineLine Y e) d) ≫ iteratedAffineLineProj Y e
    rw [← Category.assoc, hproj (blockSchemeEq Y e d), Category.assoc, ih, Category.assoc]


/-- The actual polynomial coordinate permutation of the iterated affine space.
Source: the two orderings of affine coordinates
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def coordinateMap (Y : Scheme.{u}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    iteratedAffineLine Y n ⟶ iteratedAffineLine Y n :=
  (iteratedAffineLineProj Y n).toIteratedAffineLine
    (fun j => iteratedAffineLine.coord Y n (σ j))


private theorem tower_hom_ext {X Y : Scheme.{u}} (n : ℕ)
    (f g : X ⟶ iteratedAffineLine Y n)
    (hb : f ≫ iteratedAffineLineProj Y n = g ≫ iteratedAffineLineProj Y n)
    (hc : ∀ j, f.appTop (iteratedAffineLine.coord Y n j) =
      g.appTop (iteratedAffineLine.coord Y n j)) : f = g := by
  induction n with
  | zero =>
    change X ⟶ Y at f g
    change f = g
    change f ≫ 𝟙 Y = g ≫ 𝟙 Y at hb
    simpa only [Category.comp_id] using hb
  | succ n ih =>
    change X ⟶ AffineSpace PUnit.{u + 1} (iteratedAffineLine Y n) at f g
    apply AffineSpace.hom_ext
    · apply ih
      · change f ≫ (_ ≫ _) = g ≫ (_ ≫ _) at hb
        simpa only [Category.assoc] using hb
      · intro j
        rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply, CommRingCat.comp_apply]
        exact hc j.succ
    · intro j
      cases j
      exact hc 0

private theorem coordinateMap_inverse (Y : Scheme.{u}) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    coordinateMap Y n σ ≫ coordinateMap Y n σ.symm = 𝟙 _ := by
  apply tower_hom_ext n
  · simp [coordinateMap]
  · intro j
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinateMap,
      Scheme.Hom.toIteratedAffineLine_appTop_coord, Equiv.apply_symm_apply]
    simp

/-- The concrete coordinate permutation is invertible, with inverse given by σ inverse.
Source: coordinate identification in the proposition
(blueprint: def-pur-affine-comparison-coordinate-maps).
Proof: each composite is over Y and pulls every polynomial coordinate back to itself.
The affine-space universal property, iterated over the coordinates, identifies it with
the identity. Thus coordinateMap for σ inverse is a two-sided inverse. -/
theorem coordinateMap_isIso (Y : Scheme.{u}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsIso (coordinateMap Y n σ) := by
  exact ⟨⟨coordinateMap Y n σ.symm, coordinateMap_inverse Y n σ,
    coordinateMap_inverse Y n σ.symm⟩⟩


/-- Coordinate permutation as an isomorphism with its hom fixed by coordinateMap.
Source: the two coordinate orderings (blueprint: def-pur-affine-comparison-coordinate-maps). -/
def coordinateIso (Y : Scheme.{u}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    iteratedAffineLine Y n ≅ iteratedAffineLine Y n :=
  letI := coordinateMap_isIso Y n σ
  asIso (coordinateMap Y n σ)


/-- The fixed coordinate isomorphism is over Y.
Source: the coordinate identification in the proposition
(blueprint: def-pur-affine-comparison-coordinate-maps).
Proof: coordinateIso has precisely coordinateMap as its hom. Apply the existing
Scheme.Hom.toIteratedAffineLine_proj equation to its displayed coordinate vector. -/
theorem coordinateProjection (Y : Scheme.{u}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (coordinateIso Y n σ).hom ≫ iteratedAffineLineProj Y n = iteratedAffineLineProj Y n := by
  change coordinateMap Y n σ ≫ iteratedAffineLineProj Y n = _
  exact Scheme.Hom.toIteratedAffineLine_proj _ _

/-- The block interchange, followed by the equality d+e=e+d of total dimensions.
Source: final sentence of the proposition
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def blockPermutation (d e : ℕ) : Equiv.Perm (Fin (e + d)) :=
  (finCongr (Nat.add_comm e d)).trans finAddFlip



/-- Expose compactifiability already proved for the tower, without adding an assumption.
Source: proof Step 1 (blueprint: def-pur-affine-comparison-coordinate-maps). -/
instance purityProjectionCompactification (Y : Scheme.{u}) (d : ℕ) :
    HasCompactification (iteratedAffineLineProj Y d) := (projection_geometry Y d).2


/-- The normalized exceptional object has the ordinary positive-projection coordinates.
Source: canonical target identification in the composition formula
(blueprint: def-pur-affine-comparison-coordinate-maps).
Proof: unfold exceptional at d+1. Its value is the standing exceptional functor,
with compactification proofs identified by proof irrelevance. -/
theorem exceptionalPositive_obj_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) (K : D P Y) :
    (exceptional P Y (d + 1)).obj K =
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (d + 1))).obj K := by
  unfold exceptional
  rfl

/-- The specified comparison has a unique change to positive projection coordinates.
HEq fixes the map itself, not just its source and target.
Source: canonical coordinate reassociation in the proposition
(blueprint: def-pur-affine-comparison-coordinate-maps).
Proof: unfold orderedSource and exceptional at their positive successor, together with
projectionSource. The objects are identical. Transport the given comparison through these
endpoint equalities. Heterogeneous equality fixes its hom uniquely. -/
theorem positiveComparison_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ∃! m : (projectionSource P (iteratedAffineLineProj Y (d + 1)) (d + 1)).obj K.obj ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (d + 1))).obj K.obj,
      HEq m (affineSpacePurityComparison P Y aY K Ke hKe eK (d + 1)) := by
  have hs : orderedSource P Y (d + 1) =
      projectionSource P (iteratedAffineLineProj Y (d + 1)) (d + 1) := by
    unfold orderedSource projectionSource inverseImage
    rfl
  rw [← hs, ← exceptionalPositive_obj_eq P Y d K.obj]
  exact ⟨affineSpacePurityComparison P Y aY K Ke hKe eK (d + 1), HEq.rfl,
    fun m h ↦ eq_of_heq h⟩

/-- The specified comparison in the positive-dimensional, unnormalized coordinates.
Source: the comparison in the displayed formula
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
@[irreducible]
def positiveComparison (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    (projectionSource P (iteratedAffineLineProj Y (d + 1)) (d + 1)).obj K.obj ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (d + 1))).obj K.obj :=
  (positiveComparison_existsUnique P Y aY K Ke hKe eK d).exists.choose

/-- Source transport along an isomorphism over Y, preserving the order of Tate factors.
Source: canonical pullback and twist reassociation
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
def coordinateSourceIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X Y : Scheme.{u}} (i : X' ≅ X) (g : X ⟶ Y) (g' : X' ⟶ Y)
    (h : i.hom ≫ g = g') (aX : X ⟶ Spec (.of P.field.k)) (K : D P Y) (n : ℕ) :
    (projectionSource P g' n).obj K ≅
      (inverseImage (Ring P) i.hom).obj ((projectionSource P g n).obj K) :=
  (eqToIso (congrArg (fun f => (projectionSource P f n).obj K) h)).symm ≪≫
    (twistAction P X' n).mapIso ((inverseImageComp (Ring P) i.hom g).app K) ≪≫
    (twistPullbackIso P i.hom aX ((inverseImage (Ring P) g).obj K) n).symm


/-- Transport the actual positive-dimensional comparison along a specified coordinate
isomorphism. The target transport is the inverse adjunction mate c, after identifying
extraordinary pullback along the isomorphism with ordinary pullback.
Source: canonical identification in the proposition and proof Steps 1 and 3
(blueprint: def-pur-affine-comparison-coordinate-maps). -/
@[irreducible]
def transportedComparison (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (n : ℕ)
    {X : Scheme.{u}} (i : X ≅ iteratedAffineLine Y (n + 1)) (g' : X ⟶ Y)
    [hg' : HasCompactification g'] (h : i.hom ≫ iteratedAffineLineProj Y (n + 1) = g') :
    (projectionSource P g' (n + 1)).obj K.obj ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P)) g').obj K.obj :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  letI : IsNoetherian (iteratedAffineLine Y (n + 1)) := tower_noetherian P Y aY (n + 1)
  letI : HasCompactification (i.hom ≫ iteratedAffineLineProj Y (n + 1)) :=
    HasCompactification.comp_of_isOpenImmersion
      (iteratedAffineLineProj Y (n + 1)) i.hom
  (coordinateSourceIso P i (iteratedAffineLineProj Y (n + 1)) g' h
    (towerBase aY (n + 1)) K.obj (n + 1)).hom ≫
    (inverseImage (Ring P) i.hom).map (positiveComparison P Y aY K Ke hKe eK n) ≫
    (isoExceptional (Ring P) i
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (n + 1))).obj K.obj)
      (exceptionalEtale P Y n K.obj)
      (Etale.plus_rightDerivedUpperShriek_obj (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (n + 1)) _
        (plus_rightDerivedFunctor_comparisonLowerStar_obj K.property))
      (eqToIso ((exceptionalEtale_eq P Y n K.obj).trans
        (exceptionalPositive_obj_eq P Y n K.obj)))).hom ≫
    compositionInverse (Ring P) i.hom (iteratedAffineLineProj Y (n + 1)) K ≫
    (rightDerivedUpperShriekCongr (ModuleCat.{u + 1} (Ring P)) h).hom.app K.obj


/-- Compactifiability of the two-block composite follows from its explicit coordinate
identification with the compactifiable total projection.
Source: proof Step 1 (blueprint: def-pur-affine-comparison-coordinate-maps). -/
instance blockProjectionCompactification (Y : Scheme.{u}) (d e : ℕ) :
    HasCompactification
      (iteratedAffineLineProj (iteratedAffineLine Y e) d ≫ iteratedAffineLineProj Y e) :=
  letI : HasCompactification
      ((eqToIso (blockSchemeEq Y e d)).hom ≫ iteratedAffineLineProj Y (e + d)) :=
    HasCompactification.comp_of_isOpenImmersion
      (iteratedAffineLineProj Y (e + d)) (eqToIso (blockSchemeEq Y e d)).hom
  HasCompactification.of_eq (blockProjection Y d e)


/-- The right-hand side of the displayed composition law, including its canonical
source reassociation and the inverse adjunction-preserving exceptional compositor.
Source: displayed equation (blueprint: def-pur-affine-comparison-coordinate-maps). -/
@[irreducible]
def blockComposite (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d e : ℕ) :
    (projectionSource P
      (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1) ≫
        iteratedAffineLineProj Y (e + 1)) ((e + 1) + (d + 1))).obj K.obj ⟶
    (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
      (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1) ≫
        iteratedAffineLineProj Y (e + 1))).obj K.obj :=
  letI : LocallyOfFiniteType (towerBase aY (e + 1)) := (tower_geometry aY (e + 1)).1
  letI : QuasiCompact (towerBase aY (e + 1)) := (tower_geometry aY (e + 1)).2.1
  letI : IsSeparated (towerBase aY (e + 1)) := (tower_geometry aY (e + 1)).2.2
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  letI : IsNoetherian (iteratedAffineLine Y (e + 1)) := tower_noetherian P Y aY (e + 1)
  (blockSourceIso P (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1))
    (iteratedAffineLineProj Y (e + 1)) (towerBase aY (e + 1)) K.obj (d + 1) (e + 1)).hom ≫
  (projectionSource P (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1))
    (d + 1)).map (positiveComparison P Y aY K Ke hKe eK e ≫
      eqToHom (exceptionalPositive_obj_eq P Y e K.obj).symm) ≫
  positiveComparison P (iteratedAffineLine Y (e + 1)) (towerBase aY (e + 1))
    ⟨(exceptional P Y (e + 1)).obj K.obj,
      (stage_applicability P Y aY K Ke hKe eK (e + 1)).1⟩
    (stageEtale P Y K.obj Ke (e + 1))
    (stage_applicability P Y aY K Ke hKe eK (e + 1)).2
    (stageComparison P Y K.obj Ke eK (e + 1)) d ≫
  (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
    (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1))).map
      (eqToHom (exceptionalPositive_obj_eq P Y e K.obj)) ≫
  compositionInverse (Ring P)
    (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1))
    (iteratedAffineLineProj Y (e + 1)) K

end AlgebraicGeometry.ProEtale.AffineSpacePurity

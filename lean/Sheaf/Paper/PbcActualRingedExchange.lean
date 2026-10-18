/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Mathlib.CategoryTheory.Adjunction.Mates

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Ringed exchange for the canonical completed coefficient maps

The arbitrary invertible-coefficient interface is reexported; the following
specialization also retains the noninvertible completed coefficient structure maps.
Source: Stacks Tags 03D8, 0D6D and 099N
(blueprint: def-weil-pbc-ambient-ringed-exchange).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace AlgebraicGeometry.Scheme
variable {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Fiber-product pasting determines the ordinary direct-image comparison on sections.
Source: Stacks Tag 03D8 (blueprint: def-weil-pbc-ambient-ringed-exchange).
Proof: a section of the iterated direct image is a section over the iterated
fiber product. Restrict along the canonical fiber-product pasting isomorphism.
The completed coefficient structures agree after every finite projection, hence
agree by the limit property. This section map is therefore linear. It is natural
and invertible, and the specified section formula determines it uniquely. -/
theorem pbcActualModuleDirectCompIso_exists :
    ∃! e : pbcActualModulePush h d ⋙ pbcActualModulePush k d ≅
        pbcActualModulePush (h ≫ k) d,
      ∀ (N : pbcModules Z (pbcAdicCompletion Z d)) (U : V.ProEt)
        (m : ((pbcActualModulePush h d ⋙
          pbcActualModulePush k d).obj N).val.obj (op U)),
        (e.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m := by
  sorry

/-- The unique fiber-product-pasting comparison.
Source: Stacks Tag 03D8 (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualModuleDirectCompIso := (pbcActualModuleDirectCompIso_exists h k d).exists.choose

/-- The ordinary pullback composition is the adjunction conjugate of actual pasting.
Source: Stacks Tag 03D8 (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualModulePullCompIso :
    pbcActualModulePull (h ≫ k) d ≅
      pbcActualModulePull k d ⋙ pbcActualModulePull h d :=
  (conjugateIsoEquiv
    ((pbcActualModuleAdjunction k d).comp
      (pbcActualModuleAdjunction h d))
    (pbcActualModuleAdjunction (h ≫ k) d)).symm
        (pbcActualModuleDirectCompIso h k d)

/-- Its degreewise comparison on cochain complexes.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualModulePullCompComplexIso :
    (pbcActualModulePull (h ≫ k) d).mapHomologicalComplex (.up ℤ) ≅
      (pbcActualModulePull k d).mapHomologicalComplex (.up ℤ) ⋙
        (pbcActualModulePull h d).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (pbcActualModulePullCompIso h k d) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

/-- Universal derived counits retain the ordinary composition comparison on K-flat models.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange).
Proof: both ordinary pullbacks preserve flat-term K-flat resolving complexes.
On these complexes the universal counits are invertible. Conjugate the ordinary
pasting comparison by those counits; it is natural and invariant under resolving
quasi-isomorphisms. Descent gives the displayed isomorphism. The same equation
on a resolving representative of every object proves uniqueness. -/
theorem pbcActualDerivedPullCompIso_exists :
    ∃! e : pbcActualDerivedPull (h ≫ k) d ≅
        pbcActualDerivedPull k d ⋙ pbcActualDerivedPull h d,
      ∀ P : CochainComplex (pbcModules V (pbcAdicCompletion V d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (R := pbcAdicCompletion V d) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pbcAdicCompletion V d) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcActualDerivedPull h d).map (pbcActualPullComplexCounit k d P) ≫
            pbcActualPullComplexCounit h d
              (((pbcActualModulePull k d).mapHomologicalComplex (.up ℤ)).obj P) =
          pbcActualPullComplexCounit (h ≫ k) d P ≫
            DerivedCategory.Q.map ((pbcActualModulePullCompComplexIso h k d).hom.app P) := by
  sorry

/-- The derived composition comparison with its resolving normalization retained.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualDerivedPullCompIso := (pbcActualDerivedPullCompIso_exists h k d).exists.choose

/-- Derived direct-image composition is the conjugate of canonical pullback pasting.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualDerivedDirectCompIso :
    pbcActualDerivedPush h d ⋙ pbcActualDerivedPush k d ≅
      pbcActualDerivedPush (h ≫ k) d :=
  conjugateIsoEquiv
    ((pbcActualDerivedAdjunction k d).comp (pbcActualDerivedAdjunction h d))
    (pbcActualDerivedAdjunction (h ≫ k) d) (pbcActualDerivedPullCompIso h k d)

/-- The identity direct image is normalized by the actual identity fiber-product map.
Source: Stacks Tag 03D8 (blueprint: def-weil-pbc-ambient-ringed-exchange).
Proof: base change along identity has its canonical pullbackId isomorphism.
Restrict sections along its inverse. The completed coefficient map has the
identity residue formula, so these section functions are linear. They form a
natural isomorphism, uniquely determined by the displayed section formula. -/
theorem pbcActualModuleDirectIdIso_exists (T : Scheme.{u}) :
    ∃! e : pbcActualModulePush (𝟙 T) d ≅ 𝟭 _,
      ∀ (N : pbcModules T (pbcAdicCompletion T d)) (U : T.ProEt)
        (m : ((pbcActualModulePush (𝟙 T) d).obj N).val.obj (op U)),
        (e.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackId _ _ T).inv.app U).op m := by
  sorry

/-- The ordinary identity direct-image comparison with its fiber-product normalization.
Source: Stacks Tag 03D8 (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualModuleDirectIdIso (T : Scheme.{u}) := (pbcActualModuleDirectIdIso_exists d
  T).exists.choose

/-- The ordinary pullback unit is the adjunction conjugate of identity fiber-product pasting.
Source: Stacks Tag 03D8 (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualModulePullIdIso (T : Scheme.{u}) : pbcActualModulePull (𝟙 T) d ≅ 𝟭 _ :=
  ((conjugateIsoEquiv
    (pbcActualModuleAdjunction (𝟙 T) d)
    (Adjunction.id : (𝟭 (pbcModules T (pbcAdicCompletion T d))) ⊣ 𝟭 _)).symm
      (pbcActualModuleDirectIdIso d T)).symm

/-- The ordinary identity comparison on actual cochain complexes.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualModulePullIdComplexIso (T : Scheme.{u}) :
    (pbcActualModulePull (𝟙 T) d).mapHomologicalComplex (.up ℤ) ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (pbcActualModulePullIdIso d T) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)

/-- The derived identity is uniquely fixed on resolving models by the ordinary identity.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange).
Proof: on flat-term K-flat representatives the universal pullback counit is
invertible. Compose it with the ordinary identity comparison above. This is
natural and invariant under resolving quasi-isomorphisms, so descends uniquely
to the derived localization. Resolving every object proves invertibility. -/
theorem pbcActualDerivedPullIdIso_exists (T : Scheme.{u}) :
    ∃! e : pbcActualDerivedPull (𝟙 T) d ≅ 𝟭 _,
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (R := pbcAdicCompletion T d) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pbcAdicCompletion T d) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) =
          pbcActualPullComplexCounit (𝟙 T) d P ≫
            DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso d T).hom.app P) := by
  sorry

/-- The derived pullback identity with its ordinary normalization retained.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualDerivedPullIdIso (T : Scheme.{u}) := (pbcActualDerivedPullIdIso_exists d
  T).exists.choose

/-- Derived direct-image identity is conjugate to the normalized pullback identity.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualDerivedDirectIdIso (T : Scheme.{u}) :
    pbcActualDerivedPush (𝟙 T) d ≅ 𝟭 _ :=
  conjugateIsoEquiv (pbcActualDerivedAdjunction (𝟙 T) d)
    (Adjunction.id : (𝟭 (PbcCompletedDerived T d)) ⊣ 𝟭 _)
    (pbcActualDerivedPullIdIso d T).symm

/-- Completed pullback composition is fixed by its two completion units.
Source: Stacks 099N (blueprint: def-weil-pbc-ambient-ringed-exchange).
Proof: the composite completed pullback and the completed composite ordinary
pullback represent the same completion reflection. Start with the canonical
K-flat ordinary pullback pasting and then the two quotient units. The reflection
property extends this map uniquely to complete targets. The same construction
backwards is inverse, as both composites preserve the unit. -/
theorem pbcActualCompletedPullCompIso_exists :
    ∃! e :
      (ObjectProperty.ι (PbcIsIntrinsicallyComplete V d) ⋙ pbcActualCompletedPull k d) ⋙
          pbcActualCompletedPull h d ≅
        ObjectProperty.ι (PbcIsIntrinsicallyComplete V d) ⋙ pbcActualCompletedPull (h ≫ k) d,
      ∀ K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete V d),
        (pbcActualDerivedPullCompIso h k d).hom.app K.obj ≫
            (pbcActualDerivedPull h d).map ((pbcActualCompletedPullUnit k d).app K.obj) ≫
            (pbcActualCompletedPullUnit h d).app ((pbcActualCompletedPull k d).obj K.obj) ≫
            e.hom.app K = (pbcActualCompletedPullUnit (h ≫ k) d).app K.obj := by
  sorry

/-- The canonical unit-compatible completed composition comparison.
Source: Stacks 099N (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualCompletedPullCompIso :=
  (pbcActualCompletedPullCompIso_exists h k d).exists.choose

/-- Completed identity pullback fixes complete objects through its actual unit.
Source: Stacks 099N (blueprint: def-weil-pbc-ambient-ringed-exchange).
Proof: identity ordinary pullback has the canonical identity pasting comparison.
Completion of an intrinsically complete object has invertible unit. Compose its
inverse with the identity comparison. The reflection property proves uniqueness. -/
theorem pbcActualCompletedPullIdIso_exists (T : Scheme.{u}) :
    ∃! e : ObjectProperty.ι (PbcIsIntrinsicallyComplete T d) ⋙
        pbcActualCompletedPull (𝟙 T) d ≅ ObjectProperty.ι (PbcIsIntrinsicallyComplete T d),
      ∀ K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete T d),
        (pbcActualCompletedPullUnit (𝟙 T) d).app K.obj ≫ e.hom.app K =
          (pbcActualDerivedPullIdIso d T).hom.app K.obj := by
  sorry

/-- The completed identity comparison on the actual complete subcategory.
Source: Stacks 099N (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualCompletedPullIdIso (T : Scheme.{u}) :=
  (pbcActualCompletedPullIdIso_exists d T).exists.choose

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The ringed pullback square is formed solely from canonical composition and commutativity.
Source: Stacks Tag 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualCompletedPullSquareIso :
    pbcActualDerivedPull g d ⋙ pbcActualDerivedPull f' d ≅
      pbcActualDerivedPull f d ⋙ pbcActualDerivedPull g' d :=
  (pbcActualDerivedPullCompIso f' g d).symm ≪≫
    eqToIso (congrArg (fun a ↦ pbcActualDerivedPull a d) sq.w.symm) ≪≫
    pbcActualDerivedPullCompIso g' f d

/-- Ambient exchange is the adjunction mate of the actual ringed pullback square.
It precedes completion and constructibility. Source: Stacks Tag 099N
(blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualCompletedAmbientExchange :
    pbcActualDerivedPush f d ⋙ pbcActualDerivedPull g d ⟶
      pbcActualDerivedPull g' d ⋙ pbcActualDerivedPush f' d :=
  (mateEquiv (pbcActualDerivedAdjunction f d) (pbcActualDerivedAdjunction f' d)
    (TwoSquare.mk _ _ _ _ (pbcActualCompletedPullSquareIso d sq).hom)).natTrans

/-- Completed exchange is the ambient mate followed by completion and its direct-image
comparison, with the canonical pullback-completion identifications on both sides.
Source: Stacks Tag 099N (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
def pbcActualCompletedExchange :
    pbcActualDerivedPush f d ⋙ pbcActualCompletedPull g d ⟶
      pbcActualCompletedPull g' d ⋙ pbcActualDerivedPush f' d :=
  (isoWhiskerLeft _ (Iso.refl (pbcActualCompletedPull g d))).hom ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (pbcActualCompletedAmbientExchange d sq) (pbcActualCompletion d Y') ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft _ (pbcActualDirectCompletionIso f' d).hom ≫
    (Functor.associator _ _ _).inv ≫
    (isoWhiskerRight (Iso.refl (pbcActualCompletedPull g' d)).symm _).hom

end AlgebraicGeometry.Scheme

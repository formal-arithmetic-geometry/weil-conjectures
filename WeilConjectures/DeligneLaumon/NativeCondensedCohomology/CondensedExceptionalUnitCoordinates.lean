/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-! # Ordinary exceptional-unit and native cohomology coordinates

Only the abelian category of Weil modules is encoded fully faithfully here.
There is no assertion of faithfulness for a functor from derived Weil objects to
strict pairs. Source: the heart comparison in sk-def-sf-weil-complexes.
(blueprint: lem-sf-native-condensed-cohomology-coordinates).

The exceptional-unit constructions below use the actual localizing adjunction and
its counit normalization. Both coordinate layers are supplied in this module, so
consumers need no pending source module.
(blueprint: lem-sf-native-condensed-exceptional-setup).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.NativeCondensedCohomology

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar k₀ ≠ ell)] (X : Scheme.{u}) [X.Over (Spec (.of k₀))]

/-- Exact condensed pullback along the native geometric Galois Frobenius.
Source: sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-cohomology-coordinates). -/
abbrev action := upperStar (Profinite.padicAlgClRingObj ell)
  (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom

/-- The coefficient encoding intertwines the two exact Frobenius pullbacks.
Source: the native coefficient pullback comparison
(blueprint: lem-sf-native-condensed-cohomology-coordinates). -/
def actionComparison :
    NativeEncoding.encoding ell (X ↘ Spec (.of k₀)).geometricFiber ⋙ action k₀ ell X ≅
      WeilSheaf.frobeniusPullback k₀ ell X ⋙
        NativeEncoding.encoding ell (X ↘ Spec (.of k₀)).geometricFiber :=
  (NativeEncoding.pullComparison ell
    (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom).symm ≪≫
    Functor.isoWhiskerRight
      (adicUpperStarIsoLowerStarInv ell
        (X ↘ Spec (.of k₀)).geometricGaloisFrobenius) _

/-- The specified native encoding sends the constant carrier to the regular condensed module.
Source: the coefficient-unit comparison in sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-cohomology-coordinates).
Proof: forgetting vector scalars identifies the native regular action with the
regular action on the encoded coefficient ring. Restriction along coefficientIso
then identifies this regular module with the condensed regular module. -/
def constantCarrierIso :
    (NativeEncoding.encoding ell (X ↘ Spec (.of k₀)).geometricFiber).obj
        (AdicSheaf.unit ell (X ↘ Spec (.of k₀)).geometricFiber) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (X ↘ Spec (.of k₀)).geometricFiber) :=
  (Mod.comap (NativeEncoding.coefficientIso ell
    (X ↘ Spec (.of k₀)).geometricFiber).hom).mapIso
      (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) ≪≫
    (Mod.regularIsoComapRegular (NativeEncoding.coefficientIso ell
      (X ↘ Spec (.of k₀)).geometricFiber).hom).symm

omit [Finite k₀] [Fact (ringChar k₀ ≠ ell)] in
/-- The constant-carrier identification has the specified coefficient map as its inverse.
Source: the unit normalization in sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-cohomology-coordinates).
Proof: unfold restriction of scalars and the regular-module comparison. Its
underlying inverse is coefficientIso followed by the identity. -/
theorem constantCarrierIso_inv_hom :
    (constantCarrierIso k₀ ell X).inv.hom =
      (NativeEncoding.coefficientIso ell (X ↘ Spec (.of k₀)).geometricFiber).hom := by
  simp [constantCarrierIso, Mod.regularIsoComapRegular]
  rfl

/-- The exact encoding of native Weil modules, retaining their Frobenius structure.
Source: sk-def-sf-weil-complexes, degree-zero comparison
(blueprint: lem-sf-native-condensed-cohomology-coordinates). -/
def encode : ProEtaleWeilSheaf k₀ ell X ⥤ IsoAlgebra (action k₀ ell X) :=
  IsoAlgebra.mapOfNatIso (actionComparison k₀ ell X)

/-- The encoding is fully faithful on the abelian category of Weil modules.
Source: exact coefficient equivalence, followed by fixed-pair transport
(blueprint: lem-sf-native-condensed-cohomology-coordinates).
Proof: the native coefficient encoding is an equivalence. A commuting morphism
between encoded modules has a unique native preimage. Faithfulness reflects the
commuting square, so the preimage is a Weil-module morphism. -/
def encodeFullyFaithful : (encode k₀ ell X).FullyFaithful :=
  IsoAlgebra.fullyFaithfulMapOfNatIso (actionComparison k₀ ell X)
    (Functor.FullyFaithful.ofFullyFaithful _)

/-- Compute native cohomology and then encode it in the condensed Weil heart.
Source: the exact-forgetting cohomology comparison in sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-cohomology-coordinates). -/
def nativeHomology (n : ℤ) : WeilComplex k₀ ell X ⥤ IsoAlgebra (action k₀ ell X) :=
  WeilComplex.homologySheaf n ⋙ (WeilSheaf.objectProperty k₀ ell X).ι ⋙ encode k₀ ell X

/-- Restrict the exact encoding to constructible native Weil sheaves.
Source: the full constructible heart in sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-cohomology-coordinates). -/
def sheafEncoding : WeilSheaf k₀ ell X ⥤ IsoAlgebra (action k₀ ell X) :=
  (WeilSheaf.objectProperty k₀ ell X).ι ⋙ encode k₀ ell X

/-- An isomorphism in condensed heart coordinates lifts uniquely to native sheaves.
Source: the full constructible heart in sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-cohomology-coordinates).
Proof: compose the fully faithful inclusion of the constructible heart with the
fully faithful encoding. Its inverse on Hom sets lifts the isomorphism and its
inverse; faithfulness gives the inverse equations. -/
def sheafEncodingFullyFaithful : (sheafEncoding k₀ ell X).FullyFaithful :=
  (WeilSheaf.objectProperty k₀ ell X).fullyFaithfulι.comp (encodeFullyFaithful k₀ ell X)

/-- Condensed equivariant cohomology coordinates suffice to identify a native sheaf.
Source: the heart-comparison clause of sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-cohomology-coordinates).
Proof: apply the inverse on isomorphisms of the fully faithful heart encoding. -/
theorem nativeHomology_iso_of_encoding (K : WeilComplex k₀ ell X) (n : ℤ)
    (L : WeilSheaf k₀ ell X)
    (e : (nativeHomology k₀ ell X n).obj K ≅
      (sheafEncoding k₀ ell X).obj L) :
    Nonempty ((WeilComplex.homologySheaf n).obj K ≅ L) :=
  ⟨(sheafEncodingFullyFaithful k₀ ell X).preimageIso e⟩

end WeilConjectures.NativeCondensedCohomology

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace WeilConjectures.NativeCondensedCohomology

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar k₀ ≠ ell)]

/-- The ordinary internal-module category on the native geometric fibre.
Source: sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
abbrev modules (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  Mod (Sheaf (Scheme.ProEt.topology (T ↘ Spec (.of k₀)).geometricFiber) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ell) (T ↘ Spec (.of k₀)).geometricFiber)

/-- The exact derived Frobenius pullback.
Source: sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
abbrev derivedAction (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  (action k₀ ell T).mapDerivedCategory

/-- Compare derived pullback with the derived functor of the exact heart pullback.
Source: exact inverse image; sk-thm-sf-comp-composition
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def actionDerivedComparison (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :
    moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ell)
      (T ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom ≅ derivedAction k₀ ell T :=
  (action k₀ ell T).leftDerivedFunctorIsoMapDerivedCategory

/-- Cohomology of an ordinary derived object carrying a specified Frobenius map.
Source: exact inverse image commutes with cohomology
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def pairHomology (T : Scheme.{u}) [T.Over (Spec (.of k₀))] (n : ℤ) :
    IsoAlgebra (derivedAction k₀ ell T) ⥤ IsoAlgebra (action k₀ ell T) :=
  IsoAlgebra.mapOfNatIso ((action k₀ ell T).mapDerivedCategoryHomologyFunctorIso n)

/-- The ordinary constant unit in degree zero.
Source: sk-cor-sp-all-coefficients
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def unitObject (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :
    DerivedCategory (modules k₀ ell T) :=
  (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)

/-- The canonical Frobenius structure on the ordinary constant unit.
Source: the monoidal pullback unit, sk-def-sf-weil-complexes
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def unitTheta (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :
    (derivedAction k₀ ell T).obj (unitObject k₀ ell T) ≅ unitObject k₀ ell T :=
  ((action k₀ ell T).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (action k₀ ell T)).symm

/-- The native geometric fibre as a separated finite-type scheme over the closure.
Source: geometric base change, sk-thm-sf-comp-composition
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def fiber (T : Scheme.{u}) [T.Over (Spec (.of k₀))]
    [IsSeparated (T ↘ Spec (.of k₀))] [LocallyOfFiniteType (T ↘ Spec (.of k₀))]
    [QuasiCompact (T ↘ Spec (.of k₀))] : SepFinType (AlgebraicClosure k₀) := by
  let F : Over (Spec (.of (AlgebraicClosure k₀))) :=
    Over.mk (T ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  have : IsSeparated F.hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : LocallyOfFiniteType F.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact F.hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  exact SepFinType.mk F

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  [IsSeparated (X ↘ Spec (.of k₀))] [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
  [QuasiCompact (X ↘ Spec (.of k₀))]
  [IsSeparated (Y ↘ Spec (.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (.of k₀))]
  [QuasiCompact (Y ↘ Spec (.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))]

/-- The actual base change of the native map to the algebraic closure.
Source: geometric base change
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def fiberMap : fiber k₀ X ⟶ fiber k₀ Y :=
  ⟨Over.homMk (Scheme.Hom.geometricFiberMap f (comp_over f _))
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure f _)⟩

variable (c : Compactification (fiberMap k₀ f).hom.left)
  (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj ell)
    (AlgebraicClosure k₀))

/-- The literal ordinary compact-support functor for the specified compactification.
Source: sk-thm-sf-comp-composition
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
abbrev support := rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell) c

/-- Its actual restriction to the localizing constructible closures.
Source: sk-prop-sf-existence and sk-thm-sf-comp-composition
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
abbrev localSupport := localizingLowerShriek (Profinite.padicAlgClRingObj ell) c
  (H.preserves (fiberMap k₀ f) c).1

/-- Canonical compact-support Frobenius exchange, expressed using exact derived pullback.
Source: sk-thm-sf-comp-composition, normalized exchange
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def supportExchange :
    (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
      (X ↘ Spec (.of k₀)).geometricFiber).ι ⋙
        (support k₀ ell f c ⋙ derivedAction k₀ ell Y) ≅
    (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
      (X ↘ Spec (.of k₀)).geometricFiber).ι ⋙
        (derivedAction k₀ ell X ⋙ support k₀ ell f c) :=
  Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft (support k₀ ell f c)
        (actionDerivedComparison k₀ ell Y).symm) ≪≫
    H.exchange
      (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f
        (comp_over f _)) c c ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (actionDerivedComparison k₀ ell X) _)

/-- An ordinary localizing right adjoint and the exceptional unit's Frobenius map.
The map is normalized by the actual compact-support exchange and adjunction counit.
Source: sk-prop-sf-existence and the counit square of
thm-pur-weil-equivariance-of-purity-and-trace
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
structure ExceptionalUnit where
  right : (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
    (Y ↘ Spec (.of k₀)).geometricFiber).FullSubcategory ⥤
    (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
      (X ↘ Spec (.of k₀)).geometricFiber).FullSubcategory
  adjunction : localSupport k₀ ell f c H ⊣ right
  unit_mem : localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
    (Y ↘ Spec (.of k₀)).geometricFiber (unitObject k₀ ell Y)
  theta : (derivedAction k₀ ell X).obj
      (right.obj ⟨unitObject k₀ ell Y, unit_mem⟩).obj ≅
    (right.obj ⟨unitObject k₀ ell Y, unit_mem⟩).obj
  normalized : (derivedAction k₀ ell Y).map
      (adjunction.counit.app ⟨unitObject k₀ ell Y, unit_mem⟩).hom ≫
        (unitTheta k₀ ell Y).hom =
    (supportExchange k₀ ell f c H).hom.app
        (right.obj ⟨unitObject k₀ ell Y, unit_mem⟩) ≫
      (support k₀ ell f c).map theta.hom ≫
        (adjunction.counit.app ⟨unitObject k₀ ell Y, unit_mem⟩).hom

/-- The exceptional unit as an ordinary derived object with its counit-normalized
Frobenius map. Source: sk-def-sf-weil-complexes, exceptional counit transport
(blueprint: lem-sf-native-condensed-exceptional-setup). -/
def ExceptionalUnit.pair (E : ExceptionalUnit k₀ ell f c H) :
    IsoAlgebra (derivedAction k₀ ell X) :=
  IsoAlgebra.mk (E.right.obj ⟨unitObject k₀ ell Y, E.unit_mem⟩).obj E.theta

omit [Fact (ringChar k₀ ≠ ell)] in
/-- The actual counit equation determines the exceptional unit's Frobenius datum.
Source: thm-pur-weil-equivariance-of-purity-and-trace, counit square
(blueprint: lem-sf-native-condensed-exceptional-setup).
Proof: cancel the invertible compact-support exchange. The resulting equation
identifies the adjoint transposes of the two candidate maps. The adjunction Hom
bijection is injective, hence the maps, and therefore the isomorphisms, agree. -/
theorem ExceptionalUnit.theta_unique (E : ExceptionalUnit k₀ ell f c H)
    (t : (derivedAction k₀ ell X).obj E.pair.carrier ≅ E.pair.carrier)
    (ht : (derivedAction k₀ ell Y).map
        (E.adjunction.counit.app ⟨unitObject k₀ ell Y, E.unit_mem⟩).hom ≫
          (unitTheta k₀ ell Y).hom =
      (supportExchange k₀ ell f c H).hom.app
          (E.right.obj ⟨unitObject k₀ ell Y, E.unit_mem⟩) ≫
        (support k₀ ell f c).map t.hom ≫
          (E.adjunction.counit.app ⟨unitObject k₀ ell Y, E.unit_mem⟩).hom) :
    t = E.theta := by
  let U := (⟨unitObject k₀ ell Y, E.unit_mem⟩ :
    (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
      (Y ↘ Spec (.of k₀)).geometricFiber).FullSubcategory)
  let V := E.right.obj U
  let W : (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
      (X ↘ Spec (.of k₀)).geometricFiber).FullSubcategory :=
    ⟨(derivedAction k₀ ell X).obj V.obj, fun P hP hgen ↦
      hP.2.1.of_iso E.theta.symm (V.property P hP hgen)⟩
  let a : W ⟶ V := ObjectProperty.homMk t.hom
  let b : W ⟶ V := ObjectProperty.homMk E.theta.hom
  have hab : (localSupport k₀ ell f c H).map a ≫ E.adjunction.counit.app U =
      (localSupport k₀ ell f c H).map b ≫ E.adjunction.counit.app U := by
    apply ObjectProperty.hom_ext
    apply (cancel_epi ((supportExchange k₀ ell f c H).hom.app V)).mp
    exact ht.symm.trans E.normalized
  have hab' : a = b := (E.adjunction.homEquiv W U).symm.injective (by
    simpa only [Adjunction.homEquiv_counit] using hab)
  apply Iso.ext
  exact congrArg (fun v : W ⟶ V ↦ v.hom) hab'


/-- A counit-normalized comparison with an ordinary Frobenius object is equivariant.
Source: thm-pur-weil-equivariance-of-purity-and-trace, Steps 1--2
(blueprint: lem-sf-native-condensed-exceptional-setup).
Proof: conjugate the target Frobenius map by the underlying comparison. The counit
condition and uniqueness identify this conjugate with the exceptional datum.
Cancel the inverse comparison to obtain the intertwining square. -/
def ExceptionalUnit.pairIsoOfCounit (E : ExceptionalUnit k₀ ell f c H)
    (L : IsoAlgebra (derivedAction k₀ ell X)) (e : E.pair.carrier ≅ L.carrier)
    (ht : (derivedAction k₀ ell Y).map
        (E.adjunction.counit.app ⟨unitObject k₀ ell Y, E.unit_mem⟩).hom ≫
          (unitTheta k₀ ell Y).hom =
      (supportExchange k₀ ell f c H).hom.app
          (E.right.obj ⟨unitObject k₀ ell Y, E.unit_mem⟩) ≫
        (support k₀ ell f c).map
          (((derivedAction k₀ ell X).mapIso e ≪≫ L.str ≪≫ e.symm).hom) ≫
          (E.adjunction.counit.app ⟨unitObject k₀ ell Y, E.unit_mem⟩).hom) :
    E.pair ≅ L := by
  have h := ExceptionalUnit.theta_unique k₀ ell f c H E
    ((derivedAction k₀ ell X).mapIso e ≪≫ L.str ≪≫ e.symm) ht
  refine ObjectProperty.isoMk _ (Algebra.isoMk e ?_)
  change (derivedAction k₀ ell X).map e.hom ≫ L.obj.str = E.theta.hom ≫ e.hom
  rw [← h]
  simp

end WeilConjectures.NativeCondensedCohomology

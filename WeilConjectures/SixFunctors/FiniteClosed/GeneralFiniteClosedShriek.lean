/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteClosedCondensedBridge
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenPullbackGenerators

/-!
# Finite coefficient change for the supplied constructible exceptional inverse image

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-finite-closed-shriek.md and lem-coef-finite-closed-shriek.proof.md
(blueprint: lem-coef-finite-closed-shriek).

All exceptional operations below are restrictions of `finiteSuppliedUpperShriek`.
The compact-support/direct-image identification is a specified adjunction transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures.FiniteClosed

/-- A finite ell-primary ring, with its original carrier retained.  This merely groups
three hypotheses of the blueprint statement; the small carrier is its canonical Shrink.
Source: blueprint lem-coef-finite-closed-shriek, first sentence.
(blueprint: lem-coef-finite-closed-shriek). -/
structure Coefficient (ell : ℕ) where
  carrier : Type u
  [ring : CommRing carrier]
  [finite : Finite carrier]
  primary : ∃ n : ℕ, ∀ a : Shrink.{0, u} carrier, (ell ^ n) • a = 0
attribute [instance] Coefficient.ring Coefficient.finite

/-- The existing continuous-function condensed ring of the canonically small carrier.
Source: def-sfb-continuous-map-condensed-ring.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev coeff {ell : ℕ} (A : Coefficient.{u} ell) :=
  Profinite.continuousMapRingObj.{u} (Shrink.{0, u} A.carrier)

/-- Separated finite-type schemes over the fixed base, retaining their structure map.
Source: blueprint lem-coef-finite-closed-shriek, geometric hypotheses.
(blueprint: lem-coef-finite-closed-shriek). -/
structure Space (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of k)
  [separated : IsSeparated structureMap]
  [finiteType : LocallyOfFiniteType structureMap]
  [quasiCompact : QuasiCompact structureMap]
attribute [instance] Space.separated Space.finiteType Space.quasiCompact
/-- The bundled structure map gives the scheme over k. Source: geometric hypotheses.
(blueprint: lem-coef-finite-closed-shriek). -/
instance spaceOver {k : Type u} [Field k] (X : Space k) : X.scheme.Over (Spec (.of k)) :=
  ⟨X.structureMap⟩
/-- The bundled finite-type hypothesis on the structure map. Source: geometric hypotheses.
(blueprint: lem-coef-finite-closed-shriek). -/
instance spaceLocallyOfFiniteType (k : Type u) [Field k] (X : Space k) :
    LocallyOfFiniteType (X.scheme ↘ Spec (.of k)) := X.finiteType
/-- The quasi-compact part of finite type. Source: geometric hypotheses.
(blueprint: lem-coef-finite-closed-shriek). -/
instance spaceQuasiCompact (k : Type u) [Field k] (X : Space k) :
    QuasiCompact (X.scheme ↘ Spec (.of k)) := X.quasiCompact
/-- The bundled separation hypothesis. Source: geometric hypotheses.
(blueprint: lem-coef-finite-closed-shriek). -/
instance spaceSeparated (k : Type u) [Field k] (X : Space k) :
    IsSeparated (X.scheme ↘ Spec (.of k)) := X.separated

/-- A morphism over the fixed field. Source: the same geometric hypotheses.
(blueprint: lem-coef-finite-closed-shriek). -/
structure Map {k : Type u} [Field k] (X Y : Space k) where
  hom : X.scheme ⟶ Y.scheme
  comm : hom ≫ Y.structureMap = X.structureMap
/-- The bundled morphism commutes with the structure maps. Source: morphisms over k.
(blueprint: lem-coef-finite-closed-shriek). -/
instance mapIsOver {k : Type u} [Field k] {X Y : Space k} (f : Map X Y) :
    f.hom.IsOver (Spec (.of k)) := ⟨f.comm⟩

/-- Composition of the given morphisms over k. Source: blueprint composition clause.
(blueprint: lem-coef-finite-closed-shriek). -/
def Map.comp {k : Type u} [Field k] {X Y Z : Space k} (f : Map X Y) (g : Map Y Z) :
    Map X Z := ⟨f.hom ≫ g.hom, by rw [Category.assoc, g.comm, f.comm]⟩

/-- Closed immersions compose. Source: the closed-composition clause.
(blueprint: lem-coef-finite-closed-shriek). -/
instance mapCompIsClosedImmersion {k : Type u} [Field k]
    {W Z X : Space k} (t : Map W Z) (i : Map Z X)
    [IsClosedImmersion t.hom] [IsClosedImmersion i.hom] :
    IsClosedImmersion (t.comp i).hom := by
  change IsClosedImmersion (t.hom ≫ i.hom)
  infer_instance

/-- The recorded ambient derived category of modules over the pulled-back condensed ring.
Source: def-weil-pbc-proetale-site and det-def-sfb-constructible-tor-amplitude.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev Ambient {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell) (X : Space k) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (ProEt.topology X.scheme) Ab.{u + 1})
    (ProEtale.condensedRingObj (coeff A) X.scheme))

/-- Exactly the recorded constant-model bounded constructibility and finite Tor test.
Source: det-def-sfb-constructible-tor-amplitude.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev ctf {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell) (X : Space k) :
    ObjectProperty (Ambient A X) :=
  ProEtale.constantModelBoundedConstructible (coeff A) X.scheme ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K

/-- Dctf is a full subcategory, so its objects already carry every required finite-Tor domain.
Source: sk-prop-sf-rf-shriek-preservation, restricted adjunction.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev Dctf {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell) (X : Space k) :=
  (ctf A X).FullSubcategory

/-- The canonical inclusion of the generators in their localizing closure.
Source: sk-def-localizing-closure, intersection definition.
(blueprint: lem-coef-finite-closed-shriek). -/
def localizingEquivalence {ell : ℕ} {k : Type u} [Field k]
    (A : Coefficient.{u} ell) (X : Space k) :
    Dctf A X ≌ (ProEtale.CondensedRing.localizingDctfProperty (coeff A)
      X.scheme).FullSubcategory where
  functor :=
    { obj := fun K ↦ ⟨⟨K.obj, fun P _ hP ↦ hP _ K.property⟩, K.property⟩
      map := fun f ↦ ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  inverse :=
    { obj := fun K ↦ ⟨K.obj.obj, K.property⟩
      map := fun f ↦ ObjectProperty.homMk f.hom.hom }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The coefficient map on the canonical small carriers. Source: coefficient-list convention
and the canonical Shrink ring equivalences.
(blueprint: lem-coef-finite-closed-shriek). -/
def smallMap {ell : ℕ} {A B : Coefficient.{u} ell} (φ : A.carrier →+* B.carrier) :
    Shrink.{0, u} A.carrier →+* Shrink.{0, u} B.carrier :=
  (Shrink.ringEquiv B.carrier).symm.toRingHom.comp
    (φ.comp (Shrink.ringEquiv A.carrier).toRingHom)

/-- The canonical postcomposition map of condensed coefficients.
Source: def-sfb-continuous-map-condensed-ring-map, postcomposition by smallMap φ.
(blueprint: lem-coef-finite-closed-shriek). -/
def coefficientMap {ell : ℕ} {A B : Coefficient.{u} ell} (φ : A.carrier →+* B.carrier) :
    coeff A ⟶ coeff B :=
  Profinite.continuousMapRingObjMapOfUniverse.{u, 0} (smallMap φ)
    continuous_of_discreteTopology
/-- Postcomposition is a unital ring-object morphism.
Source: def-sfb-continuous-map-condensed-ring-map, ring-object clause.
(blueprint: lem-coef-finite-closed-shriek). -/
instance coefficientMapIsMonHom {ell : ℕ} {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) :
    IsMonHom (coefficientMap φ) :=
  Profinite.isMonHom_continuousMapRingObjMapOfUniverse.{u, 0} (smallMap φ)
    continuous_of_discreteTopology

/-- Canonical derived extension of the actual pulled-back condensed coefficient rings.
This is ordinary uncompleted tensor on the recorded internal module category.
Source: det-sp-scalar-extension-functor, K-flat derived tensor construction;
its native internal-module implementation is det-def-sfb-derived-extension-of-scalars.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev scalar {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) (X : Space k) : Ambient A X ⥤ Ambient B X :=
  (Mod.extendScalars (ProEtale.coefficientMap (coefficientMap φ) X.scheme)).leftDerivedFunctor

/-- The recorded derived direct image. Source: def-weil-derived-direct-image.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev push {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {X Y : Space k} (f : Map X Y) : Ambient A X ⥤ Ambient A Y :=
  (ProEtale.CondensedRing.lowerStar (coeff A) f.hom).rightDerivedFunctor

/-- The recorded exact derived inverse image. Source: the locally closed clause.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev pull {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {X Y : Space k} (f : Map X Y) : Ambient A Y ⥤ Ambient A X :=
  (ProEtale.CondensedRing.upperStar (coeff A) f.hom).leftDerivedFunctor

/-- Pullback/tensor interchange, deriving the ordinary coefficient square on K-flat complexes.
Source: blueprint proof steps 2 and 5, ringed tensor/pullback comparison.
(blueprint: lem-coef-finite-closed-shriek). -/
def scalarPullIso {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) {X Y : Space k} (f : Map X Y) :
    pull A f ⋙ scalar φ X ≅ scalar φ Y ⋙ pull B f := by
  exact ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso (coefficientMap φ) f.hom

/-- The canonical direct-image coefficient map is the geometric adjoint transpose of
pullback/tensor interchange followed by the A-counit. Source: blueprint step 2.
(blueprint: lem-coef-finite-closed-shriek). -/
def directMap {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) {X Y : Space k} (f : Map X Y) (N : Ambient A X) :
    (scalar φ Y).obj ((push A f).obj N) ⟶ (push B f).obj ((scalar φ X).obj N) :=
  (ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction (coeff B) f.hom).homEquiv _ _
    ((scalarPullIso φ f).inv.app ((push A f).obj N) ≫
      (scalar φ X).map
        ((ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction (coeff A) f.hom).counit.app N))

/-- Canonical compact-support to direct-image map. It is transposed through f^* ⊣ Rf_*;
the transpose is the proper counit followed by the inverse open-extension unit.
Source: blueprint step 1, compactification coherence at the closed immersion.
(blueprint: lem-coef-finite-closed-shriek). -/
def compactSupportToPush {ell : ℕ} {k : Type u} [Field k]
    (A : Coefficient.{u} ell) {X Y : Space k} (f : Map X Y)
    (c : Compactification f.hom) (M : Ambient A X) :
    (ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification (coeff A) c).obj M ⟶
      (push A f).obj M := by
  let Λ := coeff A
  let J := (ProEtale.CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
  let G := (ProEtale.CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
  let adjJ := ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i
  letI : IsIso adjJ.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  refine (ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction Λ f.hom).homEquiv _ _ ?_
  exact (eqToIso (congrArg
      (fun h ↦ (ProEtale.CondensedRing.upperStar Λ h).leftDerivedFunctor) c.comm)).hom.app _ ≫
    (ProEtale.CondensedRing.leftDerivedUpperStarComp Λ c.i c.g).hom.app _ ≫
    (ProEtale.CondensedRing.upperStar Λ c.i).leftDerivedFunctor.map
      ((ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.g).counit.app (J.obj M)) ≫
    (ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.i).hom.app _ ≫
    (asIso adjJ.unit).inv.app M

/-- Scalar extension preserves the recorded finite constructible finite-Tor predicate.
Source: blueprint step 1 and det-sp-scalar-extension-functor.
Proof: compute on a K-flat resolution; tensor preserves each finite constant local model,
and testing the same resolution against B-modules preserves a finite Tor interval.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem scalar_preserves {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) (X : Space k) (M : Dctf A X) :
    ctf B X ((scalar φ X).obj M.obj) := by
  sorry

/-- Closed direct image preserves the same predicate.
Source: blueprint step 1, exact closed extension and the closed support identification.
Proof: extend each constructible stratum by the closed immersion. Exactness gives boundedness;
the projection formula identifies every Tor test with closed extension of the original test.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem push_preserves {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {X Y : Space k} (f : Map X Y) [IsClosedImmersion f.hom] (M : Dctf A X) :
    ctf A Y ((push A f).obj M.obj) := by
  sorry

/-- Open restriction preserves the same predicate.
Source: blueprint step 5.
Proof: restrict the finite stratification and test Tor against extension by zero of a test
module, using j^*j_!=id and pullback/tensor interchange.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem pull_preserves {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {X Y : Space k} (f : Map X Y) [IsOpenImmersion f.hom] (M : Dctf A Y) :
    ctf A X ((pull A f).obj M.obj) := by
  classical
  let Λ := coeff A
  let P := ProEtale.CondensedRing.upperStar Λ f.hom
  have : CompactSpace X.scheme :=
    QuasiCompact.compactSpace_of_compactSpace X.structureMap
  have : IsLocallyNoetherian X.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian X.structureMap
  have : QuasiSeparatedSpace X.scheme := inferInstance
  have : CompactSpace Y.scheme :=
    QuasiCompact.compactSpace_of_compactSpace Y.structureMap
  have : IsLocallyNoetherian Y.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian Y.structureMap
  have : QuasiSeparatedSpace Y.scheme := inferInstance
  have hP : ctf A X (P.mapDerivedCategory.obj M.obj) := by
    refine ⟨⟨P.bounded_mapDerivedCategory_obj M.property.1.1, ?_⟩, ?_⟩
    · intro n
      apply ProEtale.CondensedRing.constructible_of_iso Λ
        ((P.mapDerivedCategoryHomologyFunctorIso n).app M.obj)
      have h := M.property.1.2 n
      have hX : CompactSpace X.scheme ∧ QuasiSeparatedSpace X.scheme :=
        ⟨inferInstance, inferInstance⟩
      have hY : CompactSpace Y.scheme ∧ QuasiSeparatedSpace Y.scheme :=
        ⟨inferInstance, inferInstance⟩
      simp only [ProEtale.IsConstantModelConstructible, if_pos hY] at h
      simp only [ProEtale.IsConstantModelConstructible, if_pos hX]
      exact ProEtale.CondensedRing.stratified_pullback Λ f.hom _ h
    · have hflat := ProEtale.CondensedRing.upperStar_preservesFlat Λ f.hom
      obtain ⟨a, b, hab⟩ := M.property.2
      exact ⟨a, b, DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj P hab⟩
  let e := (ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    Λ f.hom).symm.app M.obj
  exact ⟨(ProEtale.constantModelConstructibleFiniteTor_wellDefined Λ X.scheme).2.1.of_iso
      e hP.1,
    (ProEtale.constantModelConstructibleFiniteTor_wellDefined Λ X.scheme).2.2.2.1.of_iso
      e hP.2⟩

/-- Scalar extension restricted through the full Dctf inclusions. Source: blueprint step 1.
(blueprint: lem-coef-finite-closed-shriek). -/
def S {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) (X : Space k) : Dctf A X ⥤ Dctf B X :=
  (ctf B X).lift ((ctf A X).ι ⋙ scalar φ X) (scalar_preserves φ X)

/-- Closed direct image restricted through the full Dctf inclusions. Source: step 1.
(blueprint: lem-coef-finite-closed-shriek). -/
def F {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {X Y : Space k} (f : Map X Y) [IsClosedImmersion f.hom] : Dctf A X ⥤ Dctf A Y :=
  (ctf A Y).lift ((ctf A X).ι ⋙ push A f) (push_preserves A f)

/-- Open restriction on Dctf. Source: blueprint step 5.
(blueprint: lem-coef-finite-closed-shriek). -/
def J {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {X Y : Space k} (f : Map X Y) [IsOpenImmersion f.hom] : Dctf A Y ⥤ Dctf A X :=
  (ctf A X).lift ((ctf A Y).ι ⋙ pull A f) (pull_preserves A f)

/-- Composition of the actual coefficient maps. Source: blueprint coefficient-chain clause.
Proof: postcomposition by the composite ring homomorphism is successive postcomposition;
the two canonical Shrink ring equivalences cancel.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem coefficientMap_comp {ell : ℕ} {A B C : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) (ψ : B.carrier →+* C.carrier) :
    coefficientMap φ ≫ coefficientMap ψ = coefficientMap (ψ.comp φ) := by
  have hs : (smallMap ψ).comp (smallMap φ) = smallMap (ψ.comp φ) := by
    ext a
    simp [smallMap]
  unfold coefficientMap Profinite.continuousMapRingObjMapOfUniverse
  rw [← Functor.map_comp, ← Profinite.continuousMapRingSheafMapOfUniverse_comp]
  simp only [hs]

/-- Canonical derived-tensor reassociation, via the restriction-of-scalars compositor.
Source: det-sp-scalar-extension-functor, associativity clause.
(blueprint: lem-coef-finite-closed-shriek). -/
def scalarComp {ell : ℕ} {k : Type u} [Field k] {A B C : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) (ψ : B.carrier →+* C.carrier) (X : Space k) :
    S φ X ⋙ S ψ X ≅ S (ψ.comp φ) X :=
  ((ctf C X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ctf A X).ι
      (Mod.derivedExtendScalarsCompIso
        (ProEtale.coefficientMap (coefficientMap φ) X.scheme)
        (ProEtale.coefficientMap (coefficientMap ψ) X.scheme)
        (ProEtale.coefficientMap (coefficientMap (ψ.comp φ)) X.scheme)
        (by rw [← ProEtale.coefficientMap_comp, coefficientMap_comp])).symm)

/-- The canonical direct-image coefficient comparison on Dctf.
Source: blueprint step 2; fullness changes no arrow.
(blueprint: lem-coef-finite-closed-shriek). -/
def c {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) {X Y : Space k} (f : Map X Y)
    [IsClosedImmersion f.hom] (M : Dctf A X) :
    (S φ Y).obj ((F A f).obj M) ⟶ (F B f).obj ((S φ X).obj M) :=
  ObjectProperty.homMk (directMap φ f M.obj)

/-- The closed coefficient comparison is invertible on its justified finite-Tor domain.
Source: blueprint step 2, det-prop-scalar-six-direct-image.
Proof: the closed projection formula identifies the mate with tensor by the constant B
complex. Closed direct image is exact, so this projection comparison is invertible.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem c_isIso {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) {X Y : Space k} (f : Map X Y)
    [IsClosedImmersion f.hom] (M : Dctf A X) : IsIso (c φ f M) := by
  sorry

section Supplied
variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hk : Finite k ∨ IsAlgClosed k)

/-- Proper compact support agrees with direct image through the specified map.
Source: blueprint step 1 and sk-prop-sf-comp-coherence at i = i ∘ id.
Proof: compare the chosen compactification with (id,i) by normalized compactification
coherence. Its identity-open unit is the identity, and its proper factor is i. The
adjunction transpose defining lowerComparison is exactly this normalized comparison.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem lowerComparison_isIso (A : Coefficient.{u} ell) {X Y : Space k} (f : Map X Y)
    [IsClosedImmersion f.hom] : IsIso (lowerComparison ell k hk A f) := by
  sorry

/-- The actual supplied counit after the specified left-functor transport.
Source: blueprint step 1 and the statement's exceptional counit.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev counit (A : Coefficient.{u} ell) {X Y : Space k} (f : Map X Y)
    [IsClosedImmersion f.hom] := (adjunction ell k hk A f).counit

/-- The comparison is the specified right mate, by the supplied adjunction's homEquiv.
Source: blueprint step 3; no existence choice or zero branch is used.
(blueprint: lem-coef-finite-closed-shriek). -/
def b {A B : Coefficient.{u} ell} (φ : A.carrier →+* B.carrier)
    {X Y : Space k} (f : Map X Y) [IsClosedImmersion f.hom] (M : Dctf A Y) :
    (S φ X).obj ((U ell k hk A f).obj M) ⟶ (U ell k hk B f).obj ((S φ Y).obj M) :=
  letI := c_isIso φ f ((U ell k hk A f).obj M)
  (adjunction ell k hk B f).homEquiv _ _
    (inv (c φ f ((U ell k hk A f).obj M)) ≫ (S φ Y).map ((counit ell k hk A f).app M))


/-- Direct-image composition restricted through the full Dctf inclusions.
Source: lem-weil-derived-direct-image-composition and the composition clause of the item.
(blueprint: lem-coef-finite-closed-shriek). -/
def pushComp (A : Coefficient.{u} ell) {W Z X : Space k}
    (t : Map W Z) (i : Map Z X) [IsClosedImmersion t.hom] [IsClosedImmersion i.hom] :
    F A t ⋙ F A i ≅ F A (t.comp i) :=
  ((ctf A X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ctf A W).ι
      (ProEtale.CondensedRing.rightDerivedLowerStarComp (coeff A) t.hom i.hom))

/-- The specified exceptional composition isomorphism is the unique right-adjoint
comparison whose counit is the pasted counit under the recorded direct-image compositor.
It is constructed by `rightAdjointUniq`, not selected from an existence assertion.
Source: blueprint proof step 4, composition clause.
(blueprint: lem-coef-finite-closed-shriek). -/
def exceptionalComp (A : Coefficient.{u} ell) {W Z X : Space k}
    (t : Map W Z) (i : Map Z X) [IsClosedImmersion t.hom] [IsClosedImmersion i.hom] :
    U ell k hk A i ⋙ U ell k hk A t ≅ U ell k hk A (t.comp i) :=
  Adjunction.rightAdjointUniq
    (((adjunction ell k hk A t).comp (adjunction ell k hk A i)).ofNatIsoLeft
      (pushComp ell k A t i))
    (adjunction ell k hk A (t.comp i))

end Supplied

/-- Open extension by zero in the same condensed module category.
Source: the locally closed clause and prop-exc-open-adjoint.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev openPush {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {V X : Space k} (j : Map V X) [IsOpenImmersion j.hom] : Ambient A V ⥤ Ambient A X :=
  (ProEtale.CondensedRing.openImmersionLowerShriek (coeff A) j.hom).mapDerivedCategory

/-- Open extension by zero preserves finite constant models and finite Tor amplitude.
Source: blueprint proof step 5, lem-cbc-extension-zero-projection-formula.
Proof: extend the finite locally closed stratification by the complementary closed stratum;
extension by zero is exact, and tensor commutes with it by the open projection formula.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem openPush_preserves {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {V X : Space k} (j : Map V X) [IsOpenImmersion j.hom] (M : Dctf A V) :
    ctf A X ((openPush A j).obj M.obj) := by
  sorry

/-- Extension by zero restricted through the full Dctf inclusion. Source: step 5.
(blueprint: lem-coef-finite-closed-shriek). -/
def O {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {V X : Space k} (j : Map V X) [IsOpenImmersion j.hom] : Dctf A V ⥤ Dctf A X :=
  (ctf A X).lift ((ctf A V).ι ⋙ openPush A j) (openPush_preserves A j)

/-- The actual open adjunction restricted to Dctf; no adjunction is assumed as data.
Source: blueprint proof step 5, prop-exc-open-adjoint.
(blueprint: lem-coef-finite-closed-shriek). -/
def openAdjunction {ell : ℕ} {k : Type u} [Field k] (A : Coefficient.{u} ell)
    {V X : Space k} (j : Map V X) [IsOpenImmersion j.hom] : O A j ⊣ J A j :=
  let a := (ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (coeff A) j.hom).ofNatIsoRight
      (ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (coeff A) j.hom).symm
  a.restrictFullyFaithful (ctf A V).fullyFaithfulι (ctf A X).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- The specified open-restriction/tensor identification, on the same full subcategories.
Source: blueprint proof step 5, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
(blueprint: lem-coef-finite-closed-shriek). -/
def r {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) {V X : Space k} (j : Map V X)
    [IsOpenImmersion j.hom] : J A j ⋙ S φ V ≅ S φ X ⋙ J B j :=
  ((ctf B V).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ctf A X).ι (scalarPullIso φ j))

/-- The left mate of open restriction/tensor interchange. Its inverse is the
extension-by-zero coefficient comparison, with its normalization fixed by both open units.
Source: blueprint step 5 and lem-cbc-extension-zero-projection-formula.
(blueprint: lem-coef-finite-closed-shriek). -/
def qInv {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) {V X : Space k} (j : Map V X)
    [IsOpenImmersion j.hom] (P : Dctf A V) :
    (O B j).obj ((S φ V).obj P) ⟶ (S φ X).obj ((O A j).obj P) :=
  ((openAdjunction B j).homEquiv _ _).symm
    ((S φ V).map ((openAdjunction A j).unit.app P) ≫
      (r φ j).hom.app ((O A j).obj P))

/-- This specified mate is invertible, including non-flat coefficient maps.
Source: blueprint step 5, extension-zero projection formula.
Proof: restrict to the open, where both units identify the map with the identity on the
same balanced tensor; on the complement both objects vanish. These restrictions are jointly
conservative, so the actual normalized mate is an isomorphism.
(blueprint: lem-coef-finite-closed-shriek). -/
theorem qInv_isIso {ell : ℕ} {k : Type u} [Field k] {A B : Coefficient.{u} ell}
    (φ : A.carrier →+* B.carrier) {V X : Space k} (j : Map V X)
    [IsOpenImmersion j.hom] (P : Dctf A V) : IsIso (qInv φ j P) := by
  sorry

section LocallyClosed
variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hk : Finite k ∨ IsAlgClosed k)

/-- Rh^!=Rk^!j^* for the chosen closed/open factorization, using the supplied Rk^!.
Source: blueprint locally closed clause.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev UH (A : Coefficient.{u} ell) {W V X : Space k}
    (i : Map W V) (j : Map V X) [IsClosedImmersion i.hom] [IsOpenImmersion j.hom] :=
  J A j ⋙ U ell k hk A i

/-- Rh_!=j_!k_* for the chosen factorization. Source: blueprint locally closed clause.
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev FH (A : Coefficient.{u} ell) {W V X : Space k}
    (i : Map W V) (j : Map V X) [IsClosedImmersion i.hom] [IsOpenImmersion j.hom] :=
  F A i ⋙ O A j

/-- The chained adjunction fixes the locally closed counit.
Source: blueprint step 5, epsilon_j after j_!(epsilon_i).
(blueprint: lem-coef-finite-closed-shriek). -/
def adjunctionH (A : Coefficient.{u} ell) {W V X : Space k}
    (i : Map W V) (j : Map V X) [IsClosedImmersion i.hom] [IsOpenImmersion j.hom] :
    FH ell k A i j ⊣ UH ell k hk A i j :=
  (adjunction ell k hk A i).comp (openAdjunction A j)

/-- Locally closed comparison: the closed mate followed by the supplied exceptional
image of the open tensor comparison. Source: blueprint step 5.
(blueprint: lem-coef-finite-closed-shriek). -/
def bH {A B : Coefficient.{u} ell} (φ : A.carrier →+* B.carrier) {W V X : Space k}
    (i : Map W V) (j : Map V X) [IsClosedImmersion i.hom] [IsOpenImmersion j.hom]
    (M : Dctf A X) :
    (S φ W).obj ((UH ell k hk A i j).obj M) ⟶
      (UH ell k hk B i j).obj ((S φ X).obj M) :=
  b ell k hk φ i ((J A j).obj M) ≫ (U ell k hk B i).map ((r φ j).hom.app M)

/-- The inverse compact-support coefficient comparison for the chosen factorization.
The closed inverse and open mate are actual maps on their established domains.
Source: blueprint step 5, pasting the two counit equations.
(blueprint: lem-coef-finite-closed-shriek). -/
def cHInv {A B : Coefficient.{u} ell} (φ : A.carrier →+* B.carrier) {W V X : Space k}
    (i : Map W V) (j : Map V X) [IsClosedImmersion i.hom] [IsOpenImmersion j.hom]
    (N : Dctf A W) :
    (FH ell k B i j).obj ((S φ W).obj N) ⟶
      (S φ X).obj ((FH ell k A i j).obj N) :=
  letI := c_isIso φ i N
  (O B j).map (inv (c φ i N)) ≫ qInv φ j ((F A i).obj N)

end LocallyClosed

/-- Finite coefficient change for the supplied closed exceptional inverse image, with its
counit, naturality, closed composition, coefficient chains, and every corresponding
compatibility for a chosen locally closed factorization.

`Coefficient` bundles exactly finite commutative ell-primary rings, `Space` bundles exactly
separated finite-type k-schemes, and `Dctf` is the recorded ConstantModel finite-Tor full
subcategory. Thus the domain clauses are also part of the types of both sides of b.
The characteristic hypotheses say that p=ringChar k is prime and p is different from ell.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-finite-closed-shriek.md and its proof; current DAG proof steps 1--5
(blueprint: lem-coef-finite-closed-shriek).

Proof:
1. Independently obtain all finite-Tor domains from scalar preservation and the recorded
supplied exceptional preservation theorem. The formal closed-support triangle identifies
its support object with the supplied right adjoint by the counit-compatible universal Hom
bijection on the localizing category. For closed i, compactification coherence identifies
its lower shriek with the recorded direct image through lowerComparison.
2. Tensor the support triangle by B. Closed direct image and open restriction commute with
tensor; the open direct-image coefficient comparison identifies its third term with
Rj_*j^*(M_B), compatibly with the unit. The first arrow is therefore exactly the scalar
extension of the supplied counit after c_i inverse.
3. Transpose that arrow through the supplied B adjunction. Hom exactness of the support
triangle and full faithfulness of closed direct image show that composition with b induces
a bijection on Hom from every Dctf test object. Testing its source and target gives inverse
maps, hence b is invertible. This also gives its displayed counit equation.
4. Transpose the naturality, closed-composition, and coefficient-chain paths. Naturality
of c, its direct-image compositor, and ordinary tensor reassociation make their transposes
equal to the same scalar-extended pasted counit. Injectivity gives every equality.
5. Restrict M to the chosen open, apply the closed result and then r. Chain the supplied
closed adjunction with the actual open adjunction. The open projection formula makes
qInv invertible. Pasting its counit equation with the closed one gives the locally closed
counit, naturality, coefficient-chain and composition statements. -/
theorem generalFiniteCoefficientClosedShriek
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (A B : Coefficient.{u} ell) (φ : A.carrier →+* B.carrier)
    {Z X : Space k} (i : Map Z X) [IsClosedImmersion i.hom] (M : Dctf A X) :
    let MB := (S φ X).obj M
    let NA := (U ell k hk A i).obj M
    let bᵢ := b ell k hk φ i M
    letI := c_isIso φ i NA
    ctf B Z ((S φ Z).obj NA).obj ∧
    ctf B Z ((U ell k hk B i).obj MB).obj ∧
    IsIso (c φ i NA) ∧ IsIso bᵢ ∧
    bᵢ = (adjunction ell k hk B i).homEquiv _ _
      (inv (c φ i NA) ≫ (S φ X).map ((counit ell k hk A i).app M)) ∧
    (F B i).map bᵢ ≫ (counit ell k hk B i).app MB =
      inv (c φ i NA) ≫ (S φ X).map ((counit ell k hk A i).app M) ∧
    (∀ (N : Dctf A X) (f : M ⟶ N),
      (S φ Z).map ((U ell k hk A i).map f) ≫ b ell k hk φ i N =
        bᵢ ≫ (U ell k hk B i).map ((S φ X).map f)) ∧
    (∀ (W : Space k) (t : Map W Z) [IsClosedImmersion t.hom],
      (S φ W).map ((exceptionalComp ell k hk A t i).hom.app M) ≫
          b ell k hk φ (t.comp i) M =
        b ell k hk φ t NA ≫ (U ell k hk B t).map bᵢ ≫
          (exceptionalComp ell k hk B t i).hom.app MB) ∧
    (∀ (C : Coefficient.{u} ell) (ψ : B.carrier →+* C.carrier),
      (S ψ Z).map bᵢ ≫ b ell k hk ψ i MB ≫
          (U ell k hk C i).map ((scalarComp φ ψ X).hom.app M) =
        (scalarComp φ ψ Z).hom.app NA ≫ b ell k hk (ψ.comp φ) i M) ∧
    (∀ (V W : Space k) (j : Map V X) [IsOpenImmersion j.hom]
      (t : Map W V) [IsClosedImmersion t.hom],
      let NH := (UH ell k hk A t j).obj M
      let bₕ := bH ell k hk φ t j M
      ctf B W ((S φ W).obj NH).obj ∧
      ctf B W ((UH ell k hk B t j).obj MB).obj ∧
      IsIso bₕ ∧ IsIso (cHInv ell k φ t j NH) ∧
      bₕ = (adjunctionH ell k hk B t j).homEquiv _ _
        (cHInv ell k φ t j NH ≫
          (S φ X).map ((adjunctionH ell k hk A t j).counit.app M)) ∧
      (FH ell k B t j).map bₕ ≫ (adjunctionH ell k hk B t j).counit.app MB =
        cHInv ell k φ t j NH ≫
          (S φ X).map ((adjunctionH ell k hk A t j).counit.app M) ∧
      (∀ (N : Dctf A X) (f : M ⟶ N),
        (S φ W).map ((UH ell k hk A t j).map f) ≫ bH ell k hk φ t j N =
          bₕ ≫ (UH ell k hk B t j).map ((S φ X).map f)) ∧
      (∀ (C : Coefficient.{u} ell) (ψ : B.carrier →+* C.carrier),
        (S ψ W).map bₕ ≫ bH ell k hk ψ t j MB ≫
            (UH ell k hk C t j).map ((scalarComp φ ψ X).hom.app M) =
          (scalarComp φ ψ W).hom.app NH ≫ bH ell k hk (ψ.comp φ) t j M) ∧
      (∀ (T : Space k) (s : Map T W) [IsClosedImmersion s.hom],
        (S φ T).map ((exceptionalComp ell k hk A s t).hom.app ((J A j).obj M)) ≫
            bH ell k hk φ (s.comp t) j M =
          b ell k hk φ s NH ≫ (U ell k hk B s).map bₕ ≫
            (exceptionalComp ell k hk B s t).hom.app ((J B j).obj MB))) := by
  sorry

end WeilConjectures.FiniteClosed

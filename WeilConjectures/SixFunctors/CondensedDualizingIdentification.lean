/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.DeligneLaumon.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement

/-! # The native dualizing object and coefficient change

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
prop-functor-package.md, clause (7), and its proof's final exceptional-adjunction
paragraph; thm-pur-finite-reduction-of-purity.proof.md, Step 2.
(blueprint: lem-sf-rational-dualizing-identification).

The dualizing object is the native constructible exceptional value at the regular
coefficient module in degree zero. Its comparison is the existing exceptional mate,
followed by exceptional inverse image of the canonical scalar-unit isomorphism.
All categories, tensors and internal Homs are ordinary condensed module derived ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite-field closure has prime characteristic, transported along its actual
algebra map. Source: def-sf-setting, finite-field convention
(blueprint: lem-sf-rational-dualizing-identification). -/
instance nativeDualizingCharPrime (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Fact (ringChar D.k).Prime :=
  ⟨(Algebra.ringChar_eq D.k₀ D.k) ▸ CharP.char_is_prime D.k₀ (ringChar D.k₀)⟩

/-- Algebraic closedness is a field of the specified algebraic-closure datum.
Source: def-sf-setting, fixed algebraic closure
(blueprint: lem-sf-rational-dualizing-identification). -/
instance nativeDualizingAlgClosed (D : WeilConjectures.FiniteFieldDatum.{u}) :
    IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The point's identity structure map is locally of finite type.
Source: prop-functor-package (7), structure target
(blueprint: lem-sf-rational-dualizing-identification). -/
instance nativeDualizingPointLft (k : Type u) [Field k] :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

/-- The point's identity structure map is quasi-compact.
Source: prop-functor-package (7), structure target
(blueprint: lem-sf-rational-dualizing-identification). -/
instance nativeDualizingPointQc (k : Type u) [Field k] :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

/-- The point's identity structure map is separated.
Source: prop-functor-package (7), structure target
(blueprint: lem-sf-rational-dualizing-identification). -/
instance nativeDualizingPointSeparated (k : Type u) [Field k] :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

/-- The existing derived tensor unit bundled in the full finite-Tor constructible
subcategory. Its membership is the existing coefficient-unit theorem, not an assumption.
Source: prop-functor-package (7), coefficient unit; proof step 1 of the node
(blueprint: lem-sf-rational-dualizing-identification). -/
def nativeDualizingUnit (Λ : ScalarSixRing.{u}) (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] : ConstantModelConstructibleFiniteTor Λ.X S :=
  ⟨𝟙_ (DerivedCategory (ModuleRingedComparison.internalModules Λ.X S)),
    condensedCoefficientUnit_mem Λ.X S⟩

variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  [Fact (ringChar D.k ≠ ell)]

/-- The native dualizing object, literally the restricted localizing right adjoint
at the coefficient unit. Finite base cohomological dimension is deduced from algebraic
closedness. Source: prop-functor-package (7), omega_X = Ra_X^! Lambda
(blueprint: lem-sf-rational-dualizing-identification). -/
def nativeDualizingObject (Λ : ScalarSixRing.{u})
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    ConstantModelConstructibleFiniteTor Λ.X X.left :=
  (ctfExceptionalInverseImage Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
    (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k)))) hΛ).obj
      (nativeDualizingUnit Λ (Spec (.of D.k)))

/-- Scalar extension of the regular coefficient unit, with its canonical monoidal
normalization. Source: scalar-six tensor comparison, unit isomorphism
(blueprint: lem-sf-rational-dualizing-identification). -/
def nativeDualizingUnitChange {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : ListedCoefficientMap ell a) :
    (scalarExceptionalChange ell D.k a ha (Over.mk (𝟙 (Spec (.of D.k))))).obj
        (nativeDualizingUnit Λ (Spec (.of D.k))) ≅
      nativeDualizingUnit Λ' (Spec (.of D.k)) :=
  ObjectProperty.isoMk _ (Functor.Monoidal.εIso (scalarSixChange a (Spec (.of D.k)))).symm

/-- The specified rho: exceptional mate at the coefficient unit, followed by the
exceptional image of the scalar-unit identification. Thus its transpose is inverse
compact-support comparison followed by scalar extension of the exceptional counit.
Source: prop-functor-package (7), scalar-six exceptional displayed transpose
(blueprint: lem-sf-rational-dualizing-identification). -/
def nativeDualizingComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : ListedCoefficientMap ell a) (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (scalarExceptionalChange ell D.k a ha X).obj
        (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X) ⟶
      nativeDualizingObject ell D Λ' (listedCoefficientCtf ell a ha).2.1 X :=
  (scalarSixCtfExceptionalComparison ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
      a ha (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))).app
        (nativeDualizingUnit Λ (Spec (.of D.k))) ≫
    (ctfExceptionalInverseImage Λ'.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
      (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))
      (listedCoefficientCtf ell a ha).2.1).map (nativeDualizingUnitChange ell D a ha).hom

/-- Combining the canonical internal-Hom scalar comparison with rho in the second
argument. Source: prop-functor-package (7) and scalar-six tensor-Hom comparison (2)
(blueprint: lem-sf-rational-dualizing-identification). -/
def nativeDualizingHomComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : ListedCoefficientMap ell a) (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (scalarSixChange a X.left).obj
        (((derivedHom Λ.X X.left).obj (.op K.obj)).obj
          (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X).obj) ⟶
      ((derivedHom Λ'.X X.left).obj (.op ((scalarSixChange a X.left).obj K.obj))).obj
        (nativeDualizingObject ell D Λ' (listedCoefficientCtf ell a ha).2.1 X).obj :=
  scalarSixHomComparison a X.left K.obj
      (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X).obj ≫
    (ihom ((scalarSixChange a X.left).obj K.obj)).map
      (nativeDualizingComparison ell D a ha X).hom

attribute [local irreducible] ctfLowerShriek ctfExceptionalInverseImage
  ctfExceptionalAdjunction scalarSixCtfExceptionalComparison scalarSixCtfShriekComparison
  scalarSixChange scalarSixTower scalarChangeUnit

set_option maxHeartbeats 2000000 in
-- Matching the restricted exceptional adjunction expands large derived-category instances.
/-- The native structure exceptional value is constructible of finite Tor amplitude,
and rho is an isomorphism with precisely the displayed exceptional-counit transpose.
This includes O_E to E and all finite reductions A_{E,n} to A_{E,m}; derived scalar
extension is used throughout, without flatness.
Source: prop-functor-package (7), final proof paragraph, and finite-reduction-of-purity,
Step 2 (blueprint: lem-sf-rational-dualizing-identification).

Proof: The coefficient unit is rank one, bounded constructible and of Tor amplitude
[0,0]. The base has cd_ell = 0. The restricted localizing right adjoint therefore gives
the displayed finite-Tor constructible object. Apply scalar-six exceptional comparison
at a_X and this unit; its mate is invertible. Compose with exceptional inverse image
of the canonical scalar-unit isomorphism. The mate counit equation and naturality of
the target counit give the displayed transpose equation. This is exactly the same
argument for localization O_E to E and for a nonflat finite quotient. -/
theorem nativeDualizing_identification {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : ListedCoefficientMap ell a) (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    IsIso (nativeDualizingComparison ell D a ha X) ∧
    (ctfLowerShriek Λ'.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
        (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))
        (listedCoefficientCtf ell a ha).2.1).map (nativeDualizingComparison ell D a ha X) ≫
      (ctfExceptionalAdjunction Λ'.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
        (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))
        (listedCoefficientCtf ell a ha).2.1).counit.app
          (nativeDualizingUnit Λ' (Spec (.of D.k))) =
      (scalarSixCtfShriekComparison ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
        a ha (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))).inv.app
          (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X) ≫
        (scalarExceptionalChange ell D.k a ha (Over.mk (𝟙 (Spec (.of D.k))))).map
          ((ctfExceptionalAdjunction Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
            (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))
            (listedCoefficientCtf ell a ha).1).counit.app
              (nativeDualizingUnit Λ (Spec (.of D.k)))) ≫
          (nativeDualizingUnitChange ell D a ha).hom := by
  have hβ := (scalarSixCoefficientComparison ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) a ha).2.1 X
    (Over.mk (𝟙 (Spec (.of D.k))))
    (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))
  have := hβ.2.2 (nativeDualizingUnit Λ (Spec (.of D.k)))
  constructor
  · dsimp only [nativeDualizingComparison]
    infer_instance
  · have h := (scalarSixCoefficientAdjunctionCoherence ell D.k
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k) a ha
      (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))).2.2.1
        (nativeDualizingUnit Λ (Spec (.of D.k)))
    have hn := (ctfExceptionalAdjunction Λ'.X ell D.k
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k)
      (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))
      (listedCoefficientCtf ell a ha).2.1).counit.naturality
        (nativeDualizingUnitChange ell D a ha).hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    dsimp only [nativeDualizingComparison, nativeDualizingObject]
    rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, h, Category.assoc]

/-- Rho for the identity is the identity after the canonical scalar unitor.
Source: prop-functor-package (7), scalar-six identity coherence
(blueprint: lem-sf-rational-dualizing-identification).

Proof: Specialize scalar-six identity coherence for the exceptional mate to the
coefficient unit. The scalar unitor on that unit is the canonical monoidal unit
identification. Its exceptional image is precisely the final factor defining rho. -/
theorem nativeDualizing_identity (Λ : ScalarSixRing.{u})
    (ha : ListedCoefficientMap ell (𝟙 Λ)) (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (nativeDualizingComparison ell D (𝟙 Λ) ha X).hom =
      (scalarChangeUnit Λ X.left).hom.app
        (nativeDualizingObject ell D Λ (listedCoefficientCtf ell (𝟙 Λ) ha).1 X).obj := by
  let f : X ⟶ Over.mk (𝟙 (Spec (.of D.k))) := Over.homMk X.hom
  have hm := (scalarSixCoefficientIdentityCoherence ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) Λ ha f).2.2.2.2
      (Over.mk (𝟙 (Spec (.of D.k))))
  have : NatTrans.IsMonoidal (scalarChangeUnit Λ (Spec (.of D.k))).hom := hm.1
  have hu : (nativeDualizingUnitChange ell D (𝟙 Λ) ha).hom =
      (scalarSixCtfUnit ell D.k Λ ha (Over.mk (𝟙 (Spec (.of D.k))))).hom.app
        (nativeDualizingUnit Λ (Spec (.of D.k))) := by
    apply ObjectProperty.hom_ext
    change (Functor.Monoidal.εIso (scalarSixChange (𝟙 Λ) (Spec (.of D.k)))).inv =
      (scalarChangeUnit Λ (Spec (.of D.k))).hom.app _
    apply (cancel_epi (Functor.Monoidal.εIso
      (scalarSixChange (𝟙 Λ) (Spec (.of D.k)))).hom).1
    simpa only [Functor.Monoidal.εIso_hom, Functor.Monoidal.εIso_inv,
      Functor.Monoidal.ε_η, Functor.LaxMonoidal.id_ε] using
      (NatTrans.IsMonoidal.unit (τ := (scalarChangeUnit Λ (Spec (.of D.k))).hom)).symm
  have h := (scalarSixCoefficientIdentityCoherence ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) Λ ha f).2.2.2.1
      (nativeDualizingUnit Λ (Spec (.of D.k)))
  dsimp only [nativeDualizingComparison]
  rw [hu]
  exact congrArg (fun g ↦ g.hom) h

set_option maxHeartbeats 2000000 in
-- The coefficient tower and its restricted functors share large derived-category instances.
/-- Rho respects coefficient composition under the canonical derived scalar associator.
Source: prop-functor-package (7), scalar-six coefficient composition
(blueprint: lem-sf-rational-dualizing-identification).

Proof: Specialize scalar-six tower coherence for the exceptional mate at the unit.
Naturality moves the scalar-unit identifications past the second mate; monoidality
of the scalar tower identifies their composite with its unit component. -/
theorem nativeDualizing_composition {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    (ha : ListedCoefficientMap ell a) (hb : ListedCoefficientMap ell b)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (scalarSixTower a b X.left).hom.app
        (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X).obj ≫
      (nativeDualizingComparison ell D (a ≫ b) (.comp a b ha hb) X).hom =
    (scalarSixChange b X.left).map (nativeDualizingComparison ell D a ha X).hom ≫
      (nativeDualizingComparison ell D b hb X).hom := by
  let Y := Over.mk (𝟙 (Spec (.of D.k)))
  let f : X ⟶ Y := Over.homMk X.hom
  let U := nativeDualizingUnit Λ (Spec (.of D.k))
  have ht := scalarSixCoefficientTowerCoherence ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) a b ha hb f
  have : NatTrans.IsMonoidal (scalarSixTower a b (Spec (.of D.k))).hom :=
    (ht.2.2.2.2 Y).1
  have hu : (scalarSixCtfTower ell D.k a b ha hb Y).hom.app U ≫
      (nativeDualizingUnitChange ell D (a ≫ b) (.comp a b ha hb)).hom =
      (scalarExceptionalChange ell D.k b hb Y).map
        (nativeDualizingUnitChange ell D a ha).hom ≫
          (nativeDualizingUnitChange ell D b hb).hom := by
    apply ObjectProperty.hom_ext
    change (scalarSixTower a b (Spec (.of D.k))).hom.app _ ≫
      (Functor.Monoidal.εIso (scalarSixChange (a ≫ b) (Spec (.of D.k)))).inv =
      (scalarSixChange b (Spec (.of D.k))).map
        (Functor.Monoidal.εIso (scalarSixChange a (Spec (.of D.k)))).inv ≫
      (Functor.Monoidal.εIso (scalarSixChange b (Spec (.of D.k)))).inv
    apply (cancel_epi (Functor.LaxMonoidal.ε
      (scalarSixChange a (Spec (.of D.k)) ⋙ scalarSixChange b (Spec (.of D.k))))).1
    rw [← Category.assoc, NatTrans.IsMonoidal.unit]
    simp only [Functor.LaxMonoidal.comp_ε, Functor.Monoidal.εIso_inv,
      Category.assoc, Functor.Monoidal.ε_η, Functor.Monoidal.map_ε_η_assoc]
  have hc := ht.2.2.2.1 U
  have hn := (scalarSixCtfExceptionalComparison ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) b hb f).naturality
      (nativeDualizingUnitChange ell D a ha).hom
  have hfull : (scalarSixCtfTower ell D.k a b ha hb X).hom.app
      (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X) ≫
        nativeDualizingComparison ell D (a ≫ b) (.comp a b ha hb) X =
      (scalarExceptionalChange ell D.k b hb X).map
        (nativeDualizingComparison ell D a ha X) ≫
          nativeDualizingComparison ell D b hb X := by
    dsimp only [nativeDualizingComparison, nativeDualizingObject]
    dsimp only [f, Y, U] at hc hn hu
    simp only [Functor.comp_map] at hn
    rw [← Category.assoc, hc]
    simp only [Category.assoc, Functor.map_comp]
    rw [← Functor.map_comp, hu, Functor.map_comp]
    rw [← reassoc_of% hn]
  exact congrArg (fun g ↦ g.hom) hfull

set_option maxHeartbeats 2000000 in
-- Evaluation matches both the derived tensor structure and the restricted exceptional value.
/-- The internal-Hom comparison with the dualizing object is invertible and carries
scalar-extended evaluation to evaluation over the target coefficient ring.
Source: prop-functor-package (7), scalar-six tensor-Hom (2), evaluation transpose
(blueprint: lem-sf-rational-dualizing-identification).

Proof: Both K and the native dualizing object belong to Dctf. Apply scalar-six
internal-Hom comparison there and compose its second argument with the invertible
rho. For the equation, uncurry the defining evaluation mate, then use naturality
of evaluation in its second argument. The result is scalar-extended evaluation
followed by rho; the tensor comparison is the inverse monoidal tensorator. -/
theorem nativeDualizing_hom_evaluation {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : ListedCoefficientMap ell a) (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    IsIso (nativeDualizingHomComparison ell D a ha X K) ∧
    ((scalarSixChange a X.left).obj K.obj ◁ nativeDualizingHomComparison ell D a ha X K) ≫
        (ihom.ev ((scalarSixChange a X.left).obj K.obj)).app
          (nativeDualizingObject ell D Λ' (listedCoefficientCtf ell a ha).2.1 X).obj =
      (scalarSixTensorIso a X.left K.obj
        (((derivedHom Λ.X X.left).obj (.op K.obj)).obj
          (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X).obj)).inv ≫
        (scalarSixChange a X.left).map ((ihom.ev K.obj).app
          (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X).obj) ≫
            (nativeDualizingComparison ell D a ha X).hom := by
  have hρ := (nativeDualizing_identification ell D a ha X).1
  have hρ' : IsIso (nativeDualizingComparison ell D a ha X).hom := by
    infer_instance
  have hH := (scalarSixCoefficientComparison ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) a ha).2.2 X K
      (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X)
  have := hH.2
  constructor
  · dsimp only [nativeDualizingHomComparison]
    infer_instance
  · have h := ((scalarSixCoefficientAdjunctionCoherence ell D.k
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k) a ha
      (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of D.k))))).2.2.2.2 X K
        (nativeDualizingObject ell D Λ (listedCoefficientCtf ell a ha).1 X)).1
    dsimp only [nativeDualizingHomComparison]
    rw [whiskerLeft_comp, Category.assoc, ihom.ev_naturality, ← Category.assoc, h,
      Category.assoc]
    rfl

end AlgebraicGeometry.ProEtale.CondensedRing

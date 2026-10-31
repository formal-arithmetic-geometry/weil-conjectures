/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Functoriality of condensed lisse geometric fibres

Source: current blueprint, `sec-purity-real-sheaves/sk-d-real-weil/_section.md`,
finite-reduction paragraph and complement; `sk-d-real-weil.proof.md`, second paragraph
(blueprint: lem-real-condensed-fibre-functoriality).

The comparison for inverse image is constructed from module pullback composition.
The statement below packages the simultaneous path maps on the three recorded coefficient
rings, their finite-quotient normalization, exactness, and tensor/scalar compatibilities.
Loop actions mean evaluation of this same normalized path family on automorphisms of the
finite-etale fibre functor. Thus no separate, arbitrarily chosen representation is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RealCondensedFibre

/-- The schemes allowed in the statement, including the local-ring meaning of normality.
Source: the hypotheses (blueprint: lem-real-condensed-fibre-functoriality). -/
structure Context where
  X : Scheme.{u}
  nonempty : Nonempty X
  connected : ConnectedSpace X
  locallyNoetherian : IsLocallyNoetherian X
  compact : CompactSpace X
  normal : ∀ p : X, IsDomain (X.presheaf.stalk p) ∧ IsIntegrallyClosed (X.presheaf.stalk p)

attribute [instance] Context.nonempty Context.connected Context.locallyNoetherian Context.compact

/-- Indices for the existing integral, rational and finite-subextension-valued coefficients.
Source: coefficient convention (blueprint: lem-real-condensed-fibre-functoriality). -/
inductive Coefficient (ell : ℕ) [Fact ell.Prime]
  | integral (E : PadicAlgCl.FiniteIntermediateField ell)
  | rational (E : PadicAlgCl.FiniteIntermediateField ell)
  | algebraic

variable (ell : ℕ) [Fact ell.Prime]

/-- These are precisely the dependency's coefficient objects, without a new coefficient model.
Source: thm-lisse-qlbar-representations (blueprint: lem-real-condensed-fibre-functoriality). -/
abbrev Coefficient.ring (c : Coefficient ell) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  match c with
  | .integral E => LisseQlbar.integerRing ell E
  | .rational E => LisseQlbar.fieldRing ell E
  | .algebraic => Profinite.padicAlgClRingObj ell

/-- The existing coefficient multiplication, by cases on its index.
Source: coefficient convention (blueprint: lem-real-condensed-fibre-functoriality). -/
instance coefficientMonObj (c : Coefficient ell) : MonObj (c.ring ell) := by
  cases c <;> dsimp [Coefficient.ring] <;> infer_instance

/-- The existing commutativity instance, by cases on the coefficient index.
Source: coefficient convention (blueprint: lem-real-condensed-fibre-functoriality). -/
instance coefficientCommMonObj (c : Coefficient ell) : IsCommMonObj (c.ring ell) := by
  cases c <;> dsimp [Coefficient.ring] <;> infer_instance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing internal module category over the pulled-back coefficient.
Source: thm-lisse-qlbar-representations (blueprint: lem-real-condensed-fibre-functoriality). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- Its lisse predicate is the dependency's locally-free predicate.
Source: thm-lisse-qlbar-representations (blueprint: lem-real-condensed-fibre-functoriality). -/
abbrev Lisse {X : Scheme.{u}} (L : Modules Λ X) :=
  CondensedRing.LocallyFree (condensedRingObj Λ X) L

/-- The actual scalar ring at the geometric point, as used by the recorded fibre functor.
Source: thm-lisse-qlbar-representations, Fibres
(blueprint: lem-real-condensed-fibre-functoriality). -/
abbrev FibreRing (Ω : Type u) [Field Ω] :=
  CondensedRing.Evaluation.A (Scheme.ProEt.topology (Spec (.of Ω)))
    (condensedRingObj Λ (Spec (.of Ω))) (Scheme.ProEt.mk (𝟙 _))

attribute [local irreducible] CondensedRing.upperStar in
/-- The canonical beta: first compose module inverse images, then take point sections.
Source: node proof step 1 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ LisseQlbar.fibre Λ y ≅ LisseQlbar.fibre Λ (y ≫ f) :=
  (Functor.associator (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ y)
    (CondensedRing.Evaluation.sections (Scheme.ProEt.topology (Spec (.of Ω)))
      (condensedRingObj Λ (Spec (.of Ω))) (Scheme.ProEt.mk (𝟙 _)))).symm ≪≫
    Functor.isoWhiskerRight (CondensedRing.upperStarComp Λ y f).symm
      (CondensedRing.Evaluation.sections (Scheme.ProEt.topology (Spec (.of Ω)))
        (condensedRingObj Λ (Spec (.of Ω))) (Scheme.ProEt.mk (𝟙 _)))

/-- The actual finite-quotient map on fibres, before choosing a monodromy presentation.
Source: dependency's reductionOnFibre construction, without its final representation isomorphism
(blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def finiteProjection {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (L : Modules Λ X)
    (R : Type (u + 1)) [CommRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (q : L.X ⟶ (comparisonUpperStar Ab.{u + 1} X).obj (LisseQlbar.underlyingAb R F)) :
    AddCommGrpCat.of ((LisseQlbar.fibre Λ x).obj L) ⟶
      AddCommGrpCat.of (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) :=
  (LisseQlbar.fibreUnderlyingIso Λ x L).hom ≫ (LisseQlbar.abFibre x).map q ≫
    LisseQlbar.finiteFibreMap x (LisseQlbar.underlyingAb R F) ≫
      (LisseQlbar.moduleStalkUnderlyingIso x R F).hom

/-- The same finite-fibre comparison before the last module-stalk comparison.
Source: node proof steps 1--2 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def abelianProjection {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (L : Modules Λ X)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (q : L.X ⟶ (comparisonUpperStar Ab.{u + 1} X).obj F) :
    AddCommGrpCat.of ((LisseQlbar.fibre Λ x).obj L) ⟶
      (pointSmallEtale x).sheafFiber.obj F :=
  (LisseQlbar.fibreUnderlyingIso Λ x L).hom ≫ (LisseQlbar.abFibre x).map q ≫
    LisseQlbar.finiteFibreMap x F

/-- Pull back a finite quotient through the canonical underlying-sheaf and site comparisons.
Source: node proof step 1 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def pullbackQuotient {X Y : Scheme.{u}} (f : Y ⟶ X) (L : Modules Λ X)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (q : L.X ⟶ (comparisonUpperStar Ab.{u + 1} X).obj F) :
    ((CondensedRing.upperStar Λ f).obj L).X ⟶
      (comparisonUpperStar Ab.{u + 1} Y).obj ((Etale.upperStar Ab.{u + 1} f).obj F) :=
  (CondensedRing.upperStarObjXIso Λ f L).hom ≫ (ProEtale.upperStar Ab.{u + 1} f).map q ≫
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app F

/-- Natural linear path maps on the actual fibres. Composition makes their loop evaluations
an action; conjugation and the last two equations explicitly retain the arithmetic-path
conjugation and change-of-lift identities, with the same inverse convention.
Source: node proof steps 2--5 and 10--12
(blueprint: lem-real-condensed-fibre-functoriality). -/
structure Paths (X : Scheme.{u}) where
  map : ∀ {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (_t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z) (L : Modules Λ X) (_hL : Lisse Λ L),
    AddCommGrpCat.of ((LisseQlbar.fibre Λ x).obj L) ≅
      AddCommGrpCat.of ((LisseQlbar.fibre Λ z).obj L)
  linear : ∀ {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z) (L : Modules Λ X) (hL : Lisse Λ L)
    (a : condensedScalarRing Λ) (v : (LisseQlbar.fibre Λ x).obj L),
    (map x z t L hL).hom
        (CondensedRing.affineScalarSection Λ (Spec (.of Ω)) a • v) =
      CondensedRing.affineScalarSection Λ (Spec (.of Ω')) a • (map x z t L hL).hom v
  naturality : ∀ {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z)
    (L M : Modules Λ X) (hL : Lisse Λ L) (hM : Lisse Λ M) (a : L ⟶ M) (v),
    (map x z t M hM).hom (((LisseQlbar.fibre Λ x).map a).hom v) =
      ((LisseQlbar.fibre Λ z).map a).hom ((map x z t L hL).hom v)
  identity : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (L : Modules Λ X) (hL : Lisse Λ L),
    map x x (Iso.refl _) L hL = Iso.refl _
  composition : ∀ {Ω Ω' Ω'' : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] [Field Ω''] [IsAlgClosed Ω'']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X) (w : Spec (.of Ω'') ⟶ X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z)
    (s : FiniteEtale.fiber z ≅ FiniteEtale.fiber w) (L : Modules Λ X) (hL : Lisse Λ L),
    map x w (t ≪≫ s) L hL = map x z t L hL ≪≫ map z w s L hL
  conjugation : ∀ {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z) (g : Aut (FiniteEtale.fiber x))
    (L : Modules Λ X) (hL : Lisse Λ L),
    map z z (Iso.conjAut t g) L hL =
      (map x z t L hL).symm ≪≫ map x x g L hL ≪≫ map x z t L hL
  arithmetic_conjugation : ∀ {Ω Ω' : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z)
    (a : Aut (FiniteEtale.fiber x)) (c : Aut (FiniteEtale.fiber z))
    (_h : a ≪≫ t = t ≪≫ c) (L : Modules Λ X) (hL : Lisse Λ L) (v),
    (map x z t L hL).hom ((map x x a L hL).hom v) =
      (map z z c L hL).hom ((map x z t L hL).hom v)
  change_lift : ∀ {Ω Ω' : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (t t' : FiniteEtale.fiber x ≅ FiniteEtale.fiber z)
    (a : Aut (FiniteEtale.fiber x)) (_h : t' = a.symm ≪≫ t)
    (L : Modules Λ X) (_hL : Lisse Λ L),
    map x z t' L _hL = map x x a.symm L _hL ≪≫ map x z t L _hL
  tensor_lisse : ∀ (L M : Modules Λ X), Lisse Λ L → Lisse Λ M → Lisse Λ (L ⊗ M)
  tensor : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (L M : Modules Λ X) (_hL : Lisse Λ L) (_hM : Lisse Λ M),
    ∃ e : tensorObj ((LisseQlbar.fibre Λ x).obj L) ((LisseQlbar.fibre Λ x).obj M) ≅
        (LisseQlbar.fibre Λ x).obj (L ⊗ M),
      ∀ v w, e.hom (v ⊗ₜ[FibreRing Λ Ω] w) = LisseQlbar.tensorPair Λ x L M v w
  tensor_path : ∀ {Ω Ω' : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z)
    (L M : Modules Λ X) (hL : Lisse Λ L) (hM : Lisse Λ M) (v) (w),
    (map x z t (L ⊗ M) (tensor_lisse L M hL hM)).hom
        (LisseQlbar.tensorPair Λ x L M v w) =
      LisseQlbar.tensorPair Λ z L M ((map x z t L hL).hom v) ((map x z t M hM).hom w)
  finite_free : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (L : Modules Λ X) (_hL : Lisse Λ L),
    Module.Free (FibreRing Λ Ω) ((LisseQlbar.fibre Λ x).obj L) ∧
      Module.Finite (FibreRing Λ Ω) ((LisseQlbar.fibre Λ x).obj L)
  exact : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (S : ShortComplex (Modules Λ X)), S.ShortExact →
    Lisse Λ S.X₁ → Lisse Λ S.X₂ → Lisse Λ S.X₃ →
    Function.Injective ((LisseQlbar.fibre Λ x).map S.f).hom ∧
      Function.Exact ((LisseQlbar.fibre Λ x).map S.f).hom
        ((LisseQlbar.fibre Λ x).map S.g).hom ∧
      Function.Surjective ((LisseQlbar.fibre Λ x).map S.g).hom

/-- Typed path families at the three coefficient stages. These are the same three cases
as Coefficient, retaining their canonical instance data before forming quotient maps.
Source: coefficient stages (blueprint: lem-real-condensed-fibre-functoriality). -/
structure CoefficientPaths (X : Scheme.{u}) where
  integral : ∀ E, Paths (LisseQlbar.integerRing ell E) X
  rational : ∀ E, Paths (LisseQlbar.fieldRing ell E) X
  algebraic : Paths (Profinite.padicAlgClRingObj ell) X

/-- Evaluate the typed family at a coefficient index.
Source: coefficient stages (blueprint: lem-real-condensed-fibre-functoriality). -/
def CoefficientPaths.at {X : Scheme.{u}} (p : CoefficientPaths ell X)
    (c : Coefficient ell) : Paths (c.ring ell) X :=
  match c with
  | .integral E => p.integral E
  | .rational E => p.rational E
  | .algebraic => p.algebraic

/-- Scalar compatibility is imposed for every scalar-extension presentation, including every
lattice or finite model. Together with linearity this is the pure-tensor formula
`b tensor v ↦ b tensor t(v)` and implies independence of the presentation.
Source: node proof steps 6--9 (blueprint: lem-real-condensed-fibre-functoriality). -/
def ScalarCompatible
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    {X : Scheme.{u}} (d : Paths Λ X) (e : Paths B X)
    (a : Λ ⟶ B) [IsMonHom a] : Prop :=
  ∀ {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω') ⟶ X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z)
    (L : Modules Λ X) (M : Modules B X) (hL : Lisse Λ L) (hM : Lisse B M)
    (i : L ⟶ (Mod.comap (coefficientMap a X)).obj M),
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv L M).symm i) →
    ∀ v, (e.map x z t M hM).hom (LisseQlbar.fibreMap Λ B x L M i.hom v) =
      LisseQlbar.fibreMap Λ B z L M i.hom ((d.map x z t L hL).hom v)

set_option maxHeartbeats 0 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The pullback path clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def pullbackPathProperty
    (paths : ∀ S : Context.{u}, CoefficientPaths ell S.X)
    (pullback_lisse : ∀ (S T : Context.{u}) (f : T.X ⟶ S.X) (c : Coefficient ell)
    (L : Modules (c.ring ell) S.X), Lisse (c.ring ell) L →
      Lisse (c.ring ell) ((CondensedRing.upperStar (c.ring ell) f).obj L)) : Prop :=
  ∀ (S T : Context.{u}) (f : T.X ⟶ S.X) (c : Coefficient ell)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y z : Spec (.of Ω) ⟶ T.X)
    (t : FiniteEtale.fiber y ≅ FiniteEtale.fiber z)
    (L : Modules (c.ring ell) S.X) (hL : Lisse (c.ring ell) L) (v),
    ((pullback (c.ring ell) f z).hom.app L).hom
        (((CoefficientPaths.at ell (paths T) c).map y z t
          ((CondensedRing.upperStar (c.ring ell) f).obj L)
          (pullback_lisse S T f c L hL)).hom v) =
      ((CoefficientPaths.at ell (paths S) c).map (y ≫ f) (z ≫ f)
        (AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso f t) L hL).hom
        (((pullback (c.ring ell) f y).hom.app L).hom v)

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The pullback composition clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def pullbackCompositionProperty : Prop :=
  ∀ (S T U : Context.{u}) (f : U.X ⟶ T.X) (g : T.X ⟶ S.X)
    (c : Coefficient ell) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : Spec (.of Ω) ⟶ U.X) (L : Modules (c.ring ell) S.X),
    (pullback (c.ring ell) (f ≫ g) z).hom.app L =
      (LisseQlbar.fibre (c.ring ell) z).map
          ((CondensedRing.upperStarComp (c.ring ell) f g).hom.app L) ≫
        (pullback (c.ring ell) f z).hom.app
          ((CondensedRing.upperStar (c.ring ell) g).obj L) ≫
        (pullback (c.ring ell) g (z ≫ f)).hom.app L ≫
        eqToHom (congrArg (fun p ↦ (LisseQlbar.fibre (c.ring ell) p).obj L)
          (Category.assoc z f g))

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The pullback tensor clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def pullbackTensorProperty : Prop :=
  ∀ (S T : Context.{u}) (f : T.X ⟶ S.X) (c : Coefficient ell)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T.X)
    (L M : Modules (c.ring ell) S.X) (_hL : Lisse (c.ring ell) L)
    (_hM : Lisse (c.ring ell) M) (v) (w),
    ((pullback (c.ring ell) f y).hom.app (L ⊗ M)).hom
        (((LisseQlbar.fibre (c.ring ell) y).map
          (Functor.LaxMonoidal.μ (CondensedRing.upperStar (c.ring ell) f) L M)).hom
            (LisseQlbar.tensorPair (c.ring ell) y
              ((CondensedRing.upperStar (c.ring ell) f).obj L)
              ((CondensedRing.upperStar (c.ring ell) f).obj M) v w)) =
      LisseQlbar.tensorPair (c.ring ell) (y ≫ f) L M
        (((pullback (c.ring ell) f y).hom.app L).hom v)
        (((pullback (c.ring ell) f y).hom.app M).hom w)

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The finite pullback clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def finitePullbackProperty : Prop :=
  ∀ (S T : Context.{u}) (f : T.X ⟶ S.X) (c : Coefficient ell)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T.X)
    (L : Modules (c.ring ell) S.X) (_hL : Lisse (c.ring ell) L)
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (F : Sheaf S.X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (_hF : IsFiniteLocallyConstantSheaf F)
    (q : L.X ⟶ (comparisonUpperStar Ab.{u + 1} S.X).obj (LisseQlbar.underlyingAb R F)),
    abelianProjection (c.ring ell) y ((CondensedRing.upperStar (c.ring ell) f).obj L)
        ((Etale.upperStar Ab.{u + 1} f).obj (LisseQlbar.underlyingAb R F))
        (pullbackQuotient (c.ring ell) f L (LisseQlbar.underlyingAb R F) q) ≫
        (Etale.upperStarCompSheafFiberIso Ab.{u + 1} f y).hom.app
          (LisseQlbar.underlyingAb R F) =
      (forget₂ _ Ab.{u + 1}).map ((pullback (c.ring ell) f y).hom.app L) ≫
        abelianProjection (c.ring ell) (y ≫ f) L (LisseQlbar.underlyingAb R F) q

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The pullback scalar clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def pullbackScalarProperty : Prop :=
  ∀ (S T : Context.{u}) (f : T.X ⟶ S.X) (c d : Coefficient ell)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T.X)
    (L : Modules (c.ring ell) S.X) (M : Modules (d.ring ell) S.X)
    (q : L.X ⟶ M.X) (v),
    ((pullback (d.ring ell) f y).hom.app M).hom
        (LisseQlbar.fibreMap (c.ring ell) (d.ring ell) y
          ((CondensedRing.upperStar (c.ring ell) f).obj L)
          ((CondensedRing.upperStar (d.ring ell) f).obj M)
          ((CondensedRing.upperStarObjXIso (c.ring ell) f L).hom ≫
            (ProEtale.upperStar Ab.{u + 1} f).map q ≫
            (CondensedRing.upperStarObjXIso (d.ring ell) f M).inv) v) =
      LisseQlbar.fibreMap (c.ring ell) (d.ring ell) (y ≫ f) L M q
        (((pullback (c.ring ell) f y).hom.app L).hom v)

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The finite normalization clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def finiteNormalizationProperty
    (paths : ∀ S : Context.{u}, CoefficientPaths ell S.X) : Prop :=
  ∀ (S : Context.{u}) (E : PadicAlgCl.FiniteIntermediateField ell)
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ S.X) (z : Spec (.of Ω') ⟶ S.X)
    (t : FiniteEtale.fiber x ≅ FiniteEtale.fiber z)
    (L : Modules (LisseQlbar.integerRing ell E) S.X)
    (hL : Lisse (LisseQlbar.integerRing ell E) L)
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (F : Sheaf S.X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (n : ℕ)
    (q : L.X ⟶ (comparisonUpperStar Ab.{u + 1} S.X).obj (LisseQlbar.underlyingAb R F))
    (hq : LisseQlbar.scalarEnd (LisseQlbar.integerRing ell E) S.X
      (LisseQlbar.integerScalar ell E
        ((Padic.coefficientExtensionUniformizer ell E) ^ n)) L ≫ q = 0)
    (_hcoker : IsColimit (CokernelCofork.ofπ q hq)) (v),
    finiteProjection (LisseQlbar.integerRing ell E) z L R F q
        ((((paths S).integral E).map x z t L hL).hom v) =
      hF.transport x z t (finiteProjection (LisseQlbar.integerRing ell E) x L R F q v)

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The localization clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def localizationProperty
    (paths : ∀ S : Context.{u}, CoefficientPaths ell S.X) : Prop :=
  ∀ (S : Context.{u}) (E : PadicAlgCl.FiniteIntermediateField ell),
    ScalarCompatible (LisseQlbar.integerRing ell E) (LisseQlbar.fieldRing ell E)
      ((paths S).integral E) ((paths S).rational E) (LisseQlbar.integerInclusion ell E)

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The algebraic extension clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def algebraicExtensionProperty
    (paths : ∀ S : Context.{u}, CoefficientPaths ell S.X) : Prop :=
  ∀ (S : Context.{u}) (E : PadicAlgCl.FiniteIntermediateField ell),
    ScalarCompatible (LisseQlbar.fieldRing ell E) (Profinite.padicAlgClRingObj ell)
      ((paths S).rational E) ((paths S).algebraic)
      (Profinite.padicSubfieldRingObjToPadicAlgCl ell E)

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The field extension clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def fieldExtensionProperty
    (paths : ∀ S : Context.{u}, CoefficientPaths ell S.X) : Prop :=
  ∀ (S : Context.{u}) (E F : PadicAlgCl.FiniteIntermediateField ell)
    (h : E ≤ F),
    ScalarCompatible (LisseQlbar.fieldRing ell E) (LisseQlbar.fieldRing ell F)
      ((paths S).rational E) ((paths S).rational F)
      (Profinite.padicSubfieldRingObjMap ell h)

set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
/-- The integer extension clause of the simultaneous fibre theorem.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def integerExtensionProperty
    (paths : ∀ S : Context.{u}, CoefficientPaths ell S.X) : Prop :=
  ∀ (S : Context.{u}) (E F : PadicAlgCl.FiniteIntermediateField ell)
    (h : E ≤ F),
    ∃ (a : LisseQlbar.integerRing ell E ⟶ LisseQlbar.integerRing ell F)
      (ha : IsMonHom a),
      (a ≫ LisseQlbar.integerInclusion ell F =
        LisseQlbar.integerInclusion ell E ≫ Profinite.padicSubfieldRingObjMap ell h) ∧
      (letI := ha
       ScalarCompatible (LisseQlbar.integerRing ell E) (LisseQlbar.integerRing ell F)
         ((paths S).integral E) ((paths S).integral F) a) ∧
      ∀ b : LisseQlbar.integerRing ell E ⟶ LisseQlbar.integerRing ell F,
        b ≫ LisseQlbar.integerInclusion ell F =
          LisseQlbar.integerInclusion ell E ≫ Profinite.padicSubfieldRingObjMap ell h → b = a

/-- The simultaneous normalized path family and every functoriality clause.
Source: node proof steps 1--12 (blueprint: lem-real-condensed-fibre-functoriality). -/
structure System where
  paths : ∀ S : Context.{u}, CoefficientPaths ell S.X
  correspondence : ∀ (S : Context.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ S.X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber x) G],
    LisseQlbar.Correspondence ell x G
  pullback_lisse : ∀ (S T : Context.{u}) (f : T.X ⟶ S.X) (c : Coefficient ell)
    (L : Modules (c.ring ell) S.X), Lisse (c.ring ell) L →
      Lisse (c.ring ell) ((CondensedRing.upperStar (c.ring ell) f).obj L)
  pullback_path : pullbackPathProperty ell paths pullback_lisse
  pullback_composition : pullbackCompositionProperty.{u} ell
  pullback_tensor : pullbackTensorProperty.{u} ell
  finite_pullback : finitePullbackProperty.{u} ell
  pullback_scalar : pullbackScalarProperty.{u} ell
  finite_normalization : finiteNormalizationProperty ell paths
  localization : localizationProperty ell paths
  algebraic_extension : algebraicExtensionProperty ell paths
  field_extension : fieldExtensionProperty ell paths
  integer_extension : integerExtensionProperty ell paths

/-- The simultaneous functoriality of normalized fibres, with exactly the scheme hypotheses
in Context. The chosen algebraic closure is the dependency's PadicAlgCl ell; arbitrary finite
extensions inside it occur as Coefficient.integral and Coefficient.rational.
Source: current blueprint sk-d-real-weil, second proof paragraph and finite-reduction paragraph
(blueprint: lem-real-condensed-fibre-functoriality).

Proof (postponed): define beta by pullback composition. At finite level evaluate finite-etale
paths on the representing covers of the finite local systems. Naturality with addition, scalars,
products and pure tensors gives linearity, tensor/scalar laws and conjugation. The normalized
integral fibres of thm-lisse-qlbar-representations are the inverse limits of their quotient
fibres, so define path maps coordinatewise; finite-level equalities imply their integral
versions. Localize a lattice to obtain the rational maps, clearing denominators to obtain
naturality for all rational arrows and lattice independence. Finite descent of objects and
morphisms gives the algebraic-closure maps and independence of the finite model. Scalar
comparison on every presentation gives compatibility with finite extensions. Pullback beta
reduces to the first-projection comparison, hence is equivariant. Exact pullback followed by
exact sections on an algebraically closed point gives exactness on short exact lisse sequences.
A common free trivialization at that point proves finite freeness and the canonical tensor
comparison. Finally apply the finite arithmetic-path identities without changing their inverse
convention, then pass to the integral limit and the two scalar extensions.
-/
theorem real_condensed_fibre_functoriality (ell : ℕ) [Fact ell.Prime] :
    Nonempty (System.{u} ell) := by
  sorry

end AlgebraicGeometry.ProEtale.RealCondensedFibre

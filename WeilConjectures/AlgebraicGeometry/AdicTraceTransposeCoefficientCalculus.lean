/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicTraceTransposeData

/-! # Coefficient and shift calculus of integral trace transposes

Source: blueprint sk-thm-purity-transport, Steps 2--3
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.AdicTraceTranspose
open ConstructibleExceptionalCoefficients
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (c : Compactification f.hom.left) (d : ℕ)
  (R : RingSystem.{u} C.l C.Qbar D C.different (f := f.hom.left))

private theorem fullSubcategoryIso_existsUnique_of_source_eq
    {A : Type*} [Category A] (P : ObjectProperty A) {U V : P.FullSubcategory}
    {Z : A} (h : U.obj = Z) (e : Z ≅ V.obj) :
    ∃! e' : U ≅ V, HEq e'.hom.hom e.hom := by
  subst Z
  exact ⟨P.isoMk e, HEq.rfl, fun e' he' ↦
    Iso.ext (ObjectProperty.hom_ext _ (eq_of_heq he'))⟩

/-- Root-normalized scalar comparison on the shifted line, in the full category.
Source: q_(F/E), the unit component of the pullback/tensor/twist/shift comparison
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: RingSystem.integralScalar_eq identifies the underlying source with the
strict scalar extension. Its integralScalar_normalized clause retains precisely chi
as the inverse realization map. sfOrientationIntegralScalarAmbient is normalized by
the single-complex comparison and the actual root-line scalar map. Lift through
the fully faithful inclusion. The heterogeneous underlying-arrow equation fixes
all transports and gives uniqueness. -/
theorem lineComparison_existsUnique
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    ∃! q : (scalar D C f R h true).functor.obj (line D C X E d) ≅ line D C X F d,
      HEq q.hom.hom
        (@sfOrientationIntegralScalarAmbient C.l _ (field D C E).carrier _ _ _
          (field D C F).carrier _ _ _
          (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h)
          X.obj.left (dlAdicGeometricResidueInvertible D C X.obj.left) d).hom := by
  exact fullSubcategoryIso_existsUnique_of_source_eq _
    (U := (scalar D C f R h true).functor.obj (line D C X E d))
    (V := line D C X F d)
    (congrArg (fun H ↦ H.obj (line D C X E d))
      (R.integralScalar_eq (field D C E) (field D C F)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h) true))
    (@sfOrientationIntegralScalarAmbient C.l _ (field D C E).carrier _ _ _
      (field D C F).carrier _ _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h)
      X.obj.left (dlAdicGeometricResidueInvertible D C X.obj.left) d)


/-- The actual root-normalized q_(F/E). Source: trace coefficient compatibility
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def lineComparison {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :=
  (lineComparison_existsUnique D C f d R h).exists.choose

/-- The coefficient unit comparison, uniquely specified as the degree-zero
multiplication map after chi. Source: the suppressed tensor unit in the trace equation
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: RingSystem.integralScalar_eq identifies the underlying scalar source with
the strict scalar extension, with chi retained by integralScalar_normalized. The
map constantCoefficientIntegralScalarIso is the strict coefficient-unit map; its
inverse sends a section to its quotient tower and zero shifted coordinate. Both
units are the regular coefficient complexes in degree zero. Lift through the full
subcategory. The heterogeneous underlying-arrow equation gives uniqueness. -/
theorem unitComparison_existsUnique
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    ∃! q : (scalar D C f R h false).functor.obj (unit D C Y E) ≅ unit D C Y F,
      HEq q.hom.hom
        (constantCoefficientIntegralScalarIso C.l (field D C E).carrier
          (field D C F).carrier
          (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h)
          Y.obj.left).hom := by
  exact fullSubcategoryIso_existsUnique_of_source_eq _
    (U := (scalar D C f R h false).functor.obj (unit D C Y E))
    (V := unit D C Y F)
    (congrArg (fun H ↦ H.obj (unit D C Y E))
      (R.integralScalar_eq (field D C E) (field D C F)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h) false))
    (constantCoefficientIntegralScalarIso C.l (field D C E).carrier
      (field D C F).carrier
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h) Y.obj.left)


/-- The uniquely normalized coefficient-unit comparison. Source: trace unit constraint
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def unitComparison {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :=
  (unitComparison_existsUnique D C f R h).exists.choose


/-- The actual scalar/tensor/pullback composite giving the coefficient source arrow.
Source: a_(F/E) in j_E coordinates
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def sourceComparisonArrow {E F : Padic.FiniteCoefficientFields C.l C.Qbar}
    (h : E ≤ F) (K : Cat D C Y E) :
    ((scalar D C f R h true).functor.obj ((source D C f d E).obj K)).obj ⟶
      ((source D C f d F).obj ((scalar D C f R h false).functor.obj K)).obj :=
  (scalar D C f R h true).realization.hom.app ((source D C f d E).obj K) ≫
    (PurCompactSupport.scalarTensor ((change D C h).map X.obj.left)
      (tensorModel D C X E) (tensorModel D C X F)).hom.app
        ((line D C X E d).obj,
          (PurCompactSupport.pull (PurCompactSupport.completed C.l (field D C E).carrier)
            f.hom.left).obj K.obj) ≫
    (tensorModel D C X F).tensor.map
      (Prod.mkHom
        ((scalar D C f R h true).realization.inv.app (line D C X E d) ≫
          (lineComparison D C f d R h).hom.hom)
        ((PurCompactSupport.scalarPull (change D C h) f.hom.left).hom.app K.obj ≫
          (PurCompactSupport.pull (PurCompactSupport.completed C.l (field D C F).carrier)
            f.hom.left).map ((scalar D C f R h false).realization.inv.app K)))


/-- Naturality and invertibility of the specified source comparison, with its full
underlying-arrow normalization. Source: canonical a_(F/E)
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: all factors of sourceComparisonArrow are normalized natural isomorphisms:
scalar.realization, scalarTensor, the root-line comparison and scalarPull. The full
inclusions are fully faithful, so these factors lift uniquely to a natural
isomorphism on the finite-Tor categories, with the displayed components. -/
theorem sourceComparison_existsUnique
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    ∃! a : source D C f d E ⋙ (scalar D C f R h true).functor ≅
        (scalar D C f R h false).functor ⋙ source D C f d F,
      ∀ K : Cat D C Y E, (a.hom.app K).hom = sourceComparisonArrow D C f d R h K := by
  sorry


/-- The canonical source coefficient comparison, including its tensor normalization.
Source: a_(F/E) (blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def sourceComparison {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :=
  (sourceComparison_existsUnique D C f d R h).exists.choose


/-- A family of completely arbitrary integral traces. Source: t_E in the node
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
abbrev Traces := ∀ E : Padic.FiniteCoefficientFields C.l C.Qbar,
  (operation D C f c R E).F.obj (line D C X E d) ⟶ unit D C Y E

/-- The sole trace hypothesis, with the suppressed coefficient-unit constraint restored.
Source: the displayed trace square
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def TraceCompatible (t : Traces D C f c d R) : Prop :=
  ∀ (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F),
    (supportIso D C f c R h).hom.app (line D C X E d) ≫
        (operation D C f c R F).F.map (lineComparison D C f d R h).hom ≫ t F =
      (scalar D C f R h false).functor.map (t E) ≫
        (unitComparison D C f R h).hom

private theorem tensor_unit_natural_aux
    {A : Type*} [Category A] [MonoidalCategory A]
    (T : A × A ⥤ A) (h : T = MonoidalCategory.tensor A)
    {U K K' : A} (e : 𝟙_ A ≅ U) (v : K ⟶ K') :
    T.map (Prod.mkHom (𝟙 U) v) ≫
        (eqToIso (congrArg (fun T ↦ T.obj (U, K')) h) ≪≫
          (MonoidalCategory.tensor A).mapIso (Iso.prod e.symm (Iso.refl K')) ≪≫
          MonoidalCategory.leftUnitor K').hom =
      (eqToIso (congrArg (fun T ↦ T.obj (U, K)) h) ≪≫
          (MonoidalCategory.tensor A).mapIso (Iso.prod e.symm (Iso.refl K)) ≪≫
          MonoidalCategory.leftUnitor K).hom ≫ v := by
  subst T
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.symm_hom, Iso.refl_hom]
  have hm : (Prod.mkHom (𝟙 U) v) ≫ Prod.mkHom e.inv (𝟙 K') =
      Prod.mkHom e.inv (𝟙 K) ≫ Prod.mkHom (𝟙 (𝟙_ A)) v := by
    ext <;> simp
  rw [← Category.assoc, ← Functor.map_comp, hm, Functor.map_comp, Category.assoc]
  simpa only [MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_def, id_whiskerRight,
    Category.id_comp, Category.assoc] using
    congrArg (fun z ↦ (MonoidalCategory.tensor A).map
      (Prod.mkHom e.inv (𝟙 K)) ≫ z) (leftUnitor_naturality v)


private theorem tensorUnit_natural
    (E : Padic.FiniteCoefficientFields C.l C.Qbar) {K K' : Cat D C Y E} (v : K ⟶ K') :
    (tensorModel D C Y E).tensor.map (Prod.mkHom (𝟙 _) v.hom) ≫
        (tensorUnit D C E K').hom = (tensorUnit D C E K).hom ≫ v.hom := by
  let := (closed D C Y E).monoidal
  exact @tensor_unit_natural_aux _ _ (closed D C Y E).monoidal _
    (RationalSmoothPurityCanonical.ordinaryModel_existsUnique C.l
      (field D C E).carrier Y.obj.left).exists.choose_spec.1 _ _ _ _ v.hom


private theorem inverse_trace_square
    {A : Type*} [Category A] {S S' U U' V V' K K' : A}
    (p : U ⟶ S) (p' : U' ⟶ S') [IsIso p] [IsIso p']
    (a : S ⟶ S') (b : U ⟶ U') (q : U ⟶ V) (q' : U' ⟶ V')
    (w : V ⟶ V') (u : V ⟶ K) (u' : V' ⟶ K') (v : K ⟶ K')
    (hp : b ≫ p' = p ≫ a) (hq : b ≫ q' = q ≫ w) (hu : w ≫ u' = u ≫ v) :
    a ≫ (inv p' ≫ q' ≫ u') = (inv p ≫ q ≫ u) ≫ v := by
  have hi : a ≫ inv p' = inv p ≫ b := by
    apply (cancel_epi p).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← hp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hi, Category.assoc, ← Category.assoc b, hq,
    Category.assoc, hu]
  simp only [Category.assoc]


private theorem ordinaryTrace_natural
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (t : (operation D C f c R E).F.obj (line D C X E d) ⟶ unit D C Y E)
    {K K' : Cat D C Y E} (v : K ⟶ K') :
    (PurCompactSupport.image (PurCompactSupport.completed C.l (field D C E).carrier) c).map
        ((source D C f d E).map v).hom ≫ ordinaryTrace D C f c d R E t K' =
      ordinaryTrace D C f c d R E t K ≫ v.hom := by
  let := projection_isIso D C f c d E K
  let := projection_isIso D C f c d E K'
  apply inverse_trace_square (projection D C f c d E K) (projection D C f c d E K')
    _ ((tensorModel D C Y E).tensor.map (Prod.mkHom (𝟙 _) v.hom)) _ _
    ((tensorModel D C Y E).tensor.map (Prod.mkHom (𝟙 _) v.hom)) _ _ v.hom
  · exact ((PurCompactSupport.projectionMap
      (PurCompactSupport.completed C.l (field D C E).carrier) c (tensorModel D C X E)
      (RationalSmoothPurityCanonical.ordinaryModel C.l (field D C E).carrier c.Z)
      (tensorModel D C Y E)
      (PurCompactSupport.completedPull_comp C.l (field D C E).carrier c.i c.g)).app
        (line D C X E d).obj).naturality v.hom
  · simp only [← Functor.map_comp]
    congr 1
    ext <;> simp
  · exact tensorUnit_natural D C E v


/-- The trace transpose is a natural transformation, without invertibility of the trace.
Source: node proof Step 1
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: projection is natural in its second argument; tensoring a fixed trace is natural.
The adjunction bijection is natural in both variables. These three squares compose
into the displayed naturality equation. -/
theorem gamma_natural (t : Traces D C f c d R)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar) {K K' : Cat D C Y E} (v : K ⟶ K') :
    (source D C f d E).map v ≫ gamma D C f c d R E (t E) K' =
      gamma D C f c d R E (t E) K ≫ (operation D C f c R E).G.map v := by
  change (source D C f d E).map v ≫
      (operation D C f c R E).adjunction.homEquiv _ _ (integrated D C f c d R E (t E) K') =
    (operation D C f c R E).adjunction.homEquiv _ _ (integrated D C f c d R E (t E) K) ≫
      (operation D C f c R E).G.map v
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  apply ObjectProperty.hom_ext
  change ((operation D C f c R E).F.map ((source D C f d E).map v)).hom ≫
      ((R.left c (.integral (field D C E))).hom.app _ ≫ _) = _
  erw [← Category.assoc, (R.left c (.integral (field D C E))).hom.naturality]
  erw [Category.assoc, ordinaryTrace_natural]
  exact (Category.assoc _ _ _).symm



/-- The natural integral trace transpose in canonical j-coordinates.
Source: gamma_E (blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def gammaTransformation (t : Traces D C f c d R)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    source D C f d E ⟶ (operation D C f c R E).G where
  app K := gamma D C f c d R E (t E) K
  naturality _ _ v := gamma_natural D C f c d R t E v

/-- Coefficient tower inclusions compose as actual ring-sheaf morphisms.
Source: normalized tensor associator
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: completedMap_composition identifies the composite with the map of the composite
field inclusion. The composite subtype inclusions equal the direct inclusion, by
extensionality, so their completed maps agree. -/
theorem change_comp {E F L : Padic.FiniteCoefficientFields C.l C.Qbar}
    (h : E ≤ F) (k : F ≤ L) (W : Scheme.{u}) :
    (change D C h).map W ≫ (change D C k).map W = (change D C (h.trans k)).map W := by
  change completedCoefficientMap _ _ _ _ W ≫
    completedCoefficientMap _ _ _ _ W = _
  rw [PurCompactSupport.completedMap_composition]
  rw [(AlgebraicallyClosedCoefficients.coefficientInclusion_laws C.l C.Qbar).2]
  rfl

/-- The ordinary tensor associator on the existing restricted scalar functors.
Source: alpha^W_(L,F,E)
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def scalarComposition {E F L : Padic.FiniteCoefficientFields C.l C.Qbar}
    (h : E ≤ F) (k : F ≤ L) (side : Bool) :
    (scalar D C f R h side).functor ⋙ (scalar D C f R k side).functor ≅
      (scalar D C f R (h.trans k) side).functor :=
  (R.scalarComposition (s := .integral (field D C E))
    (t := .integral (field D C F)) (r := .integral (field D C L))
    (change D C h) (change D C k) (change D C (h.trans k))
    (change_comp D C h k)
    (Allowed.integral (field D C E) (field D C F)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h))
    (Allowed.integral (field D C F) (field D C L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F L k))
    (Allowed.integral (field D C E) (field D C L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E L (h.trans k))) side).iso

/-- The actual identity completed coefficient map.
Source: normalized tensor unit
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: the subtype self-inclusion is the identity algebra map. Apply
completedMap_identity, whose proof compares every coefficient quotient projection. -/
theorem change_id (E : Padic.FiniteCoefficientFields C.l C.Qbar) (W : Scheme.{u}) :
    (change D C (le_refl E)).map W = 𝟙 _ := by
  change completedCoefficientMap _ _ _ _ W = _
  rw [(AlgebraicallyClosedCoefficients.coefficientInclusion_laws C.l C.Qbar).1]
  exact PurCompactSupport.completedMap_identity C.l (field D C E).carrier W

/-- The canonical scalar multiplication identification with identity.
Source: b_(E/E)=1, with its unit constraints explicit
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def scalarIdentity (E : Padic.FiniteCoefficientFields C.l C.Qbar) (side : Bool) :
    (scalar D C f R (le_refl E) side).functor ≅ 𝟭 _ :=
  (R.scalarIdentity (s := .integral (field D C E))
    (change D C (le_refl E)) (change_id D C E)
    (Allowed.integral (field D C E) (field D C E)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E E (le_refl E))) side).iso

private theorem exceptionalComparison_eq
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    exceptionalComparison D C f c R h =
      (letI := (scalar D C f R h true).commShift
       let := (scalar D C f R h false).commShift
       (supportComparison D C f c R h).b.hom) := by
  let := (scalar D C f R h true).commShift
  let := (scalar D C f R h false).commShift
  apply NatTrans.ext
  funext K
  apply ((operation D C f c R F).adjunction.homEquiv _ _).symm.injective
  change (operation D C f c R F).F.map
      ((mateEquiv (operation D C f c R E).adjunction
        (operation D C f c R F).adjunction
        (TwoSquare.mk _ _ _ _ (supportIso D C f c R h).inv)).app K) ≫
      (operation D C f c R F).adjunction.counit.app _ = _
  rw [mateEquiv_counit, Adjunction.homEquiv_counit]
  apply (cancel_epi ((supportIso D C f c R h).hom.app
    ((operation D C f c R E).G.obj K))).mp
  rw [Iso.hom_inv_id_app_assoc]
  exact ((supportComparison D C f c R h).counit K).symm

/-- The mate satisfies tower composition and identity before any trace is chosen.
Source: node proof Steps 5--6
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: transpose both tower composites using the pasted-mates counit formula.
The canonical c composition law identifies the transposes, after naturality of the
scalar associator at the counit. Injectivity gives the tower equation. For identity,
both inverse transposes are the counit after the scalar unit identifications. -/
theorem exceptional_tower_identity :
    (∀ (E F L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F) (k : F ≤ L)
      (K : Cat D C Y E),
      (scalarComposition D C f R h k true).hom.app ((operation D C f c R E).G.obj K) ≫
          (exceptionalComparison D C f c R (h.trans k)).app K =
        (scalar D C f R k true).functor.map
            ((exceptionalComparison D C f c R h).app K) ≫
          (exceptionalComparison D C f c R k).app
            ((scalar D C f R h false).functor.obj K) ≫
          (operation D C f c R L).G.map ((scalarComposition D C f R h k false).hom.app K)) ∧
    (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : Cat D C Y E),
      (exceptionalComparison D C f c R (le_refl E)).app K ≫
          (operation D C f c R E).G.map ((scalarIdentity D C f R E false).hom.app K) =
        (scalarIdentity D C f R E true).hom.app ((operation D C f c R E).G.obj K)) := by
  constructor
  · intro E F L h k K
    let := (scalar D C f R h true).commShift
    let := (scalar D C f R h false).commShift
    let := (scalar D C f R k true).commShift
    let := (scalar D C f R k false).commShift
    let := (scalar D C f R (h.trans k) true).commShift
    let := (scalar D C f R (h.trans k) false).commShift
    simp only [exceptionalComparison_eq]
    exact (R.cocycle c (s := .integral (field D C E))
      (t := .integral (field D C F)) (r := .integral (field D C L))
      (change D C h) (change D C k) (change D C (h.trans k))
      (change_comp D C h k)
      (Allowed.integral (field D C E) (field D C F)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h))
      (Allowed.integral (field D C F) (field D C L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F L k))
      (Allowed.integral (field D C E) (field D C L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E L
          (h.trans k)))).right K |>.symm
  · intro E K
    let := (scalar D C f R (le_refl E) true).commShift
    let := (scalar D C f R (le_refl E) false).commShift
    rw [exceptionalComparison_eq]
    exact R.identityRight c (s := .integral (field D C E))
      (change D C (le_refl E)) (change_id D C E)
      (Allowed.integral (field D C E) (field D C E)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E E
          (le_refl E))) K

/-- The constructed mate has exactly the counit transpose specified in the node.
Source: definition of b and proof Step 1
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: the mateEquiv component formula is the adjunction transpose of c inverse
followed by the scalar image of the old counit. This is its defining component
formula, without an invertibility hypothesis. -/
theorem exceptional_counit
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) (K : Cat D C Y E) :
    (exceptionalComparison D C f c R h).app K =
      (operation D C f c R F).adjunction.homEquiv _ _
        ((supportIso D C f c R h).inv.app ((operation D C f c R E).G.obj K) ≫
          (scalar D C f R h false).functor.map
            ((operation D C f c R E).adjunction.counit.app K)) := by
  apply ((operation D C f c R F).adjunction.homEquiv _ _).symm.injective
  change _ = ((operation D C f c R F).adjunction.homEquiv _ _).symm
    ((operation D C f c R F).adjunction.homEquiv _ _ _)
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact mateEquiv_counit (operation D C f c R E).adjunction
    (operation D C f c R F).adjunction
    (TwoSquare.mk _ _ _ _ (supportIso D C f c R h).inv) K


/-- The assumed ordinary tensor associator and unit equations for a.
Source: the explicit hypothesis on a in the node
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def SourceTensorCoherent : Prop :=
    (∀ (E F L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F) (k : F ≤ L)
      (K : Cat D C Y E),
      (scalarComposition D C f R h k true).hom.app ((source D C f d E).obj K) ≫
          (sourceComparison D C f d R (h.trans k)).hom.app K =
        (scalar D C f R k true).functor.map
            ((sourceComparison D C f d R h).hom.app K) ≫
          (sourceComparison D C f d R k).hom.app
            ((scalar D C f R h false).functor.obj K) ≫
          (source D C f d L).map ((scalarComposition D C f R h k false).hom.app K)) ∧
    (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : Cat D C Y E),
      (sourceComparison D C f d R (le_refl E)).hom.app K ≫
          (source D C f d E).map ((scalarIdentity D C f R E false).hom.app K) =
        (scalarIdentity D C f R E true).hom.app ((source D C f d E).obj K))

/-- Canonical shift data, normalized on every flat representative by the actual
signed total shift. This condition determines the source shift structure uniquely.
Source: the canonical tensor, pullback, twist and shift comparisons
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def SourceShiftNormalized
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (s : (source D C f d E).CommShift ℤ) : Prop :=
  (fun [_s : (source D C f d E).CommShift ℤ] ↦
    ∀ (n : ℤ)
      (P : CochainComplex (scalarReductionSource C.l (field D C E).carrier Y.obj.left) ℤ)
      (hp : proEtaleFlatRepresentatives Y.obj.left
        ((PurCompactSupport.completed C.l (field D C E).carrier).ring Y.obj.left) P)
      (hp' : proEtaleFlatRepresentatives Y.obj.left
        ((PurCompactSupport.completed C.l (field D C E).carrier).ring Y.obj.left) (P⟦n⟧))
      (K : Cat D C Y E) (e : DerivedCategory.Q.obj P ≅ K.obj),
      (sourceRepresentative D C f d E (P⟦n⟧) hp' (K⟦n⟧)
        ((DerivedCategory.Q.commShiftIso n).app P ≪≫
          (shiftFunctor _ n).mapIso e ≪≫ ((inclusion D C Y E).commShiftIso n).symm.app K)).hom ≫
          (((source D C f d E).commShiftIso n).hom.app K).hom ≫
          ((inclusion D C X E).commShiftIso n).hom.app ((source D C f d E).obj K) =
        DerivedCategory.Q.map (((sourceComplex D C f d E).commShiftIso n).hom.app P) ≫
          (DerivedCategory.Q.commShiftIso n).hom.app ((sourceComplex D C f d E).obj P) ≫
          ((sourceRepresentative D C f d E P hp K e).hom)⟦n⟧') (_s := s)

/-- The source admits exactly the canonical signed shift structure.
Source: source shift convention, node proof Step 7
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: the signed total shift on sourceComplex commutes with its differential and
with every map. Conjugate it by sourceRepresentative and descend from flat K-flat
resolutions. Naturality makes the result independent of the resolution. Zero and
addition coherence descend from total complexes. Every derived object has such a
representative, so the normalization determines every component and hence the
whole coherent shift structure uniquely. The line degree is -2d, giving the
second-variable Koszul factor (-1)^(2dn), equal to one. -/
theorem sourceShift_existsUnique (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    ∃! s : (source D C f d E).CommShift ℤ, SourceShiftNormalized D C f d E s := by
  sorry

/-- The source shift used in the node, fixed by its signed total representatives.
Source: H_E shift convention
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
@[instance_reducible]
def sourceShift (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    (source D C f d E).CommShift ℤ :=
  (sourceShift_existsUnique D C f d E).exists.choose

/-- The assumed degree-one shift square for a, with the canonical source shifts.
Source: the explicit shift hypothesis on a in the node
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def SourceShiftCoherent : Prop :=
  ∀ (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F) (K : Cat D C Y E),
    (fun [_sE : (source D C f d E).CommShift ℤ]
      [_sF : (source D C f d F).CommShift ℤ] ↦
      (sourceComparison D C f d R h).hom.app (K⟦(1 : ℤ)⟧) ≫
          (source D C f d F).map
            (((scalar D C f R h false).functor.commShiftIso (1 : ℤ)).hom.app K) ≫
          ((source D C f d F).commShiftIso (1 : ℤ)).hom.app
            ((scalar D C f R h false).functor.obj K) =
        (scalar D C f R h true).functor.map
            (((source D C f d E).commShiftIso (1 : ℤ)).hom.app K) ≫
          ((scalar D C f R h true).functor.commShiftIso (1 : ℤ)).hom.app
            ((source D C f d E).obj K) ≫
          ((sourceComparison D C f d R h).hom.app K)⟦(1 : ℤ)⟧')
      (_sE := sourceShift D C f d E) (_sF := sourceShift D C f d F)

/-- The coefficient square before and after adjunction transpose.
Source: node displayed equations and proof Steps 2--4
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: apply the normalized coefficient/projection intertwining equation to the
shifted line and K, invert both projection maps, and tensor the compatible trace
square with the identity of K. This gives the first equation. The canonical tensor
normalization of sourceComparison includes j on both sides. Inverse-transpose the
second equation: naturality of c moves the first gamma past c, and the two
transposes agree by the first equation. The adjunction bijection is injective. -/
theorem coefficient_calculus [SmoothOfRelativeDimension d f.hom.left]
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (haTensor : SourceTensorCoherent D C f d R)
    (haShift : SourceShiftCoherent D C f d R)
    (t : Traces D C f c d R) (ht : TraceCompatible D C f c d R t)
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) (K : Cat D C Y E) :
    ((supportIso D C f c R h).hom.app ((source D C f d E).obj K) ≫
        (operation D C f c R F).F.map ((sourceComparison D C f d R h).hom.app K) ≫
        integrated D C f c d R F (t F) ((scalar D C f R h false).functor.obj K) =
      (scalar D C f R h false).functor.map (integrated D C f c d R E (t E) K)) ∧
    ((scalar D C f R h true).functor.map (gamma D C f c d R E (t E) K) ≫
        (exceptionalComparison D C f c R h).app K =
      (sourceComparison D C f d R h).hom.app K ≫
        gamma D C f c d R F (t F) ((scalar D C f R h false).functor.obj K)) := by
  sorry

/-- The componentwise coefficient equation is the equation of natural transformations.
Source: node last clause
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: extensionality reduces to coefficient_calculus, second conjunct. The
naturality is already supplied by gammaTransformation and the mate construction. -/
theorem coefficient_natural [SmoothOfRelativeDimension d f.hom.left]
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (haTensor : SourceTensorCoherent D C f d R)
    (haShift : SourceShiftCoherent D C f d R)
    (t : Traces D C f c d R) (ht : TraceCompatible D C f c d R t)
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    Functor.whiskerRight (gammaTransformation D C f c d R t E)
        (scalar D C f R h true).functor ≫ exceptionalComparison D C f c R h =
      (sourceComparison D C f d R h).hom ≫
        Functor.whiskerLeft (scalar D C f R h false).functor
          (gammaTransformation D C f c d R t F) := by
  apply NatTrans.ext
  funext K
  exact (coefficient_calculus D C f c d R haTensor haShift t ht h K).2

/-- Invertibility of the transposes implies invertibility of all coefficient mates
and exactness of the specified exceptional functors.
Source: node final conditional clause and proof Step 9
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: solve the coefficient square for b, as gamma_F times a times C_X(gamma_E^-1).
Every factor is invertible. The exact-left-adjoint/right-adjoint theorem, using the
counit-characterized shifts already recorded in operation, proves exactness of G.
The tower, unit and shift compatibility is independent of this invertibility. -/
theorem invertible_exact [SmoothOfRelativeDimension d f.hom.left]
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (haTensor : SourceTensorCoherent D C f d R)
    (haShift : SourceShiftCoherent D C f d R)
    (t : Traces D C f c d R) (ht : TraceCompatible D C f c d R t)
    (hgamma : ∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : Cat D C Y E),
      IsIso (gamma D C f c d R E (t E) K)) :
    (∀ (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)
      (K : Cat D C Y E), IsIso ((exceptionalComparison D C f c R h).app K)) ∧
    (∀ E : Padic.FiniteCoefficientFields C.l C.Qbar, (operation D C f c R E).G.IsTriangulated) := by
  have _ := haTensor
  have _ := haShift
  have _ := ht
  have _ := hgamma
  constructor
  · intro E F h K
    let := (scalar D C f R h true).commShift
    let := (scalar D C f R h false).commShift
    rw [exceptionalComparison_eq]
    infer_instance
  · intro E
    exact (operation D C f c R E).rightExact

/-- The two shift hypotheses, written after the canonical source reassociation j.
The source shifts are fixed on the signed total representatives, hence are the
canonical tensor/pullback/twist shifts. No claim that every natural map respects
shift is built into the definition.
Source: the node's explicit u and adj(u) shift assumptions
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus). -/
def TraceShiftCompatible (t : Traces D C f c d R)
    : Prop :=
  ∀ E : Padic.FiniteCoefficientFields C.l C.Qbar,
    (fun [_s : (source D C f d E).CommShift ℤ] ↦
      ∀ K : Cat D C Y E,
        (integrated D C f c d R E (t E) (K⟦(1 : ℤ)⟧) =
          (operation D C f c R E).F.map
              (((source D C f d E).commShiftIso (1 : ℤ)).hom.app K) ≫
            ((operation D C f c R E).F.commShiftIso (1 : ℤ)).hom.app
              ((source D C f d E).obj K) ≫
            (integrated D C f c d R E (t E) K)⟦(1 : ℤ)⟧') ∧
        ((operation D C f c R E).adjunction.homEquiv _ _
            (integrated D C f c d R E (t E) (K⟦(1 : ℤ)⟧)) ≫
            ((operation D C f c R E).G.commShiftIso (1 : ℤ)).hom.app K =
          ((source D C f d E).commShiftIso (1 : ℤ)).hom.app K ≫
            ((operation D C f c R E).adjunction.homEquiv _ _
              (integrated D C f c d R E (t E) K))⟦(1 : ℤ)⟧')) (_s := sourceShift D C f d E)

/-- The two claimed degree-one shift equations, with all endpoint comparisons explicit.
Source: node shift conclusion and proof Steps 7--8
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: the canonical j reassociation crosses [1] past [2d], giving
(-1)^(2d)=1. Thus the two shift assumptions are exactly the integrated and adjoint
shift squares in these coordinates, and the second gives the gamma equation.
For b, transpose its shifted component: counit shift compatibility and the shift
square of c identify this with the shifted defining transpose. Injectivity of the
adjunction bijection proves the b equation, independently of the traces. -/
theorem shift_calculus [SmoothOfRelativeDimension d f.hom.left]
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (haTensor : SourceTensorCoherent D C f d R)
    (haShift : SourceShiftCoherent D C f d R)
    (t : Traces D C f c d R)
    (hs : TraceShiftCompatible D C f c d R t) :
    (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar),
      (fun [_s : (source D C f d E).CommShift ℤ] ↦ ∀ K : Cat D C Y E,
        gamma D C f c d R E (t E) (K⟦(1 : ℤ)⟧) ≫
            ((operation D C f c R E).G.commShiftIso (1 : ℤ)).hom.app K =
          ((source D C f d E).commShiftIso (1 : ℤ)).hom.app K ≫
            (gamma D C f c d R E (t E) K)⟦(1 : ℤ)⟧') (_s := sourceShift D C f d E)) ∧
    (∀ (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)
      (K : Cat D C Y E),
      (exceptionalComparison D C f c R h).app (K⟦(1 : ℤ)⟧) ≫
          (operation D C f c R F).G.map
            (((scalar D C f R h false).functor.commShiftIso (1 : ℤ)).hom.app K) ≫
          ((operation D C f c R F).G.commShiftIso (1 : ℤ)).hom.app
            ((scalar D C f R h false).functor.obj K) =
        (scalar D C f R h true).functor.map
            (((operation D C f c R E).G.commShiftIso (1 : ℤ)).hom.app K) ≫
          ((scalar D C f R h true).functor.commShiftIso (1 : ℤ)).hom.app
            ((operation D C f c R E).G.obj K) ≫
          ((exceptionalComparison D C f c R h).app K)⟦(1 : ℤ)⟧') := by
  have _ := haTensor
  have _ := haShift
  constructor
  · intro E K
    exact (hs E K).2
  · intro E F h K
    let := (scalar D C f R h true).commShift
    let := (scalar D C f R h false).commShift
    simp only [exceptionalComparison_eq]
    have := (supportComparison D C f c R h).bShift
    convert (NatTrans.shift_app_comm
      (supportComparison D C f c R h).b.hom (1 : ℤ) K).symm using 1
    all_goals
      simp only [Functor.commShiftIso_comp_hom_app, Category.assoc, endpoint, RingStage.stage]
    all_goals rfl


end WeilConjectures.AdicTraceTranspose

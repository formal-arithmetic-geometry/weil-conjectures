/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Adic.AdicPurityObjects
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
/-! # Adic reconstruction of the specified finite smooth-purity comparisons
Source: blueprint thm-pur-adic-reconstruction, current main-20261015 snapshot.
The source is integral pullback followed by the actual coefficient twist and shift.
The target is the total inverse limit of the actual exceptional coefficient system.
All finite coefficients are those of PurityFiniteSetting.{u}, without a universe lift
of the geometric datum or a divisibility restriction on the coefficient exponent.
(blueprint: def-pur-adic-source-reduction).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

universe a b v w
section GenericSource
variable {A : Type a} [Category.{v} A] [HasShift A ℤ]
  {B : Type b} [Category.{w} B] [HasShift B ℤ]

/-- Unshift a specified line comparison using the canonical shift cancellation map.
Source: blueprint source comparison (blueprint: def-pur-adic-source-reduction). -/
def purAdicUnshiftComparison {M L : A} (s : ℤ) (e : M ≅ L⟦s⟧) : M⟦-s⟧ ≅ L :=
  (shiftFunctor A (-s)).mapIso e ≪≫
    (shiftFunctorCompIsoId A s (-s) (add_neg_cancel s)).app L

/-- Compose pullback, tensor and line comparisons before identifying concrete coefficients.
The factors are the specified maps, shifted and transported by the given exact realization.
Source: blueprint source comparison (blueprint: def-pur-adic-source-reduction). -/
def purAdicSourceComparison [MonoidalCategory A]
    (F : A ⥤ B) (G : B ⥤ B)
    (M : A) (N : B) (L T : A) (s : ℤ)
    (shift : shiftFunctor A s ⋙ F ≅ F ⋙ shiftFunctor B s)
    (p : N ≅ F.obj M) (e : G.obj (F.obj M) ≅ F.obj (M ⊗ L)) (t : L ≅ T) :
    (G.obj N)⟦s⟧ ≅ F.obj ((M ⊗ T)⟦s⟧) :=
  (shiftFunctor B s).mapIso (G.mapIso p ≪≫ e) ≪≫
    shift.symm.app _ ≪≫
    F.mapIso ((shiftFunctor A s).mapIso ((tensorLeft M).mapIso t))

/-- A composite is fixed by heterogeneous equality to each specified factor and
to their generic composite. The equations retain the maps, not just their endpoints.
Source: blueprint canonical source identification
(blueprint: def-pur-adic-source-reduction). -/
def IsPurAdicSourceComparison [MonoidalCategory A]
    (F : A ⥤ B) (G : B ⥤ B)
    (M : A) (N : B) (L T : A) (degree : ℤ)
    {P S : Type w} {R : Type v} {Q H : Type (max a w)}
    (p₀ : P) (e₀ : Q) (t₀ : R) (shift₀ : H) (c : S) : Prop :=
  ∃ (shift : shiftFunctor A degree ⋙ F ≅ F ⋙ shiftFunctor B degree)
    (p : N ≅ F.obj M) (e : F ⋙ G ≅ tensorRight L ⋙ F) (t : L ≅ T),
    HEq p p₀ ∧ HEq e e₀ ∧ HEq t t₀ ∧ HEq shift shift₀ ∧
      HEq c (purAdicSourceComparison F G M N L T degree shift p (e.app M) t)
/-- Identify every datum with its fully typed abstract source-comparison model.
All heterogeneous equalities fix the original functors, objects, tensor structure,
and canonical factors; the abstract composite therefore determines the same map.
Source: blueprint canonical source identification
(blueprint: def-pur-adic-source-reduction). -/
def HasPurAdicSourceComparisonModel
    {FX : Type (max (max (max a b) v) w)} {GX : Type (max b w)}
    {MX LX TX : Type a} {NX : Type b}
    {P S : Type w} {R : Type v} {Q H : Type (max a w)}
    {I : Type (max a v)}
    (F₀ : FX) (G₀ : GX) (M₀ : MX) (N₀ : NX) (L₀ : LX) (T₀ : TX) (degree : ℤ)
    (p₀ : P) (e₀ : Q) (t₀ : R) (shift₀ : H) (c : S) (mon₀ : I) : Prop :=
  ∃ (mon : MonoidalCategory A) (F : A ⥤ B) (G : B ⥤ B)
    (M : A) (N : B) (L T : A),
    HEq mon mon₀ ∧ HEq F F₀ ∧ HEq G G₀ ∧ HEq M M₀ ∧ HEq N N₀ ∧
    HEq L L₀ ∧ HEq T T₀ ∧
    @IsPurAdicSourceComparison A inferInstance inferInstance B inferInstance inferInstance
      mon F G M N L T degree P S R Q H p₀ e₀ t₀ shift₀ c

private theorem purAdicSourceComparisonModel_unique
    {FX : Type (max (max (max a b) v) w)} {GX : Type (max b w)}
    {MX LX TX : Type a} {NX : Type b}
    {P S : Type w} {R : Type v} {Q H : Type (max a w)}
    {I : Type (max a v)}
    (F₀ : FX) (G₀ : GX) (M₀ : MX) (N₀ : NX) (L₀ : LX) (T₀ : TX) (degree : ℤ)
    (p₀ : P) (e₀ : Q) (t₀ : R) (shift₀ : H) (c c' : S) (mon₀ : I)
    (hc : HasPurAdicSourceComparisonModel (A := A) (B := B)
      F₀ G₀ M₀ N₀ L₀ T₀ degree p₀ e₀ t₀ shift₀ c mon₀)
    (hc' : HasPurAdicSourceComparisonModel (A := A) (B := B)
      F₀ G₀ M₀ N₀ L₀ T₀ degree p₀ e₀ t₀ shift₀ c' mon₀) : c = c' := by
  obtain ⟨mon, F, G, M, N, L, T, hm, hF, hG, hM, hN, hL, hT, hc⟩ := hc
  obtain ⟨mon', F', G', M', N', L', T', hm', hF', hG', hM', hN', hL', hT', hc'⟩ := hc'
  have hmon : mon' = mon := eq_of_heq (hm'.trans hm.symm)
  have hFF : F' = F := eq_of_heq (hF'.trans hF.symm)
  have hGG : G' = G := eq_of_heq (hG'.trans hG.symm)
  have hMM : M' = M := eq_of_heq (hM'.trans hM.symm)
  have hNN : N' = N := eq_of_heq (hN'.trans hN.symm)
  have hLL : L' = L := eq_of_heq (hL'.trans hL.symm)
  have hTT : T' = T := eq_of_heq (hT'.trans hT.symm)
  subst mon' F' G' M' N' L' T'
  obtain ⟨shift, p, e, t, hp, he, ht, hs, hc⟩ := hc
  obtain ⟨shift', p', e', t', hp', he', ht', hs', hc'⟩ := hc'
  have hpp : p' = p := eq_of_heq (hp'.trans hp.symm)
  have hee : e' = e := eq_of_heq (he'.trans he.symm)
  have htt : t' = t := eq_of_heq (ht'.trans ht.symm)
  have hss : shift' = shift := eq_of_heq (hs'.trans hs.symm)
  subst p' e' t' shift'
  exact eq_of_heq (hc.trans hc'.symm)

private theorem purAdicSourceComparisonModel_existsUnique [mon : MonoidalCategory A]
    (F : A ⥤ B) (G : B ⥤ B) (M : A) (N : B) (L T : A) (s : ℤ)
    (shift : shiftFunctor A s ⋙ F ≅ F ⋙ shiftFunctor B s)
    (p : N ≅ F.obj M) (e : F ⋙ G ≅ tensorRight L ⋙ F) (t : L ≅ T)
    (S : Type w) (hS : S = ((G.obj N)⟦s⟧ ≅ F.obj ((M ⊗ T)⟦s⟧))) :
    ∃! c : S, HasPurAdicSourceComparisonModel (A := A) (B := B)
      F G M N L T s p e t shift c mon := by
  subst S
  let c := purAdicSourceComparison F G M N L T s shift p (e.app M) t
  have hc : HasPurAdicSourceComparisonModel (A := A) (B := B)
      F G M N L T s p e t shift c mon :=
    ⟨mon, F, G, M, N, L, T, HEq.rfl, HEq.rfl, HEq.rfl,
      HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, shift, p, e, t,
      HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact purAdicSourceComparisonModel_unique _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc' hc

end GenericSource

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

section KanShift
variable {C₀ : Type a} [Category.{v} C₀] [HasShift C₀ ℤ]
  {D₀ : Type b} [Category.{w} D₀] [HasShift D₀ ℤ]
  {H₀ : Type u} [Category H₀] [HasShift H₀ ℤ]
  (L₀ : C₀ ⥤ D₀) [L₀.CommShift ℤ] (F₀ : C₀ ⥤ H₀) [F₀.CommShift ℤ]
  (T₀ : D₀ ⥤ H₀) (α : L₀ ⋙ T₀ ⟶ F₀)
  [T₀.IsRightKanExtension α] [L₀.HasPointwiseRightKanExtension F₀]

private theorem purAdicKanShift (s : ℤ) :
    ∃! e : shiftFunctor D₀ s ⋙ T₀ ≅ T₀ ⋙ shiftFunctor H₀ s,
      ∀ P : C₀, e.hom.app (L₀.obj P) ≫ (shiftFunctor H₀ s).map (α.app P) =
        T₀.map ((L₀.commShiftIso s).inv.app P) ≫ α.app (P⟦s⟧) ≫
          (F₀.commShiftIso s).hom.app P := by
  let β := (Functor.associator L₀ (shiftFunctor D₀ s) T₀).inv ≫
    Functor.whiskerRight (L₀.commShiftIso s).inv T₀ ≫
    (Functor.associator (shiftFunctor C₀ s) L₀ T₀).hom ≫
    Functor.whiskerLeft (shiftFunctor C₀ s) α
  have hpre := (Functor.isRightKanExtension_iff_precomp T₀ (shiftFunctor C₀ s) α).mp inferInstance
  have hβ : (shiftFunctor D₀ s ⋙ T₀).IsRightKanExtension β :=
    (Functor.isRightKanExtension_iff_postcomp₁ (shiftFunctor D₀ s)
      (L₀.commShiftIso s).symm
      ((Functor.associator (shiftFunctor C₀ s) L₀ T₀).hom ≫
        Functor.whiskerLeft (shiftFunctor C₀ s) α)).mp hpre
  let β' := β ≫ (F₀.commShiftIso s).hom
  have hβ' : (shiftFunctor D₀ s ⋙ T₀).IsRightKanExtension β' :=
    (Functor.isRightKanExtension_iff_of_iso₂ β β' (F₀.commShiftIso s)
      (Iso.refl _) (by simp [β'])).mp hβ
  let δ := (Functor.associator L₀ T₀ (shiftFunctor H₀ s)).inv ≫
    Functor.whiskerRight α (shiftFunctor H₀ s)
  have hδ : (T₀ ⋙ shiftFunctor H₀ s).IsRightKanExtension δ := inferInstance
  let e := Functor.rightKanExtensionUnique (shiftFunctor D₀ s ⋙ T₀) β'
    (T₀ ⋙ shiftFunctor H₀ s) δ
  refine ⟨e, ?_, ?_⟩
  · intro P
    simpa [e, δ, β', β] using
      (Functor.liftOfIsRightKanExtension_fac_app (T₀ ⋙ shiftFunctor H₀ s) δ
        (shiftFunctor D₀ s ⋙ T₀) β' P)
  · intro e' he'
    apply Iso.ext
    apply Functor.hom_ext_of_isRightKanExtension (T₀ ⋙ shiftFunctor H₀ s) δ
    ext P
    simp only [δ, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
    change e'.hom.app (L₀.obj P) ≫ (shiftFunctor H₀ s).map (α.app P) =
      e.hom.app (L₀.obj P) ≫ (shiftFunctor H₀ s).map (α.app P)
    rw [he']
    symm
    simpa [e, δ, β', β] using
      (Functor.liftOfIsRightKanExtension_fac_app (T₀ ⋙ shiftFunctor H₀ s) δ
        (shiftFunctor D₀ s ⋙ T₀) β' P)
end KanShift

section ReductionShift
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) (n : ℕ) (s : ℤ)

/-- The full derived-counit square fixing reduction's shift comparison.
Source: blueprint canonical source reduction
(blueprint: def-pur-adic-source-reduction). -/
def IsPurAdicReductionShift
    (e : shiftFunctor (DerivedCategory (scalarReductionSource l E W)) s ⋙
      scalarReductionDerivedExtension l E W n ≅
      scalarReductionDerivedExtension l E W n ⋙
        shiftFunctor (DerivedCategory (scalarReductionTarget l E W n)) s) : Prop :=
  ∀ P : HomotopyCategory (scalarReductionSource l E W) (.up ℤ),
    e.hom.app (DerivedCategory.Qh.obj P) ≫
      (shiftFunctor _ s).map ((scalarReductionCounit l E W n).app P) =
    (scalarReductionDerivedExtension l E W n).map
        ((DerivedCategory.Qh.commShiftIso s).inv.app P) ≫
      (scalarReductionCounit l E W n).app (P⟦s⟧) ≫
      (((scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).commShiftIso s).hom.app P

/-- Derived scalar extension has the unique shift comparison compatible with its
universal counit. Source: blueprint canonical source reduction
(blueprint: def-pur-adic-source-reduction).
Proof: shift commutes with termwise scalar extension and both localizations.
Shifting the universal left-derived pair therefore gives another universal pair
for the shifted ordinary functor. Its unique counit-compatible comparison is
invertible, with inverse obtained by shifting back. The universal property of
left derivation gives the displayed square on every homotopy complex and its
uniqueness. On K-flat representatives this is the ordinary termwise shift map. -/
theorem purAdicReductionShift_existsUnique :
    ∃! e : shiftFunctor (DerivedCategory (scalarReductionSource l E W)) s ⋙
      scalarReductionDerivedExtension l E W n ≅
      scalarReductionDerivedExtension l E W n ⋙
        shiftFunctor (DerivedCategory (scalarReductionTarget l E W n)) s,
      IsPurAdicReductionShift l E W n s e := by
  let : (scalarReductionExtension l E W n).Additive :=
    scalarReductionExtensionAdditive l E W n
  let T := scalarReductionDerivedExtension l E W n
  let ε := scalarReductionCounit l E W n
  let F := (scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh
  have hT : T.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (scalarReductionSource l E W) (.up ℤ)) :=
    (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.1
  have : T.IsRightKanExtension ε := hT.isRightKanExtension
  have : F.HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (scalarReductionSource l E W) (.up ℤ)) :=
    (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  have : DerivedCategory.Qh.HasPointwiseRightKanExtension F :=
    Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor F
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (scalarReductionSource l E W) (.up ℤ))
  exact purAdicKanShift DerivedCategory.Qh F T ε s

/-- The canonical shift comparison of the actual reduction, fixed by its full counit
square. Source: blueprint canonical source reduction
(blueprint: def-pur-adic-source-reduction). -/
@[no_expose] def purAdicReductionShift :
    shiftFunctor (DerivedCategory (scalarReductionSource l E W)) s ⋙
      scalarReductionDerivedExtension l E W n ≅
      scalarReductionDerivedExtension l E W n ⋙
        shiftFunctor (DerivedCategory (scalarReductionTarget l E W n)) s :=
  (purAdicReductionShift_existsUnique l E W n s).choose
end ReductionShift

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- Complete normalization of the finite source identification by its actual
pullback presentation, scalar-unit tensor comparison, root comparison and shift maps.
The heterogeneous factor equations allow the same canonical maps to be expressed
in the recorded endpoint coordinates without a second definitional-equality check.
Source: blueprint canonical source identification
(blueprint: def-pur-adic-source-reduction). -/
def IsPurAdicFiniteSourceIdentification
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ)
    (e :
      ((finiteComplexTwist C.l E X n (d : ℤ)).obj
        ((finiteDerivedPullback C.l E n f).obj
          ((scalarReductionDerivedExtension C.l E Y n).obj K)))⟦2 * (d : ℤ)⟧ ≅
        (purAdicFiniteArrow D C E f d K hK n).left) : Prop :=
  HasPurAdicSourceComparisonModel
    (A := DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (n + 1))))))
    (B := DerivedCategory (scalarReductionTarget C.l E X n))
    (Scheme.sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing C.l E (n + 1))).functor
    (finiteComplexTwist C.l E X n (d : ℤ))
    ((ProEtale.sfFixedDerivedPullback
      (Padic.coefficientExtensionRing C.l E (n + 1)) f).obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing C.l E (n + 1))).inverse.obj
            ((scalarReductionDerivedExtension C.l E Y n).obj K)))
    ((finiteDerivedPullback C.l E n f).obj
      ((scalarReductionDerivedExtension C.l E Y n).obj K))
    ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteTateProSheaf C.l E n X d))
    (((purAdicFiniteSetting D C E n).diagonalTwist X d)⟦-(2 * (d : ℤ))⟧) (2 * (d : ℤ))
    ((purAdicFinitePullbackPresentation C.l E f n).app
      ((scalarReductionDerivedExtension C.l E Y n).obj K))
    (adicPurityDerivedFiniteTensor C.l E n X d)
    (purAdicUnshiftComparison (2 * (d : ℤ))
      (adicPurityProDiagonal C.l E n X (purAdicCoefficientUnit D C X) n
        ((purAdicFiniteSetting D C E n).diagonalExponent_isUnit (X ↘ Spec (.of D.k)))
        (purAdicFiniteSetting D C E n).diagonalExponent_annihilates d)).symm
    ((adicPurityFiniteRealization C.l E n X).mapDerivedCategory.commShiftIso
      (2 * (d : ℤ))) e
    (inferInstance : MonoidalCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (n + 1)))))))

set_option linter.unusedSectionVars false in
/-- The specified source composite has exactly the recorded finite-purity endpoint.
Its complete factor equations fix the actual comparison, not just its isomorphism class.
Source: blueprint thm-pur-adic-reconstruction, canonical source identification
(blueprint: def-pur-adic-source-reduction).
Proof: unfold the source of smoothPurityMap and the intrinsic pullback presentation.
The finite setting has exponent n+1, so its diagonal twist is the exact root power used
in the specified root comparison. The two finite rings are the same lifted quotient. Thus the
generic composite has the displayed endpoints. Transport it along these
identifications. Heterogeneous equality to each fixed factor and their composite determines
the comparison uniquely; proof irrelevance removes the finite-Tor and exactness witnesses. -/
theorem purAdicFiniteSourceIdentification_existsUnique
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    ∃! e :
    ((finiteComplexTwist C.l E X n (d : ℤ)).obj
      ((finiteDerivedPullback C.l E n f).obj
        ((scalarReductionDerivedExtension C.l E Y n).obj K)))⟦2 * (d : ℤ)⟧ ≅
      (purAdicFiniteArrow D C E f d K hK n).left,
      IsPurAdicFiniteSourceIdentification D C E f d K hK n e := by
  unfold IsPurAdicFiniteSourceIdentification
  apply purAdicSourceComparisonModel_existsUnique
  dsimp only [purAdicFiniteArrow, Arrow.mk_left, PurityFiniteSetting.smoothPurityMap,
    PurityFiniteSetting.smoothPurityReassociation, purAdicFiniteSetting,
    PurityFiniteSetting.smoothPurityPullback, PurityFiniteSetting.smoothPurityTensor,
    ProEtale.derivedTensor, curriedTensor]
  rfl

/-- The finite source identification, fixed by equality with the canonical composite
of pullback presentation, scalar-unit tensor realization, root comparison and shift maps.
Source: blueprint thm-pur-adic-reconstruction, canonical source identification
(blueprint: def-pur-adic-source-reduction). -/
@[no_expose] def purAdicFiniteSourceIdentification
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    ((finiteComplexTwist C.l E X n (d : ℤ)).obj
      ((finiteDerivedPullback C.l E n f).obj
        ((scalarReductionDerivedExtension C.l E Y n).obj K)))⟦2 * (d : ℤ)⟧ ≅
      (purAdicFiniteArrow D C E f d K hK n).left :=
  (purAdicFiniteSourceIdentification_existsUnique D C E f d K hK n).choose

/-- b^U_n is the canonical reduction of the actual integral source. Its factors are
exact shift commutation, the root-normalized tensor/restriction mate, the actual
pullback Roos projection mate, and the specified finite source identification.
Source: blueprint thm-pur-adic-reconstruction, reduction equation
(blueprint: def-pur-adic-source-reduction). -/
@[no_expose] def purAdicSourceReduction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    (scalarReductionDerivedExtension C.l E X n).obj (purAdicSource D C E f d K) ⟶
      (purAdicFiniteArrow D C E f d K hK n).left :=
  (purAdicReductionShift C.l E X n (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (adicPurityTwistReduction C.l E n X d ((integralDerivedPullback C.l E f).obj K) ≫
        (finiteComplexTwist C.l E X n (d : ℤ)).map
          (purAdicPullbackReduction C.l E f K n)) ≫
    (purAdicFiniteSourceIdentification D C E f d K hK n).hom

end WeilConjectures

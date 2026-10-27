# WeilConjectures.CoefPairingSystem and the coefficient pairing constructions

## Reason

Separate the existing construction interface from its assembly theorem so that the
Hom comparison and compactification comparison can be proved in independent modules
without an import cycle. This is structural extraction, not a timeout workaround.
No definition, instance proof, signature, visibility or mathematical meaning changes.
The original module publicly reexports the extracted module and preserves its old
public import closure. The direct frame dinaturality proof is a new proved theorem.

## Old

File: lean/Sheaf/SixFunctors/CoefTowerEvaluationPairing.lean.
The following existing declaration block is relocated verbatim:

```lean
/-- The strict module-tower category used by the fixed trace target.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev coefPairingModules := ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)

/-- Module towers are Grothendieck abelian, without transition-surjectivity hypotheses.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: use module-valued presheaves on the small poset of natural numbers.
Filtered colimits and exactness are levelwise; coproducts of the free representables
form a generator. This is also the trivial-topology sheaf presentation. -/
@[instance] theorem coefPairingModules_grothendieck :
    IsGrothendieckAbelian.{u + 1} (coefPairingModules l E) := by
  exact { ab5OfSize := ⟨fun _ _ _ ↦ inferInstance⟩ }

/-- Functorial flat resolutions for the pointwise tensor of strict module towers.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: take the coproduct of free module-valued representables. Each value is free,
so tensor with it preserves finite limits levelwise. The free representables form
a flat separator. Apply the functorial-flat-resolution theorem for flat separators. -/
@[instance] theorem coefPairingModules_flat :
    Abelian.HasFunctorialFlatResolution (coefPairingModules l E) := by
  obtain ⟨G, hG, hflat⟩ :=
    Abelian.exists_flat_separator_of_hasFunctorialFlatResolution
      (ModuleCat.{u + 1} (coefTraceRing l E))
  apply Abelian.hasFunctorialFlatResolution_of_flat_separator _
    (Presheaf.isSeparator ℕ (S := fun _ : ULift.{u + 1} Unit ↦ G) (by
      intro X Y f g h
      exact hG.def f g (fun k ↦ h G ⟨ULift.up ()⟩ k)))
  apply ObjectProperty.flat_coproduct
  rintro ⟨n, _⟩
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have (m : ℕᵒᵖ) :
      PreservesFiniteLimits (tensorLeft ((Presheaf.freeYoneda n G).obj m)) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).1
      (ObjectProperty.prop_of_iso ObjectProperty.flat
        (Sigma.reindex (Equiv.ulift : ULift.{u + 1} _ ≃ _) _)
        (ObjectProperty.flat_coproduct _ fun _ ↦ hflat))
  exact preservesFiniteLimits_of_evaluation _ fun m ↦
    inferInstanceAs (PreservesFiniteLimits
      ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj m ⋙
        tensorLeft ((Presheaf.freeYoneda n G).obj m)))

/-- The ordinary unbounded derived category of strict R-module towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev coefPairingDerived := DerivedCategory (coefPairingModules l E)

/-- The derived tensor of towers, constructed by the existing K-flat localization.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingTensor : coefPairingDerived l E × coefPairingDerived l E ⥤
    coefPairingDerived l E := MonoidalCategory.tensor _

/-- Sections after actual quotient-scalar restriction, retaining the strict tower.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingSections (W : Scheme.{u}) :
    coefficientSequenceDerived.{u, u} l E W ⥤ coefPairingDerived l E :=
  (coefTraceSystemRestriction l E W).mapDerivedCategory ⋙
    (coefTraceSections l E W).rightDerivedFunctor

/-- The contravariant Hom tower. Scalar adjunction identifies this with termwise
Hom from K into a simultaneous K-injective resolution of Res Q.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingHom (X : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E X)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ) :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤ coefPairingDerived l E :=
  S.reduction.op ⋙ Prod.sectL _ (coefTraceInput l E X Q) ⋙
    coefficientSequenceInternalHom l E X ⋙ coefPairingSections l E X

/-- The covariant compact-support reduction tower with separately derived proper
image and point sections, using the same compactification as B_omega.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingSupport (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (S : CoefficientDerivedSystemCalculus l E X) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤ coefPairingDerived l E :=
  S.reduction ⋙ coefTraceCompactSections l E (finiteDualizingCompactification D X)


end WeilConjectures

namespace CategoryTheory

universe b c d v₁ v₂ v₃ v₄

/-- The adjoint-evaluation construction used on both the sequence site and its finite
slices. The functors J, P, R and RX are supplied independently: exact open extension,
separately derived proper image, point sections and source sections, respectively.
No invertibility of a proper or sections projection mate is included.
Source: blueprint proof steps 5--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
structure CoefPairingFrame
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (J : A ⥤ B) (P : B ⥤ C) (R : C ⥤ D) (RX : A ⥤ D) where
  /-- Derived restriction to the open subsite. -/
  jstar : B ⥤ A
  /-- Exact open extension is left adjoint to open restriction. -/
  openAdjunction : J ⊣ jstar
  /-- Derived pullback along the proper part. -/
  pstar : C ⥤ B
  /-- The ringed derived pullback/direct-image adjunction. -/
  properAdjunction : pstar ⊣ P
  /-- Derived extension of the constant base scalars after point pullback. -/
  sstar : D ⥤ C
  /-- Point sections, including scalar restriction, are its right adjoint. -/
  sectionsAdjunction : sstar ⊣ R
  /-- Pullback composition identifies source sections with this right adjoint. -/
  sourceAdjunction : sstar ⋙ pstar ⋙ jstar ⊣ RX
  /-- Canonical tensor pullback comparison along p. -/
  properTensor : TC ⋙ pstar ≅ pstar.prod pstar ⋙ TB
  /-- Canonical tensor pullback comparison along point sections and scalar extension. -/
  sectionsTensor : TD ⋙ sstar ≅ sstar.prod sstar ⋙ TC
  /-- Canonical tensor pullback along open restriction. -/
  restrictionTensor : TB ⋙ jstar ≅ jstar.prod jstar ⋙ TA
  /-- The inverse-open-projection arrow is the actual counit mate. -/
  openTensor : ∀ (L : B) (M : A), J.obj (TA.obj (jstar.obj L, M)) ≅ TB.obj (L, J.obj M)
  /-- Its adjunct is insertion into j* j!, following inverse tensor comparison. -/
  openTensor_adjunct : ∀ (L : B) (M : A),
    openAdjunction.homEquiv _ _ (openTensor L M).hom =
      TA.map (Prod.mkHom (𝟙 (jstar.obj L)) (openAdjunction.unit.app M)) ≫
        restrictionTensor.inv.app (L, J.obj M)

namespace CoefPairingFrame

variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {TA : A × A ⥤ A} {TB : B × B ⥤ B} {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame TA TB TC TD J P R RX)

/-- The left-oriented projection mate, obtained by transposing tensor of the counit.
It is the usual projection mate conjugated by the canonical graded symmetries.
Source: blueprint steps 7--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def leftMate {V : Type a} {W : Type b} [Category.{v₁} V] [Category.{v₂} W]
    (TV : V × V ⥤ V) (TW : W × W ⥤ W) (L : V ⥤ W) (G : W ⥤ V)
    (adj : L ⊣ G) (mu : TV ⋙ L ≅ L.prod L ⋙ TW) (H : V) (M : W) :
    TV.obj (H, G.obj M) ⟶ G.obj (TW.obj (L.obj H, M)) :=
  let flip := (Functor.flipping (C := V) (D := V) (E := W)).functor
  ((adj.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TW).flip) (T_D := (Functor.curryObj TV).flip)
    (flip.map (Functor.curry.map mu.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp L L TW)).hom)).app M).app H

/-- The composite of the point-sections mate, proper mate and open tensor inverse.
All three arrows live in the derived system categories before finite evaluation.
Source: blueprint steps 5--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def projection (H : D) (M : A) :
    TD.obj (H, R.obj (P.obj (J.obj M))) ⟶
      R.obj (P.obj (J.obj (TA.obj (F.jstar.obj (F.pstar.obj (F.sstar.obj H)), M)))) :=
  leftMate TD TC F.sstar R F.sectionsAdjunction F.sectionsTensor H (P.obj (J.obj M)) ≫
    R.map (leftMate TC TB F.pstar P F.properAdjunction F.properTensor
      (F.sstar.obj H) (J.obj M)) ≫
    R.map (P.map (F.openTensor (F.pstar.obj (F.sstar.obj H)) M).inv)

/-- Evaluation after the source-sections counit, followed by compact support.
This formula includes the scalar-balancing map through sstar. It ends at F(Q);
no exceptional counit or trace is composed into it.
Source: blueprint steps 6--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def pairing {HA : Aᵒᵖ × A ⥤ A} (S : WeilConjectures.CoefficientClosedStructure HA)
    (tensor_eq : S.tensor = TA) (M Q : A) :
    TD.obj (RX.obj (HA.obj (op M, Q)), R.obj (P.obj (J.obj M))) ⟶
      R.obj (P.obj (J.obj Q)) :=
  F.projection (RX.obj (HA.obj (op M, Q))) M ≫
    R.map (P.map (J.map
      (TA.map (Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q))) (𝟙 M)) ≫
        eqToHom (congrArg (fun T ↦ T.obj (HA.obj (op M, Q), M)) tensor_eq.symm) ≫
          S.evaluation M Q)))

end CoefPairingFrame
end CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary final-object sections are additive with the fixed integral scalar action.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: sections add pointwise and restriction of scalars changes no addition of maps. -/
@[instance] theorem coefPairingOrdinarySections_additive (W : Scheme.{u}) :
    ((sheafSections (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 W)))).Additive where
  map_add := rfl

/-- Ordinary sections with the fixed constant integral action, prior to deriving.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingOrdinaryIntegralSections (W : Scheme.{u}) :
    scalarReductionSource.{u, u} l E W ⥤ ModuleCat.{u + 1} (coefTraceRing l E) :=
  coefTraceConstantScalars l E W ⋙
    (sheafSections (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 W)))

/-- Additivity of ordinary integral sections follows from its two factors.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
instance coefPairingOrdinaryIntegralSections_additive (W : Scheme.{u}) :
    (coefPairingOrdinaryIntegralSections l E W).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

/-- The component differential vanishes outside the cochain shape.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: evaluate the natural transformation at each tower index. Its component is
(F.obj n).d i j, which is zero by the shape axiom of that complex. Natural
transformations are equal when all their components are equal. -/
theorem coefPairingComplexTower_shape {A : Type a} [Category.{v} A]
    [HasZeroMorphisms A] (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j : ℤ)
    (_h : ¬ (ComplexShape.up ℤ).Rel i j) :
    Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) i j) = 0 := by
  ext n
  dsimp
  change (F.obj n).d i j = 0
  exact F.obj n |>.shape i j _h

/-- The reassembled differential squares to zero.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: evaluate at n. The composite becomes (F.obj n).d i j followed by
(F.obj n).d j k, which is zero by d_comp_d of the component complex.
Extensionality of natural transformations proves the displayed identity. -/
theorem coefPairingComplexTower_d_comp_d {A : Type a} [Category.{v} A]
    [HasZeroMorphisms A] (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j k : ℤ) :
    Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) i j) ≫
      Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) j k) = 0 := by
  ext n
  dsimp
  change (F.obj n).d i j ≫ (F.obj n).d j k = 0
  exact F.obj n |>.d_comp_d i j k

/-- Reassemble a strict functor to complexes as a complex of strict towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingComplexTower {A : Type a} [Category.{v} A]
    [HasZeroMorphisms A] (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := F ⋙ HomologicalComplex.eval A (.up ℤ) i
  d i j := Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) i j)
  shape i j h := coefPairingComplexTower_shape F i j h
  d_comp_d' i j k _ _ := coefPairingComplexTower_d_comp_d F i j k

/-- The termwise global Hom complex from P to a simultaneous completed-module tower I.
Its arrows are postcomposition by the actual transitions of I, with the usual Hom
complex differential. It retains the integral scalar action before localization.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingHomComplex (X : Scheme.{u})
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E X) ℤ) :
    CochainComplex (coefPairingModules l E) ℤ :=
  coefPairingComplexTower
    (I.asFunctor ⋙
      (homComplexFunctor.{u + 1, u, u + 1, u + 1}
        (R := completedIntegralCommRingSheafUnrestricted l E X)).obj (op P) ⋙
      (coefPairingOrdinaryIntegralSections l E X).mapHomologicalComplex (.up ℤ))

/-- R-linear derived sections of completed-module sheaves.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingIntegralSections (W : Scheme.{u}) :
    DerivedCategory (scalarReductionSource.{u, u} l E W) ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (coefTraceConstantScalars l E W).mapDerivedCategory ⋙
    ((sheafSections (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 W)))).rightDerivedFunctor

/-- Finite sections with the actual quotient-induced R action.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteSections (W : Scheme.{u}) (n : ℕ) :
    normalizedDVRDerived.{u, u} l E W n ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  scalarReductionDerivedRestriction l E W n ⋙ coefPairingIntegralSections l E W

/-- Finite Hom before forgetting its quotient scalar action.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteHom (X : Scheme.{u}) (n : ℕ) (N : normalizedDVRDerived.{u, u} l E X n) :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (scalarReductionDerivedExtension l E X n).op ⋙ Prod.sectL _ N ⋙
    coefficientFiniteInternalHom l E X n ⋙ coefPairingFiniteSections l E X n


/-- The first finite Hom description, over the completed coefficient ring R_X.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingIntegralHom (X : Scheme.{u}) (n : ℕ)
    (N : normalizedDVRDerived.{u, u} l E X n) :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  Prod.sectL _ ((scalarReductionDerivedRestriction l E X n).obj N) ⋙
    coefficientIntegralInternalHom l E X ⋙ coefPairingIntegralSections l E X

/-- The existing Grothendieck instance on the actual quotient sequence site.
Source: Stacks 079P (blueprint: lem-coef-tower-evaluation-pairing). -/
instance coefPairingSequenceGrothendieck (W : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules.{u, u} l E W) :=
  (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).1

/-- Ordinary quotient-ring open extension and proper image, together with the actual
scalar-restriction comparisons. These are witnesses of the fixed ringed construction,
not hypotheses on K. The proper image is derived after open extension.
Source: blueprint steps 1 and 4--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
structure CoefPairingSystem {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (S : CoefficientDerivedSystemCalculus l E X) where
  /-- The existing K-flat tensor-Hom data on the compactification. -/
  compactTensors : CoefficientDerivedSystemTensors l E c.Z
  /-- The existing K-flat tensor-Hom data on the base. -/
  baseTensors : CoefficientDerivedSystemTensors l E Y
  /-- Exact module-sheaf extension by zero on the quotient sequence site. -/
  openModules : coefficientSequenceModules.{u, u} l E X ⥤
    coefficientSequenceModules.{u, u} l E c.Z
  /-- The separately derived ordinary module-sheaf direct image. -/
  properModules : coefficientSequenceModules.{u, u} l E c.Z ⥤
    coefficientSequenceModules.{u, u} l E Y
  [openAdditive : openModules.Additive]
  [openLimits : PreservesFiniteLimits openModules]
  [openColimits : PreservesFiniteColimits openModules]
  [properAdditive : properModules.Additive]
  /-- The underlying open operation is the recorded actual extension by zero. -/
  openRestriction : openModules ⋙ coefTraceSystemRestriction l E c.Z ≅
    coefTraceSystemRestriction l E X ⋙ coefTraceOpen l E c.i
  /-- The underlying proper operation is the recorded actual direct image. -/
  properRestriction : properModules ⋙ coefTraceSystemRestriction l E Y ≅
    coefTraceSystemRestriction l E c.Z ⋙ coefTracePush l E c.g
  /-- Ambient adjunctions, canonical pullback tensor comparisons and open tensor mate. -/
  frame : CoefPairingFrame S.systemClosed.tensor compactTensors.systemClosed.tensor
    baseTensors.systemClosed.tensor (coefPairingTensor l E)
    openModules.mapDerivedCategory properModules.rightDerivedFunctor
    (coefPairingSections l E Y) (coefPairingSections l E X)
  /-- The direct-image composition comparison after exact scalar restriction. -/
  compactSections : openModules.mapDerivedCategory ⋙ properModules.rightDerivedFunctor ⋙
    coefPairingSections l E Y ≅ coefTraceCompactSections l E c

attribute [instance] CoefPairingSystem.openAdditive CoefPairingSystem.openLimits
  CoefPairingSystem.openColimits CoefPairingSystem.properAdditive

/-- The actual system pairing: two projection mates and evaluation, transported by the
scalar-restriction/direct-image comparison to the already fixed compact-support tower.
Source: blueprint steps 6--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def CoefPairingSystem.beta {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
    {S : CoefficientDerivedSystemCalculus l E X} (G : CoefPairingSystem l E c S)
    (M Q : coefficientSequenceDerived.{u, u} l E X) :
    (coefPairingTensor l E).obj
        ((coefPairingSections l E X).obj ((coefficientSequenceInternalHom l E X).obj (op M, Q)),
          (coefTraceCompactSections l E c).obj M) ⟶
      (coefTraceCompactSections l E c).obj Q :=
  (coefPairingTensor l E).map (Prod.mkHom (𝟙 _) (G.compactSections.inv.app M)) ≫
    G.frame.pairing S.systemClosed rfl M Q ≫ G.compactSections.hom.app Q

/-- The finite compact-support/sections functor, with quotient restriction to R.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteSupport {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (n : ℕ) :
    normalizedDVRDerived.{u, u} l E X n ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
    coefPairingFiniteSections l E Y n

/-- The ambient finite projection/evaluation frame, using the recorded intrinsic open
extension, proper direct image and quotient-linear point sections. Its section mate
includes balancing from R to A_n; neither projection mate is assumed invertible.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev CoefPairingFiniteFrame {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E c S) (n : ℕ) :=
  CoefPairingFrame (S.finiteClosed n).tensor (G.compactTensors.finiteClosed n).tensor
    (G.baseTensors.finiteClosed n).tensor
    (MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))))
    (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
    (proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E (n + 1)))
    (coefPairingFiniteSections l E Y n) (coefPairingFiniteSections l E X n)

/-- The finite ambient projection followed by evaluation, before trace.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteBeta {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E c S) (n : ℕ) (F : CoefPairingFiniteFrame l E c S G n)
    (M Q : normalizedDVRDerived.{u, u} l E X n) :
    (coefPairingFiniteSections l E X n).obj
        ((coefficientFiniteInternalHom l E X n).obj (op M, Q)) ⊗
          (coefPairingFiniteSupport l E c n).obj M ⟶
      (coefPairingFiniteSupport l E c n).obj Q :=
  F.pairing (S.finiteClosed n) rfl M Q

variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite compact-support functor on integral inputs, with its actual reductions.
Source: blueprint statement C_n (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteC (n : ℕ) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  scalarReductionDerivedExtension l E X n ⋙
    coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n
```

The old public imports were:

```lean
public import Sheaf.SixFunctors.CoefTowerTraceRectification
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
```

## New

The exact declaration block under Old now lives at
lean/Sheaf/SixFunctors/CoefTowerEvaluationPairingData.lean, with the same public
imports. Its declaration text, including all data bodies and existing proofs,
is byte-identical. The original file keeps coefTowerEvaluationPairing with its
exact signature, and its public import is:

```lean
public import Sheaf.SixFunctors.CoefTowerEvaluationPairingData
```

The split comparison modules publicly import only the data, with proof dependencies
imported privately. No target statement changes and no changed definition requires
a target-meaning review.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | B4 | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | D2 | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | B6 | Same public declarations and imports through reexport; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed in local snapshot | Same public declarations and imports through reexport; no adaptation. |

## Status

landed 20261025T123614-L-1883187 2026-10-25 (merge of deliver/Q9/Sheaf.SixFunctors.CoefTowerEvaluationPairing)

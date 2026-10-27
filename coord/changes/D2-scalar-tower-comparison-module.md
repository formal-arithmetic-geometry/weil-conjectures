# ScalarExtensionTower comparison construction module

## Reason

The completed strict-square and composition proofs made the original monolithic file
exceed the 60 s checking limit. Profiling identified the repeated checking of the
large functor endpoints and proof constructions. Local unfolding changes, an equivalent
HEq predicate representation, and single-field predicate structures did not improve the
runtime; those representation changes were reverted. Following the prompt's step 3a,
separate the self-contained normalized-comparison construction from the coherence proofs.
No declaration is withdrawn: every moved public declaration is re-exported by the
original module, with its signature, attributes and definition body preserved.
The normalized construction has an ownership node; this adds no mathematics or holes.

## Old

The following unchanged construction was in
`Sheaf.Paper.ScalarExtensionTowerCoherence` (including its proved private helpers):

```lean
attribute [local semireducible] coefficientTotalTensor in
/-- The sequence site has the small pro-etale site's original size.
Source: Stacks 0941 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance (priority := 3000) sequenceSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) :=
  coefficientSequenceEssentiallySmall.{u, 0} W

/-- The original small pro-etale site, with object size u+1 and Hom size u.
Source: blueprint size convention (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance (priority := 3000) siteSmall (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _


/-- The scalar-first route, abstracted over its categories.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-scalar-extension-tower-data). -/
def leftRouteCore {C D A B : Type*}
    [Category C] [Category D] [Category A] [Category B]
    (T : C × C ⥤ C) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (F : C ⥤ D) (G : C ⥤ A) (H : D ⥤ B) (K : A ⥤ B)
    (k : F ⋙ H ≅ G ⋙ K) (s : T ⋙ G ≅ G.prod G ⋙ TA)
    (c : TA ⋙ K ≅ K.prod K ⋙ TB) :
    T ⋙ F ⋙ H ≅ G.prod G ⋙ K.prod K ⋙ TB :=
  Functor.isoWhiskerLeft T k ≪≫ Functor.isoWhiskerRight s K ≪≫
    Functor.isoWhiskerLeft (G.prod G) c

/-- The pullback-first route, abstracted over its categories.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-scalar-extension-tower-data). -/
def rightRouteCore {C D A B : Type*}
    [Category C] [Category D] [Category A] [Category B]
    (T : C × C ⥤ C) (TD : D × D ⥤ D) (TB : B × B ⥤ B)
    (F : C ⥤ D) (G : C ⥤ A) (H : D ⥤ B) (K : A ⥤ B)
    (k : F ⋙ H ≅ G ⋙ K) (s : TD ⋙ H ≅ H.prod H ⋙ TB)
    (c : T ⋙ F ≅ F.prod F ⋙ TD) :
    T ⋙ F ⋙ H ≅ G.prod G ⋙ K.prod K ⋙ TB :=
  Functor.isoWhiskerRight c H ≪≫ Functor.isoWhiskerLeft (F.prod F) s ≪≫
    Functor.isoWhiskerRight (NatIso.prod k k) TB


/-- The unit square for a functor and two specified action unitors.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def UnitSquare {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (U : C ⥤ C) (V : D ⥤ D)
    (k : F ⋙ V ≅ U ⋙ F) (u : U ≅ 𝟭 C) (v : V ≅ 𝟭 D) : Prop :=
  k ≪≫ Functor.isoWhiskerRight u F = Functor.isoWhiskerLeft F v

/-- The tensor comparison commutes with the specified action unitor.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def TensorUnitSquare {C : Type*} [Category C] (T : C × C ⥤ C)
    (U : C ⥤ C) (s : T ⋙ U ≅ U.prod U ⋙ T) (u : U ≅ 𝟭 C) : Prop :=
  s ≪≫ Functor.isoWhiskerRight (NatIso.prod u u) T = Functor.isoWhiskerLeft T u

/-- Two successive coefficient squares under their specified associators.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def CompositionSquare {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (p : A ⥤ B) (q : C ⥤ D) (r : E ⥤ F)
    (s : A ⥤ C) (t : C ⥤ E) (v : A ⥤ E)
    (s' : B ⥤ D) (t' : D ⥤ F) (v' : B ⥤ F)
    (k : p ⋙ s' ≅ s ⋙ q) (h : q ⋙ t' ≅ t ⋙ r)
    (d : p ⋙ v' ≅ v ⋙ r) (a : s ⋙ t ≅ v) (b : s' ⋙ t' ≅ v') : Prop :=
  Functor.isoWhiskerRight k t' ≪≫ Functor.isoWhiskerLeft s h ≪≫
      Functor.isoWhiskerRight a r = Functor.isoWhiskerLeft p b ≪≫ d

/-- Tensor comparison for two successive scalar extensions.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def TensorCompositionSquare {A B C : Type*} [Category A] [Category B] [Category C]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (s : A ⥤ B) (t : B ⥤ C) (v : A ⥤ C)
    (a : s ⋙ t ≅ v) (k : TA ⋙ s ≅ s.prod s ⋙ TB)
    (h : TB ⋙ t ≅ t.prod t ⋙ TC) (d : TA ⋙ v ≅ v.prod v ⋙ TC) : Prop :=
  Functor.isoWhiskerRight k t ≪≫ Functor.isoWhiskerLeft (s.prod s) h ≪≫
      Functor.isoWhiskerRight (NatIso.prod a a) TC = Functor.isoWhiskerLeft TA a ≪≫ d

private theorem map_unit_square {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B]
    (F : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    [F.Additive] [U.Additive] [V.Additive]
    (k : F ⋙ V ≅ U ⋙ F) (u : U ≅ 𝟭 A) (v : V ≅ 𝟭 B)
    (h : UnitSquare F U V k u v) :
    UnitSquare (F.mapHomologicalComplex (.up ℤ))
      (U.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex k (.up ℤ))
      (NatIso.mapHomologicalComplex u (.up ℤ))
      (NatIso.mapHomologicalComplex v (.up ℤ)) := by
  exact congrArg (fun a ↦ NatIso.mapHomologicalComplex a (.up ℤ)) h

/-- Equality of a five-map composite with a specified morphism.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def FiveStepEquation {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ G)
    {α : Type*} (f : α) : Prop := HEq (a ≫ b ≫ c ≫ d ≫ e) f

private theorem fiveStepEquation_iff_eq {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ G)
    (f : A ⟶ G) : FiveStepEquation a b c d e f ↔ a ≫ b ≫ c ≫ d ≫ e = f :=
  heq_iff_eq

variable (l : ℕ) [Fact l.Prime]

/-- Cochain quotient systems, with every transition retained in their module structure.
Source: blueprint integral operations; Stacks 0941
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev Complex (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :=
  CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ

/-- Signed direct-sum total tensor on the actual quotient sequence site.
Source: blueprint integral operations; Stacks 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def tensor (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) : Complex l E W × Complex l E W ⥤ Complex l E W :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W)


variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Additivity of the actual ordinary sequence-site scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance scalarAdditive (W : Scheme.{u}) :
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.Additive :=
  (integralComparisonSequenceScalarModel.{u, u} l E L ι W).additive

/-- Termwise scalar extension through the actual quotient-ring inclusions.
Source: blueprint integral operations; Stacks 06YY
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev scalar (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    Complex l E W ⥤ Complex l L W :=
  (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.mapHomologicalComplex (.up ℤ)

/-- Termwise constant-coefficient pro-etale pullback of entire quotient systems.
Source: blueprint integral operations; Stacks 03D2
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : Complex l E Y ⥤ Complex l E X :=
  (integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)

/-- The specified scalar-association isomorphism, lifted termwise.
Source: blueprint integral operations, proof step 3; Stacks 03EL
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def kappa {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull l E f ⋙ scalar l E L ι X ≅ scalar l E L ι Y ⋙ pull l L f :=
  NatIso.mapHomologicalComplex (integralComparisonSequenceScalarPullback.{u, u} l E L ι f) (.up ℤ)

/-- The scalar action unitor on the same strict quotient complexes.
Source: blueprint integral operations, proof step 7
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarUnit (W : Scheme.{u}) : scalar l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit.{u, u} l E W) (.up ℤ)

/-- Successive extension is identified by multiplication of the coefficient factors.
Source: blueprint integral operations, proof step 7
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarComp (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : Scheme.{u}) :
    scalar l E L ι W ⋙ scalar l L F j W ≅ scalar l E F (j.comp ι) W :=
  NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarComposition.{u, u} l E L ι F j W) (.up ℤ)

/-- Tensor generator in the (p,q) summand of the signed direct-sum total.
Source: Stacks 03EK, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev generator (W : Scheme.{u}) (P Q : Complex l E W) (p q : ℤ)
    (U : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((tensor l E W).obj (P, Q)).X (p + q)).val.obj U :=
  coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q (p + q) rfl U x y

/-- The adjunction-unit generator read as a section on the base-change object.
Source: Stacks 03D2 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y) (n : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback.{u, u} l E f).obj M).val.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)) :=
  integralComparisonSequenceGenerator.{u, u} l E f M n U x

/-- The pure-tensor formula for a scalar comparison on the whole sequence site.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def ScalarFormula (sigma : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W) : Prop :=
  ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    (P Q : Complex l A W) (p q : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l B W).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    (((sigma A B i W).hom.app (P, Q)).f (p + q)).val.app U
      (integralComparisonSequenceTensorSection.{u, u} l A B i W
        (((tensor l A W).obj (P, Q)).X (p + q)) U b
        (generator l A W P Q p q U x y)) =
      generator l B W ((scalar l A B i W).obj P) ((scalar l A B i W).obj Q) p q U
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (P.X p) U b x)
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (Q.X q) U 1 y)

/-- The unit formula for a tensor-pullback comparison on the whole sequence site.
Source: Stacks 03D2, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def PullFormula (c : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X) : Prop :=
  ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l A Y) (p q : ℤ) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l A X).obj.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)))
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))),
    (((c A f).hom.app (P, Q)).f (p + q)).val.app
      (op (n, (Scheme.proEtaleBaseChange f).obj U))
      (b • pullSection l A f
        (((tensor l A Y).obj (P, Q)).X (p + q)) n U
        (generator l A Y P Q p q (op (n, U)) x y)) =
      generator l A X ((pull l A f).obj P) ((pull l A f).obj Q) p q
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (b • pullSection l A f (P.X p) n U x)
        (pullSection l A f (Q.X q) n U y)

/-- Pure-tensor-normalized tensor comparisons on strict quotient systems.
All components, including their inverses, are chain maps of actual sequence-site modules.
Source: blueprint integral operations, proof steps 3--6; Stacks 03EL and 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
structure ComparisonData (Sigma Pullback : Type*)
    (sigmaFormula : Sigma → Prop) (pullFormula : Pullback → Prop) where
  sigma : Sigma
  sigma_formula : sigmaFormula sigma
  c : Pullback
  c_formula : pullFormula c

/-- The original two comparisons and their exact generator formulas.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-scalar-extension-tower-data). -/
abbrev Comparisons :=
  ComparisonData (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W)
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X)
    (ScalarFormula l) (PullFormula l)


private def scalar_adj (W : Scheme.{u}) :
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E ⊣
      SheafOfModules.restrictScalars ((sheafCompose
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralComparisonSequenceScalarMap.{u, u} l E L ι W)) :=
  (sequenceScalarAdjunction.{u, u} l E L ι W).choose

attribute [local irreducible] scalar_adj
  integralComparisonSequenceTensorSection

private theorem scalar_transpose_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W)
    (N : coefficientSequenceModules.{u, u} l L W)
    (a : (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.obj M ⟶ N)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : M.val.obj V) :
    (((scalar_adj l E L ι W).homEquiv M N) a).val.app V x =
      a.val.app V (integralComparisonSequenceTensorSection l E L ι W M V 1 x) := by
  rw [Adjunction.homEquiv_unit]
  change a.val.app V (((scalar_adj l E L ι W).unit.app M).val.app V x) = _
  unfold scalar_adj
  exact congrArg (a.val.app V) (sequenceScalarAdjunction_unit l E L ι W M V x)

private theorem scalar_section_naturality (W : Scheme.{u})
    {M N : coefficientSequenceModules.{u, u} l E W} (a : M ⟶ N)
    (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.map a).val.app V
        (integralComparisonSequenceTensorSection l E L ι W M V b x) =
      integralComparisonSequenceTensorSection l E L ι W N V b (a.val.app V x) := by
  obtain ⟨A, hA⟩ := SequenceScalarProof.scalarPackageExists
    (integralComparisonSequenceScalarMap.{u, u} l E L ι W)
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W)
  rw [sequenceTensorSection_eq, sequenceTensorSection_eq, ← hA]
  exact SheafOfModules.systemScalarModel_map_tmul A a V b x


open CategoryTheory.CochainPullback
open MonoidalCategory

private theorem scalar_section_smul (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (x : M.val.obj V) :
    integralComparisonSequenceTensorSection l E L ι W M V b x =
      b • integralComparisonSequenceTensorSection l E L ι W M V 1 x := by
  rw [sequenceTensorSection_eq, sequenceTensorSection_eq]
  unfold SheafOfModules.systemModelTmul
  simp only [one_smul]

attribute [local semireducible] coefficientTotalTensor in
private theorem generator_smul (W : Scheme.{u}) (P Q : Complex l E W)
    (p q : ℤ) (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    generator l E W P Q p q V (b • x) y = b • generator l E W P Q p q V x y := by
  unfold generator coefficientTensorGenerator
  simp only [← TensorProduct.smul_tmul', map_smul]

attribute [local semireducible] integralComparisonSequenceTensorSection

set_option maxHeartbeats 800000 in
-- The comparison identifies two presentations of the same total complex.

attribute [local semireducible] coefficientTotalTensor in
private theorem scalar_tensor_comparison (W : Scheme.{u}) :
    ∃ e : tensor l E W ⋙ scalar l E L ι W ≅
      (scalar l E L ι W).prod (scalar l E L ι W) ⋙ tensor l L W,
      ∀ (P Q : Complex l E W) (p q : ℤ) (V : (ℕ × W.ProEt)ᵒᵖ)
        (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        ((e.hom.app (P, Q)).f (p + q)).val.app V
          (integralComparisonSequenceTensorSection l E L ι W
            (((tensor l E W).obj (P, Q)).X (p + q)) V b
            (generator l E W P Q p q V x y)) =
          generator l L W ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q V
            (integralComparisonSequenceTensorSection l E L ι W (P.X p) V b x)
            (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) := by
  obtain ⟨e, he⟩ := scalarTensorTotal.{u + 1, u, u}
    (integralComparisonSequenceScalarMap.{u, u} l E L ι W)
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).obj_eq
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).map_eq
  refine ⟨e, ?_⟩
  intro P Q p q V b x y
  have h := he P Q p q (p + q) rfl V x y
  change ((e.hom.app (P,Q)).f (p+q)).val.app V
    (integralComparisonSequenceTensorSection l E L ι W _ V 1
      (generator l E W P Q p q V x y)) = _ at h
  rw [scalar_section_smul, map_smul]
  have hh : ((e.hom.app (P,Q)).f (p+q)).val.app V
      (integralComparisonSequenceTensorSection l E L ι W _ V 1
        (generator l E W P Q p q V x y)) =
    generator l L W ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q V
      (integralComparisonSequenceTensorSection l E L ι W (P.X p) V 1 x)
      (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) := h
  refine (congrArg (fun z ↦ b • z) hh).trans ?_
  conv_rhs => rw [scalar_section_smul]
  exact (generator_smul l L W ((scalar l E L ι W).obj P)
    ((scalar l E L ι W).obj Q) p q V b
    (integralComparisonSequenceTensorSection l E L ι W (P.X p) V 1 x)
    (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y)).symm

private def chosen_sigma (W : Scheme.{u}) :
    tensor l E W ⋙ scalar l E L ι W ≅
      (scalar l E L ι W).prod (scalar l E L ι W) ⋙ tensor l L W :=
  (scalar_tensor_comparison l E L ι W).choose

private theorem chosen_sigma_formula (W : Scheme.{u}) (P Q : Complex l E W)
    (p q : ℤ) (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((chosen_sigma l E L ι W).hom.app (P, Q)).f (p + q)).val.app V
      (integralComparisonSequenceTensorSection l E L ι W
        (((tensor l E W).obj (P, Q)).X (p + q)) V b
        (generator l E W P Q p q V x y)) =
      generator l L W ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q V
        (integralComparisonSequenceTensorSection l E L ι W (P.X p) V b x)
        (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) :=
  (scalar_tensor_comparison l E L ι W).choose_spec P Q p q V b x y

private theorem pullback_comparison (X Y : Scheme.{u}) (f : X ⟶ Y) :
    ∃ e : tensor l E Y ⋙ pull l E f ≅ (pull l E f).prod (pull l E f) ⋙ tensor l E X,
      ∀ (P Q : Complex l E Y) (p q : ℤ) (m : ℕ) (U : Y.ProEt)
        (x : (P.X p).val.obj (op (m, U))) (y : (Q.X q).val.obj (op (m, U))),
        ((e.hom.app (P, Q)).f (p + q)).val.app
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (pullSection l E f (((tensor l E Y).obj (P, Q)).X (p + q)) m U
              (generator l E Y P Q p q (op (m, U)) x y)) =
          generator l E X ((pull l E f).obj P) ((pull l E f).obj Q) p q
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (pullSection l E f (P.X p) m U x) (pullSection l E f (Q.X q) m U y) := by
  let G (r : coefficientSequenceCommRingSheaf.{u, u} l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf.{u, u} l E X)) :=
    SheafOfModules.pushforward.{u + 1} (F := integralComparisonSequenceBaseChange f)
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E Y))
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E X))
      ⟨Functor.whiskerRight r.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let H (r : coefficientSequenceCommRingSheaf.{u, u} l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf.{u, u} l E X))
      (hG : (G r).IsRightAdjoint) : Prop :=
    letI := hG
    let F := (G r).leftAdjoint.mapHomologicalComplex (.up ℤ)
    ∃ e : tensor l E Y ⋙ F ≅ F.prod F ⋙ tensor l E X,
      ∀ (P Q : Complex l E Y) (p q : ℤ) (m : ℕ) (U : Y.ProEt)
        (x : (P.X p).val.obj (op (m, U))) (y : (Q.X q).val.obj (op (m, U))),
        ((e.hom.app (P, Q)).f (p + q)).val.app
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (((Adjunction.ofIsRightAdjoint (G r)).unit.app
              (((tensor l E Y).obj (P, Q)).X (p + q))).val.app (op (m, U))
              (generator l E Y P Q p q (op (m, U)) x y)) =
          generator l E X (F.obj P) (F.obj Q) p q
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (((Adjunction.ofIsRightAdjoint (G r)).unit.app (P.X p)).val.app (op (m, U)) x)
            (((Adjunction.ofIsRightAdjoint (G r)).unit.app (Q.X q)).val.app (op (m, U)) y)
  have h1 : H (pullbackTensorSequenceRing l E f)
      (pullbackTensorSequenceDirect_rightAdjoint l E f) := by
    obtain ⟨e, he⟩ := (pullbackTensorSequenceCochain_existsUnique l E f).exists
    refine ⟨e, ?_⟩
    intro P Q p q m U x y
    exact he P Q p q (p + q) rfl (m, U) x y
  have h2 : ∃ h : (G (integralComparisonSequenceRingMap l E f)).IsRightAdjoint,
      H (integralComparisonSequenceRingMap l E f) h := by
    rw [← WeilConjectures.pullbackTensorSequenceRing_eq]
    exact ⟨_, h1⟩
  exact h2.choose_spec


attribute [local irreducible] integralComparisonSequenceTensorSection
  coefficientTensorGenerator
  integralComparisonSequenceScalarPullback
set_option maxHeartbeats 800000 in
-- Use adjunction injectivity and the generators of each tensor summand.
private theorem comparisons_unique (c d : Comparisons.{u} l) : c = d := by
  have hs : c.sigma = d.sigma := by
    funext A B _ _ _ _ _ _ i W
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ((scalar_adj l A B i W).homEquiv _ _).injective
    apply WeilConjectures.total_tensor_sections_ext l A W P Q n
    intro p q hpq V x y
    subst n
    have hc := c.sigma_formula A B i W P Q p q V 1 x y
    have hd := d.sigma_formula A B i W P Q p q V 1 x y
    exact (scalar_transpose_section l A B i W _ _ _ V _).trans
      (hc.trans (hd.symm.trans (scalar_transpose_section l A B i W _ _ _ V _).symm))
  have hc : c.c = d.c := by
    funext A _ _ _ X Y f
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage.{u, u} l A f)).homEquiv _ _).injective
    apply WeilConjectures.total_tensor_sections_ext l A Y P Q n
    intro p q hpq V
    rcases V with ⟨m, U⟩
    intro x y
    subst n
    change (((c.c A f).hom.app (P, Q)).f (p + q)).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l A f _ m U (generator l A Y P Q p q (op (m, U)) x y)) =
      (((d.c A f).hom.app (P, Q)).f (p + q)).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l A f _ m U (generator l A Y P Q p q (op (m, U)) x y))
    have h1 := c.c_formula A f P Q p q m U 1 x y
    have h2 := d.c_formula A f P Q p q m U 1 x y
    simp only [one_smul] at h1 h2
    exact h1.trans h2.symm
  cases c
  cases d
  cases hs
  cases hc
  rfl

private def chosen_c {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ≅ (pull l E f).prod (pull l E f) ⋙ tensor l E X :=
  (pullback_comparison l E X Y f).choose

private theorem chosen_c_formula {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l E Y) (p q : ℤ) (m : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l E X).obj.obj
      (op (m, (Scheme.proEtaleBaseChange f).obj U)))
    (x : (P.X p).val.obj (op (m, U))) (y : (Q.X q).val.obj (op (m, U))) :
    (((chosen_c l E f).hom.app (P, Q)).f (p + q)).val.app
      (op (m, (Scheme.proEtaleBaseChange f).obj U))
      (b • pullSection l E f (((tensor l E Y).obj (P, Q)).X (p + q)) m U
        (generator l E Y P Q p q (op (m, U)) x y)) =
      generator l E X ((pull l E f).obj P) ((pull l E f).obj Q) p q
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (b • pullSection l E f (P.X p) m U x)
        (pullSection l E f (Q.X q) m U y) := by
  rw [map_smul]
  exact ((congrArg (fun z ↦ b • z)
    ((pullback_comparison l E X Y f).choose_spec P Q p q m U x y)).trans
      (generator_smul l E X _ _ p q _ b _ _).symm)

/-- Existence and uniqueness of the two specified chain comparisons.
Source: blueprint integral operations, proof steps 3--4; Stacks 03EL and 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: apply the ordinary sheaf tensor comparison to the geometric inverse image
and to identity inverse image with the actual coefficient map. Its insertion and
multiplication formulas are inverse by balancing. Totalize over all p+q=n. The
comparison preserves bidegrees, so commutes with both differential terms, including
(-1)^p. These formulas commute with horizontal quotient maps and vertical restrictions,
hence are maps on the sequence site. Pure tensors locally generate the sheaf tensor
and its direct-sum total; this proves uniqueness as well as naturality. -/
theorem comparisons_existsUnique : Nonempty (Unique (Comparisons l)) := by
  let c : Comparisons l :=
    { sigma := fun A B _ _ _ _ _ _ i W ↦ chosen_sigma l A B i W
      sigma_formula := fun A B _ _ _ _ _ _ i W P Q p q V b x y ↦
        chosen_sigma_formula l A B i W P Q p q V b x y
      c := fun A _ _ _ _ _ f ↦ chosen_c l A f
      c_formula := fun A _ _ _ _ _ f P Q p q n U b x y ↦
        chosen_c_formula l A f P Q p q n U b x y }
  exact ⟨⟨⟨c⟩, fun d ↦ comparisons_unique l d c⟩⟩

/-- Canonical comparisons fixed by their pure-tensor characterization.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def comparisons : Comparisons l := (Classical.choice (comparisons_existsUnique l)).default

attribute [local irreducible] comparisons

/-- The left route around the scalar-extension square, as an actual strict chain iso.
Source: node proof steps 3--6 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def leftRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ⋙ scalar l E L ι X ≅
      (scalar l E L ι Y).prod (scalar l E L ι Y) ⋙
        (pull l L f).prod (pull l L f) ⋙ tensor l L X :=
  leftRouteCore (tensor l E Y) (tensor l L Y) (tensor l L X)
    (pull l E f) (scalar l E L ι Y) (scalar l E L ι X) (pull l L f)
    (kappa l E L ι f) ((comparisons l).sigma E L ι Y) ((comparisons l).c L f)

/-- The right route, using the same scalar-association maps on both tensor factors.
Source: node proof steps 3--6 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def rightRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ⋙ scalar l E L ι X ≅
      (scalar l E L ι Y).prod (scalar l E L ι Y) ⋙
        (pull l L f).prod (pull l L f) ⋙ tensor l L X :=
  rightRouteCore (tensor l E Y) (tensor l E X) (tensor l L X)
    (pull l E f) (scalar l E L ι Y) (scalar l E L ι X) (pull l L f)
    (kappa l E L ι f) ((comparisons l).sigma E L ι X) ((comparisons l).c E f)

private theorem pull_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y)
    (N : coefficientSequenceModules.{u, u} l E X)
    {a b : (integralComparisonSequencePullback.{u, u} l E f).obj M ⟶ N}
    (h : ∀ (n : ℕ) (U : Y.ProEt) (x : M.val.obj (op (n, U))),
      a.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
          (pullSection l E f M n U x) =
        b.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
          (pullSection l E f M n U x)) : a = b := by
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact h V.unop.1 V.unop.2 x

private theorem scalar_unit_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).hom.app M).val.app V
      (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V s x) =
        s • x := by
  exact (integralComparisonSequenceScalarUnit_existsUnique.{u, u} l E W).exists.choose_spec
    M V s x

private theorem scalar_unit_inv_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V x =
      integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V 1 x := by
  have h := scalar_unit_section l E W M V 1 x
  have hh := congrArg
    (fun z ↦ ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V z) h
  simpa only [one_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Iso.hom_inv_id_app, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using hh.symm

private theorem pull_section_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : coefficientSequenceModules.{u, u} l E Y} (a : M ⟶ N)
    (n : ℕ) (U : Y.ProEt) (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback.{u, u} l E f).map a).val.app
        (op (n, (Scheme.proEtaleBaseChange f).obj U)) (pullSection l E f M n U x) =
      pullSection l E f N n U (a.val.app (op (n, U)) x) := by
  have h := (Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).unit.naturality a
  exact (congrArg (fun k ↦ (k.val.app (op (n, U))) x) h).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_pull_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y) (m : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (m, U))) :
    ((integralComparisonSequenceScalarPullback.{u, u} l E L ι f).hom.app M).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι X
          ((integralComparisonSequencePullback.{u, u} l E f).obj M)
          (op (m, (Scheme.proEtaleBaseChange f).obj U)) 1
          (pullSection l E f M m U x)) =
      pullSection l L f ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj M)
        m U (integralComparisonSequenceTensorSection l E L ι Y M (op (m, U)) 1 x) := by
  simpa only [integralComparisonSequenceScalarPullback, pullSection] using
    (integralComparisonSequenceScalarPullback_existsUnique.{u, u}
      l E L ι f).exists.choose_spec M m U x

private theorem scalar_pull_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonSequenceScalarPullback.{u, u} l E E (AlgHom.id ℚ_[l] E) f ≪≫
        Functor.isoWhiskerRight (integralComparisonSequenceScalarUnit.{u, u} l E Y)
          (integralComparisonSequencePullback.{u, u} l E f) =
      Functor.isoWhiskerLeft (integralComparisonSequencePullback.{u, u} l E f)
        (integralComparisonSequenceScalarUnit.{u, u} l E X) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi ((integralComparisonSequenceScalarUnit.{u, u} l E X).inv.app
    ((integralComparisonSequencePullback.{u, u} l E f).obj M))).1
  apply pull_hom_ext l E f M
  intro n U x
  change
    ((integralComparisonSequencePullback.{u, u} l E f).map
      ((integralComparisonSequenceScalarUnit.{u, u} l E Y).hom.app M)).val.app _
      (((integralComparisonSequenceScalarPullback.{u, u} l E E
        (AlgHom.id ℚ_[l] E) f).hom.app M).val.app _
        (((integralComparisonSequenceScalarUnit.{u, u} l E X).inv.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj M)).val.app _
            (pullSection l E f M n U x))) =
    ((integralComparisonSequenceScalarUnit.{u, u} l E X).hom.app
      ((integralComparisonSequencePullback.{u, u} l E f).obj M)).val.app _
        (((integralComparisonSequenceScalarUnit.{u, u} l E X).inv.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj M)).val.app _
            (pullSection l E f M n U x))
  erw [scalar_unit_inv_section l E X
    ((integralComparisonSequencePullback.{u, u} l E f).obj M)
    (op (n, (Scheme.proEtaleBaseChange f).obj U)) (pullSection l E f M n U x)]
  have hk := scalar_pull_section l E E (AlgHom.id ℚ_[l] E) f M n U x
  change ((integralComparisonSequencePullback.{u, u} l E f).map
      ((integralComparisonSequenceScalarUnit.{u, u} l E Y).hom.app M)).val.app _
      (((integralComparisonSequenceScalarPullback.{u, u} l E E
        (AlgHom.id ℚ_[l] E) f).hom.app M).val.app _ _) = _
  erw [hk, pull_section_naturality, scalar_unit_section, one_smul]
  symm
  simpa only [Functor.id_obj, one_smul] using scalar_unit_section l E X
    ((integralComparisonSequencePullback.{u, u} l E f).obj M)
    (op (n, (Scheme.proEtaleBaseChange f).obj U)) 1 (pullSection l E f M n U x)

attribute [local irreducible] integralComparisonSequenceScalarUnit

```

## New

The construction above is now in
`Sheaf.Paper.ScalarExtensionTowerComparisonData`, with the same namespace, section
variables, instance priorities and declaration texts. The original module adds:

```lean
public import Sheaf.Paper.ScalarExtensionTowerComparisonData
public import Sheaf.Paper.ScalarExtensionTowerComposition
import all Sheaf.Paper.ScalarExtensionTowerComparisonData
```

A new proved private helper, `pull_tensor_section`, specializes the already recorded
pullback formula at coefficient one. It adds no assumption or public declaration.
The plain `import all` lets the coherence proofs reuse the proved private generator lemmas.
The original public imports are retained. The original square, unit, completed realization and quotient statements stay in
the original module. The completed composition proof is in
`Sheaf.Paper.ScalarExtensionTowerComposition`, with its original name and signature.
It imports the comparison data and reuses only their proved private generator helpers
and the existing scalar tensor generator API. A second ownership node records it.
The final file split keeps the independent composition check separate from the square
and derived-model checks. No public mathematical condition or definition body changes. DAG Lean ownership: the relocated definitions stay recorded at
def-pur-scalar-extension-tower-data (re-exported through the public import); the
new node stage3-pur-normalized-scalar-tower-comparisons records `comparisons_existsUnique`,
`sequenceSmall`, `siteSmall` and `scalarAdditive`, and stage3-pur-scalar-tower-composition
records `composition` (reviewer correction, 2026-10-27). The aggregate node's mathematical
statement and the blueprint unit route are preserved.

## Users

All transitive downstream modules from the refreshed audit are included below.
Claim holders can change after this audit. The original public module re-exports
all existing names and definitions. No consumer source adaptation is delivered.
Direct importer validation is recorded in report.md. Unchanged validation copies
are removed before delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.CartierKummerDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceChartRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.ProperOpenRefinementAlphaPlusInclusion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.FiniteStageFibreVanishing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.GeometricCurveDiagramDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.MarkedGeometricCurveModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.OrdinarySectionScalarComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.PairEigenvalueCurveTest` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.RawHeartAdicStrataBridge` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.SmoothAffineConstituentPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.FourierTransform.FourierDeligneTransform` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicActualSystemsNormalized` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicClosureScalarCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicCommonStageFibreTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicCommonStageFibreZeroMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicCommonStageHeartExactness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicCompletedProjectionShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicCompletedTensorRealizationDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicExceptionalShiftCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicFibreComparisonCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicFibreComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicFiniteConstructibilityComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicFiniteRealizationCocone` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicFiniteRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicFiniteScalarCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedFibreCommonStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedFibreCommonStageData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedFibreData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedFibreExactness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedFibrePullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedFibreScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicNormalizedPuritySystems` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicProperAdjunctionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityCanonicalSourceCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityFiniteTensorComponents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPuritySourceFiniteness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPuritySourceNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPuritySourceTransitionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicPurityTwistRestrictionComponents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicQbarConstructibleRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicRealizationFamilyData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicRealizationIsomorphismNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicReindexingCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicReindexingFunctoriality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicReindexingHom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicReindexingTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicStratifiedPullbackInterface` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicTraceTensorShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdmissibleCupCoefficientPassages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdmissibleHomSubstitution` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineCoefficientCounitMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineCoefficientCounitNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineCounitMateUnitChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalDncCoordinateIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalDncNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalIntegrationConstructions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalIntegrationOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalPowerCoefficient` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalPresentedBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalRawTransposePower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalRestrictedTransposes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalSectionCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalTateCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalTraceRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineDiagonalTransposePower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineIntegrationExponentTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineLineComparisonNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineLineCompositeTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineLinePurityComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineLinePuritySource` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineLineStandingTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedCounitData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedCounitDescentComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedCounitSuccessor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedCounitZero` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedEvaluationContraction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedFirstLineCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedIntegrationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedIntegrationSuccessor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineOrderedTransposeCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceCoordinateBoundaries` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceLastFactorProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceProductDomain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpacePurityComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpacePurityComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpacePurityCompositionMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpacePurityCoordinateInvariance` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpacePurityOrderedBlocks` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceThomMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceTraceContractionProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceTraceProductData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceTraceSuccessorContraction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceZeroSectionConstructions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineTargetDiagonalDnc` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineTowerIntegrationSiteTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineTranslationTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AffineVectorTracePresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AllStageCtfPullbackUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AmbientComparisonSystemExistence` | J5 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.AutomorphismSquareRationalScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BarrettIndRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BaseChangedLineTraceEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BasicOperationCoefficientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BasicOperationReductionAndEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryComparisonCompositionTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryFiniteEvaluationRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryFiniteSiteData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryFiniteSiteRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryFiniteTorDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.BoundedSiteExchangeTransposes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalCoefficientChainNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalCoefficientFiniteCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalCoefficientPullbackModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalCoefficientUnitNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateArrowNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateCommonComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateCompletedComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateComplexComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateNaturalityLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateOrdinaryNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateScalarComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CanonicalTateScalarNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CartierRelativeKummerRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CartierSupportedComparisonSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CentredDiagonalSourcePasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartDiagonalAssemblyData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartDiagonalSourceSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartDncNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartDncSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartDncVectorFactorData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartDncVectorFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartEpsilonPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartExceptionalCounitEquation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartExceptionalMateCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartIntegrationAdjoints` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartNormalIntegrationSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChartTargetOpenDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalFiltrationDiagramFibres` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalFiltrationExactDiagram` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalFiniteWeilDiagramData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalFiniteWeilDiagramRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalFrontierExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalLocalFrobeniusData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCommonDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCommonFibres` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCommonRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseCommonSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseFiniteConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseFiniteOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLissePointFibres` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRawLisseScalarCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRealizationLocalSpectrum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRealizationPunctualPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalRealizedAnchorEigenvalue` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalSuccessiveRestrictions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalSystemRawLisseRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalTwoFibreCommonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalTwoFibreScalarData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalWeilCoherentDiagramStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalWeilFiltrationTransportData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalWeilFiniteDiagramDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClassicalWeilRestrictionExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenCanonicalFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenCanonicalRestrictionEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenCompletedTowerRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenCounitAdjointComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenExceptionalScalarDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenPrescribedWeilFiltration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenSystemFiniteRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenSystemIntegralRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenSystemRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClopenSystemRestrictionEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClosedCoefficientTransposeCocycles` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClosedEmbeddingPerfectEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClosedScalarDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ClosedSupportExceptionalMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CochainLocalizationTensorIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefSupportOpenTensorModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefSupportPointSectionsComparisonExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefSupportPointSectionsData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefSupportPointSectionsModelExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefficientDualModelTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefficientEvaluationNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefficientFirstCompactSupportSiteSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoefficientMapGeometricSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonConstantUnitFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonFrobeniusSquareNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionCompactificationOnStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionComparisonEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionCompositionOnStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionOpenFactor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | J7 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionProperFactor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionProperOnStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionProperTensorCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | J8 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionTensorComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonProjectionTensorCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageEvaluationNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageOpenHeartAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStagePerfectEvaluationDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStagePointReturn` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageRestrictionTensorDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageSmoothOperationCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageSmoothOperationIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageSmoothOperationShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageWeilIterate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactExchangeOperationCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportArrowScalarTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCoefficientExchangeInvertible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCoefficientModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCompletedProjectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCompletedScalarArrow` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCompositeTransposeDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportCondensedRealizationSetup` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportExchangeDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportFiniteScalarMateNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportLimitEquationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportLimitEquationRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportNormalizedRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportNormalizedScalarDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportPathReductionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionCoefficientChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionCoherenceLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionFieldStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionFiniteStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionIntegralStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionRealizationLift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportProjectionRightUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportRealizationCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportRealizationFactorization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportRealizationIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportRealizedScalarTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarEvaluationSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarGammaIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarLimitFoundations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarLimitReduction` | D4 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarProjectionIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarShiftNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarShiftStructures` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportScalarShiftWitness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportStageActionAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | B4 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportStrictScalarMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportStrictScalarRefinement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportSystemScalarFiniteInvertible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportSystemTransposeNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportTermHomFinite` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactSupportTotalLimitRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationBOrdinaryProjectionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationBProjectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationBProjectionDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationBProjectionReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationCompletedRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationFiniteProjectionModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactificationStrictRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ComparedSmoothExchangeComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ComparisonImageClosedSectionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompleteIntegralConstantRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompleteProjectionDescentMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompleteProjectionMateDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompleteProjectionReductionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedComparisonCanonicalIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedComparisonQuotientNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedComparisonQuotientRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedComparisonQuotientRealizationDefs` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedComparisonScalarLimitImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedConstantRightUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedContinuousHomHypotheses` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedInverseImageScalarCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedLocalFibreComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedPullbackFractionDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedScalarAssociatorLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedScalarExactLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedScalarLocalizationBalancing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedScalarTransportCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedUnitAdmissible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedUnitMultiplicationComponents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedUnitPullbackData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedUnitPullbackTower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedUnitReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedUnitScalarNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompletedUnitStrictComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompositeProjectionCoefficients` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompositionIteratedMateExpansion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompositionModelOrientationDefinitions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompositionModelOrientationDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompositionSingleMatePresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CompositionTensorMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteOpenScalarTensorSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteProjectionCoefficientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteProjectionFactorizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteProjectionReductionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteProjectionReductionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteProperScalarTensorSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConcreteSupportScalarIsomorphism` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedCompositorRealization` | Z8 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedExceptionalCounitRepresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedExceptionalRealizationProperties` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedExceptionalReconstructionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedExceptionalRefinementCounits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedExceptionalSystemRecognition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedIntegralEndpoints` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedOpenCoefficientModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedOpenCounitComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedOpenCounitRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedOpenCounitRealizationSupport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedOpenCounitUnits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CondensedOpenUnitComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantCompletedOrdinaryAssociativity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantCompletedScalarAssociativity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantDirectImageTowerRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionCyclicSheetPartition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionPullbackReturnResidue` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionPullbackSheetComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionReturnData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionReturnExactFunctor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionReturnLocalOperators` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionReturnLocalSpectra` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionReturnTransportComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionSheetGeometry` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionSheetHeartCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionSheetHeartData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionSheetTensorSplitting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionWeilHeartData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantScalarTowerAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantScalarTowerMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantTwistCoefficientComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantWeilStageCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalCompositor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalCompositorData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalLeftRefinements` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleExceptionalRefinementMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleLeftCompositorCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleMateCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleRationalHomComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleRationalLeftRefinement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleRingLeftRefinement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleTensorComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ConstructibleWeilModelSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateAdjunctionComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateCartierBoundarySign` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateLineAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateLineAdjunctionMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateLineAugmentationRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateLineConjugateExponents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateLineCounitTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateProductPresentations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateSectionArrows` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateSectionProductRecursion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateSectionProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateSectionProjectiveTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateSectionSiteTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateSectionTensorTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateSupportedProductRecursion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateTowerCompactTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateTowerExceptionalCompositors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateTowerNormalizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateTowerNormalizationFusion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateTowerNormalizationInduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoordinateZeroBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CtfCoefficientStageSelectors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CurveClassicalFiltrationPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CurveClassicalPullbackExists` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CurveRestrictionFiltrationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CurveRestrictionFiltrationSpectrum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.CurveRestrictionLocalPowers` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DerivedHomSubstitutionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DerivedPoincarePairing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DerivedTensorRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DerivedWeilOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalAffineCounitRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalAffineIntegrationSiteSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalAffineRankZeroActual` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalAffineTraceCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalAffineTraceMapAgreement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalAffineTraceSiteComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalAffineTraceSiteData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalCounitComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncAffineModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncAssemblyGlobal` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncChartNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncEtaleBeta` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncEtaleDualizing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncEtaleFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncEtaleNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncEtaleNaturalityLocalInverse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalDncEtaleNaturalityTwist` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleAlphaSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleFactorization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleInverseDeformation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleNormalEndpoint` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleNormalTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleRestrictedDualizingData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleRhoUnitSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleSourceDualizing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleSourceEndpoint` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalEtaleSourceTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrdinaryChartLift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationGluing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrdinaryOverlap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrdinaryRealizeRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrientationChartExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrientationCharts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrientationChoiceIndependent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrientationCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrientationRefinement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DiagonalOrientationRefinementData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DifferenceCoordinateSectionIdentifications` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DifferenceFirstInputRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DifferenceSecondInputRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DirectImageCoefficientExchangeInvertible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DirectImageLimitComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DirectImageScalarRealizationSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DlLocalHeartAbelianEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DlLocalHeartCoverBasisZero` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DlLocalHeartCoverDefects` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DoubleDiagonalSectionIdentifications` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualizingCocycleSourceEtale` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualizingCompositionCoefficientMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualizingPrimitiveOpenRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualizingSigmaCocycleLocality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.DualizingUnitComposite` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EtaleCartesianTowerTensorComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EtaleCompositeEComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EtaleMiddleTensorAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EtaleOrientationLocality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EtaleTensorSourceTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EvenLineBinaryProductNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EvenLineCoefficientProjectionNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EvenLineCoordinateIntertwining` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EvenLineProductIntegrationMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EvenLineProductIntegrationSymmetry` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.EvenTateLineSelfSymmetry` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExactProperOpenProjectionMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalCommonStageFromRational` | K7 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalDualizingBaseChangePasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFieldDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFieldStageCompletion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFiniteIntrinsicBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFiniteOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFiniteScalarMates` | A4 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalIntegralSupportAdjoint` | M5 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRationalStageLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRefinementLeftConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRefinementMatesData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRefinementRightSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRefinementSystemData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRefinementSystemRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRefinementTransportData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRingScalarMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRingStageAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalRingStageAssemblyData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExchangeFunctoriality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExplicitScalarConeWordCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdCommonStageComparisonDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdCompletedCompositorNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdCompletionFiniteStageLinear` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdCompletionInverseScalarCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdIntegralInverseScalarCocycle` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdIntegralScalarDescentInputs` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdPullbackAugmentationCounitMatching` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdPullbackSignedShiftWordTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdPullbackWeilReturnSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldCohomologyPerfectDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionCompletedStrictLimit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionIntegralComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionIntegralCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionIntegralDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionIntegralModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionLimitEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionRationalComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionRationalDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionRationalModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionReductionDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionReductionLimits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionSourceNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionStrictLimits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionSystemCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldExtensionTowers` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientationSystemComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientationSystemComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientationSystemCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientationSystemFiniteOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientationSystemHeart` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientationSystemNormalizations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientationSystemRigidity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldOrientedExchangeSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldProjectionRefinementSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldPuritySystemTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldPuritySystemTransposeBase` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldPuritySystemTransposeCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldPurityTransposeArrows` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldShriekCompositionCoefficientSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldShriekCompositionIntegralComponent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldShriekCompositionIntegralNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldShriekCompositionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FilteredCondensedCanonicalComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FilteredCondensedCounitBijective` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FilteredCondensedCounitFiniteFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FilteredCondensedRepresentingPair` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FilteredCondensedRepresentingPairData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteCompactSupportCoefficientSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteCompactSupportEvaluationRefinement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteCompactificationEigenvalues` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteDiagonalBaseChangeReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteDiagonalDncReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteDiagonalOrientationAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteDiagonalVectorReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteExceptionalCompositorCoefficients` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteExceptionalSiteNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFirstRootChart` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteForwardCompactifiedSwap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteForwardProductCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCoefficientExtensionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCompactSupportData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeCompactSupportSiteSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeProperScalarComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteGammaEvaluationIsIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteGeometricOrientationExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteGeometricPurityCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteGeometricPurityFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteGeometricPurityMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteGeometricSectionsPointOrbits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteGeometricTensorExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteHorizontalShriekMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteIdentityCompositionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteMateDomain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteOrientationReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteOrientationScalarPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePartialPullbackTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePointCounitUnitNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePositiveChartFrameExt` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePositiveChartRecursion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePositiveRootChartPower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePositiveRootCharts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProductOpenRestrictionPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProductOrdinaryNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProductReductionComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProductScalarPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionBinarySquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | T6 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionCompactificationSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionCompactificationTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionCompositionTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionExchangeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionExchangeTransposes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionFromDescent` | M9 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionIdentityNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionInputNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionIterationRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | P5 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionOperationPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionRefinementLeft` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProjectionTensorSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteProperProjectionTranspose` | P6 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePublishedRootChartPower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FinitePurityCounitSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteQuotientModuleBalancing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRationalHeartComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRealizationEtaleOrigin` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionBaseChangeSource` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionExceptionalFiniteModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionLineChartScalars` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionLineInputConstructible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionPositiveLineComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionReassociation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionShiftedPullbackCube` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionSourceChartIndependence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionTensorFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionTensorPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionTensorSource` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteReductionThetaFactor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRefinementAmbientNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRefinementProjectionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRegularCoefficientComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRestrictionConstructibleVertices` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRestrictionDiagramModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRestrictionDiagramNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRestrictionStrictTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRootLinePowerTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteRootTensorPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteScalarCochainComparisonIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteScalarMonoidalRepresentative` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteScalarRepresentativeIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteScalarTensorData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteScalarTensorSource` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSheafH0Augmentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSignedTwistProducts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSiteCounitProjectionTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSiteTensorProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSourceChartPowerTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSourceChartScalarTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSupportFactorRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSupportOriginComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteSupportedReductionEquation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTargetChangeCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTateSourceMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTateSourceStructuralCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorComparisonEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorFixedComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorLineChartReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorLineDerivedExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorPresentationReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorProductFrameExt` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorProductMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorProductMapIsIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorPullbackCompositionReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorPullbackTensorReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorReductionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorSemilinearReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorShiftCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorShiftFirst` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorShiftSecond` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorSignedReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTensorSymmetryCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTripleProductDefinitions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTripleProductNormalForms` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteTypeCoordinateSupportOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FirstRootLinePullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FixProjectionCompactificationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FixedPresentationUniformizerReductions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ForwardProductCoordinateTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrameworkPbcComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrameworkPbcComparisonSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrameworkPbcIntegralComparisonLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrameworkPbcPullbackScalarBridge` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrameworkPbcRawComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrameworkPbcRawComparisonLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusAugmentationGeneric` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusCompactIntegralNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusCompactRationalNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusFixedPairComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusPullbackOrdinaryExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusSystemExchangeInverse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.FrobeniusWitnessedCompactification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeneralChartComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeometricCommonStageDirectImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeometricOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeometricQuotientWeilCompositionSeries` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeometricScalarFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GeometricSmoothReconstructionSetup` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GermReparametrizationDerivedDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GlobalIdentityNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.GlobalVerdierDualityData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.HigherIdentityCompositionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IdentificationCoefficientTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IdentityCoefficientTransportData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IdentityCompactificationLimitComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IdentityCompactificationSystemMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IdentityOpenSystemEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ImmersionWeilPullbackLocalBehavior` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralAdjunctionReconstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralAdjunctionSourceComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralClosedSupportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralCoefficientModelComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | P7 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralComparisonCanonicalShifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralComparisonCompositionReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralComparisonPullbackRealizationShifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralComparisonScalarRealizationShifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralComparisonSequenceScalarPullbackShifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralComparisonSystemData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralCompositionCoefficientSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralCompositorLimitRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralConstructibleReductionHom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralDatumPullCompositionReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralDualizingExceptionalUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralEquivarianceMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralEquivarianceNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralGeometricComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralGeometricComparisonRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralGeometricPurityRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralGeometricReindexingRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralGeometricSupportRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralGeometricTransposeIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralLissePullbackNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOpenAdjunctionReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOpenAdjunctionTransposeNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOpenEmptyPullbackVanishing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOpenProjectionCoefficientData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOpenPullTensorReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOpenSupportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOrientationShiftedSheafModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralOrientedExchangeSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPointTransportComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPointTransportTowerData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionCoordinateData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionDirectFactorEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionEvaluationFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionFactorData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionFactorEvaluationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionFiniteEvaluationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionLocalFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionMiddleMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionOpenFactorEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionOpenFactorReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionOpenTensorCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionOperationPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionProperFactorReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionPullEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionReductionCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionReductionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionReductionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionRefinementSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionSupportEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionSupportFactorCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionSystemCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionSystemEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProjectionTensorEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProperOperationProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProperProjectionCoefficientData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProperProjectionSystemNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProperSupportReductionIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralProperTensorPullbackReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPullbackAugmentationAmbient` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPurityComparisonCocycles` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralPurityCounitReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralQuotientCohomologicalBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralReconstructionComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralReductionJointFaithfulness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralReductionShiftedHomFiniteQcqs` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralScalarPullbackCompletionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralScalarPullbackCounitCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralSectionsPerfectReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralSemilinearGermSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralSmoothAdjunctionPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralStageProjectionReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralStageProjectionStructuralIdentities` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralSupportFunctorNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralSupportNormalizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralSupportReductionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegralTowerProjectionMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegrationAffineExponentTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegrationCoefficientProjectionNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegrationExponentTransposeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegrationExponentTransposeTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntegrationProjectiveExponentSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntrinsicConstructibleFibreExactness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IntrinsicLocalLatticeComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismFieldTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismFieldTransportClauses` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismFieldTransportCommonStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismFieldTransportFiniteStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismFieldTransportRationalScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismFiniteExchangeCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismOrdinaryCompletionChain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismOrdinaryModuleNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismPullbackRawStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismPullbackTExactCoefficients` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IsomorphismScalarComparisonAgreement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IteratedPurityScalarPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IteratedReturnTransportData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IteratedReturnTransportScalarCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IteratedTateSourceComposite` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.KummerSiteCohomologyNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LineCounitComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LineKummerFieldRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LineZeroClassExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseLatticeChoiceExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseLatticeHeartLift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseLatticeHeartLiftData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseLatticeLisseDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseLatticeNormalizedRealizations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseLatticeRealizationFaithful` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseLatticeSingleComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LissePointSectionsRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseTensorPullbackRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LisseTensorPullbackRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusLargeCoefficients` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusLargeScalarTower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusLargeTransportAddition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusLargeTransportNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusLargeWeilAddition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusStepCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocallyClosedRelativeTransposeNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocallyFiniteAdicCompactSupportData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | G6 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.LocallyFiniteCompactSupportStageAction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MiddleExchangeProjectionBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCompactSupportExchangeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupCoefficientChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupCoefficientData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupCoefficientSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupFieldCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupFieldNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupFieldOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupNormalizedScalars` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupOperationComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupRingedNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupTensorClosure` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupTensorComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupTensorElementary` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.MixedCupTensorNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ModelAffineIntegrationOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ModelChartOrientationAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ModelOrientationChartDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ModelOrientationSourceNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ModelOrientationTateDetection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeAdicCompactSupportSums` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeAdicFiniteNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeAdicRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeAdicReindexingData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeAdicTensorReindexing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeCoefficientInverseImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeCompactSupportFiniteComparison` | G8 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeCompactSupportGeometry` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeConstantSupportModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeDirectImageSections` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeGeometricBrownConstructibleComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeProperCoefficientOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeProperTensorComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeReductionCounitKFlat` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilComparisonStructure` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilDerivedInductionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilDualizingHomTransposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilFreeCoproduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilHeartProperties` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilInductionComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilInductionSummands` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilLocalizingBrownAdjoints` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilProperNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilScalarCounitCategories` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilScalarCounitData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalModelSectionOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalSectionIntegrationBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalSectionIntegrationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalSectionIntegrationOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedCommonCoefficientLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedCommonEvaluationForStructure` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedCommonEvaluationNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedEtaleComparisonComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedEtaleRestrictionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedFieldPurityTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedFieldPurityTraceCommonStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedFieldPurityTraceData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedFiniteRealizationFibre` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedHeartRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedIntegralGeometricCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedIntegralMixedCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedIntegralScalarCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedIntegralTraceData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedLatticeFiniteFree` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedPullbackCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedPullbackNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedPullbackObjects` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedRationalLeftComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedRationalLeftIdentity` | X9 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedRationalLeftLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedRingRefinementLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedSmoothOrientationUnits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedStageCoefficientCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.NormalizedSupportEtalePresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenProjectionFactorCoefficientChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenProjectionFactorCompositorTransport` | S6 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenProjectionIsoCoefficientChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenWeilCarrierRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenWeilCoefficientFibres` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenWeilFiniteStageFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenWeilGeometricFibres` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OpenWeilPunctualSpectrum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OperationCoefficientActionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OperationScalarTransportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedAffineComparisonNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedAffineLineTransposeNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedAffineTransposeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedAffineTransposeProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedAffineTransposeSuccessor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedIntegrationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedLineLevelBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedTateTowerCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrderedTowerOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrdinaryOpenScalarComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrdinaryScalarBalancingLevel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrdinaryScalarReductionGenerators` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationCoefficientTwists` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationCoordinateBoundaryPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationCoordinateModelBoundary` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationEtaleCoefficientTwists` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationFiniteCoefficientTwists` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationFiniteReductionTwists` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationGeometricComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationGroundFieldRetagging` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationIntegralCoefficientTwists` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationLocalResidue` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationPerfectLines` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationScalarPropagation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientationScalarTowerTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientedDoubleHomCancellation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OrientedPerfectDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.OriginalScalarMateShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.P1KummerTraceSiteTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PairingData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PbcConstantWeilTwist` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PbcWeilCoefficientComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PerAdicNormalizedFibreComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PerfectDualPairAndTateStability` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PfReductionProperOpenIdentities` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodCompletionReindexCoefficientTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodCounitScalarWordCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodMixedSupportCupProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodNormalizedTensorSignedShifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReconstructionCommonStageCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReconstructionCommonStageData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReconstructionRawRationalNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReconstructionScalarRealizations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReindexingCompletionUnitTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PodReindexingTensorCoefficientTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PoincareDualityConventions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointAutomorphismDerivedTransportInverse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointAutomorphismTransportScalarExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointEquivariantCommonStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointEquivariantDiagramData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointEquivariantDiagramLift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointEquivariantFiniteScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointEquivariantOriginalDiagram` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointExactDerivedModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointFiniteMultiplicationInverse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointFrobeniusNormalizationDefinitions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointHeartExactness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointHeartFiniteStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointHeartFiniteStageData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointHeartFiniteStageEquivalences` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointHeartFiniteStageScalars` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointHeartFiniteStageTruncations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointIdentityExchangeRecipe` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointIntegralRestrictionNatural` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointInverseImageCoefficientTower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointPowerRoosComparisonSpecialization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointPowerStrictInsertionSpecialization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointPullbackConeLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointQuotientComparisonCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointQuotientTowerCoherentSource` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointQuotientTowerData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointQuotientTowerHomotopy` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointRealizationStandardCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointReductionAugmentationComplete` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointRestrictionWholeRoosSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointRootLimitCyclotomicAction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointScalarCompatibleTransportTransfer` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointScalarPunctualSpectrum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointScalarSingleStepCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSignedCyclotomicAction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSignedCyclotomicActionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSignedCyclotomicScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemInsertionComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemInsertionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemNormalizedComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemNormalizedComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemPowerRoosData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemRoosComparisonAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemRoosRestrictionAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemRoosTransportData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemRoosTransportRepresentative` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemStrictInsertions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointSystemTransportDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTateCommonStageCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTateDerivedComparisonCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTateFiberCanonicalComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTateFiberCoefficientComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTateFiberComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTateFiniteSectionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTateNormalizedSectionGenerators` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportResolutionCancellation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportStrictQuotient` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportStrictQuotientAllComplexes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportStrictQuotientFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportStrictQuotientIdentities` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportStrictQuotientModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportStrictQuotientSections` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportTowerRealizationAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportTowerRealizationConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportTowerRealizationIdentities` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointTransportTowerRealizationSpec` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilAlgebraicFlag` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilFiniteStageDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilHeartFlag` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilHeartFlagData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilPairingCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilTensorRepresentatives` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PointWeilTransportUnitShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PositiveRootGeneratorExt` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PositiveRootTensorProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleAffineLineCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleFrameIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleOrderedIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleProjectionIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleProjectiveCoefficient` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleProjectiveLineTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleVectorIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProEtaleVectorIntegrationArrows` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductCompositionCoordinateComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductExchangeCoordinateDefinitions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductExchangeCounitCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductHorizontalExchangeFactorization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductOpenAdjunctionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductOpenCounitNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductOpenSupportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductOpenTensorProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProductOpenTensorProjectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionCompactificationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionFactorCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization` | T5 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionFiniteBaseChangeTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionIdentityAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionIdentityProperCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionIdentityPullbackUnits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionIdentityTensorUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionMateFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionPurityCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionReductionPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionReductionWitnessedFlatDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionScalarSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionTensorActionExpansion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionTensorCoefficientCocycles` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionTensorIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionUnitIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionUnitPresentationNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectionWeilTensorDomainBridge` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperBiproductCoordinate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperCoefficientDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperCoefficientDescentData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperCompactCoefficientActionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperCompactIntegralComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperCompactRationalFunctorComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperIntegralScalarSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperIntegralTowerComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperRationalScalarSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperSupportCoefficientAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperSupportFiniteAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperSystemEvaluationTransitions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ProperWeilIterateGermFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PulledOrderedLineSingle` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurCoordinateRepresentingFamily` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurIntegralRepresentingPairData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurIntegralSupportComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurIntegralSupportComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurIntegralSupportDerivedComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurIntegralSupportOrdinaryComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurRepresentingPairFiniteScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurShiftedTateUnitScalarCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurSupportPresentationAlpha` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurTateUnitFlatModelDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityAffineChartExceptionalIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityAffineLineBoundaryRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityAffineLineOrientationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityCompactSupportTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityCompositionComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityCompositionCompatibleDncCharts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityConstantFamilyBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityFiniteReductionTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityKappaStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityKummerTriangleConcentration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityOrientationDatum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityPullbackLevelBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityPullbackReductionTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityRankZeroFamilyReadings` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionBaseComparisonLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionConstantTrivialization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionEtaleRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionFibreSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionNormalizedSpecialization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionRestrictionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityTateDatum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityTowerReductionComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityWitnessedMateNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.PurityWitnessedOpenChartTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportFiniteComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportFiniteMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportImageComplete` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportNormalizedLift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportOpenComplete` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportProperComplete` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportReductionRigidity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionGamma` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` | E4 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QuotientGermTower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.QuotientStalkNaturalDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RamifiedImageBalancingEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RamifiedQuotientSectionPushout` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RamifiedReductionComparisonSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalAmbientPullComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalAmbientPullModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalBalancedFreePullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalContinuousComparisonCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalContinuousFiltrationModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalContinuousPullbackTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalCoverReflectsIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalEvaluationCover` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalOrdinaryCohomologyTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalProjectionComparisonEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalProjectionTensorCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalProjectionTensorModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPullSingleComputation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPullbackCompositionCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPullbackFibreComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPullbackFlatComputationCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityCoefficientModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityCompactLattices` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityCompactScalarInvertible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityExchangeEndpointData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityExchangeEndpoints` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityFiniteAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityIdentityDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityLocalizedFamilyData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityPresentationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityScalarModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalPurityTwistedExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalRealizationFiniteConeModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalRealizationHomTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Same public declarations through the original module; quarantined source is unchanged. |
| `Sheaf.Paper.RationalRestrictionComparisonCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalReturnBlockPower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalScalarBalancedLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalScalarCompletionUnitSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalScalarMixedUnitCancellation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalScalarSingleStepNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalStratumPullbackData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalStratumPullbackModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalTwistedPullbackCompositor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalizationOrientedExchangeSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RealWeights` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RealizedPullbackComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReconstructedBrownMateLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReconstructedPairRefinementData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReconstructedRefinementCommon` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReconstructedRefinementSingleDegree` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReconstructedRefinementTraceSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReconstructedRefinementTraceTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RefinementFiniteOriginEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReindexingSystemHomReductionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeKummerSiteNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeKunnethClosedFibre` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeKunnethConstructions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeKunnethCubeFactorTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeProductCoefficientFactorSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeProductFactorSquaresCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeProductFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeProductProperCompatibilityCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RestrictedAffineDiagonalDncTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RestrictedAffineDiagonalDncVectorCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RestrictedAffineDiagonalSectionTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RestrictedAffineDiagonalTraceBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RestrictedAffineDiagonalVectorIntegration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RetaggingCoefficientTowerTransfer` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RetaggingCoordinateOrientations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ReturnScalarSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RingOpenRefinement` | T8 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.RingRefinementScalarWord` | T9 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SbcDatumExchangeComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarComplexAdjunctionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | D2 | Publicly re-export unchanged comparison data; retain coherence and realization statements. |
| `Sheaf.Paper.ScalarFibreCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarFibreComponentData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarFibreComponents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarFibreNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarHomPresentationEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarLimitConstraintShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarLimitRestrictionKInjective` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarLimitRestrictionLimits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarLimitTensorComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarLimitTensorKInjective` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarLimitTensorRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarPullCoefficientComplexNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarPullCoefficientModuleTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarPullCoefficientTotalTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarPullTensorCoefficientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarReductionTowerBalancing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarRefinementOriginsE` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarRefinementOriginsF` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarRestrictionComplexNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarRoosComparisonUnique` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarSourceCounitUniversal` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ScalarTargetCounitUniversal` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SectionDncIntegrationSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SectionEtaleOpenCancellation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SectionsRationalModelComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearCommonOrdinaryCubes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearCommonRefinementCubes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearCommonSupportCubes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearExchangeCubeCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearExchangeCubeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearExchangeDescentData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearExchangeReindexing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearExchangeReindexingData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearGermIterationDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearRationalOrdinaryCubes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearRationalRefinementCubes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SemilinearRationalSupportCubes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfAdicCommonStageDescentEquivalence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfBcCompletedMateDomain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfCompletedExchangeTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfFieldMateDomain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfFrameworkThetaShiftCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfIntegralLocalizationConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfNormalizedCommonStageWeilSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfNormalizedRationalClosedComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfNormalizedRationalWeilSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageBaseChangeDomainRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageCommonStageTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageIntegralRecollementNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageIntegralRecollementSource` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageIntegralSupportTowerNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageLocalizationBoundaryData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageLocalizationBoundaryDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageLocalizationRationalTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPackageQbarAdjunctionMapDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfPositiveFiniteLocalizationConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfQbarLocalizationCommonStage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfQbarLocalizationExactDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfQbarLocalizationFiniteCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfQbarLocalizationFiniteData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfRationalLocalizationOrthogonality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SfRecollementReductionBoundary` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ShiftedCoefficientLinesInvertible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SimultaneousIntegralPullbackComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorMixedSupportCupProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOrientationDatum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOrientationFamily` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOrientationFiniteFamily` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOrientationHigherPair` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SixFunctorOrientationStageCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothExceptionalTensorPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOperationCoefficientModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOperationDescentSpecification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOperationIdentificationSpecification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOrientationCoefficientFamily` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOrientationPuritySquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOrientationStageExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOrientationTransportSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothOrientedExchangeComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityBaseChangeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityBaseChangeFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityCompositionFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityTensorUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SourceSectionAutomorphismModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SourceSectionIdentityModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SourceSectionRestrictionModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SourceSectionStalkConeComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SourceSectionStalkConeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SpecifiedIntegralUnitOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SpecifiedTowerAdjunctionCharts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictCoefficientOpenReduction` | V7 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictCoefficientProperReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictDirectImageMixedUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictDirectImageMixedUnitData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictMixedFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictMixedScalarSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictMixedSystemModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictProperBiproductCoordinate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictProperCompositionRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictProperRestrictionComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictQuotientStalkReindexing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictReductionCompactSupportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictRefinementRestrictionSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictRefinementSeedRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarFiniteEvaluationTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarMateEvaluationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarMateFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarMateShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarOpenComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarOpenUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarProperComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarPullComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.StrictScalarTowerAssociator` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SupportedCartierDerivedPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SupportedProjectiveChern` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SupportedProjectiveChernComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemCompactSupportRestrictionCocycle` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemCompositorRefinementSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemIdentityOpenEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemProjectionChangeCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemProjectionFormulaMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemProjectionTriangleCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemProperIdentityOpenProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemRefinementFiniteCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemScalarBasisDistributivity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemScalarProjectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemScalarRefinementRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemScalarTensorConstituents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemTensorPresentationCoreExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemTensorPresentationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemTensorPresentationIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.SystemTensorSemilinearRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorExchangeCtfDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorHeartSpecialization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorMapPresentationIndependent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorMateBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorMateInvertibleInput` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TensorTransposeTowerNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerFactorOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerFactorTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerGeometricPurityAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerGeometricPurityData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerGeometricPurityMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerIsomorphismPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerMuEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerNormalizationPreservation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerOrientationEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerOrientationWordNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerPurityAdjointTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerPurityPresentationRetagging` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerPurityRealizedData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerPurityRealizedNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerSemilinearPurityFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTateSplitNormalized` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTensorAdjointDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTensorPresentationRetagging` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTraceCanonicalIntegral` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTraceNormalizedPresentations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTraceOrientationUniqueness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTracePurityComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTracePurityComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TowerTraceScalarCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceBoundedQuotientStalkRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceStalkCompositorTowerData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceStalkCompositorTowerRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceStalkTowerDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TraceStrictStalkTowers` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TransportCondensedStageRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TransportIntegralBaseChangeRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TransportIntegralChartRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TransportIntegralCompositionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TransportIntegralCounitData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TransportIntegralCounitRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TransportIntegralStageConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwConventions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionCartier` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionOrdinary` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionProjective` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedCoordinateSectionSign` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackAdicIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackCoefficientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackCofinalModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackLineMembership` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackReductionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackReductionTower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackScalarPrimitives` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackTateReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackTowerBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackTowerDomain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.TwistedPullbackTowerOrigins` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.UniformTowerTensorClosure` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.UnshiftedLineUnitTower` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VaryingDimensionDualizingInverse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorBundleFrameOrientationRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorFrameIntegrationSiteDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorIntegrationChartComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorIntegrationChartCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorIntegrationChartTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorIntegrationIdentityAdjunct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorIntegrationUnitTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorModelChartDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorNormalizedTraceCartesian` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorTensorOrdinaryNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorTensorProjectionComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorTensorSiteEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VectorZeroSectionIntegrationBaseChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierCompositionMateNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierHomChainComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierIdentityProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierPairingThreeTransposes` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilChosenExchangeConstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilChosenTransposeNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilEquivarianceOfPurityAndTrace` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilGenericLissity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilGeometricFiberProperties` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilIndOpenRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilIndOpenRepresentability` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilIndProperHigherRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilIndProperHigherRepresentability` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilIndProperOpenHigher` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilPullbackFibreReturn` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilPurityEquivarianceData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WeilTateTwistFrobenius` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WfTateTwist` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WfTateTwistCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlCanonicalImmersionCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlImmersionFilteredReductionTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlImmersionPullbackWeightPreservation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlImmersionRestrictionAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlImmersionWeilLocalData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlOpenCompactSupportRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlOpenDiagramComparisonTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlOpenExtensionAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlOpenExtensionTExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlSfPbcNormalizedHeartModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlWeilHeartLocalizationExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlWeilPullCompositorEquivariance` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.Paper.ZlWeilShriekCoefficientLongExact` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingExponent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.NestedAffineChartFormulas` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.NestedAffineFormulaData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.RationalPurityCommonComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.RationalPurityLineComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.ReductionOrientation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientExactClopenComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientExactClopenData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientProperOpenCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientSystemBetaLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientSystemClopenLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CanonicalShiftSynchronization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CartesianCandidateCompositor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CartesianCandidateSiteSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CartesianCompactSupportCompositor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CartesianTowerRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefDualizingSiteMates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefFinitePairingEvaluationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefPairingCompactificationModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefPairingFiniteNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefPairingFrameNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefPairingHomRepresentativeComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefPairingSystemDinaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefQbarVerdierData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefQbarVerdierDualizing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefQbarVerdierExceptional` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefScalarReductionExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefSystemProjectionEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairingData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefVerdierWeilData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefWeilExceptionalCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefWeilNormalizedDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefficientDualizingClosedDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefficientProjectionPointData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefficientUnitFiniteTor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CoefficientUnitNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompactifiedProperTowerExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedOpenCartesianIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeDomains` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedProjectionExchangePaths` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedSystemPullbackPreservation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompletedTensorSlotShiftLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompositionProjectionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.DualizingSupportEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstruction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ExceptionalIntegralSystemExistence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransitionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdierData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteCounitRestrictionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteDualizingAffineRestriction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteDualizingData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteDualizingScalarRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteExceptionalData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteExceptionalDomain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteExceptionalQuotientIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteIntrinsicBidualComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteMappingAdjunctionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteOpenCartesianCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteVerdierCoefficientDiagrams` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FiniteVerdierProEtaleLeftTor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusCohomologyCoefficientCocycle` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusCohomologyComparisonFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRationalCocycle` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusPointTransportQbarNaturalTransformation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.FrobeniusPointTransportRationalScalar` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralBasicGeneratorSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralBasicRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralBasicRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCanonicalAmbientModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCanonicalRealizationSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCanonicalSystemCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationRealizationData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralComparisonRecursionLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralConstantCompleteTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralConstantCompleteTransportHom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralDualizingFiniteBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralDualizingMappingLimit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralDualizingRoosModel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExceptionalLimitConstructible` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExpressionCanonicalEquations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExpressionCanonicalSupport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExpressionCoefficientSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExpressionRecursionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralExpressionTransposeIsIso` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOpenFiniteEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOpenRealizationNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOpenScalarUnitSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares` | W9 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares` | X5 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOrdinaryExpressionNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | X7 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralProperFiniteProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralRealizationAssemblyData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | K2 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralSupportCounitProjection` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralSupportProjectionTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralSupportRealizationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralSupportTowerNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralSystemDualityCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransport` | Y7 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralVerdierModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.IntegralVerdierSignedCalculus` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.KappaCoefficientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.KappaGeometricComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.KappaMixedCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.KunnethFirstOpenSubstitution` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.KunnethSecondOpenSubstitution` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenBaseChangeReductionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenBaseChangeSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenBaseChangeSquareData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCoefficient` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCompletion` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenClosedWeilMateDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenClosedWeilMateFinite` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenClosedWeilMateIntegral` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenExternalTensorNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenFactorCoherenceData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenFactorExchangeRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenFactorOpenRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenFactorProjectionRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenInterchangeReductionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenInterchangeReductionSquares` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenNormalizedProductCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenScalarAdjunctionCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenSupportStepBounds` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OpenTensorReductionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OrdinaryAmbientAlphaPasting` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OrdinaryAmbientAlphaUnits` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.OrdinaryProperOpenInvertibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProductCompactificationIdentity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProductSystemUniformRealizationDomain` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionRefinementComparisons` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionRefinementData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionRefinementDescent` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionRefinementInputs` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionRefinementNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionRefinementSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProjectionSystemCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProperOpenLambdaReductionSquare` | Z7 | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.PublishedSystemAmbientCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.PublishedSystemTensorComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RamifiedScalarPreparation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RamifiedScalarSupportCompatibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalDualizingIdentification` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalExceptionalIdentifications` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalHomIdentifications` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalOperationsData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalVerdierComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalVerdierDatum` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalVerdierExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalVerdierModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RationalVerdierUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RealizationTreeShiftData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RealizationTreeSingleShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RealizationTreeSystemSquare` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RefinementProjectionCounit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RefinementProjectionLocalTensor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RefinementProjectionProperComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.RefinementProjectionWords` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SemilinearOpenExternalCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.StrictCompactificationProjectionShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.StructuralReductionWordSubstitution` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SupportedWeilMateLift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemProperOpenLambdaExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemProperOpenSupport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemTensorShiftCoherence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.SystemTotalEnrichedTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.TensorExchangeCoherentConclusions` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.TensorExchangeNormalizedModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.TensorExchangePresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.TensorHomTranspositionData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.ThreeCellCompositor` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.TriangleProjectionNormalForm` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.TriangleProjectionSystemNormalForm` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.VerdierExchangeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SmoothPurity.OrdinaryProductTransposeData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SmoothPurity.OrdinaryTripleLeftComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SmoothPurity.OrdinaryTripleProductTranspose` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.SmoothPurity.OrdinaryTripleRightComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.CompactDirectPowerTransportNormalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.FrobeniusCompactPowerExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.FrobeniusProperPowerExchange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.LocalNormalizationStrictRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.PointConeLiftsChainNaturality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.PointExactRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.CompactSupportBrownConstructibility` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.DualRealizationComparison` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeBidualEvaluationRealization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetful` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetfulData` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeExceptionalLeftModels` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeExceptionalPointUnit` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeExceptionalStructuralTransport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.OrdinaryClosedPresentation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.WeilSheaf.StructuralOmegaHomPairs` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.Statement` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.Karoubian` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.KaroubianPointer` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.VerdierDual` | Q1 | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Same declarations and bodies through the original public import; compile direct importers. |
| `TargetsCheck` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.ScalarExtensionTowerComparisonData` | D2 | Own the unchanged normalized comparison construction. |
| `Sheaf.Paper.ScalarExtensionTowerComposition` | D2 | Own the completed original composition proof; no new hole. |
| `Sheaf.Paper.AdicNormalizedPullbackRealization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.AdicProperOrdinaryPushPreservation` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.ComparisonPullbackRestrictionCoherence` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.CondensedTateIntegralTower` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.CondensedTateIntegralTowerData` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.ContinuousAmbientGeometricCoherence` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.DiagonalEtaleLocalityUnitChange` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization` | P4 | Same public declarations through the original module. |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | F4 | Same public declarations through the original module. |
| `Sheaf.Paper.FdNormalizedPullbackGeometry` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FdNormalizedPullbackIntegralScalar` | V7 | Same public declarations through the original module. |
| `Sheaf.Paper.FdNormalizedPullbackMixed` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteIntrinsicProjectionRealization` | T1 | Same public declarations through the original module. |
| `Sheaf.Paper.FinitePartialTensorIdentityComposition` | T2 | Same public declarations through the original module. |
| `Sheaf.Paper.FinitePuritySourceUnitReduction` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteSupportIdentityFactorCompositor` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.HigherTensorIdentityComposition` | T3 | Same public declarations through the original module. |
| `Sheaf.Paper.IntegralAutomorphismCancellationNormalization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.IntegralPublishedCounitEvaluation` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.IntegralReductionShiftedHomFiniteAlgClosed` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.IntegralScalarCounitNormalization` | G1 | Same public declarations through the original module. |
| `Sheaf.Paper.IsomorphismFieldTransportEpsilonNaturality` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.IsomorphismFieldTransportShiftDescent` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.NormalizedScalarAssociatorLocalization` | Q5 | Same public declarations through the original module. |
| `Sheaf.Paper.NormalizedTateTensorTower` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.NormalizedTateTensorTowerCore` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.NormalizedTateTensorTowerProperties` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.NormalizedTateTensorTowerZero` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.RationalRealizationOrdinaryLocalization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.RingCanonicalScalarInvertibility` | Y9 | Same public declarations through the original module. |
| `Sheaf.Paper.RingEndpointScalarRestrictions` | A3 | Same public declarations through the original module. |
| `Sheaf.Paper.SystemDirectImageEffectivity` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.SystemFiniteCompositorCoordinates` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.SystemFiniteEvaluationCoordinates` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.SystemFiniteRefinementMateCoordinates` | unclaimed | Same public declarations through the original module. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent` | unclaimed | Same public declarations through the original module. |
| `Sheaf.SixFunctors.IntegralFiniteProperMate` | unclaimed | Same public declarations through the original module. |
| `Sheaf.SixFunctors.IntegralFinitePullbackCoordinates` | unclaimed | Same public declarations through the original module. |
| `Sheaf.SixFunctors.IntegralFinitePullbackNormalization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Same public declarations through the original module. |
| `Sheaf.WeilSheaf.StructuralBidualInvertible` | A9 | Same public declarations through the original module. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.BorelMoore` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.CoefficientMorphism` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.Correspondence` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.CorrespondencePair` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.CurvePieces` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.Dualizing` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.FrobeniusLocalTerm` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.GenericQuotient` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.HomologyUnit` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.KunnethVerdier` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.LefschetzVerdier` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.LocalTerm` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.LocalTermLocality` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.Main` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.PointNormalization` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.Product` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ProperCompatibility` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ProperCurve` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ProperPushforward` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ProperPushforwardKernel` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.PullbackFamily` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ShriekTraceFunction` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionInduction` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.SupportedPairing` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.TraceClass` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.TraceClassAdditivity` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.WeilBaseChange` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.WeilSheafUpperStar` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.TraceFormula.WeilTrace` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Same public declarations through the original module. |
| `WeilConjectures.ZetaFunction.WeilObjectComparison` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.CompactSupportScalarCompletionNormalization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FdCoefficientScalarCompletionIdentification` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FdPullbackRoosMatchingUniqueness` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteDirectCounitFixedRealization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteProjectionFixedCoordinates` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteProperProjectionFixedRealization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FinitePullbackTensorFixedCoordinates` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.IntegralNormalizedRingRefinementLaws` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.OmegaProperCoefficientProjection` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.RefinementOpenRestriction` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.RingOpenMapInvertibility` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.ScalarGeometricPullComposition` | unclaimed | Same public declarations through the original module. |
| `Sheaf.SixFunctors.OpenRoosRestrictionDescent` | unclaimed | Same public declarations through the original module. |
| `Sheaf.SixFunctors.OpenRoosUnitAdjunction` | unclaimed | Same public declarations through the original module. |


| `Sheaf.Paper.CompactSupportNativeEffectivity` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.CompactSupportNativeRealization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.CompactSupportScalarLimitCompletedComparison` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.CompactSupportScalarRoosNormalization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.CompactSupportScalarRoosTensorNormalization` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.ExceptionalRingTransportFamily` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.IdentityFactorCoefficientComparison` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.NormalizedIntegralScalarUnit` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.OmegaProperCoefficientProjectionHomology` | unclaimed | Same public declarations through the original module. |
| `Sheaf.Paper.RationalScalarObjectTransport` | unclaimed | Same public declarations through the original module. |

## Status

landed 20261027T135058-L-3664568 2026-10-27 (merge of deliver/D2/Sheaf.Paper.ScalarExtensionTowerCoherence)

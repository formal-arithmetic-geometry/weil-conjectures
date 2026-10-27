# PointCompletedEvaluation canonical-map interfaces

## Reason

Repeated model and strict-cone definitions and normalization formulas make checking
expensive. This refactor preserves all mathematical objects, formulas and conditions.
The theorem `point_completed_evaluation` keeps its original signature. Its `Result`
predicate groups the original six unit, Hom and ordinary normalization proof witnesses into
`PointPerfectOrdinaryEvaluation.Normalized`, precisely the conjunction of those formulas.
All data witnesses are unchanged. The six proofs move after the data, without any
dependency on the moved proofs. Expanding the predicate and termwise-model abbreviation
and distributing conjunction recovers exactly the original existential statement.
No hypothesis or assertion is added, dropped or weakened.

`R`, `B`, the localizations, coefficient, total and model alias the existing completion
normalization constructions. The ring complex, dual and coefficient coordinate maps
alias the definitionally identical projective-model constructions. The generator uses
the existing generator with the object equality from `extension_spec`, identified
with the original choice-specification equality by proof irrelevance. The generator
and tensor comparison have inferred return types; their morphisms stay identical.
The extension functor, unique-existence theorem and additive instance are unchanged.
The proved `extension_spec` states their canonical object, additive and morphism
specifications with the named extension in its type. The extension is locally
irreducible after this API, avoiding repeated expansion of its unique-choice predicate.

The balancing existence theorem uses the existing `Balanced` predicate, whose body
is the original quantified formula. `towerBalancing` chooses directly from unique
existence; uniqueness identifies it with the original choice. The unused `roosBalancing`
wrapper is removed. `completedEvaluation` calls the existing `completedPairing` with
the fixed balancing isomorphism. Functor composition and associativity give its original
formula; `Iso.app_inv` and `Iso.symm_inv` identify its initial component. Its return
type is inferred.

`Result`, balancing, completion and tensor comparison are irreducible. The repeated complex-model abbreviations alias exactly the same existing constructions.
Fully proved private APIs supply the constructor, unit and tensor cancellation, and
the inverse-comparison argument. No new hole is added. The projective, ordinary and
completion modules are public imports because public definitions refer to them.
Other added proof imports are private. The unused direct public imports of
`PointDerivedHomEvaluation` and `DerivedPullbackTensorHom` are removed. The former's
model definitions are already public through `PointProjectiveDualTensorModels`; the
latter remains transitively public through the required point-tensor interfaces.
Their statement-dependency entries are removed because none of the actual statement
formulas uses those theorems. No module is withdrawn.

## Old

```lean
abbrev R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The completed coefficient sheaf on the original small pro-etale site.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev B := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))

/-- The recorded standard localization of completed-coefficient sheaf complexes.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev sheafQ := @DerivedCategory.Q (integralTowerModules l E (Spec (.of D.k))) _ _
  (HasDerivedCategory.standard _)

/-- The same small-Hom localization of ordinary modules used by the point fibre.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev moduleQ := @DerivedCategory.Q (ModuleCat.{u + 1} (R l E)) _ _
  (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The existing constant-to-completed coefficient map.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev alpha := PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true

/-- The ordinary coefficient complex R[0]. Source: Stacks 0A8H
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev ringComplex := (CochainComplex.singleFunctor (ModuleCat.{u + 1} (R l E)) 0).obj
  (ModuleCat.of (R l E) (R l E))

/-- The completed coefficient complex B[0]. Source: blueprint point coefficients
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev coefficient := (CochainComplex.singleFunctor
  (integralTowerModules l E (Spec (.of D.k))) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))

/-- The functor is uniquely specified on objects and maps by the existing tensor construction.
Source: Stacks 03CY, 03EK; node proof step 1
(blueprint: lem-pod-point-completed-evaluation).
Proof: use the functoriality of constant-module sheafification and of change of rings.
Their identity, composition and additive laws hold on the sheafification generators,
by the corresponding laws for constant linear maps and tensoring with the identity.
The displayed object and morphism equations determine the functor uniquely. -/
theorem extension_existsUnique :
    ∃! L : ModuleCat.{u + 1} (R l E) ⥤ integralTowerModules l E (Spec (.of D.k)),
      (∀ M, L.obj M = PointDerivedHom.extensionObject.{u, u} D.k (B D l E)
        (alpha D l E) M) ∧
      L.Additive ∧
      (∀ (M N : ModuleCat.{u + 1} (R l E)) (f : M ⟶ N),
        HEq (L.map f) (PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E)
          (alpha D l E) f)) := by
  let := PointDerivedHom.abSheafify.{u, u} D.k
  let := PointDerivedHom.abLocallyBijective.{u, u} D.k
  let T := SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u}
    (alpha D l E)
  let L := PointDerivedHom.constantModules.{u, u} D.k (CommRingCat.of (R l E)) ⋙ T
  have : T.Additive :=
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction (alpha D l E)).left_adjoint_additive
  have : (PointDerivedHom.constantPresheaf.{u, u} D.k
      (CommRingCat.of (R l E))).Additive := ⟨by intros; rfl⟩
  have : (PresheafOfModules.sheafification
      (PointDerivedHom.constantUnit.{u, u} D.k (CommRingCat.of (R l E)))).Additive :=
    (PresheafOfModules.sheafificationAdjunction
      (PointDerivedHom.constantUnit.{u, u} D.k (CommRingCat.of (R l E)))).left_adjoint_additive
  have : (PointDerivedHom.constantModules.{u, u} D.k (CommRingCat.of (R l E))).Additive := by
    dsimp only [PointDerivedHom.constantModules]
    infer_instance
  refine ⟨L, ⟨fun _ ↦ rfl, inferInstance, fun _ _ _ ↦ HEq.rfl⟩, ?_⟩
  intro L' hL'
  exact Functor.hext hL'.1 (fun M N f ↦ hL'.2.2 M N f)

/-- Actual constant-module extension, uniquely fixed by its existing object and map formulas.
Source: node proof step 1 (blueprint: lem-pod-point-completed-evaluation). -/
def extension := (extension_existsUnique D l E).exists.choose

/-- Additivity supplied by the canonical functor construction.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
instance extension_additive : (extension D l E).Additive :=
  (extension_existsUnique D l E).exists.choose_spec.2.1

/-- Apply the canonical extension termwise.
Source: Stacks 0A8X (blueprint: lem-pod-point-completed-evaluation). -/
def extensionComplex := (extension D l E).mapHomologicalComplex (.up ℤ)

/-- The same tensor generator transported through the uniquely fixed object equality.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
def generator (M : ModuleCat.{u + 1} (R l E))
    (U : (Spec (.of D.k)).ProEtᵒᵖ) (b : (B D l E).obj.obj U) (x : M) :
    ((extension D l E).obj M).val.obj U :=
  (eqToHom ((extension_existsUnique D l E).exists.choose_spec.1 M).symm).val.app U
    (PointDerivedHom.extensionElement.{u, u} D.k (B D l E) (alpha D l E) M U b x)

/-- The ordinary derived dual's bounded-projective chain model, with the recorded differential.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
abbrev dual (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  CochainComplex.moduleHomComplex P (ringComplex l E)

/-- The specified ordinary sheaf tensor model.
Source: Stacks 06YL (blueprint: lem-pod-point-completed-evaluation). -/
abbrev total (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  PointDerivedHom.total.{u, u} D.k (B D l E) C J

/-- The balancing identification of the two strict towers, uniquely on local generators.
Source: Bhatt--Scholze 3.4.10 and node proof step 6
(blueprint: lem-pod-point-completed-evaluation).
Proof: in every degree reassociate the balanced tensor products and total sums.
Send (x tensor a) tensor (y tensor b) to (x tensor y) tensor ab; the inverse sends
(x tensor y) tensor a to (x tensor 1) tensor (y tensor a). Balancing and the
signed differential give inverse chain maps. The quotient formulas commute with
all transitions. Sheafification and the total injections make the maps unique. -/
theorem towerBalancing_existsUnique
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! rho : ((integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J)) ≅
        ((integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
          (total D l E C J)),
      ∀ (n : ℕ) (p j : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (a b : (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n).obj.obj U)
        (x : (C.X p).val.obj U) (y : (J.X j).val.obj U),
        ((rho.hom.app (op n)).f (p + j)).val.app U
          (integralOperationsTotalTensorSection l E (Spec (.of D.k)) n C J p j U
            (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (C.X p) U a x)
            (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (J.X j) U b y)) =
          integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
            ((total D l E C J).X (p + j)) U (a * b)
              (PointDerivedHom.totalElement.{u, u} D.k (B D l E) C J p j U x y) := by
  sorry

/-- Balancing of the specified strict towers, with no arbitrary cone filler.
Source: node proof step 6 (blueprint: lem-pod-point-completed-evaluation). -/
def towerBalancing (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  (towerBalancing_existsUnique D l E C J).exists.choose

/-- Its actual functorial shifted-cone map acts on both product coordinates.
Source: Stacks 08TC (blueprint: lem-pod-point-completed-evaluation). -/
def roosBalancing (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  integralOperationsRoosFunctor.mapIso (towerBalancing D l E C J)

/-- Completed evaluation is the strict-cone completion of ordinary evaluation, followed
by the inverse of the specified coefficient completion unit. Both cone coordinates
are therefore fixed before localization. Source: node proof steps 6--7
(blueprint: lem-pod-point-completed-evaluation). -/
def completedEvaluation
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (e : total D l E C.obj J.obj ⟶ coefficient D l E)
    (b : (sheafQ D l E).obj (coefficient D l E) ≅
      (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).obj (coefficient D l E))) :
    (integralCompletedTensor l E (Spec (.of D.k))).obj
      ((sheafQ D l E).obj C.obj, (sheafQ D l E).obj J.obj) ⟶
        (sheafQ D l E).obj (coefficient D l E) :=
  (integralCompletedTensorComparison l E (Spec (.of D.k))).hom.app (C, J) ≫
    (sheafQ D l E).map (roosBalancing D l E C.obj J.obj).hom ≫
    (sheafQ D l E).map ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).map e) ≫ b.inv

/-- Reading the coefficient in a degree identified with zero uses the existing single-complex
isomorphism. Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def moduleValue (n : ℤ) (h : n = 0) : (ringComplex l E).X n ⟶ ModuleCat.of (R l E) (R l E) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (ModuleCat.of (R l E) (R l E)) n h).hom

/-- The same single-complex isomorphism for the coefficient sheaf.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def sheafValue (n : ℤ) (h : n = 0) : (coefficient D l E).X n ⟶
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))
      n h).hom


/-- The actual model B tensor underline P, rather than an arbitrary equivalent complex.
Source: node statement (blueprint: lem-pod-point-completed-evaluation). -/
abbrev model (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  (extensionComplex D l E).obj P

/-- The tensor comparison after identifying sections of C with P by its canonical unit.
Source: node proof step 8 and lem-sf-point-fibre-derived-tensor
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose] def tau (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :
    (pointFibreIntegralAmbient D l E).obj
      ((integralCompletedTensor l E (Spec (.of D.k))).obj
        ((sheafQ D l E).obj C, (sheafQ D l E).obj J)) ⟶
      (moduleQ l E).obj P ⊗
        (pointFibreIntegralAmbient D l E).obj ((sheafQ D l E).obj J) :=
  (pointIntegralTensorComparison D l hl E S
    ⟨(sheafQ D l E).obj C, hC⟩ ⟨(sheafQ D l E).obj J, hJ⟩).hom ≫
    (MonoidalCategory.tensor _).map
      (Prod.mkHom ((pointIntegralDerivedFactors D l E).hom.app C ≫
        (moduleQ l E).map unit.inv) (𝟙 _))


/-- All assertions concern the fixed perfect models and normalized canonical maps.
Source: node statement and proof steps 3--8
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose] def Result (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) : Prop :=
  ∃ (good_C : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E P)),
  ∃ (good_J : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E (dual l E P))),
  ∃ (_constructible_tensor : sfIntegralConstructible l E (Spec (.of D.k))
    ((sheafQ D l E).obj (total D l E (model D l E P) (model D l E (dual l E P))))),
  ∃ (ctf_C : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E P))),
  ∃ (ctf_J : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E (dual l E P)))),
  ∃ (homIso : model D l E (dual l E P) ≅
    PointDerivedHom.sheafHom.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)),
  ∃ (_hom_normalized : ∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (f : (dual l E P).X j) (x : P.X p),
    (sheafValue D l E (p + j) h).val.app U
      (PointDerivedHom.homValue.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)
        j p U ((homIso.hom.f j).val.app U
          (generator D l E ((dual l E P).X j) U b f))
        (generator D l E (P.X p) U b' x)) =
      b * b' * PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
        ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x))),
  ∃ (_derivedHom_isIso : IsIso ((sheafQ D l E).map homIso.hom ≫
    IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E)
      (model D l E P) (coefficient D l E))),
  ∃ (unit : P ≅ (pointIntegralComplexSections D l E).obj (model D l E P)),
  ∃ (_unit_normalized : ∀ (p : ℤ) (x : P.X p), (unit.hom.f p).hom x =
    generator D l E (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x),
  ∃ (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E)),
  ∃ (_coefficientUnit_normalized : ∀ x : (ringComplex l E).X 0,
    (sheafValue D l E 0 rfl).val.app (op (PointDerivedHom.finalObject D.k))
      ((coefficientUnit.hom.f 0).hom x) =
        pointIntegralSectionMap l E D.k ((moduleValue l E 0 rfl).hom x)),
  ∃ (q : (pointIntegralComplexSections D l E).obj (model D l E (dual l E P)) ≅ dual l E P),
  ∃ (_q_normalized : ∀ (p j : ℤ) (h : p + j = 0)
      (f : ((pointIntegralComplexSections D l E).obj
        (model D l E (dual l E P))).X j) (x : P.X p),
    pointIntegralSectionMap l E D.k
      ((moduleValue l E (p + j) h).hom ((((q.hom.f j).hom f).v p (p + j) rfl).hom x)) =
      (sheafValue D l E (p + j) h).val.app (op (PointDerivedHom.finalObject D.k))
        (PointDerivedHom.homValue.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)
          j p (op (PointDerivedHom.finalObject D.k))
          ((homIso.hom.f j).val.app (op (PointDerivedHom.finalObject D.k)) f)
          (generator D l E (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x))),
  ∃ (evaluation : total D l E (model D l E P) (model D l E (dual l E P)) ⟶ coefficient D l E),
  ∃ (_evaluation_normalized : ∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (x : P.X p) (f : (dual l E P).X j),
    (sheafValue D l E (p + j) h).val.app U
      ((evaluation.f (p + j)).val.app U
        (PointDerivedHom.totalElement.{u, u} D.k (B D l E)
          (model D l E P) (model D l E (dual l E P)) p j U
          (generator D l E (P.X p) U b x)
          (generator D l E ((dual l E P).X j) U b' f))) =
      (p * j).negOnePow • (b * b' *
        PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
          ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x)))),
  ∃ (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E),
  ∃ (_ringEvaluation_normalized : ∀ (p j : ℤ) (h : p + j = 0) (x : P.X p)
      (f : (dual l E P).X j),
    (moduleValue l E (p + j) h).hom ((ringEvaluation.f (p + j)).hom
      ((HomologicalComplex.ιTensorObj P (dual l E P) p j (p + j) rfl).hom
        (x ⊗ₜ[R l E] f))) =
        (p * j).negOnePow •
          (moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x)),
  ∃ (coefficientCompletion : (sheafQ D l E).obj (coefficient D l E) ≅
    (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).obj (coefficient D l E))),
  ∃ (_coefficientCompletion_normalized : coefficientCompletion.hom =
    (sheafQ D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (coefficient D l E))),
  ∃ (_tensorCompletion_isIso : IsIso ((sheafQ D l E).map
    ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (total D l E (model D l E P) (model D l E (dual l E P)))))),
    (pointFibreIntegralAmbient D l E).map
      (completedEvaluation D l E ⟨model D l E P, good_C⟩
        ⟨model D l E (dual l E P), good_J⟩ evaluation coefficientCompletion) ≫
      (pointIntegralDerivedFactors D l E).hom.app (coefficient D l E) ≫
      (moduleQ l E).map coefficientUnit.inv =
    tau D l E hl S P (model D l E P) (model D l E (dual l E P)) ctf_C ctf_J unit ≫
      (MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 ((moduleQ l E).obj P))
        ((pointIntegralDerivedFactors D l E).hom.app (model D l E (dual l E P)) ≫
          (moduleQ l E).map q.hom)) ≫
      Functor.LaxMonoidal.μ (moduleQ l E) P (dual l E P) ≫
      (moduleQ l E).map ringEvaluation
```

## New

```lean
/-- Termwise extension, with the given additive law.
Source: Stacks 0A8X (blueprint: lem-pod-point-perfect-ordinary-evaluation). -/
abbrev ordinaryModel
    (L : ModuleCat.{u + 1} (R l E) ⥤ Modules D l E) [L.Additive]
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  (L.mapHomologicalComplex (.up ℤ)).obj P

/-- The six explicit unit, Hom and ordinary evaluation formulas, grouped unchanged.
Source: parent proof step 3 (blueprint: lem-pod-point-perfect-ordinary-evaluation). -/
@[irreducible] def Normalized
    (L : ModuleCat.{u + 1} (R l E) ⥤ Modules D l E) [hL : L.Additive]
    (hobj : ∀ M, L.obj M = PointDerivedHom.extensionObject.{u, u}
      D.k (B D l E) (alpha D l E) M)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (unit : P ≅ (pointIntegralComplexSections D l E).obj (ordinaryModel D l E L P))
    (homIso : ordinaryModel D l E L (dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (B D l E)
        (ordinaryModel D l E L P) (coefficient D l E))
    (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E))
    (q : (pointIntegralComplexSections D l E).obj (ordinaryModel D l E L (dual l E P)) ≅ dual l E P)
    (evaluation : PointDerivedHom.total.{u, u} D.k (B D l E) (ordinaryModel D l E L P)
    (ordinaryModel D l E L (dual l E P)) ⟶ coefficient D l E)
    (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E) : Prop :=
  (∀ (p : ℤ) (x : P.X p), (unit.hom.f p).hom x =
      PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
        (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x) ∧
  (∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (f : (dual l E P).X j) (x : P.X p),
    (sheafValue D l E (p + j) h).val.app U
      (PointDerivedHom.homValue.{u, u} D.k (B D l E) (ordinaryModel D l E L P) (coefficient D l E)
        j p U ((homIso.hom.f j).val.app U
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E)
            L hobj ((dual l E P).X j) U b f))
        (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj (P.X p) U b' x)) =
      b * b' * PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
        ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x))) ∧
  (∀ x : (ringComplex l E).X 0,
    (sheafValue D l E 0 rfl).val.app (op (PointDerivedHom.finalObject D.k))
      ((coefficientUnit.hom.f 0).hom x) =
        pointIntegralSectionMap l E D.k ((moduleValue l E 0 rfl).hom x)) ∧
  (∀ (p j : ℤ) (h : p + j = 0)
      (f : ((pointIntegralComplexSections D l E).obj
        (ordinaryModel D l E L (dual l E P))).X j) (x : P.X p),
    pointIntegralSectionMap l E D.k
      ((moduleValue l E (p + j) h).hom ((((q.hom.f j).hom f).v p (p + j) rfl).hom x)) =
      (sheafValue D l E (p + j) h).val.app (op (PointDerivedHom.finalObject D.k))
        (PointDerivedHom.homValue.{u, u} D.k (B D l E) (ordinaryModel D l E L P) (coefficient D l E)
          j p (op (PointDerivedHom.finalObject D.k))
          ((homIso.hom.f j).val.app (op (PointDerivedHom.finalObject D.k)) f)
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj (P.X p)
            (op (PointDerivedHom.finalObject D.k)) 1 x))) ∧
  (∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (x : P.X p) (f : (dual l E P).X j),
    (sheafValue D l E (p + j) h).val.app U
      ((evaluation.f (p + j)).val.app U
        (PointDerivedHom.totalElement.{u, u} D.k (B D l E)
          (ordinaryModel D l E L P) (ordinaryModel D l E L (dual l E P)) p j U
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj (P.X p) U b x)
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E)
            L hobj ((dual l E P).X j) U b' f))) =
      (p * j).negOnePow • (b * b' *
        PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
          ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x)))) ∧
  (∀ (p j : ℤ) (h : p + j = 0) (x : P.X p)
      (f : (dual l E P).X j),
    (moduleValue l E (p + j) h).hom ((ringEvaluation.f (p + j)).hom
      ((HomologicalComplex.ιTensorObj P (dual l E P) p j (p + j) rfl).hom
        (x ⊗ₜ[R l E] f))) =
        (p * j).negOnePow •
          (moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x))
abbrev R := PointEvaluationCompletion.R l E

/-- The completed coefficient sheaf on the original small pro-etale site.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev B := PointEvaluationCompletion.B D l E

/-- The recorded standard localization of completed-coefficient sheaf complexes.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev sheafQ := PointEvaluationCompletion.Q D l E

/-- The same small-Hom localization of ordinary modules used by the point fibre.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev moduleQ := PointEvaluationCompletion.QR l E

/-- The existing constant-to-completed coefficient map.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev alpha := PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true

/-- The ordinary coefficient complex R[0]. Source: Stacks 0A8H
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev ringComplex := PointProjectiveDualTensorModels.ringComplex l E

/-- The completed coefficient complex B[0]. Source: blueprint point coefficients
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev coefficient := PointEvaluationCompletion.coefficient D l E

/-- The functor is uniquely specified on objects and maps by the existing tensor construction.
Source: Stacks 03CY, 03EK; node proof step 1
(blueprint: lem-pod-point-completed-evaluation).
Proof: use the functoriality of constant-module sheafification and of change of rings.
Their identity, composition and additive laws hold on the sheafification generators,
by the corresponding laws for constant linear maps and tensoring with the identity.
The displayed object and morphism equations determine the functor uniquely. -/
theorem extension_existsUnique :
    ∃! L : ModuleCat.{u + 1} (R l E) ⥤ integralTowerModules l E (Spec (.of D.k)),
      (∀ M, L.obj M = PointDerivedHom.extensionObject.{u, u} D.k (B D l E)
        (alpha D l E) M) ∧
      L.Additive ∧
      (∀ (M N : ModuleCat.{u + 1} (R l E)) (f : M ⟶ N),
        HEq (L.map f) (PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E)
          (alpha D l E) f)) := by
  let := PointDerivedHom.abSheafify.{u, u} D.k
  let := PointDerivedHom.abLocallyBijective.{u, u} D.k
  let T := SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u}
    (alpha D l E)
  let L := PointDerivedHom.constantModules.{u, u} D.k (CommRingCat.of (R l E)) ⋙ T
  have : T.Additive :=
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction (alpha D l E)).left_adjoint_additive
  have : (PointDerivedHom.constantPresheaf.{u, u} D.k
      (CommRingCat.of (R l E))).Additive := ⟨by intros; rfl⟩
  have : (PresheafOfModules.sheafification
      (PointDerivedHom.constantUnit.{u, u} D.k (CommRingCat.of (R l E)))).Additive :=
    (PresheafOfModules.sheafificationAdjunction
      (PointDerivedHom.constantUnit.{u, u} D.k (CommRingCat.of (R l E)))).left_adjoint_additive
  have : (PointDerivedHom.constantModules.{u, u} D.k (CommRingCat.of (R l E))).Additive := by
    dsimp only [PointDerivedHom.constantModules]
    infer_instance
  refine ⟨L, ⟨fun _ ↦ rfl, inferInstance, fun _ _ _ ↦ HEq.rfl⟩, ?_⟩
  intro L' hL'
  exact Functor.hext hL'.1 (fun M N f ↦ hL'.2.2 M N f)

/-- Actual constant-module extension, uniquely fixed by its existing object and map formulas.
Source: node proof step 1 (blueprint: lem-pod-point-completed-evaluation). -/
def extension := (extension_existsUnique D l E).exists.choose

/-- Additivity supplied by the canonical functor construction.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
instance extension_additive : (extension D l E).Additive :=
  (extension_existsUnique D l E).exists.choose_spec.2.1

/-- Apply the canonical extension termwise.
Source: Stacks 0A8X (blueprint: lem-pod-point-completed-evaluation). -/
def extensionComplex := (extension D l E).mapHomologicalComplex (.up ℤ)

/-- The construction's object, additive and morphism specifications, stated for extension.
Source: the unique construction in step 1
(blueprint: lem-pod-point-completed-evaluation). -/
theorem extension_spec :
    (∀ M, (extension D l E).obj M = PointDerivedHom.extensionObject.{u, u}
      D.k (B D l E) (alpha D l E) M) ∧
    (extension D l E).Additive ∧
    (∀ (M N : ModuleCat.{u + 1} (R l E)) (f : M ⟶ N),
      HEq ((extension D l E).map f)
        (PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E) (alpha D l E) f)) := by
  exact (extension_existsUnique D l E).exists.choose_spec

attribute [local irreducible] extension

/-- The same tensor generator transported through the uniquely fixed object equality.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
def generator (M : ModuleCat.{u + 1} (R l E))
    (U : (Spec (.of D.k)).ProEtᵒᵖ) (b : (B D l E).obj.obj U) (x : M) :=
  PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) (extension D l E)
    (extension_spec D l E).1 M U b x

/-- The ordinary derived dual's bounded-projective chain model, with the recorded differential.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
abbrev dual (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  PointProjectiveDualTensorModels.dual l E P

/-- The specified ordinary sheaf tensor model.
Source: Stacks 06YL (blueprint: lem-pod-point-completed-evaluation). -/
abbrev total (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  PointEvaluationCompletion.total D l E C J

/-- The balancing identification of the two strict towers, uniquely on local generators.
Source: Bhatt--Scholze 3.4.10 and node proof step 6
(blueprint: lem-pod-point-completed-evaluation).
Proof: in every degree reassociate the balanced tensor products and total sums.
Send (x tensor a) tensor (y tensor b) to (x tensor y) tensor ab; the inverse sends
(x tensor y) tensor a to (x tensor 1) tensor (y tensor a). Balancing and the
signed differential give inverse chain maps. The quotient formulas commute with
all transitions. Sheafification and the total injections make the maps unique. -/
theorem towerBalancing_existsUnique
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! rho : ((integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J)) ≅
        ((integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
          (total D l E C J)),
      PointEvaluationCompletion.Balanced D l E C J rho := by
  sorry

/-- Balancing of the specified strict towers, with no arbitrary cone filler.
Source: node proof step 6 (blueprint: lem-pod-point-completed-evaluation). -/
@[irreducible] def towerBalancing
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  Classical.choose (towerBalancing_existsUnique D l E C J)

/-- Completed evaluation is the strict-cone completion of ordinary evaluation, followed
by the inverse of the specified coefficient completion unit. Both cone coordinates
are therefore fixed before localization. Source: node proof steps 6--7
(blueprint: lem-pod-point-completed-evaluation). -/
@[irreducible] def completedEvaluation
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (e : total D l E C.obj J.obj ⟶ coefficient D l E)
    (b : (sheafQ D l E).obj (coefficient D l E) ≅
      (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).obj (coefficient D l E))) :=
  PointEvaluationCompletion.completedPairing D l E C J
    (towerBalancing D l E C.obj J.obj) e b

/-- Reading the coefficient in a degree identified with zero uses the existing single-complex
isomorphism. Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def moduleValue (n : ℤ) (h : n = 0) :=
  PointProjectiveDualTensorModels.moduleValue l E n h

/-- The same single-complex isomorphism for the coefficient sheaf.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def sheafValue (n : ℤ) (h : n = 0) :=
  PointProjectiveDualTensorModels.sheafValue D l E n h

/-- The actual model B tensor underline P, rather than an arbitrary equivalent complex.
Source: node statement (blueprint: lem-pod-point-completed-evaluation). -/
abbrev model (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  PointEvaluationCompletion.model D l E (extension D l E) P

/-- The tensor comparison after identifying sections of C with P by its canonical unit.
Source: node proof step 8 and lem-sf-point-fibre-derived-tensor
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose, irreducible] def tau (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :=
  (pointIntegralTensorComparison D l hl E S
    ⟨(sheafQ D l E).obj C, hC⟩ ⟨(sheafQ D l E).obj J, hJ⟩).hom ≫
    (MonoidalCategory.tensor _).map
      (Prod.mkHom ((pointIntegralDerivedFactors D l E).hom.app C ≫
        (moduleQ l E).map unit.inv) (𝟙 _))


private theorem inverse_comparison_isIso (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :
    IsIso (PointEvaluationCompletion.inverseTensorComparison D l E hl S P C J hC hJ
      unit.hom) := by
  dsimp [PointEvaluationCompletion.inverseTensorComparison]
  infer_instance

private theorem inverse_tau (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :
    PointEvaluationCompletion.inverseTensorComparison D l E hl S P C J hC hJ unit.hom ≫
      tau D l E hl S P C J hC hJ unit = 𝟙 _ := by
  unfold tau
  dsimp only [PointEvaluationCompletion.inverseTensorComparison]
  simp only [Category.assoc]
  exact tensor_transport_cancel ((moduleQ l E).mapIso unit)
    ((pointIntegralDerivedFactors D l E).symm.app C)
    (pointIntegralTensorComparison D l hl E S
      ⟨(sheafQ D l E).obj C, hC⟩ ⟨(sheafQ D l E).obj J, hJ⟩).symm

private theorem completion_unit_isIso
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅
        (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
          (total D l E C.obj J.obj))
    (h : IsIso (PointEvaluationCompletion.chi D l E C J rho)) :
    IsIso ((sheafQ D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (total D l E C.obj J.obj))) := by
  dsimp only [PointEvaluationCompletion.chi] at h
  exact unit_iso_of_comparison (PointEvaluationCompletion.Q D l E)
    ((PointEvaluationCompletion.unit D l E).app (total D l E C.obj J.obj))
    (integralOperationsRoosFunctor.mapIso rho).symm
    (PointEvaluationCompletion.tensorModelIso D l E C J) h

attribute [local irreducible] PointEvaluationCompletion.inverseTensorComparison
  PointEvaluationCompletion.completedPairing PointEvaluationCompletion.chi

/-- All assertions concern the fixed perfect models and normalized canonical maps.
Source: node statement and proof steps 3--8
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose, irreducible] def Result (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) : Prop :=
  ∃ (good_C : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E P)),
  ∃ (good_J : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E (dual l E P))),
  ∃ (_constructible_tensor : sfIntegralConstructible l E (Spec (.of D.k))
    ((sheafQ D l E).obj (total D l E (model D l E P) (model D l E (dual l E P))))),
  ∃ (ctf_C : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E P))),
  ∃ (ctf_J : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E (dual l E P)))),
  ∃ (homIso : model D l E (dual l E P) ≅
    PointDerivedHom.sheafHom.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)),
  ∃ (_derivedHom_isIso : IsIso ((sheafQ D l E).map homIso.hom ≫
    IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E)
      (model D l E P) (coefficient D l E))),
  ∃ (unit : P ≅ (pointIntegralComplexSections D l E).obj (model D l E P)),
  ∃ (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E)),
  ∃ (q : (pointIntegralComplexSections D l E).obj (model D l E (dual l E P)) ≅ dual l E P),
  ∃ (evaluation : total D l E (model D l E P) (model D l E (dual l E P)) ⟶ coefficient D l E),
  ∃ (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E),
  ∃ (_ordinary_normalized : PointPerfectOrdinaryEvaluation.Normalized D l E
    (extension D l E) (hL := extension_additive D l E)
    (extension_spec D l E).1 P unit homIso
    coefficientUnit q evaluation ringEvaluation),
  ∃ (coefficientCompletion : (sheafQ D l E).obj (coefficient D l E) ≅
    (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).obj (coefficient D l E))),
  ∃ (_coefficientCompletion_normalized : coefficientCompletion.hom =
    (sheafQ D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (coefficient D l E))),
  ∃ (_tensorCompletion_isIso : IsIso ((sheafQ D l E).map
    ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (total D l E (model D l E P) (model D l E (dual l E P)))))),
    (pointFibreIntegralAmbient D l E).map
      (completedEvaluation D l E ⟨model D l E P, good_C⟩
        ⟨model D l E (dual l E P), good_J⟩ evaluation coefficientCompletion) ≫
      (pointIntegralDerivedFactors D l E).hom.app (coefficient D l E) ≫
      (moduleQ l E).map coefficientUnit.inv =
    tau D l E hl S P (model D l E P) (model D l E (dual l E P)) ctf_C ctf_J unit ≫
      (MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 ((moduleQ l E).obj P))
        ((pointIntegralDerivedFactors D l E).hom.app (model D l E (dual l E P)) ≫
          (moduleQ l E).map q.hom)) ≫
      Functor.LaxMonoidal.μ (moduleQ l E) P (dual l E P) ≫
      (moduleQ l E).map ringEvaluation
```

## Projective-model aliases

`Sheaf.Paper.PointProjectiveDualTensorModels` is unclaimed in the current local claim
snapshot and absent from the current proof queue. It has no importers in the shared
snapshot; this packet's parent and ordinary module are its direct consumers. Only the
following five aliases change; the model retains an explicit `CochainComplex` result type. The module's theorem statement and entire
proof, public imports and original attributes are byte-for-byte unchanged.
The original unit retains its original body; its result type now explicitly names
termwise concrete point sections, already available from the existing public imports. Two proved public APIs, `unit_apply` and `unit_isIso`,
respectively expose its original generator formula and lift a componentwise isomorphism
to a complex isomorphism. The parent treats the unit irreducibly and uses these APIs. The definitions are
definitionally identical: the integral branch of `coefficientSheaf` is the completed
commutative sheaf; forgetting its commutativity recovers the existing completed ring
sheaf. Using that ring directly in the unit complex and its coordinate map avoids
repeated normalization of its algebraic structure. The mathematical proof route stays valid. The node records the two proved APIs and
the concrete point-sections statement dependency. This module has zero holes before and after.

The termwise `model` now applies `L.mapHomologicalComplex` directly, with the same
adjunction-supplied additive proof that `PointDerivedHom.extensionComplex` installs.
This is definitionally the original model, with proof irrelevance identifying the
additive-law proofs. The private categorical APIs also match the tensor-functor map
presentation of the supplied formulas; their proofs reduce it to tensor notation only
in abstract categories, before the application to concrete complexes.

Old:

```lean
abbrev B := PointDerivedHom.coefficientSheaf.{u, u} D.k l E 1 true

abbrev Modules := PointDerivedHom.Modules.{u, u} D.k (B D l E)

abbrev coefficient := (CochainComplex.singleFunctor (Modules D l E) 0).obj
  (SheafOfModules.unit (PointDerivedHom.ring.{u, u} D.k (B D l E)))

abbrev sheafValue (n : ℤ) (h : n = 0) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
    (SheafOfModules.unit (PointDerivedHom.ring.{u, u} D.k (B D l E))) n h).hom

abbrev model (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  (PointDerivedHom.extensionComplex.{u, u} D.k (B D l E) (alpha D l E) L adj).obj P
```

New:

```lean
abbrev B := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))

abbrev Modules := integralTowerModules l E (Spec (.of D.k))

abbrev coefficient := (CochainComplex.singleFunctor (Modules D l E) 0).obj
  (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))

abbrev sheafValue (n : ℤ) (h : n = 0) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
    (SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))) n h).hom

abbrev model (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :
    CochainComplex (Modules D l E) ℤ :=
  letI := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  letI := adj.left_adjoint_additive
  (L.mapHomologicalComplex (.up ℤ)).obj P
```

The unit's old inferred signature and new explicit signature are definitionally equal.
Its old declaration was:

```lean
def unit (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  letI := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  letI := adj.left_adjoint_additive
  (adj.mapHomologicalComplex (.up ℤ)).unit.app P
```

Its body is unchanged:

```lean
def unit (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :
    P ⟶ ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
      (model D l E L adj P) :=
  letI := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  letI := adj.left_adjoint_additive
  (adj.mapHomologicalComplex (.up ℤ)).unit.app P
```

The two new APIs are proved from the explicit adjunction and the general componentwise
isomorphism criterion. Neither adds a hole. No new public import is needed. The original model theorem's
proof is retained verbatim.

## Projective-model APIs

`Sheaf.Paper.PointDerivedHomModels` is not changed by this delivery: the reviewer
reverted the re-association of `sections` (the other three modules and the consumer
compile against the published, unchanged `sections`).

The projective-model module also proves `scalar_eq` by reflexivity: its generic scalar
map at the final object equals `pointIntegralSectionMap`. The parent transports
bijectivity using this named equality instead of repeating that reduction in its proof.
The producer also names the canonical isomorphism as `unitIso`, whose body is
`asIso (unit D l E L adj P)`. Its `IsIso` assumption determines the inverse uniquely.
The proved `unitIso_apply` is the existing `unit_apply` formula after unfolding that
named isomorphism. The parent uses this data constant instead of repeatedly expanding
a local `asIso` value. All its ordinary normalization conditions are unchanged.
Both constructions and the existing DAG mathematical route are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointProjectiveDualTensorModels | unclaimed | Equivalent aliases and unit codomain; proved scalar and unit APIs. |
| Sheaf.Paper.PointPerfectOrdinaryEvaluation | B2 | Uses the shared coefficient representation. |
| Sheaf.Paper.PointCompletedEvaluation | B2 | Uses proved APIs and grouped normalization. |
| Sheaf.Paper.CompletedHomScalarTranspose | H3 | Unchanged; compiles against the delivered modules (reviewer check); no adaptation. |

The inventory was refreshed against the current shared source for this repair.
`CompletedHomScalarTranspose` is now held by H3; no source belonging to H3 is edited.
The projective-model interfaces are used by this packet's parent and ordinary module.
No consumer mentions the removed `roosBalancing` wrapper. Its declaration attachment
is removed, with no node or module withdrawn. The new predicate is a statement dependency
of the owning node. Independent review should expand its six formulas and verify the
unchanged canonical-map formulas above.

The completed-Hom consumer retains its original source and compiles against both the
published parent and this delivery (reviewer, lcompile.py). No consumer copy is delivered.

## Returned-delivery repair

The review of returned head `c03b7d88872` answered FIX (it reverted the unforced
`sections` re-association in `PointDerivedHomModels`). Landing failed while
reading a reviewer correction under the bare record filename. The record is included
at its actual delivery path:
`coord/changes/B2-point-completed-evaluation-canonical-map-api.md`.
The stage-3 lander's `fixes` function in `tools/batch_land.py` identifies change-record
corrections by the record stem followed by `.change.md`. Therefore a reviewer correction
must be named `B2-point-completed-evaluation-canonical-map-api.change.md` in the fix
directory. The bare `.md` name from the failed landing is not a supported correction
alias. No launcher or repository tool is changed.

This repair re-delivered the `sections` re-association; the reviewer of head
`c68ffaf96f1` reverted it again. This repair refreshes the full consumer table and holders on the current source,
records the correct correction alias, and recompiles the retained mathematical packet
against the current server build. The delivery tool reconstructs the commit on current
`sheaf-dag` while preserving current node fields outside this delivery's owned fields.

## Status

landed 20261026T065140-L-2717919 2026-10-26 (merge of deliver/B2/Sheaf.Paper.PointCompletedEvaluation)

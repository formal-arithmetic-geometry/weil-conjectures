# Integral-heart scalar realization declaration locations

## Reason

The parent proof needs the already proved integralHeartRealization_exact_free theorem.
Its original import of IntegralHeartLocalModel couples the realization definitions to the
unproved local-model theorem and creates a cycle when the latter uses exactness. Relocate
exactly the existing declaration block, including all instances and proof bodies, to
Sheaf.Paper.IntegralHeartLocalModelData. The original module publicly reexports it and keeps
all its original public imports. No definition, signature, visibility, attribute, universe,
statement or mathematical meaning changes. The item theorem keeps its exact signature.
The existing exactness module changes its public import to the data module; its only direct
consumer, IntegralHeartDualizable, already publicly imports IntegralHeartLocalModel itself.
The new comparison lemmas import only the data and do not depend on the parent theorem.

The declaration block below was checked byte-for-byte identical between old and new files.
The DAG attachment for this block moves to the new definition node. The parent keeps the
local-model theorem attachment. The exactness node's dependencies now name that data node,
which is what its unchanged proof actually uses; this removes the corresponding artificial
DAG cycle. No target requires semantic re-review: all definitions have their identical bodies.

## Old

In lean/Sheaf/Paper/IntegralHeartLocalModel.lean:

```lean
/-- The coefficient DVR, lifted only to the sheaf-value universe.
Source: integral-heart coefficient setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartScalars (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :=
  ULift.{u + 1} (SmallAdicCompletion.Coefficients.integers ℓ E)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- The actual section ring sheaf of the condensed integral ring.
Source: pulled-back coefficient setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartPointRing :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E))

/-- A scalar as its constant continuous function, in the reconstructed section ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartScalarSection (S : Profinite.{u}ᵒᵖ)
    (a : integralHeartScalars.{u} ℓ E) :
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj.obj S :=
  ULift.up (ContinuousMap.const S.unop a.down)

/-- The constant scalar one is the unit of the reconstructed section ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model).
Proof: the internal unit of continuous functions is the constant function one.
Evaluating its section-ring reconstruction gives the same constant function. -/
theorem integralHeartScalarSection_one (S : Profinite.{u}ᵒᵖ) :
    integralHeartScalarSection.{u} ℓ E S 1 = 1 := by
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let F := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let : MonObj R.obj :=
    (Profinite.continuousMapRingSheaf.{u}
      (SmallAdicCompletion.Coefficients.integers ℓ E)).obj.monObjCompForget₂
  change _ = ((Functor.LaxMonoidal.ε F ≫ F.map η[R]).app S).hom (ULift.up 1)
  rw [Sheaf.ε_comp_map_one]
  change ULift.up (ContinuousMap.const S.unop
    (1 : SmallAdicCompletion.Coefficients.integers ℓ E)) =
      ((1 : ℤ) : ULift.{u + 1} C(S.unop, SmallAdicCompletion.Coefficients.integers ℓ E))
  simp only [Int.cast_one]
  rfl

/-- Constant continuous functions preserve multiplication in the reconstructed ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model).
Proof: the reconstructed internal multiplication evaluated on a pure tensor is the
original pointwise multiplication of continuous functions. The two constant functions
multiply to the constant function on the scalar product. -/
theorem integralHeartScalarSection_mul (S : Profinite.{u}ᵒᵖ)
    (a b : integralHeartScalars.{u} ℓ E) :
    integralHeartScalarSection.{u} ℓ E S (a * b) =
      integralHeartScalarSection.{u} ℓ E S a * integralHeartScalarSection.{u} ℓ E S b := by
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let F := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let : MonObj R.obj :=
    (Profinite.continuousMapRingSheaf.{u}
      (SmallAdicCompletion.Coefficients.integers ℓ E)).obj.monObjCompForget₂
  change _ = ((Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]).app S).hom
    (integralHeartScalarSection.{u} ℓ E S a ⊗ₜ[ℤ]
      integralHeartScalarSection.{u} ℓ E S b)
  rw [Sheaf.μ_comp_map_mul]
  rfl

/-- Constant scalar functions in every profinite section ring.
Source: the scalar-extension model in clause (1)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantMap :
    (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)) ⟶
      (sectionRingSheaf (coherentTopology Profinite.{u})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj where
  app S := @CommRingCat.ofHom
    (integralHeartScalars.{u} ℓ E)
    ((sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).obj.obj S) inferInstance
    (CommRingCat.commRing _)
    { toFun := integralHeartScalarSection.{u} ℓ E S
      map_one' := integralHeartScalarSection_one.{u} ℓ E S
      map_mul' := integralHeartScalarSection_mul.{u} ℓ E S
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- Constant scalar module presheaves on the point, with identity restrictions.
Source: the scalar-extension model in clause (1)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantPresheaf : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    PresheafOfModules.{u + 1}
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (integralHeartScalars.{u} ℓ E))) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- Additivity of constant module presheaves.
Source: clause (1), constant realization (blueprint: det-lem-int-integral-heart-local-model).
Proof: evaluate a sum of morphisms at each profinite object; its value is the original
sum of linear maps, so additivity is pointwise. -/
theorem integralHeartConstantPresheaf_additive :
    (integralHeartConstantPresheaf.{u} ℓ E).Additive := by
  constructor
  intro X Y f g
  ext S x
  rfl

attribute [instance] integralHeartConstantPresheaf_additive

/-- The constant scalar ring sheaf.
Source: the scalar model in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartConstantRing :=
  (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
    (CommRingCat.of (integralHeartScalars.{u} ℓ E))

/-- The sheafification unit for the constant scalar ring, forgetting commutativity.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantUnit :=
  Functor.whiskerRight
    (toSheafify (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj
        (CommRingCat.of (integralHeartScalars.{u} ℓ E))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- The constant ring sheafification unit is locally injective after forgetting
commutativity. Source: constant sheafification, Stacks 03DA
(blueprint: det-lem-int-integral-heart-local-model).
Proof: the underlying functions and equalizer sieves are unchanged by forgetting
commutativity, and the original sheafification unit is locally injective. -/
theorem integralHeartConstantUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (integralHeartConstantUnit.{u} ℓ E) := by
  let τ := toSheafify (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)))
  constructor
  intro S x y h
  exact Presheaf.equalizerSieve_mem (coherentTopology Profinite.{u}) τ x y h

/-- The constant ring sheafification unit is locally surjective after forgetting
commutativity. Source: constant sheafification, Stacks 03DA
(blueprint: det-lem-int-integral-heart-local-model).
Proof: the underlying functions and image sieves are unchanged by forgetting
commutativity, and the original sheafification unit is locally surjective. -/
theorem integralHeartConstantUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (integralHeartConstantUnit.{u} ℓ E) := by
  let τ := toSheafify (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)))
  constructor
  intro U x
  exact Presheaf.imageSieve_mem (coherentTopology Profinite.{u}) τ x

attribute [instance] integralHeartConstantUnit_isLocallyInjective
  integralHeartConstantUnit_isLocallySurjective

/-- The canonical ring map from constant scalars to continuous coefficients.
Source: scalar realization in clauses (1)--(2)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartScalarMap : integralHeartConstantRing.{u} ℓ E ⟶
    sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).homEquiv
    _ _).symm (integralHeartConstantMap.{u} ℓ E)

/-- Modules over the constant scalar ring on the point.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartConstantModules :=
  SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))

/-- The map laws of the existing canonical sectionwise scalar-extension construction.
Source: sheaf tensor, Stacks 03EK (blueprint: det-lem-int-integral-heart-local-model).
Proof: before sheafification all maps are id tensor f. Tensor functoriality gives
identity and composition on pure tensors. Sheafification preserves both equations. -/
theorem integralHeartExtension_laws :
    (∀ M : integralHeartConstantModules.{u} ℓ E,
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M (𝟙 M) = 𝟙 _) ∧
    (∀ (M N P : integralHeartConstantModules.{u} ℓ E) (f : M ⟶ N) (g : N ⟶ P),
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M (f ≫ g) =
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M f ≫
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) N g) := by
  let α := integralHeartScalarMap.{u} ℓ E
  let L := PresheafOfModules.sheafification.{u + 1}
    (𝟙 (integralHeartPointRing.{u} ℓ E).obj)
  constructor
  · intro M
    let t : SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M ⟶
        SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M :=
      { app U := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (α.hom.app U).hom).map (𝟙 (M.val.obj U))
        naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
          α M (𝟙 M) }
    have ht : t = 𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map_id _
    change L.map t = 𝟙 _
    rw [ht, L.map_id]
  · intro M N P f g
    let t {A B : integralHeartConstantModules.{u} ℓ E} (h : A ⟶ B) :
        SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α A ⟶
          SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α B :=
      { app U := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map (h.val.app U)
        naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
          α A h }
    have ht : t (f ≫ g) = t f ≫ t g := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map_comp _ _
    change L.map (t (f ≫ g)) = L.map (t f) ≫ L.map (t g)
    rw [ht, L.map_comp]

/-- Actual completed scalar extension, sheafifying the sectionwise tensor product.
Source: scalar realization in clauses (1)--(2)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartExtension :
    SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E)) ⥤
    SheafOfModules.{u + 1} (integralHeartPointRing.{u} ℓ E) where
  obj M := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralHeartScalarMap.{u} ℓ E) M
  map {M _N} f := SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralHeartScalarMap.{u} ℓ E) M f
  map_id M := (integralHeartExtension_laws.{u} ℓ E).1 M
  map_comp f g := (integralHeartExtension_laws.{u} ℓ E).2 _ _ _ f g

private theorem integralHeartExtension_additive :
    (integralHeartExtension.{u} ℓ E).Additive where
  map_add {M N} f g := by
    let α := integralHeartScalarMap.{u} ℓ E
    let L := PresheafOfModules.sheafification.{u + 1}
      (𝟙 (integralHeartPointRing.{u} ℓ E).obj)
    let t (h : M ⟶ N) :
        SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M ⟶
          SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α N :=
      { app U := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map (h.val.app U)
        naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
          α M h }
    have ht : t (f + g) = t f + t g := by
      apply PresheafOfModules.hom_ext
      intro U
      have : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).Additive :=
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          (α.hom.app U).hom).left_adjoint_additive
      exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)
    have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
    have : L.Additive := Functor.additive_of_preserves_binary_products L
    change L.map (t (f + g)) = L.map (t f) + L.map (t g)
    rw [ht, L.map_add]

/-- The canonical completed scalar-module realization on the point. It first forms
constant module sheaves, then extends scalars along constant functions, and finally
uses the existing internal-module equivalence. No realization functor is an input.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartPointRealization : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    CategoryTheory.Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) :=
  integralHeartConstantPresheaf.{u} ℓ E ⋙
    PresheafOfModules.sheafification
      (R := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))
      (integralHeartConstantUnit.{u} ℓ E) ⋙
    integralHeartExtension.{u} ℓ E ⋙
    (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).inverse

/-- Additivity of completed scalar realization.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model).
Proof: constant presheaves preserve addition pointwise. Scalar extension and
sheafification are additive; the inverse of an additive equivalence is additive. -/
theorem integralHeartPointRealization_additive :
    (integralHeartPointRealization.{u} ℓ E).Additive := by
  have := integralHeartExtension_additive.{u} ℓ E
  let L := PresheafOfModules.sheafification.{u + 1}
    (R := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))
    (integralHeartConstantUnit.{u} ℓ E)
  have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  change (integralHeartConstantPresheaf.{u} ℓ E ⋙ L ⋙
    integralHeartExtension.{u} ℓ E ⋙ _).Additive
  infer_instance

attribute [instance] integralHeartPointRealization_additive

/-- Scalar-module realization on a scheme by the published inverse image from the point.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartRealization (X : Scheme.{u}) :=
  integralHeartPointRealization.{u} ℓ E ⋙
    (upperStarFromPoint X).mapMod (SmallAdicCompletion.Coefficients.integerRing ℓ E)

/-- Additivity of realization on the scheme.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model).
Proof: point realization is additive and inverse image is additive; compose these
properties. This is only the structure needed to map cochain complexes. -/
theorem integralHeartRealization_additive (X : Scheme.{u}) :
    (integralHeartRealization.{u} ℓ E X).Additive := by
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold integralHeartRealization
  infer_instance

attribute [instance] integralHeartRealization_additive

/-- The ordinary unbounded category with exactly the integral-heart coefficient ring.
Source: the standing setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartDerivedCategory (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) X))

/-- The q-th cohomology sheaf in degree zero.
Source: clause (2) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartCohomology (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X) (q : ℤ) :=
  (DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ q).obj K)

/-- Finite free models and all their cohomology models on the same strata and charts.
The differential matrices are over the scalar DVR since P is a scalar cochain complex.
Source: clauses (1) and (2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartFiniteFreeLocalModel (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X) : Prop :=
  ∃ s : Scheme.FiniteLocallyClosedStratification X,
    (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
    ∀ a : Fin s.n, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
      ∀ i : 𝒰.I₀,
        ∃ (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
          (b c : ℤ),
          P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
          (∀ q : ℤ, Module.Free (integralHeartScalars.{u} ℓ E) (P.X q) ∧
            Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q)) ∧
          Nonempty (((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
              (𝒰.f i ≫ s.immersion a)).mapDerivedCategory).obj K ≅
            DerivedCategory.Q.obj
              (((integralHeartRealization.{u} ℓ E (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj P)) ∧
          (∀ q : ℤ,
            Module.Finite (integralHeartScalars.{u} ℓ E) (P.homology q) ∧
            Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj K) ≅
              (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj (P.homology q)))

```

In lean/Sheaf/Paper/IntegralHeartRealizationExact.lean:

```lean
public import Sheaf.Paper.IntegralHeartLocalModel
```

## New

Exactly the preceding declaration block is in
lean/Sheaf/Paper/IntegralHeartLocalModelData.lean, byte-for-byte unchanged.
The original module additionally publicly reexports it:

```lean
public import Sheaf.Paper.IntegralHeartLocalModelData
```

The exactness module imports the data directly:

```lean
public import Sheaf.Paper.IntegralHeartLocalModelData
```

## Users

The following is the complete transitive downstream list returned by tools/downstream.py.
All consumers continue to see the identical declarations through the original public import.
Only the exactness module requires an import adaptation, to remove the cycle described above.
A batched whole-library textual audit found references to relocated names only in
IntegralConstructibleHeart, IntegralHeartDualizable, IntegralHeartRealizationExact and
IntegralHeartResidueDual. The original theorem has exactly one textual consumer,
IntegralConstructibleHeart; its signature is unchanged. Current holder information is from
the available shared claim records; no adapted source module is held there by another group.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralHeartLocalModel | V2 | Proves the original theorem by assembly; publicly reexports the identical definitions. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AffineCounitScalar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownTowerRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.BrownTowerSite | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemMixed | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FieldShriekSystemTransitions | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed in available shared records | Import changes to the data module to remove the cycle; proof and signature unchanged. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.MateOpenCompactSupportExchange | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.MateOpenProperRestrictionIso | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.MateOpenRestriction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.MateOpenRestrictionMaps | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.P1CounitScalar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.P1SplittingScalar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RestrictionLocal | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TateTwistedProjection | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.VerdierExchange | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Targets.PoincareUncurry | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| TargetsCheck | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.SmoothPurity.Defs | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.Statement | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Additivity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Basic | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Main | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Product | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Stalk | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.Statement | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.WeilSheaf.Curve | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.Examples | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.Weights | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed in available shared records | No adaptation: identical definitions through the original public reexport. |

## Status

landed 20261025T203442-L-2818468 2026-10-25 (merge of deliver/V2/Sheaf.Paper.IntegralHeartLocalModel)

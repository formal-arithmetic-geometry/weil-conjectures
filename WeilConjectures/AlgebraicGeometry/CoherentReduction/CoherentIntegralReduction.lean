/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.ConstantCoefficientSystem
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteProperExceptionalQuotient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Instances.Discrete
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis

/-! # The actual coherent integral reduction system

Source: Zheng, Construction 4.1, and the first step of
`lem-sfb-finite-proper-exceptional-coherent-tower`.
(blueprint: def-sfb-coherent-integral-reduction)

Coefficients are continuous condensed rings pulled back from the point. The
reduction is one derived scalar extension on the sequence site. The field of
coefficients may have universe u+1 while the schemes have universe u.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CoherentReduction

/-- The small pro-etale site in the coefficient universe, with its original morphisms.
Source: Bhatt--Scholze, section 4.1, small pro-etale site size convention
(blueprint: def-sfb-coherent-integral-reduction). -/
local instance proEtSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  @essentiallySmall_of_small_of_locallySmall.{u + 1, u, u + 1} X.ProEt _ inferInstance
    (@locallySmall_of_univLE.{u + 1, u, u + 1} X.ProEt _
      (@univLE_of_max.{u, u + 1} UnivLE.self))

/-- The sequence site has the same coefficient-size bound.
Source: Zheng, Construction 4.1, coefficient system site
(blueprint: def-sfb-coherent-integral-reduction). -/
local instance sequenceSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  @essentiallySmall_of_small_of_locallySmall.{u + 1, u, u + 1} (ℕ × X.ProEt) _ inferInstance
    (@locallySmall_of_univLE.{u + 1, u, u + 1} (ℕ × X.ProEt) _
      (@univLE_of_max.{u, u + 1} UnivLE.self))

/-- Continuous functions on profinite tests, with pointwise commutative ring operations.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPresheaf (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Profinite.{u}ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj S := CommRingCat.of C(S.unop, T)
  map f := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The continuous condensed coefficient ring, with its actual section construction.
Sheafification is included so the construction does not require a sheaf proof as data.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPoint (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  (presheafToSheaf _ CommRingCat.{u + 1}).obj (continuousPresheaf T)

/-- Continuous postcomposition defines the coefficient homomorphisms.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPointMap {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) : continuousPoint T ⟶ continuousPoint S :=
  (presheafToSheaf _ CommRingCat.{u + 1}).map
    { app := fun U ↦ CommRingCat.ofHom (f.compLeftContinuous U.unop hf)
      naturality := fun _ _ _ ↦ rfl }

/-- The sheafified map sending a scalar to its constant continuous function.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def pointConstants (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of T) ⟶ continuousPoint T :=
  (presheafToSheaf _ CommRingCat.{u + 1}).map
    { app := fun U ↦ CommRingCat.ofHom (ContinuousMap.C (α := U.unop))
      naturality := fun _ _ _ ↦ rfl }

/-- Forget commutativity and then multiplication, retaining the canonical internal ring.
Source: the ring-object construction, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev abelianPoint (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (continuousPoint T))

/-- The continuous coefficients are commutative internal ring objects.
Source: pointwise multiplication, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
instance abelianPoint_comm (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : IsCommMonObj (abelianPoint T) :=
  Sheaf.isCommMonObj_sheafCompose_obj
    (coherentTopology Profinite.{u})
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (continuousPoint T))
    (fun U a b ↦ @mul_comm ((continuousPoint T).obj.obj U) inferInstance a b)

/-- The actual internal coefficient ring p_T^* underline(A).
Source: the blueprint's pulled-back-coefficient convention
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev internalRing (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  condensedRingObj (abelianPoint T) X

/-- The actual multiplication on the pulled-back continuous ring.
Source: pointwise multiplication, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
instance internalRingMonObj (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] : MonObj (internalRing X T) :=
  inferInstanceAs (MonObj (condensedRingObj (abelianPoint T) X))

/-- Commutativity is transported by the original pullback, rather than chosen afresh.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance internalRingComm (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] : IsCommMonObj (internalRing X T) :=
  inferInstanceAs (IsCommMonObj (condensedRingObj (abelianPoint T) X))

/-- The section-ring presentation of the same internal coefficients.
Source: Stacks 00YV, the recorded section-action equivalence
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev sectionRing (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (internalRing X T)

/-- A morphism of internal rings, reconstructed on their original sections.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
def internalSectionMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf _ Ab.{u + 1}).mapCommMon.map (CommMon.homMk (Mon.ofHom f))))
    InternalAbelianSheafModule.commMonToRing.{u + 1}⟩

/-- Pull back a continuous scalar homomorphism, then reconstruct the section homomorphism.
Source: the blueprint's coefficient morphisms
(blueprint: def-sfb-coherent-integral-reduction). -/
def sectionMap (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) : sectionRing X T ⟶ sectionRing X S :=
  internalSectionMap X ((upperStarFromPoint X).map
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousPointMap f hf))))

/-- The underlying constant-section map on the scheme, using the canonical
constant-sheaf comparison for inverse image from the coefficient point.
Source: the blueprint's pulled-back coefficients
(blueprint: def-sfb-coherent-integral-reduction). -/
def schemeConstants (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of T) ⟶
      internalRing X T := by
  letI : HasSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  letI : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  exact (constantSchemeIso X).hom.app (AddCommGrpCat.of T) ≫
    (upperStarFromPoint X).map
      (((constantCommuteCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).inv ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (pointConstants T)))

/-- Forgetting a ring sheaf preserves local isomorphisms on the pro-etale site.
Source: Stacks 00WH (blueprint: def-sfb-coherent-integral-reduction). -/
instance coefficientForgetPreserves (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  GrothendieckTopology.instPreservesSheafification _ _

/-- The presheaf map sending a scalar to its constant continuous function; its
sheafification is `pointConstants`. -/
noncomputable def constantFunctions (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of T) ⟶ continuousPresheaf T where
  app U := CommRingCat.ofHom (ContinuousMap.C (α := U.unop))
  naturality _ _ _ := rfl

theorem pointConstants_eq (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    pointConstants T = (presheafToSheaf _ CommRingCat.{u + 1}).map (constantFunctions T) :=
  rfl

/-- Continuous functions into a finite discrete ring are locally constant. -/
instance constantFunctions_locallySurjective (T : Type (u + 1)) [CommRing T] [Finite T]
    [TopologicalSpace T] [DiscreteTopology T] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (constantFunctions T) where
  imageSieve_mem {S} s := by
    let f : C(S, T) := s
    have hclosed (a : T) : IsClosed {x : S | f x = a} :=
      isClosed_singleton.preimage f.continuous
    let (a : T) : CompactSpace {x : S // f x = a} :=
      isCompact_iff_compactSpace.mp (hclosed a).isCompact
    let := Fintype.ofFinite T
    let e := (Fintype.equivFin T).symm
    let U (i : Fin (Fintype.card T)) : Profinite.{u} :=
      Profinite.of {x : S // f x = e i}
    let incl (i : Fin (Fintype.card T)) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨e.symm (f x), ⟨x, (e.apply_symm_apply (f x)).symm⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card T), inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨e i, ?_⟩
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

/-- Equality of constant functions is detected locally (using the empty cover of the
empty profinite set). -/
instance constantFunctions_locallyInjective (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (constantFunctions T) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (congrArg (fun t : C(S.unop, T) ↦ t x) h)⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

/-- For finite discrete coefficients, constant functions sheafify to all continuous
functions. -/
instance pointConstants_isIso (T : Type (u + 1)) [CommRing T] [Finite T]
    [TopologicalSpace T] [DiscreteTopology T] : IsIso (pointConstants T) := by
  rw [pointConstants_eq, ← GrothendieckTopology.W_iff]
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

/-- Precomposing the inverse constant-sheaf comparison with the sheafification unit gives
the whiskered sheafification unit. -/
theorem toSheafify_comp_constantCommuteCompose_inv_app_hom {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {D B : Type*} [Category* D] [Category* B] (U : D ⥤ B)
    [HasWeakSheafify J D] [HasWeakSheafify J B] [J.PreservesSheafification U]
    [J.HasSheafCompose U] (R : D) :
    toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj R)) ≫
        ((constantCommuteCompose J U).app R).inv.hom =
      (Functor.constComp Cᵒᵖ R U).inv ≫
        Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj R)) U := by
  refine (Iso.comp_inv_eq ((sheafToPresheaf J B).mapIso ((constantCommuteCompose J U).app R))).2
    ?_
  rw [Functor.mapIso_hom, sheafToPresheaf_map, Iso.app_hom, constantCommuteCompose_hom_app_hom,
    Category.assoc, sheafComposeIso_inv_fac_assoc, ← toSheafify_naturality, Iso.inv_hom_id_assoc]

/-- The underlying additive map of `pointConstants`, with constant abelian source. -/
noncomputable def pointAbelianConstants (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj (AddCommGrpCat.of T) ⟶
      abelianPoint T := by
  letI : HasSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  letI : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  exact ((constantCommuteCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).inv ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (pointConstants T))

theorem schemeConstants_eq (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    schemeConstants X T = (constantSchemeIso X).hom.app (AddCommGrpCat.of T) ≫
      (upperStarFromPoint X).map (pointAbelianConstants T) :=
  rfl

/-- `pointAbelianConstants` is the sheafified constant-function map, followed by the
counit identification of the underlying abelian sheaf of `continuousPoint`. -/
theorem pointAbelianConstants_eq (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    pointAbelianConstants T =
      (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (Functor.whiskerRight (Functor.whiskerRight
          (constantFunctions T ≫ toSheafify _ (continuousPresheaf T))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
          (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
        (Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (continuousPoint T))).hom := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (abelianPoint T).property
  have h : toSheafify _ _ ≫ (pointConstants T).hom =
      constantFunctions T ≫ toSheafify _ (continuousPresheaf T) :=
    (toSheafify_naturality _ _).symm
  rw [ObjectProperty.FullSubcategory.comp_hom, ← toSheafify_naturality_assoc,
    Sheaf.sheafifyRingPresheafIso, asIso_hom, sheafificationAdjunction_counit_app_val,
    toSheafify_sheafifyLift, pointAbelianConstants, ObjectProperty.FullSubcategory.comp_hom,
    ← Category.assoc]
  let : HasSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have he := toSheafify_comp_constantCommuteCompose_inv_app_hom (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})
    (CommRingCat.of T)
  refine (congrArg (· ≫ ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (pointConstants T))).hom) he).trans ?_
  ext U a
  exact ConcreteCategory.congr_hom (congr_app h U) a

/-- The ring object structure on a constant abelian sheaf with ring values, transported by
the lax monoidal constant-sheaf functor, is the sheafification of the constant presheaf of
rings. -/
theorem constantSheaf_monObjObj_eq {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal] (B : Type w) [CommRing B] :
    (constantSheaf J Ab.{w}).monObjObj (AddCommGrpCat.of B) =
      Sheaf.monObj_presheafToSheaf_obj J
        ((Functor.const Cᵒᵖ).obj (RingCat.of B) ⋙ forget₂ RingCat Ab) := by
  refine (Functor.monObjObj_comp (Functor.const Cᵒᵖ) (presheafToSheaf J Ab.{w})
    (AddCommGrpCat.of B)).trans ?_
  have h : (Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B) =
      Functor.monObjCompForget₂ ((Functor.const Cᵒᵖ).obj (RingCat.of B)) := by
    apply MonObj.ext
    ext U
    rfl
  exact congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _ (presheafToSheaf J Ab.{w}) _ _ m) h

/-- The constant-function map on the point is multiplicative. -/
instance pointAbelianConstants_isMonHom (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : IsMonHom (pointAbelianConstants T) := by
  rw [pointAbelianConstants_eq]
  exact IsMonHom.of_eq _ (constantSheaf_monObjObj_eq _ T).symm rfl

/-- The inverse of a monoid-object isomorphism is a monoid-object morphism, with all
monoid structures explicit. -/
theorem isMonHom_iso_inv_explicit {C : Type*} [Category* C] [MonoidalCategory C]
    {M N : C} (mM : MonObj M) (mN : MonObj N) (e : M ≅ N)
    (h : @IsMonHom _ _ _ M N mM mN e.hom) :
    @IsMonHom _ _ _ N M mN mM e.inv := by
  let := mM
  let := mN
  let := h
  infer_instance

/-- A composite of monoid-object morphisms, with all monoid structures explicit. -/
theorem isMonHom_comp_explicit {C : Type*} [Category* C] [MonoidalCategory C]
    {M N O : C} (mM : MonObj M) (mN : MonObj N) (mO : MonObj O)
    (f : M ⟶ N) (g : N ⟶ O)
    (hf : @IsMonHom _ _ _ M N mM mN f)
    (hg : @IsMonHom _ _ _ N O mN mO g) :
    @IsMonHom _ _ _ M O mM mO (f ≫ g) := by
  let := mM
  let := mN
  let := mO
  let := hf
  let := hg
  infer_instance

/-- The constant-section map on the scheme is multiplicative. -/
instance schemeConstants_isMonHom (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] : IsMonHom (schemeConstants X T) := by
  have hi := Functor.isMonHom_compAlgHom (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (upperStarFromPoint X) (constantSchemeIso X).inv (AddCommGrpCat.of T)
  let mP := (upperStarFromPoint X).monObjObj
    ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj (AddCommGrpCat.of T))
  let mQ := (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).monObjObj (AddCommGrpCat.of T)
  have hh := isMonHom_iso_inv_explicit mP mQ
    ((constantSchemeIso X).app (AddCommGrpCat.of T)).symm hi
  have hmap : @IsMonHom _ _ _ _ _ mP _ ((upperStarFromPoint X).map (pointAbelianConstants T)) :=
    inferInstance
  rw [schemeConstants_eq]
  exact isMonHom_comp_explicit mQ mP _ _ _ hh hmap

/-- The constant-section map, as a map of abelian presheaves out of the constant presheaf. -/
noncomputable abbrev schemeConstantsPresheaf (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of T) ⟶ (internalRing X T).obj :=
  toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of T)) ≫
    (schemeConstants X T).hom

/-- A lax monoidal functor maps monoid-object morphisms to monoid-object morphisms, with all
monoid structures explicit. -/
theorem isMonHom_map_explicit {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {M N : C} (mM : MonObj M) (mN : MonObj N) (f : M ⟶ N)
    (hf : @IsMonHom _ _ _ M N mM mN f) :
    @IsMonHom _ _ _ _ _ (F.monObjObj M) (F.monObjObj N) (F.map f) := by
  let := mM
  let := mN
  let := hf
  infer_instance

/-- The presheaf constant-section map is multiplicative. -/
theorem schemeConstantsPresheaf_isMonHom (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    @IsMonHom _ _ _ _ _ ((Functor.const X.ProEtᵒᵖ).monObjObj (AddCommGrpCat.of T))
      ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).monObjObj (internalRing X T))
      (schemeConstantsPresheaf X T) := by
  let J := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of T)
  let mS := (presheafToSheaf J Ab.{u + 1}).monObjObj P
  have hm : (constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of T) = mS :=
    Functor.monObjObj_comp _ _ _
  have hc := IsMonHom.of_eq (schemeConstants X T) hm rfl
  have hu := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
  have hf := isMonHom_map_explicit (sheafToPresheaf J Ab.{u + 1}) mS _ (schemeConstants X T) hc
  exact isMonHom_comp_explicit _ _ _ _ _ hu hf

open CategoryTheory.MonObj in
open scoped TensorProduct in
/-- A multiplicative map from a constant presheaf of rings into the sections of a commutative
internal ring sheaf, as a map into the reconstructed section-ring sheaf. -/
noncomputable def constantSectionRingMapOfMonHom
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [UnivLE.{_, u + 1}] [HasSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (B : Type (u + 1)) [CommRing B]
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (φ : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B) ⟶ R.obj)
    (hφ : @IsMonHom _ _ _ _ _
      ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ) :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf J R).obj where
  app U := by
    letI := CommRingCat.commRing
      ((InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U)
    refine CommRingCat.ofHom
      (R := B) (S := (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U) ?_
    refine
      { toFun := fun a ↦ φ.app U a
        map_zero' := map_zero _
        map_add' := map_add _
        map_one' := ?_
        map_mul' := ?_ }
    · have h := @IsMonHom.one_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ hφ
      convert! ConcreteCategory.congr_hom (congr_app h U) (ULift.up 1) using 1
      simp only [Functor.const_obj_obj, Monoidal.tensorUnit_obj, ObjectProperty.ι_obj,
        Functor.obj.η_def, Category.assoc, NatTrans.comp_app, Functor.const_map_app,
        AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      change (φ.app U) (1 : B) = (φ.app U) ((η[AddCommGrpCat.of B]).hom (ULift.up 1))
      rw [AddCommGrpCat.ringMonObj_one_apply]
      simp
    · intro a b
      have h := @IsMonHom.mul_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ hφ
      have he := ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b)
      convert! he using 1
  naturality U V f := by
    ext a
    exact ConcreteCategory.congr_hom (φ.naturality f) a

/-- The constant-section homomorphism of ring sheaves, obtained by sheafifying the
multiplicative constant-section map. -/
noncomputable def constantSectionsMap (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ⟶ sectionRing X T :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv _
    (sectionRing X T)).symm
    (constantSectionRingMapOfMonHom (Scheme.ProEt.topology X) T (internalRing X T)
      (schemeConstantsPresheaf X T) (schemeConstantsPresheaf_isMonHom X T))

/-- The underlying additive map of `constantSectionsMap` is the constant-section map. -/
theorem sheafCompose_map_constantSectionsMap (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map (constantSectionsMap X T) =
      ((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).hom ≫
        schemeConstants X T := by
  rw [← Iso.inv_comp_eq]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (internalRing X T).property
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    toSheafify_comp_constantCommuteCompose_inv_app_hom]
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv _
    (sectionRing X T)).apply_symm_apply
    (constantSectionRingMapOfMonHom (Scheme.ProEt.topology X) T (internalRing X T)
      (schemeConstantsPresheaf X T) (schemeConstantsPresheaf_isMonHom X T))
  ext U a
  exact ConcreteCategory.congr_hom (congr_app h U) a

/-- Constant sections determine the map to the reconstructed continuous coefficient ring.
Source: the constant-ring/section-action comparison, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction).

Proof: constant functions preserve addition, multiplication and one before
sheafification. Monoidal pullback from the point preserves those identities.
The section-action equivalence reconstructs this map as a homomorphism of
commutative ring sheaves. Its underlying additive map is exactly the composite
displayed here, because constantSchemeIso is the constant-pullback comparison.
The forgetful functor from commutative rings to abelian groups is faithful;
the prescribed additive map therefore proves uniqueness. Reconstructing the
section rings retains their original carriers and additive restrictions, which
accounts for the heterogeneous equality of the two ring presentations.
-/
theorem constantSections_existsUnique (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    ∃! f : realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ⟶ sectionRing X T,
      HEq ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map f)
        (((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).hom ≫
          schemeConstants X T) := by
  refine ⟨constantSectionsMap X T, heq_of_eq (sheafCompose_map_constantSectionsMap X T), ?_⟩
  intro f hf
  apply (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact (eq_of_heq hf).trans (sheafCompose_map_constantSectionsMap X T).symm

/-- The uniquely specified constant-section homomorphism.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
def constantSections (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  (constantSections_existsUnique X T).exists.choose

/-- For finite discrete coefficients, `pointAbelianConstants` is an isomorphism. -/
instance pointAbelianConstants_isIso (T : Type (u + 1)) [CommRing T] [Finite T]
    [TopologicalSpace T] [DiscreteTopology T] : IsIso (pointAbelianConstants T) := by
  rw [pointAbelianConstants]
  infer_instance

/-- For finite discrete coefficients the constant-section homomorphism is an isomorphism.
Source: Bhatt--Scholze, finite coefficient comparison
(blueprint: def-sfb-coherent-integral-reduction).

Proof: continuous functions into a finite discrete ring are locally constant.
On a profinite test each such function is constant on a finite clopen partition.
These partitions are covers for the coherent topology, so pointConstants is
locally surjective. Equality of constant functions is locally detected, giving
local injectivity. Sheafification makes it an isomorphism. Pullback to X and
section-ring reconstruction preserve it. The preceding additive normalization
identifies the resulting map with constantSections by uniqueness. This includes
the zero ring and the empty scheme.
-/
theorem constantSections_isIso (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [Finite T] [TopologicalSpace T] [DiscreteTopology T] :
    IsIso (constantSections X T) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})),
    constantSections, eq_of_heq (constantSections_existsUnique X T).exists.choose_spec,
    schemeConstants_eq]
  infer_instance

/-- The finite constant-coefficient identification, with its original constant-section map.
Source: finite coefficient comparison
(blueprint: def-sfb-coherent-integral-reduction). -/
def finiteConstantIso (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [Finite T] [TopologicalSpace T] [DiscreteTopology T] :
    realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ≅ sectionRing X T :=
  letI := constantSections_isIso X T
  asIso (constantSections X T)

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The spectral topology on the ring of integers, with no discrete replacement.
Source: the blueprint's integral coefficient ring
(blueprint: def-sfb-coherent-integral-reduction). -/
instance integersTopology : TopologicalSpace (Padic.coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  inferInstance

/-- The spectral topology makes O a topological ring.
Source: the blueprint's integral coefficient ring
(blueprint: def-sfb-coherent-integral-reduction). -/
instance integersTopologicalRing : IsTopologicalRing (Padic.coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  inferInstance

/-- Every finite quotient carries its discrete topology.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientTopology (n : ℕ) : TopologicalSpace (Etale.FiniteProperQuotient.Ring l E n) :=
  ⊥

/-- These specified finite quotient topologies are discrete.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientDiscrete (n : ℕ) : DiscreteTopology (Etale.FiniteProperQuotient.Ring l E n) :=
  ⟨rfl⟩

/-- The quotient homomorphism from O to the positive ell-power quotient.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
def quotient (n : ℕ) : Padic.coefficientExtensionIntegers l E →+*
    Etale.FiniteProperQuotient.Ring l E n :=
  Ideal.Quotient.mk _

/-- The ideal generated by a power of `ℓ` in the ring of integers is a power of the
maximal ideal. -/
theorem exists_span_pow_eq_coefficientExtensionIdeal (r : ℕ) :
    ∃ k : ℕ, Ideal.span ({(l : Padic.coefficientExtensionIntegers l E) ^ r} :
      Set (Padic.coefficientExtensionIntegers l E)) = Padic.coefficientExtensionIdeal l E k := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) := h.2.2.2.2.2.2.2.1
  have hgen := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hirr : Irreducible (Padic.coefficientExtensionUniformizer l E) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalRing.eq_maximalIdeal h.2.2.2.2.1]
    exact hgen.symm
  have hl : ((l : Padic.coefficientExtensionIntegers l E) ^ r) ≠ 0 := by
    refine pow_ne_zero _ fun h0 ↦ ?_
    have h1 := congrArg (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) h0
    simp only [Subring.coe_natCast, ZeroMemClass.coe_zero] at h1
    have h2 : algebraMap ℚ_[l] E (l : ℚ_[l]) = 0 := by simpa using h1
    have h3 := (FaithfulSMul.algebraMap_injective ℚ_[l] E) (h2.trans (map_zero _).symm)
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h3
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(l : Padic.coefficientExtensionIntegers l E) ^ r})
    (by simpa [Ideal.span_singleton_eq_bot] using hl) hirr
  exact ⟨k, by rw [hk, Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]⟩

/-- Positive ell-power quotients of the ring of integers are finite rings.
Source: the blueprint's finite torsion coefficients
(blueprint: def-sfb-coherent-integral-reduction).

Proof: the integer ring of the finite extension is a DVR with finite residue
field. The nonzero element ell has positive valuation, so ell^(n+1) generates
the same ideal as a positive power of a uniformizer. Filter its quotient by
successive powers of that uniformizer. Each successive quotient is the finite
residue field. Induction on the positive exponent makes the entire quotient
finite. Ramified extensions are included: the exponent is multiplied by their
ramification index, not replaced by n+1.
-/
theorem quotient_finite (n : ℕ) : Finite (Etale.FiniteProperQuotient.Ring l E n) := by
  obtain ⟨k, hk⟩ := exists_span_pow_eq_coefficientExtensionIdeal l E (n + 1)
  exact @Finite.of_surjective _ _
    (Padic.finite_coefficientExtensionRing l E (k + 1) (Nat.le_add_left 1 k))
    ((Ideal.quotEquivOfEq hk.symm) ∘
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k)))
    ((Ideal.quotEquivOfEq hk.symm).surjective.comp (Ideal.Quotient.factor_surjective _))

/-- Finiteness for the actual positive ell-power quotients.
Source: finite torsion coefficients
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientFinite (n : ℕ) : Finite (Etale.FiniteProperQuotient.Ring l E n) :=
  quotient_finite l E n

/-- Positive ell-power quotients of the spectral ring of integers are continuous
with their discrete topology.
Source: the finite torsion levels in the blueprint; Zheng, Construction 4.1
(blueprint: def-sfb-coherent-integral-reduction).

Proof: the spectral absolute value restricts to the given l-adic absolute value.
The ideal generated by ell^(n+1) in O is therefore open: a sufficiently small
spectral ball is contained in it, using the discrete valuation of the finite
extension. Every fibre of the quotient map is a translate of this open ideal.
Preimages of arbitrary sets of the discrete quotient are unions of these open
fibres. The quotient homomorphism is continuous. Positivity of n+1 excludes the
zero-exponent convention; ramification changes the valuation of ell but not
openness of its positive powers.
-/
theorem quotient_continuous (n : ℕ) : Continuous (quotient l E n) := by
  obtain ⟨k, hk⟩ := exists_span_pow_eq_coefficientExtensionIdeal l E (n + 1)
  have hle : Padic.coefficientExtensionIdeal l E (k + 1) ≤
      Ideal.span {(l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)} :=
    hk ▸ Ideal.pow_le_pow_right (Nat.le_succ k)
  have hq : IsLocallyConstant
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (k + 1))) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    exact (Padic.coefficientExtension_integers_coset_basis l E x).mem_of_mem (i := k) trivial
  have : quotient l E n = (Ideal.Quotient.factor hle).comp
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (k + 1))) :=
    (Ideal.Quotient.factor_comp_mk hle).symm
  rw [this]
  exact (hq.comp (Ideal.Quotient.factor hle)).continuous

/-- Finite coefficient sheaves on the pro-etale site, obtained from the point.
Source: the blueprint's quotient coefficient system
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :=
  sectionRing X (Etale.FiniteProperQuotient.Ring l E n)

/-- Adjacent quotient maps on the actual pulled-back section rings.
Source: the blueprint's quotient coefficient system
(blueprint: def-sfb-coherent-integral-reduction). -/
def transitions (X : Scheme.{u}) (n : ℕ) :
    coefficients l E X (n + 1) ⟶ coefficients l E X n :=
  sectionMap X (Etale.FiniteProperQuotient.quotient l E (Nat.le_succ n))
    (continuous_of_discreteTopology)

/-- The actual coefficient morphism from continuous integral to finite coefficients.
Source: the blueprint's derived reduction
(blueprint: def-sfb-coherent-integral-reduction). -/
def coefficientMap (X : Scheme.{u}) (n : ℕ) :
    sectionRing X (Padic.coefficientExtensionIntegers l E) ⟶ coefficients l E X n :=
  sectionMap X (quotient l E n) (quotient_continuous l E n)

/-- Postcomposition with continuous ring homomorphisms is functorial. -/
theorem continuousPointMap_comp {T S W : Type (u + 1)} [CommRing T] [CommRing S] [CommRing W]
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace W] [IsTopologicalRing T]
    [IsTopologicalRing S] [IsTopologicalRing W] (f : T →+* S) (hf : Continuous f)
    (g : S →+* W) (hg : Continuous g) :
    continuousPointMap f hf ≫ continuousPointMap g hg =
      continuousPointMap (g.comp f) (hg.comp hf) := by
  unfold continuousPointMap
  rw [← Functor.map_comp]
  rfl

/-- Reconstructing section rings is functorial. -/
theorem internalSectionMap_comp (X : Scheme.{u})
    {R S W : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj W] [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj W]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ W) [IsMonHom g] :
    internalSectionMap X f ≫ internalSectionMap X g = internalSectionMap X (f ≫ g) :=
  rfl

/-- `sectionMap` is functorial. -/
theorem sectionMap_comp (X : Scheme.{u}) {T S W : Type (u + 1)} [CommRing T] [CommRing S]
    [CommRing W] [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace W]
    [IsTopologicalRing T] [IsTopologicalRing S] [IsTopologicalRing W]
    (f : T →+* S) (hf : Continuous f) (g : S →+* W) (hg : Continuous g) :
    sectionMap X f hf ≫ sectionMap X g hg = sectionMap X (g.comp f) (hg.comp hf) := by
  unfold sectionMap
  rw [internalSectionMap_comp]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, continuousPointMap_comp]

/-- The integral quotient maps form a morphism of the actual ring systems.
Source: Zheng, Construction 4.1, and the original quotient maps in blueprint step 1
(blueprint: def-sfb-coherent-integral-reduction).

Proof: both ring homomorphisms O to A_n send x to its class modulo ell^(n+1).
Postcomposition on continuous functions preserves composition. So do sheafification,
forgetting to abelian groups, pullback from the point, and section-ring reconstruction.
Their images are the displayed equality of sheaf morphisms. This also proves the
equal-index and composite quotient identities; no coefficient quotient is treated as flat.
-/
theorem coefficientMap_compatible (X : Scheme.{u}) (n : ℕ) :
    coefficientMap l E X (n + 1) ≫ transitions l E X n =
      (𝟙 (sectionRing X (Padic.coefficientExtensionIntegers l E))) ≫
        coefficientMap l E X n := by
  rw [Category.id_comp]
  unfold coefficientMap transitions
  rw [sectionMap_comp]
  congr 1

/-- Constant continuous functions commute with continuous postcomposition. -/
theorem pointConstants_comp_continuousPointMap {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) :
    pointConstants T ≫ continuousPointMap f hf =
      (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom f) ≫ pointConstants S := by
  dsimp only [pointConstants, continuousPointMap, constantSheaf, Functor.comp_map]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The constant-section map into the pulled-back continuous ring is natural in the
coefficient ring. -/
theorem schemeConstants_naturality (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T]
    [CommRing S] [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T]
    [IsTopologicalRing S] (f : T →+* S) (hf : Continuous f) :
    schemeConstants X T ≫ (upperStarFromPoint X).map
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (continuousPointMap f hf))) =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom f.toAddMonoidHom) ≫ schemeConstants X S := by
  let : HasSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  dsimp only [schemeConstants]
  rw [Category.assoc, ← Functor.map_comp, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, pointConstants_comp_continuousPointMap]
  rw [(constantSchemeIso X).hom.naturality_assoc, Functor.comp_map, ← Functor.map_comp]
  refine congrArg (_ ≫ ·) (congrArg (upperStarFromPoint X).map ?_)
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ _) ?_
  exact ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).inv.naturality (CommRingCat.ofHom f)).symm

/-- The section ring of a continuous coefficient ring has the pulled-back continuous ring as
underlying abelian sheaf, and section maps are the pulled-back continuous postcompositions. -/
theorem sheafCompose_map_sectionMap (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T]
    [CommRing S] [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T]
    [IsTopologicalRing S] (f : T →+* S) (hf : Continuous f) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map (sectionMap X f hf) =
      (upperStarFromPoint X).map
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (continuousPointMap f hf))) := rfl

/-- The constant-section homomorphisms commute with the section maps of a continuous
coefficient homomorphism. -/
theorem constantSections_comp_sectionMap (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T]
    [CommRing S] [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T]
    [IsTopologicalRing S] (f : T →+* S) (hf : Continuous f) :
    constantSections X T ≫ sectionMap X f hf =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom f) ≫ constantSections X S := by
  apply (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  have hT : (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map (constantSections X T) =
      ((constantCommuteCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).hom ≫
        schemeConstants X T :=
    eq_of_heq (constantSections_existsUnique X T).exists.choose_spec
  have hS : (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map (constantSections X S) =
      ((constantCommuteCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of S)).hom ≫
        schemeConstants X S :=
    eq_of_heq (constantSections_existsUnique X S).exists.choose_spec
  rw [Functor.map_comp, Functor.map_comp, hT, hS, sheafCompose_map_sectionMap, Category.assoc,
    schemeConstants_naturality, ← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ _) ?_
  exact ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).hom.naturality (CommRingCat.ofHom f)).symm

/-- The normalized simultaneous derived extension of the constant integral system.
Source: Zheng, Construction 4.1; the existing normalized semilinear calculus
(blueprint: def-sfb-coherent-integral-reduction). -/
def reductionScalar (X : Scheme.{u}) :
    ScalarSystems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E)))
      (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E)))
      (coefficients l E X) (transitions l E X) (coefficientMap l E X)
      (coefficientMap_compatible l E X) :=
  SemilinearDerivedSectionsData.coefficientExtension.{u + 1, u, u + 1}
    (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X)
    (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)))
    (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)))))
    (coefficients l E X) (transitions l E X) (coefficientMap l E X)
    (coefficientMap_compatible l E X)

/-- The exact section-action equivalence, on the actual continuous integral coefficients.
Source: the recorded internal/sectionwise module equivalence, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
def integralSections (X : Scheme.{u}) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (internalRing X (Padic.coefficientExtensionIntegers l E))).functor

/-- Section-action transport leaves addition of morphisms unchanged.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_additive (X : Scheme.{u}) : (integralSections l E X).Additive where
  map_add := by intros; rfl

/-- An equivalence preserves kernels.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (integralSections l E X) :=
  inferInstanceAs (PreservesFiniteLimits
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (internalRing X (Padic.coefficientExtensionIntegers l E))).functor)

/-- An equivalence preserves cokernels.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (integralSections l E X) :=
  inferInstanceAs (PreservesFiniteColimits
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (internalRing X (Padic.coefficientExtensionIntegers l E))).functor)

/-- Bounded constructible integral complexes, with precisely the existing cohomology predicate.
Source: the blueprint's Dbc notation
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev Bc (X : Scheme.{u}) :=
  BoundedConstructible (internalRing X (Padic.coefficientExtensionIntegers l E))

/-- Actual integral reductions as one object of the ordinary derived category of systems.
This is section-action transport, the exact diagonal, and one simultaneous derived
scalar extension. Its K-flat normalization is part of reductionScalar's model.
Source: Zheng, Construction 4.1; blueprint coherent-tower proof, step 1
(blueprint: def-sfb-coherent-integral-reduction). -/
def reduction (X : Scheme.{u}) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (internalRing X (Padic.coefficientExtensionIntegers l E))) ⥤
      DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) :=
  (integralSections l E X).mapDerivedCategory ⋙
    derivedConstantSystem.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)) ⋙
    ScalarData.T.{u + 1, u, u + 1} _ (reductionScalar l E X).scalar

/-- Restrict the canonical reduction functor to the full bounded constructible category.
Source: blueprint coherent-tower statement
(blueprint: def-sfb-coherent-integral-reduction). -/
def reductionBc (X : Scheme.{u}) : Bc l E X ⥤
    DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) :=
  (boundedConstructible (internalRing X (Padic.coefficientExtensionIntegers l E))).ι ⋙
    reduction l E X

end AlgebraicGeometry.ProEtale.CoherentReduction

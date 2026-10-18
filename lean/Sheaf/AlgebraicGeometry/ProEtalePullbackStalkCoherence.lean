/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Coherence of pro-etale pullback stalk comparisons

Source: Stacks Project, Tags 05V1 and 0F4F, and proetale.tex Tag 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The stalk functor on cochain complexes, obtained term by term from the
finite-coefficient geometric stalk.  Source: Stacks Tags 0F4F and 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable def proEtaleFiniteCoefficientStalkComplexFunctor
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (u : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ℤ :=
  (finiteCoefficientModuleStalkFunctor u A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Pullback followed by the termwise geometric stalk on complexes.  Source:
Stacks Tags 05V1 and 0F4F (blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable def proEtalePullbackFiniteCoefficientStalkComplexFunctor
    {T S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : T ⟶ S) (u : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules S (proEtaleConstantRing S A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ℤ :=
  (proEtaleConstantRingPullback A t).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    proEtaleFiniteCoefficientStalkComplexFunctor u A

/-- The actual additive colimit coprojection, viewed in the stalk with constant scalars.
Source: Stacks Tags 0F6B and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleCoefficientModuleGerm {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)) :
    (finiteCoefficientModuleStalkFunctor x A).obj M :=
  (colimit.ι ((proEtaleGeometricNeighbourhoodForget x).op ⋙ M.val.presheaf) (op N)) a

/-- Both representative formulas defining the canonical comparison. The first quantifies
all comma representatives `(P, theta, a)`; the equality of lifts says that `N` is their
projected pointed neighbourhood. The second is the inverse formula on unit germs.
Source: Stacks Tags 05V1 and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def ProEtalePullbackStalkGermNormalized (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (c : proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A) : Prop :=
  (∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (N : ProEtaleGeometricNeighbourhood (x ≫ t))
    (P : ProEtaleGeometricNeighbourhood x)
    (θ : P.right ⟶ (proEtaleBaseChange t).obj N.right)
    (a : M.val.obj (op N.right)),
    P.hom.left ≫ θ.left ≫ pullback.fst N.right.hom t = N.hom.left →
    c.hom.app M (proEtaleCoefficientModuleGerm x A
      ((proEtaleConstantRingPullback A t).obj M) P
      (((proEtaleConstantRingPullback A t).obj M).val.map θ.op
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a))) =
      proEtaleCoefficientModuleGerm (x ≫ t) A M N a) ∧
  (∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (N : ProEtaleGeometricNeighbourhood (x ≫ t))
    (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
    (a : M.val.obj (op N.right)),
    l.left ≫ pullback.fst N.right.hom t = N.hom.left →
    c.inv.app M (proEtaleCoefficientModuleGerm (x ≫ t) A M N a) =
      proEtaleCoefficientModuleGerm x A ((proEtaleConstantRingPullback A t).obj M)
        (StructuredArrow.mk l)
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a))

/-- The normalized comparison exists uniquely; this fixes its data before any coherence
assertion. Source: Stacks Tags 05V1 and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: apply `proEtaleInverseImage_abelianStalk` to the underlying abelian sheaf.
Sheafification does not change its stalk by `proEtaleGeometricStalk_sheafification`.
The two colimit maps send `(P,theta,a)` to the projected germ and a germ to its
pullback-unit section. Restriction relations make both maps well defined; the pointed
arrow theta proves the second composite is the identity. Constant scalars are preserved
by the specified coefficient comparison, so these maps are A-linear. The unit is the
normalized module adjunction unit. A module morphism acts only on a, giving naturality.
Every stalk element is represented after sheafification by such a germ; hence the first
formula determines every component, proving uniqueness. -/
theorem proEtalePullbackStalkComparison_existsUnique (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    ∃! c : proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A,
      ProEtalePullbackStalkGermNormalized A t x c := by
  sorry

/-- The unique comparison specified on all represented germs, not a choice of an
unnormalized isomorphism. Source: Stacks Tags 05V1 and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtalePullbackStalkComparison (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A :=
  (proEtalePullbackStalkComparison_existsUnique A t x).exists.choose

/-- Reindex pointed neighbourhoods by precomposition with the field automorphism.
The underlying site object and section are unchanged. Source: Stacks Tag 05V1
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkNeighbourhoodReparam {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    ProEtaleGeometricNeighbourhood x ⥤
      ProEtaleGeometricNeighbourhood (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) :=
  StructuredArrow.map (T := ProEt.forget T)
    (Over.homMk (Spec.map (CommRingCat.ofHom α.toRingHom)) rfl)

/-- The colimit map of neighbourhood reindexing is a unique A-linear natural
isomorphism. Source: Stacks Tag 05V1
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: each coprojection is sent to the coprojection at its reindexed neighbourhood.
Reindexing preserves pointed arrows, so the colimit universal property supplies the
additive map. Common pointed refinements show compatibility with the constant scalar
action. Reindexing by alpha inverse supplies the inverse. Module maps apply to sections
and commute with reindexing, giving naturality. Coprojections jointly determine maps,
so the displayed formula determines the natural isomorphism uniquely. -/
theorem proEtaleStalkReparam_existsUnique (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    ∃! r : finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A,
      ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
        (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)),
        r.hom.app M (proEtaleCoefficientModuleGerm x A M N a) =
          proEtaleCoefficientModuleGerm _ A M ((proEtaleStalkNeighbourhoodReparam x α).obj N)
            a := by
  sorry

/-- The map induced by the specified neighbourhood reindexing, uniquely fixed by
its formula on coprojections. Source: Stacks Tag 05V1
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkReparam (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A :=
  (proEtaleStalkReparam_existsUnique A x α).exists.choose

/-- The identity-pullback comparison is uniquely fixed by its inverse, the unit
followed by restriction along the diagonal. Source: Stacks Tags 05V1 and 09A5
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: inverse image for the identity is the identity left Kan extension followed by
sheafification. The inverse is its unit restricted along U to U times_T T. The comma
universal property and the sheaf axiom show this is an isomorphism. The coefficient
comparison preserves constants and the tensor unit, so this is A-linear and natural.
The formula fixes its inverse sectionwise and therefore determines the isomorphism. -/
theorem proEtaleStalkIdentityPullback_existsUnique (A : Type u) [CommRing A]
    (T : Scheme.{u}) :
    ∃! e : proEtaleConstantRingPullback A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)),
      ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEt)
        (a : M.val.obj (op V)),
        (e.inv.app M).val.app (op V) a =
          ((proEtaleConstantRingPullback A (𝟙 T)).obj M).val.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V).op
            (((proEtaleConstantRingAdjunction A (𝟙 T)).unit.app M).val.app (op V) a) := by
  sorry

/-- The canonical identity-pullback isomorphism with its diagonal-unit normalization.
Source: Stacks Tags 05V1 and 09A5
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkIdentityPullback (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingPullback A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)) :=
  (proEtaleStalkIdentityPullback_existsUnique A T).exists.choose

/-- Exactness of the geometric module stalk, needed for ordinary derived localization.
Source: Stacks Tags 0993 and 00Y8
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: `proEtale_classical_stalk` gives exactness of the abelian stalk. Kernels and
cokernels of module sheaves and modules have the corresponding underlying abelian
groups. The module colimit construction has that abelian stalk, and restriction along
the constant germ changes only the action. Thus both finite limits and finite colimits
are preserved, with no nonzero-ring or nonempty-scheme condition. -/
theorem proEtaleCoefficientStalk_exact (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    PreservesFiniteLimits (finiteCoefficientModuleStalkFunctor x A) ∧
      PreservesFiniteColimits (finiteCoefficientModuleStalkFunctor x A) := by
  sorry

/-- Left exactness from the underlying abelian stalk. Source: Stacks Tag 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable instance proEtaleCoefficientStalk_preservesFiniteLimits
    (A : Type u) [CommRing A] {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    PreservesFiniteLimits (finiteCoefficientModuleStalkFunctor x A) :=
  (proEtaleCoefficientStalk_exact A x).1

/-- Right exactness from the underlying abelian stalk. Source: Stacks Tag 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable instance proEtaleCoefficientStalk_preservesFiniteColimits
    (A : Type u) [CommRing A] {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    PreservesFiniteColimits (finiteCoefficientModuleStalkFunctor x A) :=
  (proEtaleCoefficientStalk_exact A x).2

/-- The ordinary derived stalk obtained by localizing the termwise stalk functor.
Source: Stacks Tag 0D6D and the localization universal property
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
abbrev proEtaleFiniteCoefficientDerivedStalk (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :=
  (finiteCoefficientModuleStalkFunctor x A).mapDerivedCategory

/-- The normalized comparison descended by the localization universal property.
Source: Stacks Tags 05V1 and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleDerivedPullbackStalkComparison (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    proEtaleConstantRingDerivedPullback A t ⋙ proEtaleFiniteCoefficientDerivedStalk A x ≅
      proEtaleFiniteCoefficientDerivedStalk A (x ≫ t) :=
  letI : PreservesFiniteLimits
      (proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A t)
      (finiteCoefficientModuleStalkFunctor x A)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (proEtalePullbackStalkComparison A t x)

/-- Neighbourhood reindexing descended to ordinary derived categories.
Source: Stacks Tags 05V1 and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleDerivedStalkReparam (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    proEtaleFiniteCoefficientDerivedStalk A x ≅
      proEtaleFiniteCoefficientDerivedStalk A (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) :=
  Functor.mapDerivedCategoryNatIso (proEtaleStalkReparam A x α)

/-- The canonical identity comparison descended termwise, including the localization
identity unitor. Source: Stacks Tag 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkDerivedIdentityPullback (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingDerivedPullback A (𝟙 T) ≅ 𝟭 (proEtaleDerivedCategory T A) :=
  Functor.mapDerivedCategoryNatIso (proEtaleStalkIdentityPullback A T) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The precise normalized stalk comparison and its coherence, including the equations
in the ordinary derived category for bounded complexes. Reassociation of point maps
is written explicitly as transport by equality.
Source: Stacks Tags 05V1, 0F4F and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def ProEtalePullbackStalkCoherent (A : Type u) [CommRing A] [Finite A] : Prop :=
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T),
    ProEtalePullbackStalkGermNormalized A t x (proEtalePullbackStalkComparison A t x)) ∧
  (∀ {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)),
    (proEtaleStalkReparam A x α).hom.app M (proEtaleCoefficientModuleGerm x A M N a) =
      proEtaleCoefficientModuleGerm _ A M ((proEtaleStalkNeighbourhoodReparam x α).obj N) a) ∧
  (∀ {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (M : proEtaleRingModules T (proEtaleConstantRing T A)),
    (proEtalePullbackStalkComparison A (𝟙 T) x).hom.app M ≫
        eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M)
          (Category.comp_id x)) =
      (finiteCoefficientModuleStalkFunctor x A).map
        ((proEtaleStalkIdentityPullback A T).hom.app M)) ∧
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (M : proEtaleRingModules S (proEtaleConstantRing S A)),
    (proEtalePullbackStalkComparison A t x).hom.app M ≫
        (proEtaleStalkReparam A (x ≫ t) α).hom.app M =
      (proEtaleStalkReparam A x α).hom.app ((proEtaleConstantRingPullback A t).obj M) ≫
        (proEtalePullbackStalkComparison A t
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).hom.app M ≫
        eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M)
          (Category.assoc (Spec.map (CommRingCat.ofHom α.toRingHom)) x t))) ∧
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (H : CochainComplex (proEtaleRingModules S (proEtaleConstantRing S A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A t x).hom.app (DerivedCategory.Q.obj H) ≫
        (finiteCoefficientModuleStalkFunctor (x ≫ t) A).mapDerivedCategoryFactors.hom.app H =
      (proEtaleFiniteCoefficientDerivedStalk A x).map
        ((proEtaleConstantRingPullback A t).mapDerivedCategoryFactors.hom.app H) ≫
        (finiteCoefficientModuleStalkFunctor x A).mapDerivedCategoryFactors.hom.app
          (((proEtaleConstantRingPullback A t).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj H) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (proEtalePullbackStalkComparison A t x)
            (ComplexShape.up ℤ)).hom.app H)) ∧
  (∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ Z)
    (H : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A (h ≫ f) v).hom.app
        (DerivedCategory.Q.obj H) =
      (proEtaleFiniteCoefficientDerivedStalk A v).map
        ((proEtaleConstantRingPullbackComposition h f A).inv.app (DerivedCategory.Q.obj H)) ≫
        (proEtaleDerivedPullbackStalkComparison A h v).hom.app
          ((proEtaleConstantRingDerivedPullback A f).obj (DerivedCategory.Q.obj H)) ≫
        (proEtaleDerivedPullbackStalkComparison A f (v ≫ h)).hom.app
          (DerivedCategory.Q.obj H) ≫
        eqToHom (congrArg
          (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj (DerivedCategory.Q.obj H))
          (Category.assoc v h f))) ∧
  (∀ {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (H : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A (𝟙 T) x).hom.app (DerivedCategory.Q.obj H) ≫
        eqToHom (congrArg
          (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj (DerivedCategory.Q.obj H))
          (Category.comp_id x)) =
      (proEtaleFiniteCoefficientDerivedStalk A x).map
        ((proEtaleStalkDerivedIdentityPullback A T).hom.app (DerivedCategory.Q.obj H))) ∧
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (H : CochainComplex (proEtaleRingModules S (proEtaleConstantRing S A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A t x).hom.app (DerivedCategory.Q.obj H) ≫
        (proEtaleDerivedStalkReparam A (x ≫ t) α).hom.app (DerivedCategory.Q.obj H) =
      (proEtaleDerivedStalkReparam A x α).hom.app
        ((proEtaleConstantRingDerivedPullback A t).obj (DerivedCategory.Q.obj H)) ≫
        (proEtaleDerivedPullbackStalkComparison A t
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).hom.app (DerivedCategory.Q.obj H) ≫
        eqToHom (congrArg
          (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj (DerivedCategory.Q.obj H))
          (Category.assoc (Spec.map (CommRingCat.ofHom α.toRingHom)) x t)))

/-- Coherence of the canonical finite-coefficient pro-etale pullback--stalk comparison.
Source: Stacks Tags 05V1, 0F4F, 0993 and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence).

Proof:
1. Apply `proEtaleInverseImage_abelianStalk` to the underlying abelian sheaf of M.
   Before sheafification, a double-colimit representative `(P,theta,a)` maps to
   `[V,pr_V theta x',a]`; the inverse uses the unit on `T times_S V` with paired
   lift `(x,w)`. `proEtaleGeometricStalk_sheafification` identifies this calculation
   with the actual inverse-image stalk. The two restriction relations are preserved;
   the pointed arrow theta identifies the second composite with the identity.
   The specified constant-section coefficient map transports the action without
   changing the underlying abelian sheaf, so the comparison is A-linear. These are
   exactly the two clauses of `ProEtalePullbackStalkGermNormalized`; they fix c uniquely.
2. A module morphism applies only to the section a, and commutes with restrictions,
   proving naturality. For identity pullback, restriction of its unit along the
   diagonal is the inverse of the canonical identity comparison. The germ formulas
   therefore identify c with the stalk of `proEtaleStalkIdentityPullback`, yielding
   the displayed identity equation, rather than an isomorphism cancellation law.
3. For h followed by f the canonical constant-section comparisons agree with the
   composite, since both preserve every constant section. Reassociate the two fibre
   products by their universal property. Both germ computations then give the same
   projected germ. The normalized module adjunctions and termwise K-flat formula in
   `proEtaleCanonicalPullbackComposition` fix chi to precisely this reassociation.
   `proEtaleConstantRingPullbackComposition` transports chi to the constant-ring
   coefficients; its inverse has the direction chi_(h,f) in the displayed equation.
4. `proEtaleStalkNeighbourhoodReparam` precomposes each lift by Spec(alpha) and leaves
   its section unchanged. It preserves pointed arrows; alpha inverse supplies the
   inverse colimit map. Common refinements prove A-linearity. On every germ the two
   paths r after c and c after r have the same section and projected lift. Colimit
   uniqueness proves the module equation, with the written associativity transport.
5. `proEtale_classical_stalk` gives exactness on underlying abelian sheaves; module
   kernels and cokernels are computed there. Pullback is exact by the recorded
   operations. Thus termwise stalk and pullback preserve quasi-isomorphisms. Apply
   steps 1--4 in every degree; naturality makes them chain maps and equalities of
   chain maps. The localization universal property lifts the comparisons and their
   equalities. Its representative equation is the fifth conjunct; its composition,
   identity and reparametrization equations are the last three conjuncts. The
   comparison chi is the recorded normalized derived comparison, so this passage
   introduces no new compositor or choice of representatives. -/
theorem proEtalePullbackStalkCoherence :
    ∀ (A : Type u) [CommRing A] [Finite A],
      ProEtalePullbackStalkCoherent A := by
  sorry

end AlgebraicGeometry.Scheme

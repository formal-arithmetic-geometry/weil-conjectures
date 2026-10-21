/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.Sites.CoherentToposRepair
public import Sheaf.CategoryTheory.ProfiniteActionParameters
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.TraceFormula.FinitarySiteCoherentGenerators
import Sheaf.CategoryTheory.SheafTensor
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.CategoryTheory.Yoneda

/-! # The coherent profinite action-space presentation

Source: main-20261015, direct-image stability, paragraph (3), the agent-formulated
finite-cover action-space infrastructure
(blueprint: lem-sfb-profinite-action-coherent-presentation).

`AsSmall` implements the size convention without changing spaces or continuous maps.
The presentation below specifies every functor by natural section identifications. No
object or equivalence is selected from the existence theorem. In particular the module
and coefficient identifications are tied to the same restricted Yoneda functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction.CoherentPresentation

/-- The small model of the profinite parameter category.
Source: paragraph (3), size convention
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
abbrev Base := AsSmall.{u + 1} Profinite.{u}

/-- Read the original profinite space from the canonical small-model parameter.
Source: paragraph (3), size convention
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
abbrev parameter (S : Base.{u}) : Profinite.{u} := AsSmall.down.obj S

/-- Finite jointly surjective covering presieves, including the empty cover of the empty space.
Source: paragraph (3), finite-cover site
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def baseCoverage : Precoverage Base.{u} where
  coverings S := {W | W.uncurry.Finite ∧
    ∀ s : (parameter S), ∃ (T : Base.{u}) (f : T ⟶ S), W f ∧ ∃ t : parameter T, f.down t = s}

/-- The finite-surjection covers satisfy the site axioms.
Source: paragraph (3), proof steps 1--3
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: isomorphisms are surjective; pull back a lift of a point to lift each point of
any base change. Lift twice for composition; a finite union of finite families is finite.
The empty family covers precisely the empty object. `AsSmall` changes none of these maps. -/
theorem base_site : baseCoverage.{u}.IsSiteForCoverings := by
  sorry

/-- The continuous-map group presheaf, lifted to the common containing universe.
Source: paragraph (3), the represented internal group
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def groupPresheaf (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J] :
    Base.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj S := GrpCat.of (ULift.{u + 1} C((parameter S.unop), J))
  map f := GrpCat.ofHom
    { toFun := fun g ↦ ULift.up (g.down.comp (ULift.down f.unop).hom.hom)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Continuous maps into a topological group descend along finite profinite covers.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: the finite coproduct of a cover maps onto its compact Hausdorff target by a
quotient map (lem-sfb-compact-hausdorff-surjection-quotient). Matching continuous maps
therefore glue uniquely to a continuous map. Group operations and lifts are pointwise. -/
theorem group_isSheaf (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J] :
    Presheaf.IsSheaf baseCoverage.toGrothendieck
      (groupPresheaf J ⋙ forget GrpCat.{u + 1}) := by
  sorry

/-- Internal actions use precisely the recorded Mathlib internal-module encoding.
Source: paragraph (3), internal group actions
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
abbrev Actions (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J] :=
  InternalActionSite.SetActions baseCoverage (groupPresheaf J) (group_isSheaf J)

variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]

/-- The actual category of continuous actions on profinite spaces, in a small model.
Source: paragraph (3), definition of P_J
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
abbrev Space := AsSmall.{u + 1} (ContAction Profinite.{u} J)

/-- Forgetting a continuous action retains the original underlying profinite space and map.
Source: paragraph (3), underlying-space finite limits
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def underlying : Space J ⥤ Profinite.{u} :=
  AsSmall.down ⋙ forget₂ (ContAction Profinite.{u} J) Profinite.{u}

/-- The finite jointly surjective action-space covers.
Source: paragraph (3), definition of P_J
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def coverage : Precoverage (Space J) where
  coverings S := {W | W.uncurry.Finite ∧
    ∀ s : (underlying J).obj S,
      ∃ (T : Space J) (f : T ⟶ S), W f ∧
        ∃ t : (underlying J).obj T, (underlying J).map f t = s}

/-- Trivial-action parameters, using the definition-node functor.
Source: paragraph (3), t
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def trivialParameter : Base.{u} ⥤ Space J :=
  AsSmall.down ⋙ Profinite.ContinuousActionParameter.trivialAction J ⋙ AsSmall.up

/-- Free parameters J times S, using the definition-node translation functor.
Source: paragraph (3), free evaluation
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def freeParameter : Base.{u} ⥤ Space J :=
  AsSmall.down ⋙ Profinite.ContinuousActionParameter.freeAction J ⋙ AsSmall.up

/-- Finite limits exist in P_J.
Source: paragraph (3), proof step 1
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: use the one-point trivial action, diagonal actions on finite products, and
restricted actions on equalizers. Products are compact by Tychonoff; equalizers are
closed in compact spaces since the target is Hausdorff. Clopen bases give total
disconnectedness. The coordinate universal maps are continuous and equivariant. -/
theorem space_hasFiniteLimits : HasFiniteLimits (Space J) := by
  sorry

attribute [instance] space_hasFiniteLimits

/-- The finite-cover topology is subcanonical, with underlying-space finite limits,
covering pullbacks and finite composition. The trivial parameter functor is left exact
and preserves covers.
Source: paragraph (3), proof steps 1--4 and 14
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: use the limits just constructed. Lift points to prove covering stability.
For subcanonicity glue equivariant maps through the quotient map from the finite
coproduct of a cover; lifting a point proves equivariance of the glued map. Trivial
actions preserve the same terminal objects, products, equalizers and surjections. -/
theorem site_properties :
    PreservesFiniteLimits (underlying J) ∧ (coverage J).IsSiteForCoverings ∧
    (coverage J).toGrothendieck.Subcanonical ∧
    PreservesFiniteLimits (trivialParameter J) ∧
    (∀ (S : Base.{u}) (W : Presieve S), W ∈ baseCoverage S →
      W.map (trivialParameter J) ∈ coverage J ((trivialParameter J).obj S)) := by
  sorry

/-- Ordinary representables are sheaves on the subcanonical action-space site.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: glue continuous equivariant maps through the compact quotient of a finite cover;
uniqueness is pointwise joint surjectivity. This includes the empty cover. -/
theorem representable_isSheaf (T : Space J) :
    Presheaf.IsSheaf (coverage J).toGrothendieck (yoneda.obj T) := by
  sorry

/-- The actual representable sheaf, without an arbitrary choice of sheafification.
Source: paragraph (3), coherent representables
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def representable (T : Space J) : Sheaf (coverage J).toGrothendieck (Type (u + 1)) :=
  ⟨yoneda.obj T, representable_isSheaf J T⟩

/-- Small coproducts in the action-space sheaf topos, at the stated universe.
Source: paragraph (3), proof step 4
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: the site is small in universe u+1. Type-valued sheafification exists there by
Mathlib's small-site sheafification theorem. Sheafify the pointwise presheaf coproduct;
the sheafification adjunction proves its coproduct universal property. -/
theorem sheaves_hasCoproducts : HasCoproducts.{u + 1}
    (Sheaf (coverage J).toGrothendieck (Type (u + 1))) := by
  sorry

attribute [instance] sheaves_hasCoproducts

/-- The representables are coherent and generate the sheaf topos.
Source: paragraph (3), proof step 4
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: apply lem-trf-finitary-site-coherent-generators to the finite-limit site of
steps 1--2. Its sheafified representables are the actual representables by step 3.
The resulting epic coproducts give the stated generating family. -/
theorem coherent_generators :
    CoherentToposRepair.IsCoherentTopos.{u + 1}
      (Sheaf (coverage J).toGrothendieck (Type (u + 1))) ∧
    (∀ T : Space J, IsCoherentObject.{u + 1} (representable J T)) ∧
    (∀ F : Sheaf (coverage J).toGrothendieck (Type (u + 1)),
      ∃ (I : Type (u + 1)) (T : I → Space J) (f : ∀ i, representable J (T i) ⟶ F),
        Epi (Sigma.desc f)) := by
  sorry

/-- Restriction along trivial-action parameters preserves sheaves.
Source: paragraph (3), proof step 14
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: the trivial-action functor preserves covers and their pullback diagrams, so the
matching-family equalizers are those of the original sheaf on the corresponding covers. -/
theorem trivial_restriction_isSheaf
    (F : Sheaf (coverage J).toGrothendieck (Type (u + 1))) :
    Presheaf.IsSheaf baseCoverage.toGrothendieck ((trivialParameter J).op ⋙ F.obj) := by
  sorry

/-- The direct-image formula as an actual precomposition functor.
Source: paragraph (3), p_J direct image
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def trivialRestriction : Sheaf (coverage J).toGrothendieck (Type (u + 1)) ⥤
    Sheaf baseCoverage.toGrothendieck (Type (u + 1)) :=
  InternalActionSite.precomposition _ _ (trivialParameter J) (Type (u + 1))
    (trivial_restriction_isSheaf J)

/-- The lifted parameter site has the same sheaves as the original coherent site.
Source: paragraph (3), size convention and proof steps 2--3
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: finite effective epimorphic families of profinite spaces are exactly finite
jointly surjective families. Transport covers and matching families along `AsSmall.equiv`.
Thus the generated topologies impose identical gluing conditions. -/
theorem base_transport (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) :
    Presheaf.IsSheaf baseCoverage.toGrothendieck (AsSmall.down.op ⋙ F) ↔
      Presheaf.IsSheaf (coherentTopology Profinite.{u}) F := by
  sorry

/-- Finite limits of parameters are unchanged by the small-model equivalence.
Source: paragraph (3), proof step 1
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: transport the existing finite limits of profinite spaces along `AsSmall.equiv`. -/
theorem base_hasFiniteLimits : HasFiniteLimits Base.{u} := by
  sorry

attribute [instance] base_hasFiniteLimits

/-- The represented action spaces and their restricted Yoneda equivalence. All section
identifications are natural; the internal action on each representable is the given
continuous action on its underlying space.
Source: paragraph (3), Phi and proof steps 5--10
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
structure SetPresentation where
  /-- The representable condensed sets with their induced internal actions. -/
  h : Space J ⥤ Actions J
  /-- The underlying presheaf of h_T is exactly the represented presheaf. -/
  hSections (T : Space J) : (h.obj T).X.obj ≅
    yoneda.obj (AsSmall.up.obj ((underlying J).obj T) : Base.{u})
  /-- Maps between represented actions are induced by the original continuous maps. -/
  hMaps {T V : Space J} (f : T ⟶ V) :
    (h.map f).hom.hom ≫ (hSections V).hom =
      (hSections T).hom ≫ yoneda.map (AsSmall.up.map ((underlying J).map f))
  /-- The action on h_T acts pointwise on every continuous parameter map. -/
  hAction (T : Space J) (S : Base.{u}ᵒᵖ)
      (g : (groupPresheaf J).obj S) (x : (h.obj T).X.obj.obj S) (s : (parameter S.unop)) :
    ((hSections T).hom.app S
        (InternalActionSite.setAction _ _ _ (h.obj T) S g x)).down s =
      ((AsSmall.down.obj T).obj.ρ (g.down s)).hom.hom
        (((hSections T).hom.app S x).down s)
  /-- The asserted equivalence of topoi. -/
  equivalence : Actions J ≌ Sheaf (coverage J).toGrothendieck (Type (u + 1))
  /-- Phi is restricted Yoneda, naturally in both actions and action spaces. -/
  phi : equivalence.functor ⋙ sheafToPresheaf _ (Type (u + 1)) ≅
    yoneda ⋙ (Functor.whiskeringLeft _ _ (Type (u + 1))).obj h.op

/-- Evaluate an equivariant represented map at the identity of its underlying space.
Source: paragraph (3), Yoneda and proof step 5
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def evaluate (P : SetPresentation J) (T : Space J) (X : Actions J) (f : P.h.obj T ⟶ X) :
    X.X.obj.obj (op (AsSmall.up.obj ((underlying J).obj T) : Base.{u})) :=
  f.hom.hom.app _ ((P.hSections T).inv.app _ (𝟙 _))

/-- The set-level direct image is restriction to trivial parameters. This states the
adjunction to the recorded trivial inflation, using any normalized realization of that
recorded geometric restriction theorem.
Source: paragraph (3), p_J and proof step 14
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def PresentsDirectImage (P : SetPresentation J) : Prop :=
  ∀ D : InternalActionSite.GeometricRestriction baseCoverage base_site,
    Nonempty ((InternalActionSite.inflation baseCoverage base_site (groupPresheaf J)
      (Type (u + 1)) ⋙ (D.equivalence (groupPresheaf J) (group_isSheaf J)).inverse) ⊣
        (P.equivalence.functor ⋙ trivialRestriction J))

/-- The existing section-ring construction, without restricting to topological coefficients.
Source: paragraph (3), arbitrary commutative condensed rings
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
abbrev coefficient (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :=
  InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) R.X

/-- The underlying coefficient presheaf transports to the parameter site.
Source: paragraph (3), proof step 11
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof: the existing internal/section-module equivalence gives the section-ring sheaf.
Its underlying set presheaf is a sheaf, and `base_transport` transports its gluing. -/
theorem coefficientSets_isSheaf (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :
    Presheaf.IsSheaf baseCoverage.toGrothendieck
      (AsSmall.down.op ⋙ (coefficient R).obj ⋙ forget CommRingCat.{u + 1}) := by
  sorry

/-- The coefficient set sheaf with the actual transported sections.
Source: paragraph (3), trivial coefficient action
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def coefficientSets (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :
    Sheaf baseCoverage.toGrothendieck (Type (u + 1)) :=
  ⟨AsSmall.down.op ⋙ (coefficient R).obj ⋙ forget CommRingCat.{u + 1},
    coefficientSets_isSheaf R⟩

/-- The prescribed trivial internal action on the original coefficient set sheaf.
Source: paragraph (3), R with trivial action
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
def trivialCoefficient (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] : Actions J :=
  Mod.trivialAction
    (Mon.mk (InternalActionSite.groupSheaf baseCoverage (groupPresheaf J) (group_isSheaf J)))
    (coefficientSets R)

-- Avoid generating recursive-size and constructor-injectivity lemmas for categorical data.
set_option genSizeOf false in
set_option genInjectivity false in
/-- The construction data of the module lift of the specified restricted Yoneda functor.
The accompanying `ModuleProperties` fixes their operations, maps and normalizations.
Source: paragraph (3), module equivalence and proof steps 11--15
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
structure ModuleData (P : SetPresentation J) (R : Profinite.CondensedRing.{u})
    [IsCommMonObj R.X] where
  /-- The original module regarded as a set object with its original internal action. -/
  underlyingAction : ActionModule R J ⥤ Actions J
  /-- Its underlying sections and restrictions are precisely those of N. -/
  actionSections (N : ActionModule R J) :
    (underlyingAction.obj N).X.obj ≅
      AsSmall.down.op ⋙ N.module.X.obj ⋙ forget AddCommGrpCat.{u + 1}
  /-- The coefficient ring sheaf on P_J. -/
  ring : Sheaf (coverage J).toGrothendieck CommRingCat.{u + 1}
  /-- Its underlying set sheaf is Phi applied to the trivially acted-on R. -/
  ringPhi : (sheafCompose _ (forget CommRingCat.{u + 1})).obj ring ≅
    P.equivalence.functor.obj (trivialCoefficient J R)
  /-- The exact equivalence of the stated internal-action module category. -/
  equivalence : ActionModule R J ≌ ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ring)
  /-- The module equivalence is induced by the same Phi on underlying set sheaves. -/
  modulePhi : equivalence.functor ⋙ InternalActionSite.moduleSets _
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ring) ≅
    underlyingAction ⋙ P.equivalence.functor
  /-- Evaluating a ring section at the identity is a ring map into the original R(T). -/
  ringSection (T : Space J) : ring.obj.obj (op T) →+*
    (coefficient R).obj.obj (op ((underlying J).obj T))
  /-- Module operations are the original operations, with pointwise scalars through R_J. -/
  moduleSection (N : ActionModule R J) (T : Space J) :
    (equivalence.functor.obj N).val.obj (op T) →ₛₗ[ringSection T]
      sectionModule R N.module ((underlying J).obj T)
  /-- At a trivial parameter the coefficient evaluation is the canonical ring identification. -/
  trivialRing (S : Base.{u}) : ring.obj.obj (op ((trivialParameter J).obj S)) ≃+*
    (coefficient R).obj.obj (op (parameter S))
  /-- The free-parameter coefficient identification is also the actual Phi evaluation.
  It is restriction along s mapped to (1,s). -/
  freeRing (S : Base.{u}) : ring.obj.obj (op ((freeParameter J).obj S)) ≃+*
    (coefficient R).obj.obj (op (parameter S))
  /-- The invariant functor uses the recorded normalized internal-module adjunction. -/
  invariants : Invariants R J
  /-- The tS identification takes values in those actual invariant section modules. -/
  fixedSections (N : ActionModule R J) (S : Base.{u}) :
    (equivalence.functor.obj N).val.obj (op ((trivialParameter J).obj S)) ≃
      sectionModule R (invariants.functor.obj N) (parameter S)
  /-- Free module evaluation is restriction along s mapped to (1,s). -/
  freeSection (N : ActionModule R J) (S : Base.{u}) :
    (equivalence.functor.obj N).val.obj (op ((freeParameter J).obj S)) →
      sectionModule R N.module (parameter S)

/-- The complete equations and exactness requirements of the pointwise module lift.
These constrain every datum to be the same Phi, with the original pointwise operations.
Source: paragraph (3), module equivalence and proof steps 11--15
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
structure ModuleProperties (P : SetPresentation J) (R : Profinite.CondensedRing.{u})
    [IsCommMonObj R.X] (D : ModuleData J P R) : Prop where
  /-- Its maps are the original component maps. -/
  actionMaps {M N : ActionModule R J} (f : M ⟶ N) (S : Base.{u}ᵒᵖ)
      (x : (D.underlyingAction.obj M).X.obj.obj S) :
    (D.actionSections N).hom.app S ((D.underlyingAction.map f).hom.hom.app S x) =
      (f.val.hom.hom.app (op (parameter S.unop))).hom ((D.actionSections M).hom.app S x)
  /-- Its action is exactly the given sectionwise linear action. -/
  actionAct (N : ActionModule R J) (S : Base.{u}ᵒᵖ)
      (g : (groupPresheaf J).obj S) (x : (D.underlyingAction.obj N).X.obj.obj S) :
    (D.actionSections N).hom.app S
        (InternalActionSite.setAction _ _ _ (D.underlyingAction.obj N) S g x) =
      N.act (parameter S.unop) g.down ((D.actionSections N).hom.app S x)
  /-- The module functor preserves sums of equivariant maps. -/
  additive : D.equivalence.functor.Additive
  /-- Exactness, in the kernel sense. -/
  limits : PreservesFiniteLimits D.equivalence.functor
  /-- Exactness, in the cokernel sense. -/
  colimits : PreservesFiniteColimits D.equivalence.functor
  /-- The ring map is the actual represented-map evaluation under Phi. -/
  ringSection_eq (T : Space J) (r : D.ring.obj.obj (op T)) :
    D.ringSection T r = evaluate J P T (trivialCoefficient J R)
      (((P.phi.hom.app (trivialCoefficient J R)).app (op T))
        ((D.ringPhi.hom.hom.app (op T)) r))
  /-- This semilinear map is precisely represented-map evaluation of the same Phi. -/
  moduleSection_eq (N : ActionModule R J) (T : Space J)
      (x : (D.equivalence.functor.obj N).val.obj (op T)) :
    D.moduleSection N T x = (D.actionSections N).hom.app _
      (evaluate J P T (D.underlyingAction.obj N)
        (((P.phi.hom.app (D.underlyingAction.obj N)).app (op T))
          (((D.modulePhi.hom.app N).hom.app (op T)) x)))
  /-- The identification is the same normalized coefficient evaluation. -/
  trivialRing_eq (S : Base.{u}) (r : D.ring.obj.obj (op ((trivialParameter J).obj S))) :
    D.trivialRing S r = D.ringSection ((trivialParameter J).obj S) r
  /-- Free coefficient evaluation restricts at the group identity. -/
  freeRing_eq (S : Base.{u}) (r : D.ring.obj.obj (op ((freeParameter J).obj S))) :
    D.freeRing S r = (coefficient R).obj.map
      (CompHausLike.ofHom _ ⟨fun s : (parameter S) ↦ ((1 : J), s), continuous_const.prodMk
        continuous_id⟩ : (parameter S) ⟶ Profinite.of (J × (parameter S))).op
      (D.ringSection ((freeParameter J).obj S) r)
  /-- Fixed sections include every profinite base change, using the recorded predicate. -/
  trivialInjective (N : ActionModule R J) (S : Base.{u}) :
    Function.Injective (D.moduleSection N ((trivialParameter J).obj S))
  /-- Composing with the invariant inclusion is the normalized represented evaluation. -/
  fixedSections_eq (N : ActionModule R J) (S : Base.{u})
      (x : (D.equivalence.functor.obj N).val.obj (op ((trivialParameter J).obj S))) :
    ((D.invariants.inclusion.app N).hom.hom.app (op (parameter S))).hom
        (D.fixedSections N S x) = D.moduleSection N ((trivialParameter J).obj S) x
  /-- Evaluation at tS has exactly the fully fixed image. -/
  trivialImage (N : ActionModule R J) (S : Base.{u}) (x : sectionModule R N.module (parameter S)) :
    (∃ y, D.moduleSection N ((trivialParameter J).obj S) y = x) ↔ FixedAll N (parameter S) x
  /-- It uses the original restriction of N after represented evaluation. -/
  freeSection_eq (N : ActionModule R J) (S : Base.{u})
      (x : (D.equivalence.functor.obj N).val.obj (op ((freeParameter J).obj S))) :
    D.freeSection N S x = (N.module.X.obj.map
      (CompHausLike.ofHom _ ⟨fun s : (parameter S) ↦ ((1 : J), s), continuous_const.prodMk
        continuous_id⟩ : (parameter S) ⟶ Profinite.of (J × (parameter S))).op).hom
      (D.moduleSection N ((freeParameter J).obj S) x)
  /-- Free evaluation is a bijection, including for the empty parameter. -/
  freeBijective (N : ActionModule R J) (S : Base.{u}) : Function.Bijective (D.freeSection N S)
  /-- The free identification respects addition. -/
  freeAdd (N : ActionModule R J) (S : Base.{u})
      (x y : (D.equivalence.functor.obj N).val.obj (op ((freeParameter J).obj S))) :
    D.freeSection N S (x + y) = D.freeSection N S x + D.freeSection N S y
  /-- Its scalar identification is the one already fixed on the coefficient ring. -/
  freeScalar (N : ActionModule R J) (S : Base.{u})
      (r : D.ring.obj.obj (op ((freeParameter J).obj S)))
      (x : (D.equivalence.functor.obj N).val.obj (op ((freeParameter J).obj S))) :
    D.freeSection N S (r • x) = D.freeRing S r • D.freeSection N S x
  /-- On maps at tS, evaluation restricts the original component to fixed sections. -/
  trivialMaps {M N : ActionModule R J} (f : M ⟶ N) (S : Base.{u})
      (x : (D.equivalence.functor.obj M).val.obj (op ((trivialParameter J).obj S))) :
    D.moduleSection N ((trivialParameter J).obj S)
        ((D.equivalence.functor.map f).val.app _ x) =
      (f.val.hom.hom.app (op (parameter S))).hom
        (D.moduleSection M ((trivialParameter J).obj S) x)
  /-- On free parameters the map is the original component at S. -/
  freeMaps {M N : ActionModule R J} (f : M ⟶ N) (S : Base.{u})
      (x : (D.equivalence.functor.obj M).val.obj (op ((freeParameter J).obj S))) :
    D.freeSection N S ((D.equivalence.functor.map f).val.app _ x) =
      (f.val.hom.hom.app (op (parameter S))).hom (D.freeSection M S x)
  /-- Naturality of trivial evaluation in continuous profinite parameters. -/
  trivialRestriction (N : ActionModule R J) {S V : Base.{u}} (f : S ⟶ V)
      (x : (D.equivalence.functor.obj N).val.obj (op ((trivialParameter J).obj V))) :
    D.moduleSection N ((trivialParameter J).obj S)
        ((D.equivalence.functor.obj N).val.map ((trivialParameter J).map f).op x) =
      (N.module.X.obj.map f.down.op).hom
        (D.moduleSection N ((trivialParameter J).obj V) x)
  /-- Naturality of free evaluation in continuous profinite parameters. -/
  freeRestriction (N : ActionModule R J) {S V : Base.{u}} (f : S ⟶ V)
      (x : (D.equivalence.functor.obj N).val.obj (op ((freeParameter J).obj V))) :
    D.freeSection N S
        ((D.equivalence.functor.obj N).val.map ((freeParameter J).map f).op x) =
      (N.module.X.obj.map f.down.op).hom (D.freeSection N V x)

/-- Pointwise module presentation, with its construction data and all their equations.
Separating the data and equations avoids generating large irrelevant structural lemmas;
no data are selected from the theorem asserting existence of this specification.
Source: paragraph (3), module equivalence and proof steps 11--15
(blueprint: lem-sfb-profinite-action-coherent-presentation). -/
structure ModulePresentation (P : SetPresentation J) (R : Profinite.CondensedRing.{u})
    [IsCommMonObj R.X] where
  /-- The functors, coefficient ring and normalized evaluation maps. -/
  data : ModuleData J P R
  /-- Every action, linearity, exactness and naturality equation in the statement. -/
  properties : ModuleProperties J P R data

/-- The full coherent presentation, its exact module lift and its normalized direct image.
Source: paragraph (3), agent-formulated finite-cover action-space infrastructure
(blueprint: lem-sfb-profinite-action-coherent-presentation).
Proof:
1. Construct finite limits on underlying profinite spaces, with the induced actions;
   use Tychonoff, closed equalizers and the clopen basis for profiniteness.
2. Pull back point lifts and compose lifts to verify the finite-cover site axioms.
3. Finite coproduct covers are compact Hausdorff quotient maps. Descend continuous maps
   and check equivariance on lifts, proving subcanonicity.
4. Apply lem-trf-finitary-site-coherent-generators for coherence and generation.
5. Yoneda identifies equivariant maps h_T to X with sections satisfying the universal
   action equation on J times T; glue it using the cover J times T_i.
6. Free evaluation restricts at (1,s); its inverse sends (a,b) to a acting on b-star x.
7. Define G(F)(S)=F(J times S). Free parameters preserve covering fibre products, so G(F)
   is a sheaf on the original parameter site.
8. Right translations r_g(j,s)=(j g(s),s) give the internal action by F(r_g).
   Contravariance and r_h after r_g=r_(gh) give the left-action law and naturality.
9. The action map J times T to T is a cover. Its fibre square has coordinates (j,k,t),
   with projections (j,kt) and (jk,t). Its sheaf equalizer is exactly the equation of 5.
10. The descent bijections of 9 and free evaluation of 6 give natural quasi-inverses.
11. Use the recorded internal/section-module equivalence and the monoidal abelian
    sheafification of sk-def-sfb-sheaf-tensor. Equivariant sections are closed under
    addition and pointwise multiplication by equivariant coefficient sections.
12. Recover a module from its sections at J times S; right translation acts trivially
    on the coefficient ring there. The two inverse maps are linear over the original R.
13. The two functors preserve sums. Equivalences preserve kernels and cokernels by
    transporting their universal properties, so this module equivalence is exact.
14. Trivial parameters preserve covers and finite limits. The adjunction to trivial
    inflation identifies p_*X(S) with equivariant maps h_(tS) to X.
15. These maps are exactly sections fixed after every profinite base change. On tS,
    a module map restricts its original component to fixed sections; free evaluation
    gives its original component at S. All maps commute with parameter restriction.
-/
theorem profiniteAction_coherentPresentation :
    ∃ P : SetPresentation J, PresentsDirectImage J P ∧
      ∀ (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X],
        Nonempty (ModulePresentation J P R) := by
  sorry

end Profinite.CondensedAction.CoherentPresentation

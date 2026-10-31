/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormContinuousMonodromyData
public import WeilConjectures.CategoryTheory.CondensedEquivariantBarData
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Continuous representations as internal condensed modules

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
continuous-representation coefficients (blueprint: def-sfb-continuous-representation-condensation).

A realization is specified on every profinite test object, including scalar action,
restriction and generalized group action. Its section identifications prevent replacing
continuous functions by locally constant functions. No realization is chosen from an
uncharacterized existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction.ContinuousRepresentation

open AlgebraicGeometry.ProEtale

variable (F : Type u) [NormedField F]

variable (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  (V : Type (u + 1)) [AddCommGroup V] [Module F V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul F V]
  (ρ : Representation F P V)

/-- The continuous-section realization of a representation. Every structure map is
specified on sections; the additive equivalences identify the actual continuous maps.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
structure Realization where
  /-- The internal module equipped with its condensed-group action. -/
  object : ActionModule (normContinuousRing F) P
  /-- Its additive sections are precisely all continuous maps into V. -/
  sections (S : Profinite.{u}) : sectionModule (normContinuousRing F) object.module S ≃+
    ULift.{u + 1} C(S, V)
  /-- Pointwise scalar multiplication, over the original continuous-map coefficient ring. -/
  scalar (S : Profinite.{u})
      (r : (InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj (op S))
      (m : sectionModule (normContinuousRing F) object.module S) (s : S) :
    (sections S (r • m)).down s = r.down s • (sections S m).down s
  /-- Restriction is precomposition. -/
  restriction (S T : Profinite.{u}) (f : T ⟶ S)
      (m : sectionModule (normContinuousRing F) object.module S) (t : T) :
    (sections T ((object.module.X.obj.map f.op).hom m)).down t =
      (sections S m).down (f t)
  /-- The group action is the given joint continuous action, pointwise. -/
  action (S : Profinite.{u}) (g : C(S, P))
      (m : sectionModule (normContinuousRing F) object.module S) (s : S) :
    (sections S (object.act S g m)).down s = ρ (g s) ((sections S m).down s)

-- The sheafification counit recovers the original pointwise section multiplication.
private def pointwiseRingHom (S : Profinite.{u}) :
    (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj (op S) →+*
        ULift.{u + 1} C(S, F) := by
  let J := coherentTopology Profinite.{u}
  let A := continuousMapRingObjOfUniverse.{u, u} F
  let : MonObj A := continuousMapRingObjOfUniverseMonObj.{u, u} F
  have hmon : (sheafToPresheaf J AddCommGrpCat.{u + 1}).monObjObj A =
      (continuousMapRingPresheafOfUniverse.{u, u} F).monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := (continuousMapRingPresheafOfUniverse.{u, u} F).monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  let e : (InternalAbelianSheafModule.sectionRings J (normContinuousRing F).X).obj
      (op S) ≃+* ULift.{u + 1} C(S, F) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_mul' := by
        intro a b
        change (((sheafToPresheaf J AddCommGrpCat.{u + 1}).monObjObj A).mul.app
          (op S)).hom (a ⊗ₜ[ℤ] b) =
            (show ULift.{u + 1} C(S, F) from a) * (show ULift.{u + 1} C(S, F) from b)
        have hm := congrArg (fun m : MonObj A.obj ↦ m.mul) hmon
        rw [hm]
        rfl }
  exact e.toRingHom

/-- Every joint continuous linear action has its continuous-section realization.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: form the presheaf with section modules ULift C(S,V), pointwise C(S,F)-action,
and precomposition restrictions. A finite coproduct of profinite sets turns sections
into a finite product; a surjection is a quotient map and continuous maps descend
uniquely along it. Thus this is a module sheaf. Apply the inverse of
`InternalAbelianSheafModule.sectionModuleEquivalence` to obtain the internal module.
Its counit gives the section identifications, intertwining scalars and restrictions.
Joint continuity makes s mapping to rho(g(s))(v(s)) continuous. Transport these
linear actions through the counit. The representation laws give the monoid homomorphism
and naturality under every base change, including the empty profinite set. -/
theorem exists_realization
    (_hρ : Continuous (fun x : P × V ↦ ρ x.1 x.2)) :
    Nonempty (Realization F P V ρ) := by
  let A := InternalAbelianSheafModule.sectionRings
    (coherentTopology Profinite.{u}) (normContinuousRing F).X
  let (S : Profinite.{u}ᵒᵖ) : Module (A.obj S) (ULift.{u + 1} C(S.unop, V)) :=
    Module.compHom _ (pointwiseRingHom F S.unop)
  let N₀ : PresheafOfModules.{u + 1} (A ⋙ forget₂ CommRingCat RingCat) :=
    { obj := fun S ↦ ModuleCat.of (A.obj S) (ULift.{u + 1} C(S.unop, V))
      map := fun {S T} a ↦ ModuleCat.ofHom
        (X := ModuleCat.of (A.obj S) (ULift.{u + 1} C(S.unop, V)))
        (Y := (ModuleCat.restrictScalars ((A ⋙ forget₂ CommRingCat RingCat).map a).hom).obj
          (ModuleCat.of (A.obj T) (ULift.{u + 1} C(T.unop, V))))
        { toFun := fun x ↦ ULift.up (x.down.comp a.unop.hom.hom)
          map_add' := by intro x y; rfl
          map_smul' := by intro r x; rfl }
      map_id := by intro S; rfl
      map_comp := by intros; rfl }
  have hs : Presheaf.IsSheaf (coherentTopology Profinite.{u}) N₀.presheaf := by
    let e : N₀.presheaf ⋙ forget AddCommGrpCat.{u + 1} ≅
        ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} V ⋙
          uliftFunctor.{u + 1} :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u + 1})
    rw [Presheaf.isSheaf_of_iso_iff e,
      isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
      ← isSheaf_iff_isSheaf_of_type]
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    refine ⟨inferInstance, ?_⟩
    apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} V
    intro Z B π hπ
    exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 0 2).mp hπ)
      π.hom.hom.continuous
  let N : SheafOfModules.{u + 1}
      ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat RingCat)).obj
        (InternalAbelianSheafModule.sectionRingSheaf
          (coherentTopology Profinite.{u}) (normContinuousRing F).X)) := ⟨N₀, hs⟩
  let M := InternalAbelianSheafModule.liftedSheafModule
    (coherentTopology Profinite.{u}) (normContinuousRing F).X N
  let ε := InternalAbelianSheafModule.sectionModuleFunctor_counit
    (coherentTopology Profinite.{u}) (normContinuousRing F).X N
  let e (S : Profinite.{u}) : sectionModule (normContinuousRing F) M S ≃ₗ[A.obj (op S)]
      ULift.{u + 1} C(S, V) :=
    ((SheafOfModules.evaluation _ (op S)).mapIso ε).toLinearEquiv
  have restr (S T : Profinite.{u}) (a : T ⟶ S)
      (m : sectionModule (normContinuousRing F) M S) (t : T) :
      (e T ((M.X.obj.map a.op).hom m)).down t = (e S m).down (a t) := by
    have h := PresheafOfModules.naturality_apply ε.hom.val a.op m
    exact congrArg (fun x : ULift.{u + 1} C(T, V) ↦ x.down t) h
  let act (S : Profinite.{u}) : C(S, P) →*
      Module.End (A.obj (op S)) (ULift.{u + 1} C(S, V)) :=
    { toFun := fun g ↦
        { toFun := fun m ↦ ULift.up
            ⟨fun s ↦ ρ (g s) (m.down s), _hρ.comp (g.continuous.prodMk m.down.continuous)⟩
          map_add' := by intro x y; ext s; exact (ρ (g s)).map_add _ _
          map_smul' := by intro r x; ext s; exact (ρ (g s)).map_smul _ _ }
      map_one' := by ext m s; exact congrArg (fun f ↦ f (m.down s)) ρ.map_one
      map_mul' := by
        intro g h
        ext m s
        exact congrArg (fun f ↦ f (m.down s)) (ρ.map_mul (g s) (h s)) }
  let transported (S : Profinite.{u}) : C(S, P) →*
      Module.End (A.obj (op S)) (sectionModule (normContinuousRing F) M S) :=
    { toFun := fun g ↦ (e S).symm.toLinearMap.comp ((act S g).comp (e S).toLinearMap)
      map_one' := by ext m; simp
      map_mul' := by intro g h; ext m; simp [map_mul, Module.End.mul_apply] }
  have action_formula (S : Profinite.{u}) (g : C(S, P))
      (m : sectionModule (normContinuousRing F) M S) (s : S) :
      (e S (transported S g m)).down s = ρ (g s) ((e S m).down s) := by
    change (e S ((e S).symm (act S g (e S m)))).down s = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨{ object := { module := M, act := transported, naturality := ?_ }
            sections := fun S ↦ (e S).toAddEquiv
            scalar := ?_
            restriction := restr
            action := action_formula }⟩
  · intro S T a g m
    apply (e T).injective
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    rw [restr, action_formula, action_formula, restr]
    rfl
  · intro S r m t
    exact congrArg (fun x : ULift.{u + 1} C(S, V) ↦ x.down t) ((e S).map_smul r m)

variable {F P V ρ}

/-- A map between continuous realizations is characterized by its actual section formula.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def RepresentsMap {W : Type (u + 1)} [AddCommGroup W] [Module F W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul F W] {σ : Representation F P W}
    (M : Realization F P V ρ) (N : Realization F P W σ)
    (f : V →ₗ[F] W) (g : M.object ⟶ N.object) : Prop :=
  ∀ (S : Profinite.{u}) (m : sectionModule (normContinuousRing F) M.object.module S) (s : S),
    (N.sections S ((g.val.hom.hom.app (op S)).hom m)).down s =
      f ((M.sections S m).down s)

set_option linter.unusedSectionVars false in
/-- Continuous equivariant linear maps induce unique morphisms of realizations.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: postcomposition by f is continuous and sectionwise C(S,F)-linear. It commutes
with restriction and, by equivariance, with generalized group elements. Transport it
through the two section identifications and the fully faithful internal-module
section functor. Uniqueness follows by evaluating on every section of every test
object. Consequently identities, compositions and additions are preserved. -/
theorem exists_unique_map {W : Type (u + 1)} [AddCommGroup W] [Module F W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul F W]
    {σ : Representation F P W} (M : Realization F P V ρ) (N : Realization F P W σ)
    (f : V →ₗ[F] W) (_hf : Continuous f)
    (_heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    ∃! g : M.object ⟶ N.object, RepresentsMap M N f g := by
  let post (S : Profinite.{u}) :
      sectionModule (normContinuousRing F) M.object.module S →+
        sectionModule (normContinuousRing F) N.object.module S :=
    (N.sections S).symm.toAddMonoidHom.comp
      (({ toFun := fun x ↦ ULift.up ((⟨f, _hf⟩ : C(V, W)).comp x.down)
          map_zero' := by ext t; exact f.map_zero
          map_add' := by intro x y; ext t; exact f.map_add _ _ } :
          ULift.{u + 1} C(S, V) →+ ULift.{u + 1} C(S, W)).comp
        (M.sections S).toAddMonoidHom)
  have formula (S : Profinite.{u}) (m : sectionModule (normContinuousRing F)
      M.object.module S) (t : S) :
      (N.sections S (post S m)).down t = f ((M.sections S m).down t) := by
    change (N.sections S ((N.sections S).symm
      (ULift.up ((⟨f, _hf⟩ : C(V, W)).comp (M.sections S m).down)))).down t = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  have section_ext (S : Profinite.{u}) {x y : sectionModule (normContinuousRing F)
      N.object.module S} (h : ∀ t : S, (N.sections S x).down t =
        (N.sections S y).down t) : x = y :=
    (N.sections S).injective (ULift.ext _ _ (ContinuousMap.ext h))
  let q : (InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj M.object.module ⟶
      (InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj N.object.module :=
    ⟨{ app := fun S ↦ ModuleCat.ofHom
        (X := sectionModule (normContinuousRing F) M.object.module S.unop)
        (Y := sectionModule (normContinuousRing F) N.object.module S.unop)
        ({ (post S.unop) with
          map_smul' := by
            intro r m
            apply section_ext
            intro t
            change (N.sections S.unop (post S.unop (r • m))).down t =
              (N.sections S.unop (r • post S.unop m)).down t
            exact (formula _ _ _).trans
              ((congrArg f (M.scalar S.unop r m t)).trans
                ((f.map_smul _ _).trans
                  ((congrArg (fun z ↦ r.down t • z) (formula S.unop m t).symm).trans
                    (N.scalar S.unop r (post S.unop m) t).symm))) } :
          sectionModule (normContinuousRing F) M.object.module S.unop →ₗ[
            (InternalAbelianSheafModule.sectionRings
              (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj S]
            sectionModule (normContinuousRing F) N.object.module S.unop)
       naturality := by
         intro S T a
         ext m
         apply section_ext
         intro t
         change (N.sections T.unop (post T.unop
           ((M.object.module.X.obj.map a).hom m))).down t =
             (N.sections T.unop
               ((N.object.module.X.obj.map a).hom (post S.unop m))).down t
         exact (formula _ _ _).trans
           ((congrArg f (M.restriction S.unop T.unop a.unop m t)).trans
             ((formula S.unop m (a.unop t)).symm.trans
               (N.restriction S.unop T.unop a.unop (post S.unop m) t).symm)) }⟩
  let g := (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
    (coherentTopology Profinite.{u}) (normContinuousRing F).X).preimage q
  have hg (S : Profinite.{u}) (m : sectionModule (normContinuousRing F)
      M.object.module S) : (g.hom.hom.app (op S)).hom m = post S m := by
    have h := (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
      (coherentTopology Profinite.{u}) (normContinuousRing F).X).map_preimage q
    exact congrArg (fun k ↦ (k.val.app (op S)).hom m) h
  have geq : Equivariant M.object N.object g := by
    intro S p m
    apply section_ext
    intro t
    rw [hg, formula, N.action, hg, formula, M.action]
    exact _heq (p t) _
  refine ⟨⟨g, geq⟩, ?_, ?_⟩
  · intro S m t
    rw [hg, formula]
  · intro h hh
    apply Subtype.ext
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    ext m
    apply section_ext S.unop
    intro t
    exact (hh S.unop m t).trans (by rw [hg, formula])

/-- The morphism determined uniquely by postcomposition on every continuous section.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def map {W : Type (u + 1)} [AddCommGroup W] [Module F W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul F W] {σ : Representation F P W}
    (M : Realization F P V ρ) (N : Realization F P W σ) (f : V →ₗ[F] W)
    (hf : Continuous f) (heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    M.object ⟶ N.object :=
  Classical.choose (exists_unique_map M N f hf heq).exists

/-- Restriction keeps the realization and its sections and precomposes the group action.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def Realization.inflate {Q : Type u} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] {σ : Representation F Q V}
    (M : Realization F Q V σ) (π : P →ₜ* Q) :
    Realization F P V (σ.comp π.toMonoidHom) where
  object := (CondensedAction.inflate (R := normContinuousRing F) π).obj M.object
  sections := M.sections
  scalar := M.scalar
  restriction := M.restriction
  action S g m s := M.action S (π.toContinuousMap.comp g) m s

section ScalarMaps
variable (F)

/-- Bundle the existing norm-continuous ring with its existing commutativity proof.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def coefficientRing : CategoryTheory.CondensedBar.Ring.{u} :=
  { X := (normContinuousRing F).X }

variable {K : Type u} [NormedField K] (φ : F →+* K) (hφ : Continuous φ)

/-- The recorded continuous-map ring morphism, with commutativity bundled.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def coefficientRingMap : coefficientRing F ⟶ coefficientRing K :=
  CommMon.homMk {
    hom := continuousMapRingObjMapOfUniverse φ hφ
    isMonHom_hom := isMonHom_continuousMapRingObjMapOfUniverse φ hφ }

variable {F}

/-- Scalar-changing maps have the specified pointwise section formula after the
normalized underlying scalar-restriction identification.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def RepresentsScalarMap {W : Type (u + 1)} [AddCommGroup W] [Module K W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul K W]
    {σ : Representation K P W} (M : Realization F P V ρ) (N : Realization K P W σ)
    (s : CategoryTheory.CondensedBar.ScalarAction (coefficientRingMap F φ hφ) P)
    (f : V →+ W) (g : M.object ⟶ s.functor.obj N.object) : Prop :=
  ∀ (S : Profinite.{u}) (m : sectionModule (normContinuousRing F) M.object.module S)
      (t : S),
    (N.sections S (((g.val ≫ s.underlying.hom.app N.object).hom.hom.app (op S)).hom m)).down t =
      f ((M.sections S m).down t)

set_option linter.unusedSectionVars false in
/-- Continuous semilinear equivariant maps induce uniquely characterized scalar-changing
maps of continuous realizations.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: postcompose continuous sections by f. The scalar equation makes this linear
for the section ring map given by postcomposition with phi. Transport through the
section equivalences and the normalized underlying scalar-action comparison. The
ScalarAction.action equation and equivariance give an action morphism. Restriction
naturality is pointwise precomposition. The section functor is fully faithful, so
this constructs a unique morphism, including on the empty test object. -/
theorem exists_unique_scalarMap {W : Type (u + 1)} [AddCommGroup W] [Module K W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul K W]
    {σ : Representation K P W} (M : Realization F P V ρ) (N : Realization K P W σ)
    (s : CategoryTheory.CondensedBar.ScalarAction (coefficientRingMap F φ hφ) P)
    (f : V →+ W) (_hf : Continuous f)
    (_hscalar : ∀ (a : F) (v : V), f (a • v) = φ a • f v)
    (_heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    ∃! g : M.object ⟶ s.functor.obj N.object, RepresentsScalarMap φ hφ M N s f g := by
  let a : (normContinuousRing F).X ⟶ (normContinuousRing K).X :=
    (coefficientRingMap F φ hφ).hom.hom
  let T : Modules (normContinuousRing F) := (Mod.comap a).obj N.object.module
  let post (S : Profinite.{u}) : sectionModule (normContinuousRing F) M.object.module S →+
      sectionModule (normContinuousRing F) T S :=
    (N.sections S).symm.toAddMonoidHom.comp
      (({ toFun := fun x ↦ ULift.up ((⟨f, _hf⟩ : C(V, W)).comp x.down)
          map_zero' := by ext t; exact f.map_zero
          map_add' := by intro x y; ext t; exact f.map_add _ _ } :
          ULift.{u + 1} C(S, V) →+ ULift.{u + 1} C(S, W)).comp
        (M.sections S).toAddMonoidHom)
  have formula (S : Profinite.{u}) (m : sectionModule (normContinuousRing F)
      M.object.module S) (t : S) :
      (N.sections S (post S m)).down t = f ((M.sections S m).down t) := by
    change (N.sections S ((N.sections S).symm
      (ULift.up ((⟨f, _hf⟩ : C(V, W)).comp (M.sections S m).down)))).down t = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  have section_ext (S : Profinite.{u}) {x y : sectionModule (normContinuousRing K)
      N.object.module S} (h : ∀ t : S, (N.sections S x).down t =
        (N.sections S y).down t) : x = y :=
    (N.sections S).injective (ULift.ext _ _ (ContinuousMap.ext h))
  have scalar_restrict (S : Profinite.{u})
      (r : (InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj (op S))
      (m : sectionModule (normContinuousRing F) T S) :
      (r • m : sectionModule (normContinuousRing F) T S) =
        @SMul.smul
          ((InternalAbelianSheafModule.sectionRings
            (coherentTopology Profinite.{u}) (normContinuousRing K).X).obj (op S))
          (sectionModule (normContinuousRing K) N.object.module S) _
          ((a.hom.app (op S)).hom r) m := by
    have hμ := congr_app (Functor.LaxMonoidal.μ_natural_left
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
      a N.object.module.X) (op S)
    exact (ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f ≫ (Mod.act N.object.module.X).hom.app (op S)) hμ)
        (r ⊗ₜ[ℤ] m)).symm
  let q : (InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj M.object.module ⟶
      (InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj T :=
    ⟨{ app := fun S ↦ ModuleCat.ofHom
        (X := sectionModule (normContinuousRing F) M.object.module S.unop)
        (Y := sectionModule (normContinuousRing F) T S.unop)
        { (post S.unop) with
          map_smul' := by
            intro r m
            apply section_ext
            intro t
            change (N.sections S.unop (post S.unop (r • m))).down t =
              (N.sections S.unop (r • post S.unop m :
                sectionModule (normContinuousRing F) T S.unop)).down t
            exact (formula _ _ _).trans
              ((congrArg f (M.scalar S.unop r m t)).trans
                ((_hscalar _ _).trans
                  ((congrArg (fun z ↦ φ (r.down t) • z)
                    (formula S.unop m t).symm).trans
                    ((N.scalar S.unop ((a.hom.app S).hom r) (post S.unop m) t).symm.trans
                      (congrArg (fun z ↦ (N.sections S.unop z).down t)
                        (scalar_restrict S.unop r (post S.unop m)).symm))))) }
       naturality := by
         intro S S' b
         ext m
         apply section_ext
         intro t
         change (N.sections S'.unop (post S'.unop
           ((M.object.module.X.obj.map b).hom m))).down t =
             (N.sections S'.unop
               ((N.object.module.X.obj.map b).hom (post S.unop m))).down t
         exact (formula _ _ _).trans
           ((congrArg f (M.restriction S.unop S'.unop b.unop m t)).trans
             ((formula S.unop m (b.unop t)).symm.trans
               (N.restriction S.unop S'.unop b.unop (post S.unop m) t).symm)) }⟩
  let g₀ := (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
    (coherentTopology Profinite.{u}) (normContinuousRing F).X).preimage q
  have hg₀ (S : Profinite.{u}) (m : sectionModule (normContinuousRing F)
      M.object.module S) : (g₀.hom.hom.app (op S)).hom m = post S m := by
    have h := (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
      (coherentTopology Profinite.{u}) (normContinuousRing F).X).map_preimage q
    exact congrArg (fun k ↦ (k.val.app (op S)).hom m) h
  let u := s.underlying.app N.object
  let g : M.object.module ⟶ (s.functor.obj N.object).module := g₀ ≫ u.inv
  have hgu : g ≫ u.hom = g₀ := by simp [g]
  have hg (S : Profinite.{u}) (m : sectionModule (normContinuousRing F)
      M.object.module S) :
      (u.hom.hom.hom.app (op S)).hom ((g.hom.hom.app (op S)).hom m) = post S m := by
    exact (congrArg (fun k ↦ (k.hom.hom.app (op S)).hom m) hgu).trans (hg₀ S m)
  have huinj (S : Profinite.{u}) :
      Function.Injective (u.hom.hom.hom.app (op S)).hom := by
    intro x y h
    have h' := congrArg (fun z ↦ (u.inv.hom.hom.app (op S)).hom z) h
    have hx := congrArg (fun k ↦ (k.hom.hom.app (op S)).hom x) u.hom_inv_id
    have hy := congrArg (fun k ↦ (k.hom.hom.app (op S)).hom y) u.hom_inv_id
    exact hx.symm.trans (h'.trans hy)
  have geq : Equivariant M.object (s.functor.obj N.object) g := by
    intro S p m
    apply huinj S
    apply section_ext
    intro t
    rw [hg, formula]
    have ha := s.action N.object S p ((g.hom.hom.app (op S)).hom m)
    change (u.hom.hom.hom.app (op S)).hom
      ((s.functor.obj N.object).act S p ((g.hom.hom.app (op S)).hom m)) =
        N.object.act S p
          ((u.hom.hom.hom.app (op S)).hom ((g.hom.hom.app (op S)).hom m)) at ha
    exact (congrArg f (M.action S p m t)).trans
      ((_heq (p t) _).trans
        ((congrArg (fun z ↦ σ (p t) z)
          ((formula S m t).symm.trans
            (congrArg (fun z ↦ (N.sections S z).down t) (hg S m).symm))).trans
          ((N.action S p _ t).symm.trans
            (congrArg (fun z ↦ (N.sections S z).down t) ha.symm))))
  refine ⟨⟨g, geq⟩, ?_, ?_⟩
  · intro S m t
    change (N.sections S ((u.hom.hom.hom.app (op S)).hom
      ((g.hom.hom.app (op S)).hom m))).down t = _
    rw [hg, formula]
  · intro h hh
    apply Subtype.ext
    apply (cancel_mono u.hom).1
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    ext m
    apply section_ext S.unop
    intro t
    exact (hh S.unop m t).trans (by change _ =
      (N.sections S.unop ((u.hom.hom.hom.app (op S.unop)).hom
        ((g.hom.hom.app (op S.unop)).hom m))).down t; rw [hg, formula])

/-- The unique scalar-changing morphism with its prescribed continuous section formula.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def scalarMap {W : Type (u + 1)} [AddCommGroup W] [Module K W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul K W]
    {σ : Representation K P W} (M : Realization F P V ρ) (N : Realization K P W σ)
    (s : CategoryTheory.CondensedBar.ScalarAction (coefficientRingMap F φ hφ) P)
    (f : V →+ W) (hf : Continuous f)
    (hscalar : ∀ (a : F) (v : V), f (a • v) = φ a • f v)
    (heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    M.object ⟶ s.functor.obj N.object :=
  Classical.choose (exists_unique_scalarMap φ hφ M N s f hf hscalar heq).exists

end ScalarMaps

end Profinite.CondensedAction.ContinuousRepresentation

namespace Profinite.CondensedAction.PrimeToEll

section Representations
variable (E F : Type u) [Field E] [Field F] [Algebra E F]
  (V : Type (u + 1)) [AddCommGroup V] [Module E V]

/-- Scalar extension with its finite-dimensional module topology. The underlying module
is the recorded algebraic tensor product; the copy pins its topology without altering
any pre-existing topology instance on tensor products.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def Extended := F ⊗[E] V

/-- The original additive structure on scalar extension.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedAdd : AddCommGroup (Extended E F V) :=
  inferInstanceAs (AddCommGroup (F ⊗[E] V))

/-- The original F-module structure on scalar extension.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedModule : Module F (Extended E F V) :=
  inferInstanceAs (Module F (F ⊗[E] V))

/-- The original restricted E-module on the tensor product.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedRestrictModule : Module E (Extended E F V) :=
  inferInstanceAs (Module E (F ⊗[E] V))

/-- The actual scalar tower on the tensor product.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
instance extendedScalarTower : IsScalarTower E F (Extended E F V) :=
  inferInstanceAs (IsScalarTower E F (F ⊗[E] V))

variable [TopologicalSpace F]

/-- Finite-dimensional product topology, without any completion of F.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedTopology : TopologicalSpace (Extended E F V) :=
  moduleTopology F (Extended E F V)

/-- The topology is by construction the module topology.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
instance extendedModuleTopology : IsModuleTopology F (Extended E F V) := ⟨rfl⟩

/-- Topological addition and negation in the specified module topology.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
instance extendedTopologicalAddGroup [IsTopologicalRing F] :
    IsTopologicalAddGroup (Extended E F V) :=
  IsModuleTopology.topologicalAddGroup F _

variable (P : Type u) [Group P] (ρ : Representation E P V)

/-- The extended action sends a pure tensor a tensor v to a tensor rho(p)v.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def extendedRepresentation : Representation F P (Extended E F V) :=
  (Module.End.baseChangeHom E F V).toMonoidHom.comp ρ

variable {E V} (B L : Type u) [Group B] [Group L]

/-- The ordinary E-linear B-fixed subspace, using Mathlib invariants.
It carries the induced subspace topology when V is topological.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
abbrev fixedSpace (ρ : Representation E (B × L) V) :=
  Representation.invariants (ρ.comp (MonoidHom.inl B L))

/-- The commuting L-action preserves B-fixed vectors.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: for b in B and l in L, (b,1)(1,l)=(1,l)(b,1). Apply the representation
law and the defining equation rho(b,1)v=v. This works for the zero subspace. -/
theorem fixed_stable (ρ : Representation E (B × L) V) :
    ∀ l : L, fixedSpace B L ρ ≤ (fixedSpace B L ρ).comap (ρ (1, l)) := by
  intro l v hv b
  change ρ (b, 1) (ρ (1, l) v) = ρ (1, l) v
  calc
    ρ (b, 1) (ρ (1, l) v) = ρ ((b, 1) * (1, l)) v :=
      (Module.End.mul_apply _ _ _).symm.trans (congrArg (fun f ↦ f v) (ρ.map_mul _ _).symm)
    _ = ρ ((1, l) * (b, 1)) v := by simp
    _ = ρ (1, l) (ρ (b, 1) v) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (1, l) v := congrArg (ρ (1, l)) (hv b)

/-- Restriction to the actual fixed subspace, with its residual L-action.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def fixedRepresentation (ρ : Representation E (B × L) V) :
    Representation E L (fixedSpace B L ρ) :=
  Representation.subrepresentation (ρ.comp (MonoidHom.inr B L)) (fixedSpace B L ρ)
    (fixed_stable B L ρ)

/-- The scalar-extended inclusion of the invariant subspace.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def fixedInclusion (ρ : Representation E (B × L) V) :
    Extended E F (fixedSpace B L ρ) →ₗ[F] Extended E F V :=
  (fixedSpace B L ρ).subtype.baseChange F

set_option linter.unusedSectionVars false in
/-- The invariant inclusion intertwines projection inflation with the original action.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: on a pure tensor a tensor v, write (b,l)=(1,l)(b,1) and use fixedness
of v. Both maps are F-linear, so tensor induction proves the formula on all tensors. -/
theorem fixedInclusion_equivariant (ρ : Representation E (B × L) V) :
    ∀ (p : B × L) (v : Extended E F (fixedSpace B L ρ)),
      fixedInclusion F B L ρ
        (extendedRepresentation E F (fixedSpace B L ρ) L (fixedRepresentation B L ρ) p.2 v) =
      extendedRepresentation E F V (B × L) ρ p (fixedInclusion F B L ρ v) := by
  intro p v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a v =>
    change a ⊗ₜ[E] ρ (1, p.2) v.val = a ⊗ₜ[E] ρ p v.val
    congr 1
    calc
      ρ (1, p.2) v.val = ρ (1, p.2) (ρ (p.1, 1) v.val) :=
        congrArg (ρ (1, p.2)) (v.property p.1).symm
      _ = ρ ((1, p.2) * (p.1, 1)) v.val := by
        rw [map_mul, Module.End.mul_apply]
      _ = ρ p v.val := by simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An equivariant linear map sends B-fixed vectors to B-fixed vectors.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).
Proof: for a fixed vector v, equivariance gives rho'(b,1)f(v)=f(rho(b,1)v)=f(v).
This is precisely membership in the target invariant subspace. -/
theorem mapFixed_mem {V' : Type (u + 1)} [AddCommGroup V'] [Module E V']
    (σ : Representation E (B × L) V) (σ' : Representation E (B × L) V')
    (f : V →ₗ[E] V') (heq : ∀ (p : B × L) (v : V), f (σ p v) = σ' p (f v))
    (v : fixedSpace B L σ) : f v ∈ fixedSpace B L σ' := by
  intro b
  exact (heq (b, 1) v).symm.trans (congrArg f (v.property b))

/-- Restriction of an equivariant map to the actual B-fixed subspaces.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def fixedMap {V' : Type (u + 1)} [AddCommGroup V'] [Module E V']
    (σ : Representation E (B × L) V) (σ' : Representation E (B × L) V')
    (f : V →ₗ[E] V') (heq : ∀ (p : B × L) (v : V), f (σ p v) = σ' p (f v)) :
    fixedSpace B L σ →ₗ[E] fixedSpace B L σ' :=
  (f.comp (fixedSpace B L σ).subtype).codRestrict (fixedSpace B L σ')
    (mapFixed_mem B L σ σ' f heq)

/-- Coefficient insertion on scalar-extended vectors: a tensor v maps to a tensor v,
where a is carried by the E-algebra map. Under E tensor V = V this is v to 1 tensor v.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def scalarInsertion (V : Type (u + 1)) [AddCommGroup V] [Module E V] :
    Extended E E V →ₗ[E] Extended E F V :=
  TensorProduct.map (Algebra.linearMap E F) (LinearMap.id : V →ₗ[E] V)

set_option linter.unusedSectionVars false in
/-- Scalar insertion intertwines the two representations on the nose.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).
Proof: on a tensor a tensor v, both composites give the image of a tensor rho(p)v.
Tensor induction proves the equality, including for zero vectors and zero modules. -/
theorem scalarInsertion_equivariant : ∀ (p : P) (v : Extended E E V),
    scalarInsertion F V (extendedRepresentation E E V P ρ p v) =
      extendedRepresentation E F V P ρ p (scalarInsertion F V v) := by
  intro p v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option linter.unusedSectionVars false in
/-- Scalar insertion commutes with the actual fixed-space inclusion.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).
Proof: tensor functoriality reduces the equation to a pure tensor. Both maps take
a tensor v in the fixed subspace to the image of a tensor its inclusion in V. -/
theorem scalarInsertion_fixed (σ : Representation E (B × L) V) :
    (scalarInsertion F V).comp (fixedInclusion E B L σ) =
      ((fixedInclusion F B L σ).restrictScalars E).comp
        (scalarInsertion F (fixedSpace B L σ)) := by
  apply TensorProduct.ext'
  intro a v
  rfl

end Representations

end Profinite.CondensedAction.PrimeToEll

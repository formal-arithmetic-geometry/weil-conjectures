/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Sheaf.AlgebraicGeometry.StrictLocalSectionCone
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.Paper.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity

/-!
# Local acyclicity relative to an abelian étale sheaf

Source: Stacks Project, Tag 0GJP, definition-locally-acyclic and equation-alpha-K
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The pointed map of strict localizations is unique.
Source: Stacks Project, Tag 0GJP, preceding diagram; Tags 04GU and 04HX
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf).

Proof: pull back pointed étale neighbourhoods of the image point along `f`.
The limit cone at `x` supplies compatible maps into these pullbacks, hence a map into
its target strict localization. The map commutes with the structural morphisms and
with the distinguished geometric points. Conversely these two equations determine
its composites with every étale neighbourhood leg by pointed étale rigidity over a
strictly henselian local ring. The limit property makes the map unique. -/
theorem existsUnique_localAcyclicityStrictMap
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃! h : Scheme.strictHenselizationScheme x ⟶ Scheme.strictHenselizationScheme (x ≫ f),
      h ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
        Scheme.strictHenselizationStructuralMap x ≫ f ∧
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation x)) ≫ h =
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation (x ≫ f))) := by
  let := (Scheme.descResidueField (Scheme.stalkClosedPointTo (x ≫ f))).hom.toAlgebra
  let := (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom.toAlgebra
  obtain ⟨hS, _, _, _, σS, ⟨hσS, _⟩, _⟩ :=
    strictHenselizationResidue (x ≫ f) rfl
  let := hS
  obtain ⟨hX, _, _, _, σX, ⟨hσX, _⟩, _⟩ :=
    strictHenselizationResidue x rfl
  let := hX
  let ψS := (((IntermediateField.val
    (separableClosure (S.residueField ((x ≫ f) (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σS.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing (x ≫ f))))
  let ψX := (((IntermediateField.val
    (separableClosure (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σX.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing x)))
  have hψS : Spec.map (CommRingCat.ofHom ψS) =
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation (x ≫ f))) := by
    obtain ⟨hl⟩ := (Scheme.strictHenselization_properties (x ≫ f)).2.2
    apply hl.hom_ext
    intro j
    apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{u}
      (Scheme.strictHenselizationNeighbourhoods (x ≫ f))).inverse.obj
        j.unop.unop).1.left)).isoSpec.inv).1
    exact (hσS j.unop.unop).trans
      (Scheme.strictHenselizationPointEvaluation_pointed (x ≫ f) j.unop.unop).symm
  have hψX : Spec.map (CommRingCat.ofHom ψX) =
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation x)) := by
    obtain ⟨hl⟩ := (Scheme.strictHenselization_properties x).2.2
    apply hl.hom_ext
    intro j
    apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{u}
      (Scheme.strictHenselizationNeighbourhoods x)).inverse.obj
        j.unop.unop).1.left)).isoSpec.inv).1
    exact (hσX j.unop.unop).trans
      (Scheme.strictHenselizationPointEvaluation_pointed x j.unop.unop).symm
  obtain ⟨_, h, _, hbase, hres, _, _⟩ :=
    strictHenselizationFunctoriality f x (x ≫ f) rfl rfl rfl σS σX hσS hσX
  have hpoint : Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation x)) ≫
      Spec.map h =
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation (x ≫ f))) := by
    rw [← hψX, ← hψS, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hres.symm
  refine ⟨Spec.map h, ⟨hbase, hpoint⟩, ?_⟩
  rintro h' ⟨h'base, h'point⟩
  obtain ⟨hl⟩ := (Scheme.strictHenselization_properties (x ≫ f)).2.2
  apply hl.hom_ext
  intro j
  apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{u}
    (Scheme.strictHenselizationNeighbourhoods (x ≫ f))).inverse.obj
      j.unop.unop).1.left)).isoSpec.inv).1
  let c := (Scheme.strictHenselizationCone (x ≫ f)).π.app j ≫
    (Spec (Opposite.unop ((equivSmallModel.{u}
      (Scheme.strictHenselizationNeighbourhoods (x ≫ f))).inverse.obj
        j.unop.unop).1.left)).isoSpec.inv
  let p := ((Scheme.AffineEtale.Spec S).obj ((equivSmallModel.{u}
    (Scheme.strictHenselizationNeighbourhoods (x ≫ f))).inverse.obj j.unop.unop).1).hom
  have hc : c ≫ p = Scheme.strictHenselizationStructuralMap (x ≫ f) := by
    simpa only [c, p, Scheme.isoSpec_Spec_inv] using!
      ((Scheme.exists_strictHenselizationStructuralMap (x ≫ f)).choose_spec j.unop.unop)
  change h' ≫ c = Spec.map h ≫ c
  apply etalePointedMapRigidity ψX p
  · simpa only [Category.assoc, hc] using h'base.trans hbase.symm
  · rw [hψX]
    simpa only [Category.assoc] using!
      (congrArg (fun q ↦ q ≫ c) h'point).trans
        (congrArg (fun q ↦ q ≫ c) hpoint).symm

/-- The canonical pointed strict-local map induced by pulling back neighbourhoods.
Source: Stacks Project, Tag 0GJP, preceding diagram
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf). -/
noncomputable def localAcyclicityStrictMap
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    Scheme.strictHenselizationScheme x ⟶ Scheme.strictHenselizationScheme (x ≫ f) :=
  Classical.choose (existsUnique_localAcyclicityStrictMap f x)

/-- The variety of vanishing cycles, with no algebraicity requirement on the test point.
Source: Stacks Project, Tag 0GJP, preceding diagram
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf). -/
noncomputable def localAcyclicityFiber
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f)) : Scheme.{u} :=
  pullback (localAcyclicityStrictMap f x) t

/-- The canonical map from the stalk to sections on the variety of vanishing cycles.
The uniquely characterized strict-local restriction is the inverse of the germ
isomorphism (Tags 03QO and 03Q1). It is followed by pullback of global sections and
the composition comparison for inverse images.
Source: Stacks Project, Tag 0GJP, equation-alpha-K
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf). -/
noncomputable def localAcyclicityAlpha
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale x).sheafFiber.obj G ⟶
      (Sheaf.Γ (localAcyclicityFiber f x t).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst (localAcyclicityStrictMap f x) t ≫
            Scheme.strictHenselizationStructuralMap x)).obj G) :=
  Classical.choose ((strictLocalSectionCone x).existsUnique_restriction G) ≫
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1}
      (pullback.fst (localAcyclicityStrictMap f x) t)
      ((upperStar AddCommGrpCat.{u + 1}
        (Scheme.strictHenselizationStructuralMap x)).obj G) ≫
    (Sheaf.Γ (localAcyclicityFiber f x t).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((upperStarComp AddCommGrpCat.{u + 1}
        (pullback.fst (localAcyclicityStrictMap f x) t)
        (Scheme.strictHenselizationStructuralMap x)).inv.app G)

/-- Local acyclicity at a geometric point relative to an abelian sheaf: the canonical
map is an isomorphism in degree zero and all positive cohomology groups vanish.
Source: Stacks Project, Tag 0GJP, definition-locally-acyclic (1)
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf). -/
def IsLocallyAcyclicAtRelative
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f)),
    IsIso (localAcyclicityAlpha f x t G) ∧
      ∀ q : ℕ, 0 < q → IsZero
        ((cohomology AddCommGrpCat.{u + 1} (localAcyclicityFiber f x t) (q : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1}
              (pullback.fst (localAcyclicityStrictMap f x) t ≫
                Scheme.strictHenselizationStructuralMap x)).obj G)))

/-- Local acyclicity relative to an abelian sheaf at every geometric point.
Source: Stacks Project, Tag 0GJP, definition-locally-acyclic (2)
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf). -/
def IsLocallyAcyclicRelative
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    IsLocallyAcyclicAtRelative f x G

/-- Local acyclicity for all constant cyclic coefficients of positive order prime
to the residue characteristic, including every positive order in characteristic zero.
Source: Stacks Project, Tag 0GJP, definition-locally-acyclic (4)
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf). -/
def IsLocallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (n : ℕ), 0 < n →
    (ringChar (X.residueField (x default)) = 0 ∨
      n.Coprime (ringChar (X.residueField (x default)))) →
    IsLocallyAcyclicAtRelative f x
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))

/-- Universal local acyclicity: local acyclicity after every scheme base change.
Source: Stacks Project, Tag 0GJP, definition-locally-acyclic (5)
(blueprint: def-weil-pbc-local-acyclicity-abelian-sheaf). -/
def IsUniversallyLocallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (S' : Scheme.{u}) (g : S' ⟶ S), IsLocallyAcyclic (pullback.snd f g)

end AlgebraicGeometry.Etale

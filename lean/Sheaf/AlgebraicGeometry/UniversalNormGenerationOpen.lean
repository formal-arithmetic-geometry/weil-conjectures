/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.SeparatingPairOpen
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated

/-! # Universal polynomial norm sections and their generating locus

Source: Stacks Project, Tags 02KH, 02O5, 01W1, 01JU, 0H7K and 01NE;
the finite tensor expansion and reindexing in the node's proof.
(blueprint: lem-sfb-universal-norm-generation-open)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry
open Scheme.Modules

/-- Pull a global section back using the section-normalized adjunction.
Source: Stacks, Tag 01CD (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormPullSection {X Y : Scheme.{u}} (q : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) : Γ((tensorPullback q).obj M, ⊤) :=
  ((tensorPullback q).obj M).presheaf.map
    (homOfLE (Scheme.Hom.preimage_top q).ge).op
    (((tensorPullbackSectionAdjunction q).unit.app M).app ⊤ s)

/-- Extract one tensor factor by adjacent symmetric interchanges, preserving all other factors.
Source: Stacks, Tag 01CA (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormRemoveFactor {Y : Scheme.{u}} {G : Type v}
    [DecidableEq G] (ρ : G → Aut Y) (L : Y.Modules) (g : G) :
    ∀ (l : List G) (_h : g ∈ l), pencilTranslateTensor ρ L l ≅
      (tensorPullback (ρ g).hom).obj L ⊗ pencilTranslateTensor ρ L (l.erase g)
  | [], h => False.elim (by simp at h)
  | a :: l, h => by
      classical
      by_cases ha : a = g
      · subst a
        simpa [pencilTranslateTensor] using
          Iso.refl ((tensorPullback (ρ g).hom).obj L ⊗ pencilTranslateTensor ρ L l)
      · have hg : g ∈ l := (List.mem_cons.mp h).resolve_left (Ne.symm ha)
        have he : (a :: l).erase g = a :: l.erase g := by
          simp [ha]
        rw [he]
        exact
          (Iso.refl ((tensorPullback (ρ a).hom).obj L) ⊗ᵢ universalNormRemoveFactor ρ L g l hg) ≪≫
            (α_ _ _ _).symm ≪≫ ((β_ _ _) ⊗ᵢ Iso.refl _) ≪≫ α_ _ _ _

/-- Reorder translated factors by the deterministic successive-extraction algorithm.
Source: Stacks, Tag 01CA (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormReorder {Y : Scheme.{u}} {G : Type v} [DecidableEq G]
    (ρ : G → Aut Y) (L : Y.Modules) :
    ∀ (m l : List G) (_h : l.Perm m), pencilTranslateTensor ρ L l ≅
      pencilTranslateTensor ρ L m
  | [], [], _ => Iso.refl _
  | [], a :: l, h => False.elim (by simpa using h.length_eq)
  | g :: m, l, h =>
      universalNormRemoveFactor ρ L g l (h.mem_iff.mpr (by simp)) ≪≫
        (Iso.refl _ ⊗ᵢ universalNormReorder ρ L m (l.erase g)
          (by simpa using h.erase g))

/-- Distribute pullback through the translated tensor, with factor `g` moved to `g*k`.
Source: Stacks, Tag 01CD (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormTranslateIso {Y : Scheme.{u}} {G : Type v} [Group G]
    (ρ : G →* Aut Y) (L : Y.Modules) (k : G) :
    ∀ l : List G, (tensorPullback (ρ k).hom).obj (pencilTranslateTensor (fun g ↦ ρ g) L l)
      ≅ pencilTranslateTensor (fun g ↦ ρ g) L (l.map (fun g ↦ g * k))
  | [] => (boundaryPullbackComparison (ρ k).hom).app _ ≪≫ pullbackObjUnitIso _
  | g :: l =>
      boundaryPullbackTensorIso (ρ k).hom ((tensorPullback (ρ g).hom).obj L)
        (pencilTranslateTensor (fun a ↦ ρ a) L l) ≪≫
      ((((tensorPullbackSectionComp (ρ k).hom (ρ g).hom).app L).symm ≪≫
        eqToIso (congrArg (fun h ↦ (tensorPullback h).obj L)
          (congrArg (fun x : Aut Y ↦ x.hom)
            (ρ.map_mul g k)).symm)) ⊗ᵢ universalNormTranslateIso ρ L k l)

/-- The canonical right-translation permutation of the orbit bundle, raised to power `n`.
Source: Stacks, Tags 01CA, 01CD (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormPermutation {Y : Scheme.{u}} {G : Type v}
    [Group G] [Finite G] (ρ : G →* Aut Y) (L : Y.Modules) (n : ℕ) (k : G) :
    (tensorPullback (ρ k).hom).obj ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n) ≅
      (pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n := by
  classical
  letI := Fintype.ofFinite G
  have hp : ((pencilGroupElements G).map (fun g ↦ g * k)).Perm
      (pencilGroupElements G) := by
    apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
    · intro g
      change g ∈ (List.ofFn (Fintype.equivFin G).symm).map (fun h ↦ h * k) ↔
        g ∈ List.ofFn (Fintype.equivFin G).symm
      constructor
      · intro _
        exact List.mem_ofFn.mpr
          ⟨Fintype.equivFin G g, (Fintype.equivFin G).symm_apply_apply g⟩
      · intro _
        exact List.mem_map.mpr ⟨g * k⁻¹, List.mem_ofFn.mpr
          ⟨Fintype.equivFin G (g * k⁻¹), (Fintype.equivFin G).symm_apply_apply _⟩,
          by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩
    · exact (List.nodup_ofFn.mpr (Fintype.equivFin G).symm.injective).map
        (mul_left_injective k)
    · exact List.nodup_ofFn.mpr (Fintype.equivFin G).symm.injective
  exact boundaryPullbackPowIso (ρ k).hom _ n ≪≫ boundaryTensorPowIso
    (universalNormTranslateIso ρ L k (pencilGroupElements G) ≪≫
      universalNormReorder (fun g ↦ ρ g) L _ _ hp) n


/-- The base-changed group action on a fibre product.
Source: Stacks, Tag 01CD (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormAction {C S T : Scheme.{u}} (f : C ⟶ S) (p : T ⟶ S)
    {G : Type v} [Group G] (ρ : G →* Aut (Over.mk f)) :
    G →* Aut (pullback f p) :=
  ((Over.pullback p ⋙ Over.forget T).mapAut (Over.mk f)).comp ρ

/-- Identify the pullback of the orbit power with the orbit power for the base-changed action.
Source: Stacks, Tag 01CD (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormBaseChangeIso {C S T : Scheme.{u}} (f : C ⟶ S) (p : T ⟶ S)
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut (Over.mk f))
    (L : C.Modules) (n : ℕ) :
    (tensorPullback (pullback.fst f p)).obj
        ((pencilOrbitBundle (fun g ↦ (Over.forget S).mapIso (ρ g)) L).tensorPow n) ≅
      (pencilOrbitBundle (fun g ↦ universalNormAction f p ρ g)
        ((tensorPullback (pullback.fst f p)).obj L)).tensorPow n :=
  boundaryPullbackPowIso (pullback.fst f p) _ n ≪≫
    boundaryTensorPowIso (normPencilTranslateBaseChangeIso (pullback.fst f p)
      (fun g ↦ (Over.forget S).mapIso (ρ g))
      (fun g ↦ universalNormAction f p ρ g)
      (fun g ↦ (baseChange_morphism_projections (ρ g).hom (Over.mk p)).1)
      L (pencilGroupElements G)) n

/-- Universal norm sections obtained by tensoring universal linear combinations of a basis.
Source: Stacks, Tags 01CA, 01CD; node proof step 4.
(blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormPair {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) {G : Type v} [Group G] [Finite G]
    (ρ : G →* Aut (Over.mk f)) (L : C.Modules) (n : ℕ)
    {I : Type u} [Fintype I] (b : I → Γ(L.tensorPow n, ⊤)) :
    ULift.{u} (Fin 2) → Γ((tensorPullback
      (pullback.fst f (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)))).obj
        ((pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L).tensorPow n), ⊤) :=
  fun j ↦ (universalNormBaseChangeIso f
      (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)) ρ L n).inv.app ⊤
    ((pencilNormSection
      (fun g ↦ universalNormAction f
        (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)) ρ g)
      ((tensorPullback (pullback.fst f
        (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)))).obj L) n
      (SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
        ((boundaryPullbackPowIso (pullback.fst f
          (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))) L n).hom.app ⊤
          (∑ i : I, (pullback.snd f
              (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))).appTop
                (AffineSpace.coord (Spec (.of F)) (i, j)) •
            universalNormPullSection _ (L.tensorPow n) (b i)))))).val (op ⊤))

/-- Pull back a section and identify the successive pullbacks along a commuting triangle.
Source: Stacks, Tag 01CD (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormSpecialize {C X Y : Scheme.{u}} (q : X ⟶ C) (r : Y ⟶ X)
    (a : Y ⟶ C) (h : r ≫ q = a) (M : C.Modules)
    (s : Γ((tensorPullback q).obj M, ⊤)) : Γ((tensorPullback a).obj M, ⊤) :=
  (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj M) h)).hom.app ⊤
    (((tensorPullbackSectionComp r q).app M).inv.app ⊤
      (universalNormPullSection r _ s))

/-- The map from a field fibre into the universal family over a parameter point.
Source: Stacks, Tag 01JU (blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormFiberMap {F E : Type u} [Field F] [Field E] [Algebra F E]
    {C P : Scheme.{u}} (f : C ⟶ Spec (.of F)) (p : P ⟶ Spec (.of F))
    (z : Spec (.of E) ⟶ P) (hz : z ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F E))) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⟶ pullback f p :=
  pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F E))))
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F E))) ≫ z)
    (by rw [Category.assoc, hz, pullback.condition])


/-- Evaluate a polynomial in one of the two independent sets of section coordinates.
Source: Stacks, Tag 01CA; node proof step 4.
(blueprint: lem-sfb-universal-norm-generation-open). -/
noncomputable def universalNormPolynomial (F : Type u) [Field F] (I : Type u)
    (j : ULift.{u} (Fin 2)) (p : MvPolynomial I F) :
    Γ(𝔸(I × ULift.{u} (Fin 2); Spec (.of F)), ⊤) :=
  MvPolynomial.eval₂Hom
    (((Scheme.ΓSpecIso (.of F)).inv ≫
      (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)).appTop).hom)
    (fun i ↦ AffineSpace.coord (Spec (.of F)) (i, j)) p

/-- Invariance of both norms under the specified canonical permutation, and of their
coordinate morphism whenever they generate. No invertibility or generation is assumed here.
Source: Stacks, Tag 01NE; node proof steps 10–11.
(blueprint: lem-sfb-universal-norm-generation-open). -/
def UniversalNormInvariantPair {E : Type u} [Field E] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of E)) {G : Type v} [Group G] [Finite G]
    (ρ : G →* Aut Y) (L : Y.Modules) (n : ℕ)
    (a : ULift.{u} (Fin 2) → (L.tensorPow n).sections) : Prop :=
  (∀ (k : G) (j : ULift.{u} (Fin 2)),
    (universalNormPermutation ρ L n k).hom.app ⊤
      (universalNormPullSection (ρ k).hom _
        ((pencilNormSection (fun g ↦ ρ g) L n (a j)).val (op ⊤))) =
      (pencilNormSection (fun g ↦ ρ g) L n (a j)).val (op ⊤)) ∧
  ∀ (hB : ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n).IsInvertible)
    (hs : Epi (((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n).freeHomEquiv.symm
      (fun j : ULift.{u} (Fin 2) ↦ pencilNormSection (fun g ↦ ρ g) L n (a j)))) (k : G),
    (ρ k).hom ≫ @ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2))
        inferInstance Y (Spec (.of E)) f
        ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n) hB
        (fun j ↦ pencilNormSection (fun g ↦ ρ g) L n (a j)) hs =
      @ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2))
        inferInstance Y (Spec (.of E)) f
        ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n) hB
        (fun j ↦ pencilNormSection (fun g ↦ ρ g) L n (a j)) hs

/-- The precise zero-scheme, polynomial-coordinate and specialization assertions for a
chosen basis. The common zero scheme is specified by its local two-generator ideals.
Source: Stacks, Tags 01JU, 01W1, 01CY, 01NE; node proof steps 4–11.
(blueprint: lem-sfb-universal-norm-generation-open). -/
def UniversalNormGenerationFamily {F : Type u} [Field F] {C : Scheme.{u}}
    [C.Over (Spec (.of F))] {G : Type v} [Group G] [Fintype G]
    (ρ : G →* Aut (Over.mk (C ↘ Spec (.of F)))) (L : C.Modules) (n : ℕ)
    {I : Type u} [Fintype I] (b : Module.Basis I F ((L.tensorPow n).H 0)) : Prop :=
  (∀ (R : Type u) [Fintype R]
    (c : Module.Basis R F
      (HOver (C ↘ Spec (.of F))
        ((pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L).tensorPow n) 0)),
    ∃ p : R → MvPolynomial I F,
      (∀ r : R, (p r).IsHomogeneous (Nat.card G)) ∧
      ∀ j : ULift.{u} (Fin 2),
        universalNormPair (C ↘ Spec (.of F)) ρ L n
            (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) j =
          ∑ r : R,
            (pullback.snd (C ↘ Spec (.of F))
              (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))).appTop
                (universalNormPolynomial F I j (p r)) •
              universalNormPullSection _ _ (H.zeroLinearEquiv _ (c r))) ∧
  ∃ (Z : (Limits.pullback (C ↘ Spec (.of F))
      (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))).IdealSheafData)
    (U : (𝔸(I × ULift.{u} (Fin 2); Spec (.of F))).Opens),
    (∀ (W : (Limits.pullback (C ↘ Spec (.of F))
        (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))).affineOpens)
      (e : Γ((tensorPullback (pullback.fst (C ↘ Spec (.of F))
          (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)))).obj
        ((pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L).tensorPow n), W.1)),
      IsFreeGenerator e → ∀ a d : Γ((Limits.pullback (C ↘ Spec (.of F))
        (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))), W.1),
        (∀ j : ULift.{u} (Fin 2),
          ((tensorPullback (pullback.fst (C ↘ Spec (.of F))
            (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)))).obj
            ((pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L).tensorPow n)).presheaf.map
            (homOfLE le_top).op
              (universalNormPair (C ↘ Spec (.of F)) ρ L n
                (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) j) =
            (if j.down = 0 then a else d) • e) →
        Z.ideal W = Ideal.span {a, d}) ∧
    IsClosed ((pullback.snd (C ↘ Spec (.of F))
      (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))) '' (Z.support : Set _)) ∧
    (U : Set _) = ((pullback.snd (C ↘ Spec (.of F))
      (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F))) ''
        (Z.support : Set _))ᶜ ∧
    ∀ (E : Type u) [Field E] [Algebra F E]
      (z : Spec (.of E) ⟶ 𝔸(I × ULift.{u} (Fin 2); Spec (.of F)))
      (hz : z ≫ 𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F) =
        Spec.map (CommRingCat.ofHom (algebraMap F E))),
      (∀ j : ULift.{u} (Fin 2),
        universalNormSpecialize
          (pullback.fst (C ↘ Spec (.of F))
            (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F)))
          (universalNormFiberMap (C ↘ Spec (.of F)) _ z hz)
          (pullback.fst (C ↘ Spec (.of F))
            (Spec.map (CommRingCat.ofHom (algebraMap F E))))
          (by simp [universalNormFiberMap]) _
          (universalNormPair (C ↘ Spec (.of F)) ρ L n
            (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) j) =
          (boundaryPullbackPowIso (pullback.fst (C ↘ Spec (.of F))
            (Spec.map (CommRingCat.ofHom (algebraMap F E)))) _ n).inv.app ⊤
            ((normPencilSections (C ↘ Spec (.of F)) ρ L n
              (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z j).val (op ⊤))) ∧
      (Set.range z ⊆ U ↔ Epi ((SheafOfModules.freeHomEquiv _).symm
        (normPencilSections (C ↘ Spec (.of F)) ρ L n
          (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z))) ∧
      UniversalNormInvariantPair
        (pullback.snd (C ↘ Spec (.of F))
          (Spec.map (CommRingCat.ofHom (algebraMap F E))))
        (universalNormAction (C ↘ Spec (.of F))
          (Spec.map (CommRingCat.ofHom (algebraMap F E))) ρ)
        ((tensorPullback (pullback.fst (C ↘ Spec (.of F))
          (Spec.map (CommRingCat.ofHom (algebraMap F E))))).obj L) n
        (fun j ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
          (normPencilCoordinateSection
            (pullback.fst (C ↘ Spec (.of F))
              (Spec.map (CommRingCat.ofHom (algebraMap F E))))
            (pullback.snd (C ↘ Spec (.of F))
              (Spec.map (CommRingCat.ofHom (algebraMap F E)))) L n
            (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z j)))

/-- On a smooth projective geometrically integral curve, the section spaces are finite,
canonical field base change is bijective, and the universal norms have exactly the open
common-zero complement as their generating locus, with canonical equivariance.

Source: Stacks, Tags 02KH, 02O5, 01W1, 01JU, 0H7K, 01CY and 01NE.
(blueprint: lem-sfb-universal-norm-generation-open).

Proof, following the node's eleven steps:
1. Pullback and finite tensor products preserve invertibility, so all powers and their
pullbacks are locally free of rank one, hence quasi-coherent and finitely presented.
2. Projectivity implies properness; proper coherent finiteness in degree zero makes the
spaces V and J finite dimensional (lem-fin-proper-coherent-finite-dimensional).
3. Field extension is flat. Apply the canonical comparison of
lem-pc-flat-cohomology-separated in degree zero to the quasi-compact separated curve.
The normalized pullback comparisons identify the resulting tensors and powers.
4. Expand the product of the universal sums in a basis: the coefficient indexed by
alpha : G → I is the monomial product_g X_(alpha g) times the corresponding tensor.
In every basis of J these are homogeneous polynomials of degree card G.
5. Specializing the coefficients gives exactly the tensor of the pulled-back sections,
since every action morphism is over the extension field.
6. Form the common zero scheme. In a frame its ideal is (a,d); this formula commutes
with arbitrary base change (lem-pc-closed-subscheme-base-change-ideal-image).
7. Properness makes the image of this closed subscheme closed; take its open complement.
8. A fibre is nonempty exactly when the parameter image lies in that image. For a
nonclosed image use lem-weil-common-extension-fields over its residue field to produce
a point of the fibre; no closed-point hypothesis enters.
9. The invertible generating-sections fibre criterion identifies emptiness of the common
zero fibre with generation (lem-weil-pbc-invertible-generating-sections-fibre).
10. Pullback sends the factor g to g*k. The deterministic symmetric permutation above
reindexes the same pure tensor, and commutes with grouping the power factors (g,j).
It therefore fixes both norm sections; no division by card G or faithfulness is used.
11. The projective-space functor of points identifies the translated generating pair
with the original pair. Uniqueness over Spec E proves invariance of its morphism.
-/
theorem universal_norm_generation_open
    {F : Type u} [Field F] (C : Scheme.{u}) [C.Over (Spec (.of F))]
    [Smooth (C ↘ Spec (.of F))] [IsHProjective (C ↘ Spec (.of F))]
    [LocallyOfFiniteType (C ↘ Spec (.of F))] [QuasiCompact (C ↘ Spec (.of F))]
    [GeometricallyIntegral (C ↘ Spec (.of F))] [IsIntegral C]
    (hdim : topologicalKrullDim C = 1)
    (G : Type v) [Group G] [Fintype G]
    (ρ : G →* Aut (Over.mk (C ↘ Spec (.of F))))
    (L : C.Modules) [L.IsInvertible] (n : ℕ) (hn : 1 ≤ n) :
    FiniteDimensional F ((L.tensorPow n).H 0) ∧
    FiniteDimensional F
      (HOver (C ↘ Spec (.of F))
        ((pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L).tensorPow n) 0) ∧
    (∀ (E : Type u) [Field E] [Algebra F E],
      Function.Bijective (H.baseChange (S := E) (C ↘ Spec (.of F)) (L.tensorPow n) 0) ∧
      Function.Bijective (H.baseChange (S := E) (C ↘ Spec (.of F))
        ((pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L).tensorPow n) 0)) ∧
    ∀ (I : Type u) [Fintype I] (b : Module.Basis I F ((L.tensorPow n).H 0)),
      UniversalNormGenerationFamily ρ L n b := by
  sorry

end AlgebraicGeometry

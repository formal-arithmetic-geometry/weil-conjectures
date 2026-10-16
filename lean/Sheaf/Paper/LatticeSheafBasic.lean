/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Coset.Defs
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The sheaf of integral lattices

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.8.4(6),
pp. 59--60 (blueprint: lem-weil-pbc-lattice-sheaf-locally-constant).

The presentation by a surjection from pairs with its exact kernel relation avoids choosing
representatives of isomorphism classes. Restriction is characterized by the embedded images
on every object of the slice. This also specifies the normalization of the constant-coset
isomorphism without making arbitrary choices of bases for integral modules.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- The commutative-ring version of the continuous coefficient presheaf, with exactly the
same sections and precomposition maps as `continuousMapRingPresheaf`.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientPresheaf (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj V := CommRingCat.of (ULift.{u + 1} C(V.unop.left, T))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.left.base.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction of the scalar-extension ring map to the localized site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), slice restrictions
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def latticeScalarMap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (U : X.ProEt) : R.over U ⟶ S.over U :=
  ⟨Functor.whiskerLeft (Over.forget U).op a.hom⟩

/-- A lattice pair, including the rationalization isomorphism, over a slice object.
Finite local freeness allows varying ranks and the zero module.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
structure IntegralLatticePair {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) (U : X.ProEt) where
  module : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U))
  locallyFree : module.IsFiniteLocallyFree
  rationalization :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) module ≅ L.over U

/-- The exact equivalence relation on pairs: an integral isomorphism intertwines their
rationalizations. Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def IntegralLatticePair.Equivalent {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} {a : R ⟶ S}
    {L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)} {U : X.ProEt}
    (P Q : IntegralLatticePair a L U) : Prop :=
  ∃ e : P.module ≅ Q.module,
    SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (latticeScalarMap a U) P.module e.hom ≫
      Q.rationalization.hom = P.rationalization.hom

set_option backward.isDefEq.respectTransparency false in
/-- The embedded image of a pair on a test object of its slice: apply the rationalization
map to the image of `1 ⊗ m` under the change-of-rings sheafification unit.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, first local calculation
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def IntegralLatticePair.image {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} {a : R ⟶ S}
    {L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)} {U : X.ProEt}
    (P : IntegralLatticePair a L U) (T : (Over U)ᵒᵖ) : Set ((L.over U).val.obj T) :=
  Set.range fun m : P.module.val.obj T ↦
    P.rationalization.hom.val.app T
      ((((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (S.over U)).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module)).app T)
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m))

/-- Continuous coefficients satisfy the sheaf axiom.
Source: Bhatt--Scholze, Lemma 4.2.12 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant).
Proof: forget to sets and identify the presheaf with the lifted restriction of
`continuousMapPresheaf T`. Mathlib's fpqc continuous-function descent theorem makes this
a sheaf. The pro-etale topology is contained in the fpqc topology. Restriction and the
universe lift preserve the sheaf condition, and the forgetful functor from commutative
rings reflects it. Thus the same functions form a sheaf of commutative rings. -/
theorem isSheaf_latticeCoefficientPresheaf (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (latticeCoefficientPresheaf X T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (latticeCoefficientPresheaf X T) (forget CommRingCat.{u + 1})]
  let e : latticeCoefficientPresheaf X T ⋙ forget CommRingCat.{u + 1} ≅
      (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙
        continuousMapPresheaf T ⋙ uliftFunctor.{u + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  rw [Presheaf.isSheaf_of_iso_iff e]
  refine Functor.op_comp_isSheaf_of_isSheaf
    (F := Scheme.ProEt.forget X ⋙ Over.forget X)
    (J := Scheme.ProEt.topology X) (K := Scheme.proetaleTopology) _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact (isSheaf_fpqcTopology_continuousMapPresheaf T).of_le
    Scheme.proetaleTopology_le_fpqcTopology

/-- The continuous coefficient sheaf, with its commutative-ring structure retained.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientSheaf (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨latticeCoefficientPresheaf X T, isSheaf_latticeCoefficientPresheaf X T⟩

/-- The coefficient map is postcomposition with the specified continuous ring map.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientSheafMap (X : Scheme.{u}) {T T' : Type u}
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
    (f : T →+* T') (hf : Continuous f) :
    latticeCoefficientSheaf X T ⟶ latticeCoefficientSheaf X T' :=
  ⟨{ app := fun _ ↦ CommRingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         ((f.compLeftContinuous _ hf).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The given valuation subring in the field equipped with its canonical absolute value.
`WithAbs.equiv` only changes the topology-bearing type synonym.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientIntegers (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Subring (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) :=
  (Padic.coefficientExtensionIntegers l E).comap
    (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)).toRingHom

/-- The integral matrix subgroup in the rational general linear group. Its cosets `gH`
are the orbits of right multiplication, hence use Mathlib's `leftRel` quotient.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def integralMatrixSubgroup {K : Type u} [Field K] (A : Subring K) (n : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) K) :=
  (Matrix.GeneralLinearGroup.map A.subtype).range

/-- The discrete set of lattices in a trivial rank `n` rational module, including `n = 0`.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
abbrev integralMatrixCosets {K : Type u} [Field K] (A : Subring K) (n : ℕ) :=
  Matrix.GeneralLinearGroup (Fin n) K ⧸ integralMatrixSubgroup A n

/-- The underlying ring sheaf of continuous coefficients, retaining the universe lift.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable abbrev latticeModuleRing (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (latticeCoefficientSheaf X T)

/-- The canonical inclusion of continuous integral coefficients in rational coefficients.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def integralLatticeCoefficientMap (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ⟶
      latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) :=
  latticeCoefficientSheafMap X (latticeCoefficientIntegers l E).subtype continuous_subtype_val

/-- A sheaf presentation of isomorphism classes of lattice pairs. The first two clauses
say exactly that its sections are the quotient by intertwining integral isomorphisms.
The last clause specifies restriction by equality of embedded images on every slice object.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, descent of embedded lattices
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def IsLatticeClassPresentation {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt, IntegralLatticePair a L U → F.obj.obj (op U)) : Prop :=
  (∀ U : X.ProEt, Function.Surjective (c U)) ∧
  (∀ (U : X.ProEt) (P Q : IntegralLatticePair a L U), c U P = c U Q ↔ P.Equivalent Q) ∧
  (∀ (U V : X.ProEt) (f : V ⟶ U)
    (P : IntegralLatticePair a L U) (Q : IntegralLatticePair a L V),
    F.obj.map f.op (c U P) = c V Q ↔
      ∀ T : Over V, P.image (op ((Over.map f).obj T)) = Q.image (op T))

/-- The free rank `n` coefficient sheaf on the localized site, with a lifted finite index.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable abbrev latticeFreeSheaf (X : Scheme.{u}) (K : Type u)
    [TopologicalSpace K] [CommRing K] [IsTopologicalRing K] (U : X.ProEt) (n : ℕ) :=
  SheafOfModules.free (R := (latticeModuleRing X K).over U) (ULift.{u + 1} (Fin n))

/-- A constant rational coefficient as an actual section of the coefficient sheaf.
Source: Bhatt--Scholze, Proposition 6.8.4(6), constant matrix entries
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeConstantCoefficient (X : Scheme.{u}) (K : Type u)
    [TopologicalSpace K] [CommRing K] [IsTopologicalRing K] (V : X.ProEt) (x : K) :
    (latticeCoefficientSheaf X K).obj.obj (op V) :=
  ULift.up (ContinuousMap.const V.left x)

set_option backward.isDefEq.respectTransparency false in
/-- The embedded module `g A^n`: its sections are the integral linear combinations of the
columns of `g`, in the standard coordinate basis of the rational free sheaf.
Source: Bhatt--Scholze, Proposition 6.8.4(6), the map `g ↦ g A^n`
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def matrixLatticeImage (X : Scheme.{u}) (K : Type u) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K) (U : X.ProEt) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ) :
    Set ((latticeFreeSheaf X K U n).val.obj T) :=
  Set.range fun b : Fin n → (latticeCoefficientSheaf X A).obj.obj (op T.unop.left) ↦
    ∑ i : Fin n,
      (∑ j : Fin n,
        latticeConstantCoefficient X K T.unop.left (g.val i j) *
        (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
          (op T.unop.left) (b j)) •
      (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
        (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
          (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))

section LatticePairImages

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

section Classes

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
  (a : R ⟶ S)
  (L : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
  (U : X.ProEt)



open scoped ChangeOfRings

private noncomputable def latticeTensorUnit
    (M : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U))) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap a U) M)

private theorem latticeExtension_unit
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)))
    (f : M ⟶ N) (T : (Over U)ᵒᵖ) (m : M.val.obj T) :
    (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) M f).val.app T ((latticeTensorUnit a U M).app T
      ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] m)) =
      (latticeTensorUnit a U N).app T
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] (f.val.app T m)) := by
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a U) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (latticeScalarMap a U) N :=
    { app := fun W ↦ (ModuleCat.extendScalars
        ((latticeScalarMap a U).hom.app W).hom).map (f.val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality
        (latticeScalarMap a U) M f }
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)).unit.naturality p
  have hv := congrArg (fun f ↦ f.app T) hn
  have hx := ConcreteCategory.congr_hom hv
    ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
      ((latticeScalarMap a U).hom.app T).hom] m)
  change (latticeTensorUnit a U N).app T
    ((ModuleCat.extendScalars ((latticeScalarMap a U).hom.app T).hom).map
      (f.val.app T) _) =
      (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) M f).val.app T ((latticeTensorUnit a U M).app T _) at hx
  rw [ModuleCat.ExtendScalars.map_tmul] at hx
  exact hx.symm

private noncomputable def pairSection (P : IntegralLatticePair a L U)
    (T : (Over U)ᵒᵖ) (m : P.module.val.obj T) : (L.over U).val.obj T :=
  P.rationalization.hom.val.app T ((latticeTensorUnit a U P.module).app T
    ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
      ((latticeScalarMap a U).hom.app T).hom] m))

private theorem pairSection_naturality {P Q : IntegralLatticePair a L U}
    (e : P.module ≅ Q.module)
    (he : SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module e.hom ≫ Q.rationalization.hom =
      P.rationalization.hom)
    (T : (Over U)ᵒᵖ) (m : P.module.val.obj T) :
    pairSection a L U Q T (e.hom.val.app T m) = pairSection a L U P T m := by
  have h := congrArg (fun f ↦ f.val.app T) he
  have hx := ConcreteCategory.congr_hom h ((latticeTensorUnit a U P.module).app T
    ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
      ((latticeScalarMap a U).hom.app T).hom] m))
  change Q.rationalization.hom.val.app T
    ((SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module e.hom).val.app T _) = _ at hx
  rw [latticeExtension_unit] at hx
  exact hx

private theorem pair_image_eq_of_equivalent {P Q : IntegralLatticePair a L U}
    (h : P.Equivalent Q) (T : (Over U)ᵒᵖ) : P.image T = Q.image T := by
  obtain ⟨e, he⟩ := h
  change SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module e.hom ≫ Q.rationalization.hom =
    P.rationalization.hom at he
  change Set.range (pairSection a L U P T) = Set.range (pairSection a L U Q T)
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨e.hom.val.app T m, pairSection_naturality a L U e he T m⟩
  · rintro ⟨m, rfl⟩
    refine ⟨e.inv.val.app T m, ?_⟩
    rw [← pairSection_naturality a L U e he T]
    congr 1
    have h := congrArg (fun f ↦ f.val.app T) e.inv_hom_id
    exact ConcreteCategory.congr_hom h m


private noncomputable def pairTensorMap (P : IntegralLatticePair a L U) :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module ⟶ (L.over U).val :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)) P.rationalization.hom

private noncomputable def pairEmbedding (P : IntegralLatticePair a L U) :
    P.module ⟶ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeScalarMap a U))).obj (L.over U) where
  val :=
    { app T := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1, u + 1}
        ((latticeScalarMap a U).hom.app T).hom ((pairTensorMap a L U P).app T)
      naturality := by
        intro T T' f
        ext m
        change (pairTensorMap a L U P).app T'
          ((1 : (S.over U).obj.obj T') ⊗ₜ[(R.over U).obj.obj T',
            ((latticeScalarMap a U).hom.app T').hom] P.module.val.map f m) =
            (L.over U).val.map f ((pairTensorMap a L U P).app T
              ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
                ((latticeScalarMap a U).hom.app T).hom] m))
        have hn := PresheafOfModules.naturality_apply (pairTensorMap a L U P) f
          ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
            ((latticeScalarMap a U).hom.app T).hom] m)
        have hm := Classical.choose_spec
          (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module f) (1 : (S.over U).obj.obj T) m
        change (pairTensorMap a L U P).app T'
          (SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module f _) = _ at hn
        change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
          (latticeScalarMap a U) P.module f
            ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
              ((latticeScalarMap a U).hom.app T).hom] m) = _ at hm
        rw [hm, map_one] at hn
        exact hn }

private noncomputable def pairComparisonSection (P Q : IntegralLatticePair a L U)
    (hQ : ∀ T, Function.Injective ((pairEmbedding a L U Q).val.app T))
    (hle : ∀ T, P.image T ⊆ Q.image T) (T : (Over U)ᵒᵖ) :
    P.module.val.obj T ⟶ Q.module.val.obj T :=
  ModuleCat.ofHom (X := P.module.val.obj T) (Y := Q.module.val.obj T)
    (LinearMap.codRestrictOfInjective (R := (R.over U).obj.obj T)
      ((pairEmbedding a L U P).val.app T).hom
      ((pairEmbedding a L U Q).val.app T).hom (hQ T) (fun m ↦ by
        change pairSection a L U P T m ∈ Q.image T
        exact hle T ⟨m, rfl⟩))

private theorem pairComparisonSection_spec (P Q : IntegralLatticePair a L U)
    (hQ : ∀ T, Function.Injective ((pairEmbedding a L U Q).val.app T))
    (hle : ∀ T, P.image T ⊆ Q.image T) (T : (Over U)ᵒᵖ)
    (m : P.module.val.obj T) :
    (pairEmbedding a L U Q).val.app T
      (pairComparisonSection a L U P Q hQ hle T m) =
        (pairEmbedding a L U P).val.app T m := by
  exact LinearMap.codRestrictOfInjective_comp_apply
    (R := (R.over U).obj.obj T) _ _ _ _ m

private noncomputable def pairComparison (P Q : IntegralLatticePair a L U)
    (hQ : ∀ T, Function.Injective ((pairEmbedding a L U Q).val.app T))
    (hle : ∀ T, P.image T ⊆ Q.image T) : P.module ⟶ Q.module where
  val :=
    { app := pairComparisonSection a L U P Q hQ hle
      naturality := by
        intro T T' f
        ext m
        apply hQ T'
        change (pairEmbedding a L U Q).val.app T'
          (pairComparisonSection a L U P Q hQ hle T' (P.module.val.map f m)) =
            (pairEmbedding a L U Q).val.app T'
              (Q.module.val.map f (pairComparisonSection a L U P Q hQ hle T m))
        rw [pairComparisonSection_spec]
        have hq := PresheafOfModules.naturality_apply (pairEmbedding a L U Q).val f
          (pairComparisonSection a L U P Q hQ hle T m)
        have hp := PresheafOfModules.naturality_apply (pairEmbedding a L U P).val f m
        change (pairEmbedding a L U Q).val.app T' (Q.module.val.map f _) =
          (L.over U).val.map f ((pairEmbedding a L U Q).val.app T _) at hq
        rw [pairComparisonSection_spec] at hq
        exact hp.trans hq.symm }

private theorem pairComparison_intertwines (P Q : IntegralLatticePair a L U)
    (hQ : ∀ T, Function.Injective ((pairEmbedding a L U Q).val.app T))
    (hle : ∀ T, P.image T ⊆ Q.image T) :
    SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module (pairComparison a L U P Q hQ hle) ≫
      Q.rationalization.hom = P.rationalization.hom := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)).injective
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change Q.rationalization.hom.val.app T
    ((SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module (pairComparison a L U P Q hQ hle)).val.app T
      ((latticeTensorUnit a U P.module).app T
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m))) = _
  rw [latticeExtension_unit]
  exact pairComparisonSection_spec a L U P Q hQ hle T m

private theorem pair_equivalent_of_image_eq
    (P Q : IntegralLatticePair a L U)
    (hP : ∀ T, Function.Injective ((pairEmbedding a L U P).val.app T))
    (hQ : ∀ T, Function.Injective ((pairEmbedding a L U Q).val.app T))
    (heq : ∀ T, P.image T = Q.image T) : P.Equivalent Q := by
  let f := pairComparison a L U P Q hQ (fun T ↦ (heq T).le)
  let g := pairComparison a L U Q P hP (fun T ↦ (heq T).ge)
  have hfg : f ≫ g = 𝟙 P.module := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    ext m
    apply hP T
    change (pairEmbedding a L U P).val.app T
      (pairComparisonSection a L U Q P hP (fun T ↦ (heq T).ge) T
        (pairComparisonSection a L U P Q hQ (fun T ↦ (heq T).le) T m)) =
          (pairEmbedding a L U P).val.app T m
    rw [pairComparisonSection_spec, pairComparisonSection_spec]
  have hgf : g ≫ f = 𝟙 Q.module := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    ext m
    apply hQ T
    change (pairEmbedding a L U Q).val.app T
      (pairComparisonSection a L U P Q hQ (fun T ↦ (heq T).le) T
        (pairComparisonSection a L U Q P hP (fun T ↦ (heq T).ge) T m)) =
          (pairEmbedding a L U Q).val.app T m
    rw [pairComparisonSection_spec, pairComparisonSection_spec]
  refine ⟨⟨f, g, hfg, hgf⟩, ?_⟩
  exact pairComparison_intertwines a L U P Q hQ (fun T ↦ (heq T).le)

private theorem scalarUnit_injective
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    (ha : Function.Injective a) (M : Type (u + 1)) [AddCommGroup M] [Module A M]
    [Module.Free A M] :
    Function.Injective (fun m : M ↦ (1 : B) ⊗ₜ[A, a] m) := by
  let : Algebra A B := a.toAlgebra
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr ha
  exact Module.Flat.tensorProduct_mk_injective A M B

private theorem pairTensor_injective_at_basis
    (P : IntegralLatticePair a L U)
    (q : P.module.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) {W : Over U} (t : W ⟶ q.X i)
    (ha : Function.Injective (((latticeScalarMap a U).hom.app (op W)).hom)) :
    Function.Injective (fun m : P.module.val.obj (op W) ↦
      (1 : (S.over U).obj.obj (op W)) ⊗ₜ[(R.over U).obj.obj (op W),
        ((latticeScalarMap a U).hom.app (op W)).hom] m) := by
  classical
  let := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  let : Fintype (q.generators i).I := Fintype.ofFinite _
  let ee : P.module.val.obj (op W) ≃ₗ[(R.over U).obj.obj (op W)]
      ((q.generators i).I → (R.over U).obj.obj (op W)) :=
    SheafOfModules.sectionsLinearEquivOfIsoFree
      (asIso (q.generators i).π).symm (op (Over.mk t))
  let : Module.Free ((R.over U).obj.obj (op W)) (P.module.val.obj (op W)) :=
    Module.Free.of_equiv ee.symm
  exact scalarUnit_injective _ ha _

private theorem pairEmbedding_injective
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P : IntegralLatticePair a L U) (T : (Over U)ᵒᵖ) :
    Function.Injective ((pairEmbedding a L U P).val.app T) := by
  classical
  obtain ⟨q, hq, hf⟩ := P.locallyFree.exists_localGeneratorsData
  let := hq
  let := hf
  intro m n hmn
  have ht : (latticeTensorUnit a U P.module).app T
      ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] m) =
      (latticeTensorUnit a U P.module).app T
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] n) := by
    exact ((SheafOfModules.evaluation _ T).mapIso P.rationalization).toLinearEquiv.injective hmn
  let N := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    (latticeScalarMap a U) P.module
  let J := (Scheme.ProEt.topology X).over U
  have hz := Presheaf.equalizerSieve_mem J (toSheafify J N.presheaf)
    ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
      ((latticeScalarMap a U).hom.app T).hom] m)
    ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
      ((latticeScalarMap a U).hom.app T).hom] n) ht
  let F := P.module.val.presheaf ⋙ forget AddCommGrpCat.{u + 1}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J P.module.val.presheaf (forget AddCommGrpCat.{u + 1})
      P.module.isSheaf
  have heq : Presheaf.equalizerSieve (F := F) m n ∈ J T.unop := by
    apply J.transitive hz _
    intro V f hfz
    apply J.superset_covering _ (q.coversTop V)
    rintro W g ⟨i, ⟨t⟩⟩
    change F.map (g ≫ f).op m = F.map (g ≫ f).op n
    apply pairTensor_injective_at_basis a L U P q i t (ha (op W))
    have hfg := congrArg (fun x ↦ N.presheaf.map g.op x) hfz
    change N.presheaf.map g.op (N.presheaf.map f.op _) =
      N.presheaf.map g.op (N.presheaf.map f.op _) at hfg
    simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp] at hfg
    have hm := Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a U) P.module (g ≫ f).op) (1 : (S.over U).obj.obj T) m
    have hn := Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a U) P.module (g ≫ f).op) (1 : (S.over U).obj.obj T) n
    change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module (g ≫ f).op _ =
        SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
          (latticeScalarMap a U) P.module (g ≫ f).op _ at hfg
    change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module (g ≫ f).op
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m) = _ at hm
    change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module (g ≫ f).op
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] n) = _ at hn
    rw [map_one] at hm hn
    exact hm.symm.trans (hfg.trans hn)
  exact (((isSheaf_iff_isSheaf_of_type _ _).mp hF).isSeparated _ heq).ext
    (fun _ _ h ↦ h)

private theorem coefficientMap_injective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : (Over U)ᵒᵖ) :
    Function.Injective
      (((latticeScalarMap (integralLatticeCoefficientMap X l E) U).hom.app T).hom) := by
  intro f g h
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun s ↦ s.down x) h

private theorem pair_intertwining_unique
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P Q : IntegralLatticePair a L U) (e f : P.module ≅ Q.module)
    (he : SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module e.hom ≫ Q.rationalization.hom =
      P.rationalization.hom)
    (hf : SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module f.hom ≫ Q.rationalization.hom =
      P.rationalization.hom) : e = f := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  ext m
  apply pairEmbedding_injective a L U ha Q T
  exact (pairSection_naturality a L U e he T m).trans
    (pairSection_naturality a L U f hf T m).symm

/-- Embedded images classify pairs over an injective coefficient map.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, first local calculation.
(blueprint: lem-weil-pbc-lattice-pair-image-classification).
Proof: the tensor unit is injective locally in an integral basis, since tensoring
an injective scalar map with a free module is injective. Local injectivity of
sheafification and separatedness descend this to every section of each pair.
An intertwining isomorphism identifies the images by naturality of the tensor
unit. Conversely, equal images lift the embedding of one module uniquely through
the other's injective embedding; the lifts are linear and natural. The two lifts
are inverse, and agree with rationalization on pure tensors, hence everywhere.
The same injectivity makes every intertwining isomorphism unique. -/
theorem IntegralLatticePair.equivalent_iff_image_eq
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P Q : IntegralLatticePair a L U) :
    P.Equivalent Q ↔ ∀ T, P.image T = Q.image T := by
  constructor
  · exact fun h T ↦ pair_image_eq_of_equivalent a L U h T
  · exact pair_equivalent_of_image_eq a L U P Q
      (pairEmbedding_injective a L U ha P) (pairEmbedding_injective a L U ha Q)

/-- Intertwining integral isomorphisms are unique.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, first local calculation.
(blueprint: lem-weil-pbc-lattice-pair-image-classification).
Proof: both isomorphisms compose with the second pair's injective embedding to
the first pair's embedding. Injectivity on every section makes their components
identical; extensionality of morphisms and isomorphisms gives equality. -/
theorem IntegralLatticePair.intertwiningIso_unique
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P Q : IntegralLatticePair a L U) (e f : P.module ≅ Q.module)
    (he : SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module e.hom ≫
        Q.rationalization.hom = P.rationalization.hom)
    (hf : SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module f.hom ≫
        Q.rationalization.hom = P.rationalization.hom) : e = f :=
  pair_intertwining_unique a L U ha P Q e f he hf


/-- The image criterion for the specified integral coefficient inclusion.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, first local calculation.
(blueprint: lem-weil-pbc-lattice-pair-image-classification).
Proof: postcomposition by the inclusion A → E is injective on continuous
functions, including over empty objects. Apply the image classification for
an injective map of coefficient sheaves. -/
theorem integralLatticePair_equivalent_iff_image_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L' : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (P Q : IntegralLatticePair (integralLatticeCoefficientMap X l E) L' U) :
    P.Equivalent Q ↔ ∀ T, P.image T = Q.image T :=
  IntegralLatticePair.equivalent_iff_image_eq (integralLatticeCoefficientMap X l E)
    L' U (coefficientMap_injective U l E) P Q


end Classes

end LatticePairImages

section LatticeMatrixImages

open scoped Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- The ring homomorphism of constant coefficient sections.
Source: Bhatt--Scholze, Proposition 6.8.4(6), constant matrix coefficients
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeConstantRingHom (X : Scheme.{u}) (K : Type u)
    [TopologicalSpace K] [CommRing K] [IsTopologicalRing K] (V : X.ProEt) :
    K →+* (latticeCoefficientSheaf X K).obj.obj (op V) where
  toFun := latticeConstantCoefficient X K V
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

section MatrixImages

variable (X : Scheme.{u}) (K : Type u) [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K) (U : X.ProEt) (n : ℕ)

private theorem coefficientMap_constant (T : (Over U)ᵒᵖ) (a : A) :
    (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
      (op T.unop.left) (latticeConstantRingHom X A T.unop.left a) =
        latticeConstantRingHom X K T.unop.left (a : K) := rfl

private theorem matrixLatticeImage_integral_mul_subset
    (g : Matrix.GeneralLinearGroup (Fin n) K)
    (h : Matrix.GeneralLinearGroup (Fin n) A) (T : (Over U)ᵒᵖ) :
    matrixLatticeImage X K A U n (g * Matrix.GeneralLinearGroup.map A.subtype h) T ⊆
      matrixLatticeImage X K A U n g T := by
  let f := latticeConstantRingHom X K T.unop.left
  let fA := latticeConstantRingHom X A T.unop.left
  let φ := (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
    (op T.unop.left)
  rintro y ⟨b, rfl⟩
  let b' : Fin n → (latticeCoefficientSheaf X A).obj.obj (op T.unop.left) :=
    h.val.map fA *ᵥ b
  refine ⟨b', ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ∑ j, f (g.val i j) * φ (b' j) =
    ∑ j, f ((g * Matrix.GeneralLinearGroup.map A.subtype h).val i j) * φ (b j)
  have hv : (fun j ↦ φ (b' j)) = (h.val.map (f.comp A.subtype)) *ᵥ (fun j ↦ φ (b j)) := by
    funext j
    change φ (∑ k, fA (h.val j k) * b k) = _
    simp only [map_sum, map_mul, Matrix.mulVec, dotProduct, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [coefficientMap_constant X K A U]
    rfl
  change (g.val.map f *ᵥ (fun j ↦ φ (b' j))) i = _
  rw [hv, Matrix.mulVec_mulVec]
  change ((g.val.map f * h.val.map (f.comp A.subtype)) *ᵥ (fun j ↦ φ (b j))) i = _
  have hm : g.val.map f * h.val.map (f.comp A.subtype) =
      (g * Matrix.GeneralLinearGroup.map A.subtype h).val.map f := by
    change g.val.map f * (h.val.map A.subtype).map f =
      (g.val * h.val.map A.subtype).map f
    exact Matrix.map_mul.symm
  rw [hm]
  rfl

private theorem matrixLatticeImage_integral_mul
    (g : Matrix.GeneralLinearGroup (Fin n) K)
    (h : Matrix.GeneralLinearGroup (Fin n) A) (T : (Over U)ᵒᵖ) :
    matrixLatticeImage X K A U n (g * Matrix.GeneralLinearGroup.map A.subtype h) T =
      matrixLatticeImage X K A U n g T := by
  apply Set.Subset.antisymm (matrixLatticeImage_integral_mul_subset X K A U n g h T)
  have hh := matrixLatticeImage_integral_mul_subset X K A U n
    (g * Matrix.GeneralLinearGroup.map A.subtype h) h⁻¹ T
  simpa only [map_inv, mul_assoc, mul_inv_cancel, mul_one] using hh

/-- Equal integral matrix cosets have the same embedded lattice on every test object.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, construction of g A^n.
(blueprint: lem-weil-pbc-matrix-lattice-coset-invariance).
Proof: right multiplication by an integral matrix changes each integral coefficient
vector by its integral matrix action. The matrix multiplication formula identifies
its rational image with the original coordinate sum. The inverse integral matrix
proves equality of ranges. Equal left cosets differ by such a right multiplier. -/
theorem matrixLatticeImage_eq_of_coset_eq
    (g h : Matrix.GeneralLinearGroup (Fin n) K)
    (heq : (Quotient.mk _ g : integralMatrixCosets A n) = Quotient.mk _ h)
    (T : (Over U)ᵒᵖ) :
    matrixLatticeImage X K A U n g T = matrixLatticeImage X K A U n h T := by
  have hmem : g⁻¹ * h ∈ integralMatrixSubgroup A n :=
    (QuotientGroup.leftRel_apply).mp (Quotient.exact heq)
  obtain ⟨k, hk⟩ := hmem
  have hh : h = g * Matrix.GeneralLinearGroup.map A.subtype k := by
    rw [hk]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hh, matrixLatticeImage_integral_mul]


private theorem free_coordinate_basis (T : (Over U)ᵒᵖ) (i j : Fin n) :
    (SheafOfModules.freeπ (R := (latticeModuleRing X K).over U)
      (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
        ((SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
          (ULift.up j : ULift.{u + 1} (Fin n))).val.app T
            (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))) =
      if j = i then (1 : (latticeModuleRing X K).obj.obj (op T.unop.left)) else 0 := by
  classical
  have h := SheafOfModules.ιFree_freeπ (R := (latticeModuleRing X K).over U)
    (ULift.up i : ULift.{u + 1} (Fin n)) (ULift.up j)
  let one : (SheafOfModules.unit ((latticeModuleRing X K).over U)).val.obj T :=
    (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))
  have hh := congrArg (fun f ↦ f.val.app T one) h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] at hh
  by_cases hji : j = i
  · subst j
    simpa only [one, if_pos rfl, if_true, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using hh
  · have hij : (ULift.up j : ULift.{u + 1} (Fin n)) ≠ ULift.up i := by
      intro e
      exact hji (ULift.up_injective e)
    rw [if_neg hij] at hh
    rw [if_neg hji]
    exact hh

private theorem free_coordinate_sum (T : (Over U)ᵒᵖ)
    (c : Fin n → (latticeModuleRing X K).obj.obj (op T.unop.left)) (i : Fin n) :
    (SheafOfModules.freeπ (R := (latticeModuleRing X K).over U)
      (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
        (∑ j, c j •
          (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
            (ULift.up j : ULift.{u + 1} (Fin n))).val.app T
              (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))) = c i := by
  classical
  rw [map_sum]
  simp_rw [map_smul, free_coordinate_basis]
  simp


private noncomputable def matrixColumnSection
    (g : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ) (j : Fin n) :
    (latticeFreeSheaf X K U n).val.obj T :=
  ∑ i, latticeConstantCoefficient X K T.unop.left (g.val i j) •
    (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
      (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
        (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))

private theorem matrixColumnSection_mem
    (g : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ) (j : Fin n) :
    matrixColumnSection X K U n g T j ∈ matrixLatticeImage X K A U n g T := by
  classical
  refine ⟨fun k ↦ latticeConstantRingHom X A T.unop.left (if k = j then 1 else 0), ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ∑ k, latticeConstantRingHom X K T.unop.left (g.val i k) *
    ((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
      (op T.unop.left)) (latticeConstantRingHom X A T.unop.left
        (if k = j then 1 else 0)) = _
  simp only [apply_ite, map_one, map_zero, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

private theorem matrixColumn_coordinates
    (g h : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ) (j : Fin n)
    (heq : matrixLatticeImage X K A U n h T = matrixLatticeImage X K A U n g T) :
    ∃ b : Fin n → (latticeCoefficientSheaf X A).obj.obj (op T.unop.left),
      ∀ i, latticeConstantCoefficient X K T.unop.left (h.val i j) =
        ∑ k, latticeConstantCoefficient X K T.unop.left (g.val i k) *
          (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
            (op T.unop.left) (b k) := by
  have hmem := matrixColumnSection_mem X K A U n h T j
  rw [heq] at hmem
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, fun i ↦ ?_⟩
  have hh := congrArg (fun x ↦
    (SheafOfModules.freeπ (R := (latticeModuleRing X K).over U)
      (ULift.up i : ULift.{u + 1} (Fin n))).val.app T x) hb
  change _ = (SheafOfModules.freeπ (R := (latticeModuleRing X K).over U)
    (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
      (∑ k, latticeConstantCoefficient X K T.unop.left (h.val k j) •
        (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
          (ULift.up k : ULift.{u + 1} (Fin n))).val.app T
            (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))) at hh
  rw [free_coordinate_sum, free_coordinate_sum] at hh
  exact hh.symm


/-- Evaluation of continuous coefficient sections at a point.
Source: Bhatt--Scholze, Proposition 6.8.4(6), evaluation of matrix coefficients
(blueprint: lem-weil-pbc-matrix-lattice-coset-invariance). -/
noncomputable def latticeEvaluationRingHom (V : X.ProEt) (x : V.left) :
    (latticeCoefficientSheaf X K).obj.obj (op V) →+* K where
  toFun c := c.down x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem matrixChange_entries_integral
    (g h : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ) (x : T.unop.left.left)
    (heq : matrixLatticeImage X K A U n h T =
      matrixLatticeImage X K A U n g T) (i j : Fin n) :
    (g⁻¹ * h).val i j ∈ A := by
  obtain ⟨b, hb⟩ := matrixColumn_coordinates X K A U n g h T j heq
  let c : Fin n → K := fun k ↦ ((b k).down x : K)
  have hv : (fun k ↦ h.val k j) = g.val *ᵥ c := by
    funext k
    have hh := congrArg (latticeEvaluationRingHom X K T.unop.left x) (hb k)
    rw [map_sum] at hh
    simp only [map_mul] at hh
    exact hh
  have hid : (g⁻¹).val * g.val = 1 := congrArg Units.val (inv_mul_cancel g)
  have hh : (g⁻¹ * h).val i j = c i := by
    change ((g⁻¹).val *ᵥ (fun k ↦ h.val k j)) i = c i
    rw [hv, Matrix.mulVec_mulVec, hid, Matrix.one_mulVec]
  rw [hh]
  exact ((b i).down x).property


omit [TopologicalSpace K] [IsTopologicalRing K] in
private theorem integralMatrixSubgroup_mem_of_entries
    (g : Matrix.GeneralLinearGroup (Fin n) K)
    (hg : ∀ i j, g.val i j ∈ A) (hgi : ∀ i j, (g⁻¹).val i j ∈ A) :
    g ∈ integralMatrixSubgroup A n := by
  let m : Matrix (Fin n) (Fin n) A := fun i j ↦ ⟨g.val i j, hg i j⟩
  let mi : Matrix (Fin n) (Fin n) A := fun i j ↦ ⟨(g⁻¹).val i j, hgi i j⟩
  let f : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) K :=
    RingHom.mapMatrix A.subtype
  have hf : Function.Injective f := Matrix.map_injective Subtype.val_injective
  have hm : f m = g.val := rfl
  have hmi : f mi = (g⁻¹).val := rfl
  have hl : m * mi = 1 := by
    apply hf
    rw [map_mul, map_one, hm, hmi]
    exact congrArg Units.val (mul_inv_cancel g)
  have hr : mi * m = 1 := by
    apply hf
    rw [map_mul, map_one, hm, hmi]
    exact congrArg Units.val (inv_mul_cancel g)
  refine ⟨⟨m, mi, hl, hr⟩, ?_⟩
  apply Units.ext
  rfl

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- An invertible rational matrix is integral exactly when it and its inverse have integral entries.
Source: Bhatt--Scholze, Proposition 6.8.4(6), integral changes of basis
(blueprint: lem-weil-pbc-matrix-lattice-coset-invariance).
Proof: an integral invertible lift supplies both sets of entries. Conversely lift the two
matrices entrywise; injectivity of the integral inclusion proves their inverse equations. -/
theorem integralMatrixSubgroup_mem_iff (g : Matrix.GeneralLinearGroup (Fin n) K) :
    g ∈ integralMatrixSubgroup A n ↔
      (∀ i j, g.val i j ∈ A) ∧ (∀ i j, (g⁻¹).val i j ∈ A) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j ↦ (h.val i j).property, ?_⟩
    rw [← map_inv]
    exact fun i j ↦ ((h⁻¹).val i j).property
  · rintro ⟨hg, hgi⟩
    exact integralMatrixSubgroup_mem_of_entries K A n g hg hgi

/-- On a nonempty object, equality of constant lattice images detects the matrix coset.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, evaluation of constant lattices.
(blueprint: lem-weil-pbc-matrix-lattice-coset-invariance).
Proof: each column of h is an integral coefficient combination of the columns of g.
Evaluate at one point and multiply by g inverse: every entry of g inverse times h
belongs to A. Reverse g and h to obtain the same assertion for the inverse matrix.
These two integral matrices are mutually inverse over A, so g inverse times h
lies in the image of GL_n(A). This is precisely equality of left cosets gH and hH. -/
theorem matrixLatticeImage_coset_eq_of_eq
    (g h : Matrix.GeneralLinearGroup (Fin n) K) (hU : Nonempty U.left)
    (heq : matrixLatticeImage X K A U n g (op (Over.mk (𝟙 U))) =
      matrixLatticeImage X K A U n h (op (Over.mk (𝟙 U)))) :
    (Quotient.mk _ g : integralMatrixCosets A n) = Quotient.mk _ h := by
  obtain ⟨x⟩ := hU
  have hg : ∀ i j, (g⁻¹ * h).val i j ∈ A :=
    matrixChange_entries_integral X K A U n g h (op (Over.mk (𝟙 U))) x heq.symm
  have hgi : ∀ i j, ((g⁻¹ * h)⁻¹).val i j ∈ A := by
    simpa only [mul_inv_rev, inv_inv] using
      matrixChange_entries_integral X K A U n h g (op (Over.mk (𝟙 U))) x heq
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  exact integralMatrixSubgroup_mem_of_entries K A n (g⁻¹ * h) hg hgi


/-- Equality of constant lattice images at any nonempty slice object detects the coset.
Source: Bhatt--Scholze, Proposition 6.8.4(6), evaluation of constant lattices
(blueprint: lem-weil-pbc-matrix-lattice-coset-invariance).
Proof: evaluate the integral coordinates of each column at a point of the test object.
The change matrix and its inverse have integral entries, hence define an integral unit. -/
theorem matrixLatticeImage_coset_eq_of_eq_at
    (g h : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ)
    (hT : Nonempty T.unop.left.left)
    (heq : matrixLatticeImage X K A U n g T = matrixLatticeImage X K A U n h T) :
    (Quotient.mk _ g : integralMatrixCosets A n) = Quotient.mk _ h := by
  obtain ⟨x⟩ := hT
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  apply integralMatrixSubgroup_mem_of_entries K A n (g⁻¹ * h)
  · exact matrixChange_entries_integral X K A U n g h T x heq.symm
  · simpa only [mul_inv_rev, inv_inv] using
      matrixChange_entries_integral X K A U n h g T x heq

/-- On a nonempty object, constant matrix lattices are classified by their cosets.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, constant lattice comparison.
(blueprint: lem-weil-pbc-matrix-lattice-coset-invariance).
Proof: equality of cosets preserves images by an integral change of coordinates.
For the converse, specialize equality of images to the identity slice object and
evaluate there at a point. The two change matrices are integral inverses, which
identifies the cosets. -/
theorem matrixLatticeImage_coset_eq_iff
    (g h : Matrix.GeneralLinearGroup (Fin n) K) (hU : Nonempty U.left) :
    (Quotient.mk _ g : integralMatrixCosets A n) = Quotient.mk _ h ↔
      ∀ T, matrixLatticeImage X K A U n g T = matrixLatticeImage X K A U n h T := by
  constructor
  · exact fun heq T ↦ matrixLatticeImage_eq_of_coset_eq X K A U n g h heq T
  · exact fun heq ↦ matrixLatticeImage_coset_eq_of_eq X K A U n g h hU
      (heq (op (Over.mk (𝟙 U))))


end MatrixImages

end LatticeMatrixImages

section FreeExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
  (a : R ⟶ S) (U : X.ProEt) (I : Type (u + 1)) [Fintype I] [DecidableEq I]

private noncomputable def freeTensorSection (T : (Over U)ᵒᵖ) :
    (ModuleCat.extendScalars ((latticeScalarMap a U).hom.app T).hom).obj
      ((SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I).val.obj T) ≅
    (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I).val.obj T := by
  let φ : R.obj.obj (op T.unop.left) →+* S.obj.obj (op T.unop.left) :=
    ((latticeScalarMap a U).hom.app T).hom
  letI := φ.toAlgebra
  let eR : ((SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I).val.obj T) ≃ₗ[
        R.obj.obj (op T.unop.left)] (I → R.obj.obj (op T.unop.left)) :=
    SheafOfModules.freeSectionsLinearEquiv
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I T
  let eS : ((SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I).val.obj T) ≃ₗ[
        S.obj.obj (op T.unop.left)] (I → S.obj.obj (op T.unop.left)) :=
    SheafOfModules.freeSectionsLinearEquiv
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I T
  let e1 := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (S.obj.obj (op T.unop.left)) (S.obj.obj (op T.unop.left))) eR
  let e2 := TensorProduct.piRight (R.obj.obj (op T.unop.left))
    (S.obj.obj (op T.unop.left)) (S.obj.obj (op T.unop.left))
    (fun _ : I ↦ R.obj.obj (op T.unop.left))
  let e3 := LinearEquiv.piCongrRight (fun _ : I ↦
    TensorProduct.AlgebraTensorModule.rid (R.obj.obj (op T.unop.left))
      (S.obj.obj (op T.unop.left)) (S.obj.obj (op T.unop.left)))
  exact (e1.trans (e2.trans (e3.trans eS.symm))).toModuleIso

private theorem freeTensorSection_coordinate (T : (Over U)ᵒᵖ) (i : I)
    (b : (S.over U).obj.obj T)
    (m : (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I).val.obj T) :
    (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) i).val.app T
        ((freeTensorSection a U I T).hom
          (b ⊗ₜ[(R.over U).obj.obj T, ((latticeScalarMap a U).hom.app T).hom] m)) =
      b * ((latticeScalarMap a U).hom.app T)
        ((SheafOfModules.freeπ (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) i).val.app T m) := by
  let φ : R.obj.obj (op T.unop.left) →+* S.obj.obj (op T.unop.left) :=
    ((latticeScalarMap a U).hom.app T).hom
  let := φ.toAlgebra
  let eS := SheafOfModules.freeSectionsLinearEquiv
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)) I T
  change eS (eS.symm (fun j ↦ φ
    ((SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) j).val.app T m) *
        (show S.obj.obj (op T.unop.left) from b))) i = _
  rw [LinearEquiv.apply_symm_apply]
  change φ ((SheafOfModules.freeπ (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) i).val.app T m) *
      (show S.obj.obj (op T.unop.left) from b) =
        (show S.obj.obj (op T.unop.left) from b) * _
  exact mul_comm _ _

private noncomputable def freeTensorPresheafIso :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a U) (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I) ≅
    (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I).val := by
  refine PresheafOfModules.isoMk (freeTensorSection a U I) ?_
  intro T T' f
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (freeTensorSection a U I T').hom
    (SheafOfModules.changeOfRingsMap (latticeScalarMap a U)
      (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I) f
          ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
            ((latticeScalarMap a U).hom.app T).hom] m)) =
    (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I).val.map f
        ((freeTensorSection a U I T).hom
          ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
            ((latticeScalarMap a U).hom.app T).hom] m))
  rw [show SheafOfModules.changeOfRingsMap (latticeScalarMap a U)
      (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I) f
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m) =
      ((S.over U).obj.map f 1) ⊗ₜ[(R.over U).obj.obj T',
        ((latticeScalarMap a U).hom.app T').hom]
        ((SheafOfModules.free (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I).val.map f m) from
    Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap
      (latticeScalarMap a U) (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I) f) 1 m]
  rw [map_one]
  apply (SheafOfModules.freeSectionsLinearEquiv (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I T').injective
  funext i
  change (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) i).val.app T'
        ((freeTensorSection a U I T').hom _) =
    (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) i).val.app T' _
  rw [freeTensorSection_coordinate, one_mul]
  have hs := PresheafOfModules.naturality_apply
    (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) i).val f
      ((freeTensorSection a U I T).hom
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m))
  rw [hs, freeTensorSection_coordinate, one_mul]
  have hr : (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) i).val.app T'
        ((SheafOfModules.free (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I).val.map f m) =
      (R.over U).obj.map f ((SheafOfModules.freeπ (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) i).val.app T m) :=
    PresheafOfModules.naturality_apply _ f m
  rw [hr]
  exact ConcreteCategory.congr_hom ((latticeScalarMap a U).hom.naturality f) _

private noncomputable def freeTensorSheafIso :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1}
      (latticeScalarMap a U) (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I) ≅
    SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I :=
  (PresheafOfModules.sheafification (𝟙 ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)).obj)).mapIso
      (freeTensorPresheafIso a U I) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)).obj)).counit.app
        (SheafOfModules.free (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I))

private theorem freeTensorSheafIso_formula (T : (Over U)ᵒᵖ)
    (x : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a U) (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I)).obj T) :
    (freeTensorSheafIso a U I).hom.val.app T
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (latticeScalarMap a U) (SheafOfModules.free (R := (sheafCompose _
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I))).app T x) =
      (freeTensorSection a U I T).hom x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)).obj)
  let Q := SheafOfModules.free (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I
  let q := (freeTensorPresheafIso a U I).hom
  have hn := congrArg (fun z ↦ z.app T x) (adj.unit_naturality q)
  have hc (y : Q.val.obj T) :=
    congrArg (fun z ↦ z.app T y) (adj.right_triangle_components Q)
  change (adj.counit.app Q).val.app T
    (((PresheafOfModules.sheafification (𝟙 ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)).obj)).map q).val.app T
        ((adj.unit.app _).app T x)) = _
  exact (congrArg ((adj.counit.app Q).val.app T) hn).trans
    (hc ((freeTensorSection a U I T).hom x))

omit [Fintype I] in
private theorem freeBasisCoordinate
    (B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (T : (Over U)ᵒᵖ) (i j : I) :
    (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (B.over U)) j).val.app T
        ((SheafOfModules.ιFree (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (B.over U)) i).val.app T
            (1 : (B.over U).obj.obj T)) =
      if i = j then (1 : (B.over U).obj.obj T) else 0 := by
  have h := SheafOfModules.ιFree_freeπ (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (B.over U)) j i
  let one : (SheafOfModules.unit ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (B.over U))).val.obj T :=
    (1 : (B.over U).obj.obj T)
  have hh := congrArg (fun f ↦ f.val.app T one) h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] at hh
  by_cases hij : i = j
  · subst i
    simpa only [one, if_pos rfl, if_true, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using hh
  · rw [if_neg hij] at hh ⊢
    exact hh

omit [Fintype I] [DecidableEq I] in
/-- Scalar extension of a finite free coefficient-module sheaf has its standard basis.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, scalar extension of A^n.
(blueprint: lem-weil-pbc-lattice-free-scalar-extension).
Proof: identify sections of each finite free sheaf with the finite product of its
coefficient ring. Tensor product commutes with that finite product, and S tensor_R R
is S. The resulting sectionwise isomorphisms respect restrictions by the coefficient
map's naturality. Sheafify this presheaf isomorphism and use the sheafification counit
on the free target sheaf. Naturality of the unit and the adjunction triangle prove
the formula on tensors, and the coordinate projections give the basis normalization.
This construction also applies to empty objects and the empty index type. -/
theorem exists_latticeFreeScalarExtensionIso [Finite I] :
    ∃ e : SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (latticeScalarMap a U) (SheafOfModules.free (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I) ≅
        SheafOfModules.free (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I,
      ∀ (T : (Over U)ᵒᵖ) (i : I), e.hom.val.app T
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
              (latticeScalarMap a U) (SheafOfModules.free (R := (sheafCompose _
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) I))).app T
          ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
            ((latticeScalarMap a U).hom.app T).hom]
              ((SheafOfModules.ιFree (R := (sheafCompose _
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)) i).val.app T
                  (1 : (R.over U).obj.obj T)))) =
        (SheafOfModules.ιFree (R := (sheafCompose _
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) i).val.app T
            (1 : (S.over U).obj.obj T) := by
  classical
  let := Fintype.ofFinite I
  refine ⟨freeTensorSheafIso a U I, ?_⟩
  intro T i
  rw [freeTensorSheafIso_formula]
  apply (SheafOfModules.freeSectionsLinearEquiv (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) I T).injective
  funext j
  change (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) j).val.app T
        ((freeTensorSection a U I T).hom _) =
    (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)) j).val.app T _
  rw [freeTensorSection_coordinate, one_mul, freeBasisCoordinate, freeBasisCoordinate]
  split_ifs <;> simp only [map_one, map_zero]

end FreeExtension

section ConstantMatrix

open scoped Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

variable (X : Scheme.{u}) (K : Type u) [CommRing K]
  [TopologicalSpace K] [IsTopologicalRing K] (U : X.ProEt) (n : ℕ)

private noncomputable def finiteFreeCoordinates (T : (Over U)ᵒᵖ) :
    (latticeFreeSheaf X K U n).val.obj T ≃ₗ[
      (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)]
        (Fin n → (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) := by
  let e : (latticeFreeSheaf X K U n).val.obj T ≃ₗ[
      (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)]
        (ULift.{u + 1} (Fin n) → (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) :=
    SheafOfModules.freeSectionsLinearEquiv (R := (latticeModuleRing X K).over U)
      (ULift.{u + 1} (Fin n)) T
  exact e.trans (LinearEquiv.funCongrLeft _ _ Equiv.ulift.symm)

private noncomputable def constantMatrixSectionIso
    (g : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ) :
    (latticeFreeSheaf X K U n).val.obj T ≅ (latticeFreeSheaf X K U n).val.obj T :=
  ((finiteFreeCoordinates X K U n T).trans
    ((Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map
        (latticeConstantRingHom X K T.unop.left) g)).toLinearEquiv.trans
        (finiteFreeCoordinates X K U n T).symm)).toModuleIso

private theorem constantMatrixSectionIso_coordinates
    (g : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ)
    (m : (latticeFreeSheaf X K U n).val.obj T) (i : Fin n) :
    finiteFreeCoordinates X K U n T ((constantMatrixSectionIso X K U n g T).hom m) i =
      ∑ j, latticeConstantCoefficient X K T.unop.left (g.val i j) *
        finiteFreeCoordinates X K U n T m j := by
  change finiteFreeCoordinates X K U n T
    ((finiteFreeCoordinates X K U n T).symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem finiteFreeCoordinates_naturality {T T' : (Over U)ᵒᵖ} (f : T ⟶ T')
    (m : (latticeFreeSheaf X K U n).val.obj T) (i : Fin n) :
    finiteFreeCoordinates X K U n T'
      ((latticeFreeSheaf X K U n).val.map f m) i =
    (latticeCoefficientSheaf X K).obj.map ((Over.forget U).op.map f)
      (finiteFreeCoordinates X K U n T m i) :=
  PresheafOfModules.naturality_apply (SheafOfModules.freeπ
    (R := (latticeModuleRing X K).over U) (ULift.up i)).val f m

private noncomputable def constantMatrixSheafIso
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    latticeFreeSheaf X K U n ≅ latticeFreeSheaf X K U n := by
  let p : (latticeFreeSheaf X K U n).val ≅ (latticeFreeSheaf X K U n).val := by
    refine PresheafOfModules.isoMk (constantMatrixSectionIso X K U n g) ?_
    intro T T' f
    ext m
    apply (finiteFreeCoordinates X K U n T').injective
    funext i
    change finiteFreeCoordinates X K U n T'
      ((constantMatrixSectionIso X K U n g T').hom
        ((latticeFreeSheaf X K U n).val.map f m)) i =
      finiteFreeCoordinates X K U n T'
        ((latticeFreeSheaf X K U n).val.map f
          ((constantMatrixSectionIso X K U n g T).hom m)) i
    rw [constantMatrixSectionIso_coordinates, finiteFreeCoordinates_naturality,
      constantMatrixSectionIso_coordinates, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, finiteFreeCoordinates_naturality]
    rfl
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso p

private theorem constantMatrixSheafIso_coordinates
    (g : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ)
    (m : (latticeFreeSheaf X K U n).val.obj T) (i : Fin n) :
    finiteFreeCoordinates X K U n T ((constantMatrixSheafIso X K U n g).hom.val.app T m) i =
      ∑ j, latticeConstantCoefficient X K T.unop.left (g.val i j) *
        finiteFreeCoordinates X K U n T m j :=
  constantMatrixSectionIso_coordinates X K U n g T m i

private theorem finiteFreeCoordinates_sum (T : (Over U)ᵒᵖ)
    (c : Fin n → (latticeModuleRing X K).obj.obj (op T.unop.left)) (i : Fin n) :
    finiteFreeCoordinates X K U n T
      (∑ j, c j • (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
        (ULift.up j : ULift.{u + 1} (Fin n))).val.app T
          (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))) i = c i := by
  change (SheafOfModules.freeπ (R := (latticeModuleRing X K).over U)
    (ULift.up i : ULift.{u + 1} (Fin n))).val.app T _ = _
  rw [map_sum]
  simp_rw [map_smul]
  have hb (j : Fin n) :
      (SheafOfModules.freeπ (R := (latticeModuleRing X K).over U)
        (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
          ((SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
            (ULift.up j : ULift.{u + 1} (Fin n))).val.app T
              (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))) =
        if j = i then (1 : (latticeModuleRing X K).obj.obj (op T.unop.left)) else 0 := by
    have hh := freeBasisCoordinate U (ULift.{u + 1} (Fin n))
      (latticeCoefficientSheaf X K) T (ULift.up j) (ULift.up i)
    by_cases h : j = i
    · subst j
      rw [if_pos rfl] at hh ⊢
      exact hh
    · have h' : (ULift.up j : ULift.{u + 1} (Fin n)) ≠ ULift.up i := by
        intro e
        exact h (ULift.up_injective e)
      rw [if_neg h'] at hh
      rw [if_neg h]
      exact hh
  simp_rw [hb]
  simp

private theorem finiteFree_locallyFree (A : Subring K) :
    (latticeFreeSheaf X A U n).IsFiniteLocallyFree := by
  let q := (SheafOfModules.free.generatingSections
    (R := (latticeModuleRing X A).over U) (ULift.{u + 1} (Fin n))).localGeneratorsData
  have hq : q.IsLocallyFreeData := by
    dsimp [q]
    infer_instance
  have hf : q.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite (ULift.{u + 1} (Fin n))
    infer_instance
  exact { exists_localGeneratorsData := ⟨q, hq, hf⟩ }

end ConstantMatrix
section ConstantPairs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A constant matrix lattice is the embedded image of an actual finite free lattice pair.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, the construction g A^n.
(blueprint: lem-weil-pbc-constant-matrix-lattice-pair).
Proof: take the free integral coefficient-module sheaf. Its scalar extension is the
free rational sheaf by the explicit finite-product tensor comparison. Compose that
comparison with the constant matrix automorphism and the inverse trivialization.
The standard free generators witness finite local freeness. Coordinate projections
identify the resulting embedding with the sums defining matrixLatticeImage, and
surjectivity of the integral coordinate equivalence identifies their ranges. -/
theorem exists_matrixIntegralLatticePair (X : Scheme.{u}) (K : Type u) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K) (U : X.ProEt) (n : ℕ)
    (L : SheafOfModules.{u + 1} (latticeModuleRing X K))
    (e : L.over U ≅ latticeFreeSheaf X K U n)
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    ∃ P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype
        continuous_subtype_val) L U,
      ∀ T, Set.image (e.hom.val.app T) (P.image T) = matrixLatticeImage X K A U n g T := by
  let a := latticeCoefficientSheafMap X A.subtype continuous_subtype_val
  let t := freeTensorSheafIso a U (ULift.{u + 1} (Fin n))
  let P : IntegralLatticePair a L U :=
    { module := latticeFreeSheaf X A U n
      locallyFree := finiteFree_locallyFree X K U n A
      rationalization := t ≪≫ constantMatrixSheafIso X K U n g ≪≫ e.symm }
  refine ⟨P, ?_⟩
  intro T
  let j : (latticeFreeSheaf X A U n).val.obj T →
      (latticeFreeSheaf X K U n).val.obj T := fun m ↦
    (constantMatrixSheafIso X K U n g).hom.val.app T
      (t.hom.val.app T
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((latticeModuleRing X K).over U).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (latticeScalarMap a U) (latticeFreeSheaf X A U n))).app T
              ((1 : (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) ⊗ₜ[
                (latticeCoefficientSheaf X A).obj.obj (op T.unop.left),
                ((latticeScalarMap a U).hom.app T).hom] m)))
  change Set.image (e.hom.val.app T)
    (Set.range fun m ↦ e.inv.val.app T (j m)) = _
  rw [← Set.range_comp']
  have he (z : (latticeFreeSheaf X K U n).val.obj T) :
      e.hom.val.app T (e.inv.val.app T z) = z := by
    have hh := congrArg (fun f ↦ f.val.app T z) e.inv_hom_id
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using hh
  change Set.range (fun m ↦ e.hom.val.app T (e.inv.val.app T (j m))) = _
  simp_rw [he]
  have hj (m : (latticeFreeSheaf X A U n).val.obj T) :
      j m = ∑ i : Fin n,
        (∑ k : Fin n, latticeConstantCoefficient X K T.unop.left (g.val i k) *
          (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
            (op T.unop.left) (finiteFreeCoordinates X A U n T m k)) •
        (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
          (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
            (1 : (latticeModuleRing X K).obj.obj (op T.unop.left)) := by
    apply (finiteFreeCoordinates X K U n T).injective
    funext i
    change finiteFreeCoordinates X K U n T
      ((constantMatrixSheafIso X K U n g).hom.val.app T _) i = _
    rw [constantMatrixSheafIso_coordinates, finiteFreeCoordinates_sum]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    change (SheafOfModules.freeπ (R := (latticeModuleRing X K).over U)
      (ULift.up k : ULift.{u + 1} (Fin n))).val.app T
        (t.hom.val.app T _) = _
    have ht := freeTensorSheafIso_formula a U (ULift.{u + 1} (Fin n)) T
      ((1 : ((latticeCoefficientSheaf X K).over U).obj.obj T) ⊗ₜ[
        ((latticeCoefficientSheaf X A).over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] m)
    have htc := congrArg (fun z ↦
      (SheafOfModules.freeπ (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((latticeCoefficientSheaf X K).over U))
            (ULift.up k : ULift.{u + 1} (Fin n))).val.app T z) ht
    have hn := freeTensorSection_coordinate a U (ULift.{u + 1} (Fin n)) T
      (ULift.up k) 1 m
    rw [one_mul] at hn
    exact htc.trans hn
  apply Set.Subset.antisymm
  · rintro y ⟨m, rfl⟩
    exact ⟨finiteFreeCoordinates X A U n T m, (hj m).symm⟩
  · rintro y ⟨b, rfl⟩
    refine ⟨(finiteFreeCoordinates X A U n T).symm b, ?_⟩
    change j ((finiteFreeCoordinates X A U n T).symm b) = _
    calc
      _ = _ := hj _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [LinearEquiv.apply_symm_apply]

end ConstantPairs

end AlgebraicGeometry.ProEtale

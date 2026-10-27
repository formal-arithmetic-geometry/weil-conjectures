module

public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.Algebra.Homology.KFlatTotalTensorModel
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.AlgebraicGeometry.SpaceKFlatPullbackCounit
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Unbounded pullback and K-flat coordinates on algebraic spaces

Source: Stacks Project, spaces-perfect.tex, equation-bc preceding Tag 0DKG;
Cohomology on Sites, Tags 06YS and 07A4
(blueprint: def-sfb-space-derived-pullback-models).

The pullback and its total left derived functor are the recorded ones of
def-sfb-space-derived-tensor-pullback.
Tensor representative comparisons are inherited from the existing normalized datum.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.AlgebraicSpace.SingleComplex

variable {S : Scheme.{u}}

/-- Tensor pullback transported along the existing affine-basis equivalences: the
recorded small-model pullback of def-sfb-space-derived-tensor-pullback, not a copy.
Source: Stacks 03G8, 03D7 (blueprint: def-sfb-space-derived-pullback-models). -/
abbrev pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Y.SmallModules ⥤ X.SmallModules :=
  smallModuleTensorPullback f

variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]

/-- The universal total left derived tensor pullback: the recorded
`derivedTensorPullback` of def-sfb-space-derived-tensor-pullback, with a common
localization universe.
Source: Stacks 06YS (blueprint: def-sfb-space-derived-pullback-models). -/
abbrev derivedPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.DerivedModules ⥤ X.DerivedModules :=
  derivedTensorPullback.{u, w, w} f

/-- The counit specifying this total left derived functor.
Source: Stacks 06YS (blueprint: def-sfb-space-derived-pullback-models). -/
def counit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ derivedPullback f ⟶ smallTensorPullbackComplex f :=
  (smallTensorPullbackComplex f).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ))

/-- Flat-term K-flat representatives, with no bounds on the degrees.
Source: Stacks 06YS (blueprint: def-sfb-space-derived-pullback-models). -/
def FlatKFlat (X : AlgebraicSpace S) (P : CochainComplex X.SmallModules ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf) P ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf) (P.X n)

/-- The total tensor complex on the existing small ringed model.
Source: Stacks 07A4 (blueprint: def-sfb-space-derived-pullback-models). -/
def total (X : AlgebraicSpace S) :=
  SheafOfModules.KFlatTotalTensorModel.total X.smallStructureSheaf

/-- The already normalized K-flat derived tensor of small-model modules.
Source: Stacks 06YS, 07A4 (blueprint: def-sfb-space-derived-pullback-models). -/
def tensor (X : AlgebraicSpace S) := X.derivedDualityModel.closed.tensor

/-- Its specified K-flat representative comparison, inherited from the shared model.
Source: Stacks 06YS (blueprint: def-sfb-space-derived-pullback-models). -/
def tensorModel (X : AlgebraicSpace S) (P Q : CochainComplex X.SmallModules ℤ)
    (hP : FlatKFlat X P) (hQ : FlatKFlat X Q) :
    DerivedCategory.Q.obj ((total X).obj (P, Q)) ≅
      (tensor X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  X.derivedDualityModel.models.iso X.smallEtaleModelTopology X.smallStructureSheaf
    X.derivedDualityModel.closed P Q hP.1 hQ.1

/-- K-flat coordinates of the given derived coefficient map, retaining its counit equation.
Source: Stacks 0DKG, 06YS (blueprint: def-sfb-space-derived-pullback-models). -/
structure Coordinates {X X' : AlgebraicSpace S} (g' : X' ⟶ X)
    (K : X.DerivedModules) (K' : X'.DerivedModules)
    (φ : (derivedPullback g').obj K ⟶ K') where
  P : CochainComplex X.SmallModules ℤ
  N : CochainComplex X'.SmallModules ℤ
  flatKFlat : FlatKFlat X P
  e : DerivedCategory.Q.obj P ≅ K
  e' : DerivedCategory.Q.obj N ≅ K'
  counit_isIso : IsIso ((counit g').app P)
  t : ((pullback g').mapHomologicalComplex (.up ℤ)).obj P ⟶ N
  represents : (counit g').app P ≫
      DerivedCategory.Q.map t ≫ e'.hom = (derivedPullback g').map e.hom ≫ φ

/-- Such coordinates exist, so a condition quantified over them is never vacuous.
Source: Stacks 06YS, 06YY; Mathlib DerivedCategory.left_fac
(blueprint: def-sfb-space-derived-pullback-models).
Proof: choose a flat-term K-flat resolution P of a representative of K. The
derived counit is invertible on P. Compose its inverse with the localized
coefficient map and an inverse representative identification for K'. Mathlib's
left-fraction factorization expresses this map as Q(t) followed by the inverse
of a localized quasi-isomorphism. Use its target as N; compose the inverse
quasi-isomorphism with the original representative identification for e'. The
fraction identity and the counit inverse identities give the required equation. -/
theorem coordinates_nonempty {X X' : AlgebraicSpace S} (g' : X' ⟶ X)
    (K : X.DerivedModules) (K' : X'.DerivedModules)
    (φ : (derivedPullback g').obj K ⟶ K') : Nonempty (Coordinates g' K K' φ) := by
  classical
  let G : CochainComplex X.SmallModules ℤ := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := X.smallStructureSheaf) G
  have hflat' : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf) (P.X n) := by
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso X.smallStructureSheaf (P.X n)).symm
      (hflat n)
  have hp' : IsIso (DerivedCategory.Q.map p) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hp
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hc : IsIso ((counit g').app P) :=
    smallTensorPullbackComplex_counit_isIso_of_flatKFlat g' P hP hflat'
  let N₀ : CochainComplex X'.SmallModules ℤ := DerivedCategory.Q.objPreimage K'
  let e₀ : DerivedCategory.Q.obj N₀ ≅ K' := DerivedCategory.Q.objObjPreimageIso K'
  let a : DerivedCategory.Q.obj
      (((pullback g').mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj N₀ :=
    inv ((counit g').app P) ≫ (derivedPullback g').map e.hom ≫ φ ≫ e₀.inv
  obtain ⟨N, t, s, hs, ha⟩ := DerivedCategory.left_fac a
  refine ⟨{
    P := P
    N := N
    flatKFlat := ⟨hP, hflat'⟩
    e := e
    e' := (asIso (DerivedCategory.Q.map s)).symm ≪≫ e₀
    counit_isIso := hc
    t := t
    represents := ?_ }⟩
  change (counit g').app P ≫ DerivedCategory.Q.map t ≫
    (inv (DerivedCategory.Q.map s) ≫ e₀.hom) = _
  rw [← Category.assoc (DerivedCategory.Q.map t), ← ha]
  simp [a]

end AlgebraicGeometry.AlgebraicSpace.SingleComplex

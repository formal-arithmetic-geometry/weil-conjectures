module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineGroupDistributionCalculus
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization

/-! # Relative external sections over a commutative ring

Source: Stacks Project, Varieties, Tag 0BED, the map preceding
`equation-kunneth-on-cech`; Groupoids, Tag 03LF, the action-groupoid specialization.
(blueprint: def-sfb-relative-external-sections)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.RelativeExternalSections

/-- Ordinary global sections with scalars restricted from the base ring.
Source: Stacks 0BED (blueprint: def-sfb-relative-external-sections). -/
def sections (R : CommRingCat.{u}) (X : Over (Spec R)) (F : X.left.Modules) : ModuleCat R :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ X.hom.appTop).hom).obj
    (F.val.obj (op ⊤))

/-- The actual section-normalized pullback, restricted to the top open.
Source: Stacks 0096 (blueprint: def-sfb-relative-external-sections). -/
def pullSection {X Y : Scheme.{u}} (a : X ⟶ Y) (F : Y.Modules) (s : Γ(F, ⊤)) :
    Γ((Scheme.Modules.tensorPullback a).obj F, ⊤) :=
  ((Scheme.Modules.tensorPullback a).obj F).presheaf.map
    (homOfLE a.preimage_top.ge).op (Scheme.Modules.tensorPullbackSection a F ⊤ s)

/-- The external tensor sheaf on the chosen fibre product, with no new tensor construction.
Source: Stacks 0BED (blueprint: def-sfb-relative-external-sections). -/
abbrev coefficients {R : CommRingCat.{u}} {X Y : Over (Spec R)}
    (F : X.left.Modules) (G : Y.left.Modules) : (X ⊗ Y).left.Modules :=
  (Scheme.Modules.tensorPullback (fst X Y).left).obj F ⊗
    (Scheme.Modules.tensorPullback (snd X Y).left).obj G

/-- The external product of two ordinary sections.
Source: Stacks 0BED (blueprint: def-sfb-relative-external-sections). -/
def pure {R : CommRingCat.{u}} {X Y : Over (Spec R)}
    (F : X.left.Modules) (G : Y.left.Modules) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    Γ(coefficients F G, ⊤) :=
  Scheme.Modules.tmulSection (pullSection (fst X Y).left F s) (pullSection (snd X Y).left G t)

/-- Comparison across a commutative square, from uniquely normalized adjunctions.
Source: Stacks 0097 (blueprint: def-sfb-relative-external-sections). -/
def square {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Z)
    (c : W ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d) (F : Z.Modules) :
    (Scheme.Modules.tensorPullback a).obj ((Scheme.Modules.tensorPullback b).obj F) ≅
      (Scheme.Modules.tensorPullback c).obj ((Scheme.Modules.tensorPullback d).obj F) :=
  (Scheme.Modules.tensorPullbackSectionComp a b).symm.app F ≪≫
    eqToIso (congrArg (fun q ↦ (Scheme.Modules.tensorPullback q).obj F) h) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp c d).app F

/-- The normalized tensor comparison already characterized on all local tensor sections.
Source: Stacks 01CD (blueprint: def-sfb-relative-external-sections). -/
def pullTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.tensorPullback f).obj (M ⊗ N) ≅
      (Scheme.Modules.tensorPullback f).obj M ⊗ (Scheme.Modules.tensorPullback f).obj N :=
  Classical.choose (Scheme.Modules.module_pullback_tensor f) M N

/-- The canonical comparison for pullback of external coefficients.
Source: Stacks 0097 and 01CD (blueprint: def-sfb-relative-external-sections). -/
def pullCoefficients {R : CommRingCat.{u}} {X Y X' Y' : Over (Spec R)}
    (a : X' ⟶ X) (b : Y' ⟶ Y) (F : X.left.Modules) (G : Y.left.Modules) :
    (Scheme.Modules.tensorPullback (a ⊗ₘ b).left).obj (coefficients F G) ≅
      coefficients ((Scheme.Modules.tensorPullback a.left).obj F)
        ((Scheme.Modules.tensorPullback b.left).obj G) :=
  pullTensor _ _ _ ≪≫ tensorIso
    (square _ _ _ _ (congrArg (fun q ↦ q.left) (tensorHom_fst a b)) F)
    (square _ _ _ _ (congrArg (fun q ↦ q.left) (tensorHom_snd a b)) G)

/-- The diagonal action on the chosen product, constructed by the product universal property.
Source: Stacks 03LF (blueprint: def-sfb-relative-external-sections). -/
def diagonalAction {R : CommRingCat.{u}} (H X Y : Over (Spec R))
    [GrpObj H] [ModObj H X] [ModObj H Y] : H ⊗ (X ⊗ Y) ⟶ X ⊗ Y :=
  lift (H ◁ fst X Y ≫ ModObj.smul (M := H) (X := X))
    (H ◁ snd X Y ≫ ModObj.smul (M := H) (X := Y))

/-- Pulling the two linearizations to the same group variable and tensoring them.
The supplied maps are the existing target-to-source descent isomorphisms.
Source: Stacks 03LF and 01CD (blueprint: def-sfb-relative-external-sections). -/
def externalDescent {R : CommRingCat.{u}} {H X Y : Over (Spec R)}
    [GrpObj H] [ModObj H X] [ModObj H Y] (F : X.left.Modules) (G : Y.left.Modules)
    (βF : (Scheme.Modules.tensorPullback (ModObj.smul (M := H) (X := X)).left).obj F ≅
      (Scheme.Modules.tensorPullback (snd H X).left).obj F)
    (βG : (Scheme.Modules.tensorPullback (ModObj.smul (M := H) (X := Y)).left).obj G ≅
      (Scheme.Modules.tensorPullback (snd H Y).left).obj G) :
    (Scheme.Modules.tensorPullback (diagonalAction H X Y).left).obj (coefficients F G) ≅
      (Scheme.Modules.tensorPullback (snd H (X ⊗ Y)).left).obj (coefficients F G) :=
  pullTensor _ _ _ ≪≫ tensorIso
    (square _ _ _ _ (congrArg (fun q ↦ q.left) (lift_fst
      (H ◁ fst X Y ≫ ModObj.smul (M := H) (X := X))
      (H ◁ snd X Y ≫ ModObj.smul (M := H) (X := Y)))) F ≪≫
      (Scheme.Modules.tensorPullback (H ◁ fst X Y).left).mapIso βF ≪≫
      (square _ _ _ _ (congrArg (fun q ↦ q.left) (whiskerLeft_snd H (fst X Y))) F))
    (square _ _ _ _ (congrArg (fun q ↦ q.left) (lift_snd
      (H ◁ fst X Y ≫ ModObj.smul (M := H) (X := X))
      (H ◁ snd X Y ≫ ModObj.smul (M := H) (X := Y)))) G ≪≫
      (Scheme.Modules.tensorPullback (H ◁ snd X Y).left).mapIso βG ≪≫
      (square _ _ _ _ (congrArg (fun q ↦ q.left) (whiskerLeft_snd H (snd X Y))) G)) ≪≫
    (pullTensor _ _ _).symm

/-- The existing groupoid descent isomorphism with its tensor-pullback interface exposed.
Source: Stacks 03LF (blueprint: def-sfb-relative-external-sections). -/
def descent {R : CommRingCat.{u}} {H X : Over (Spec R)} [GrpObj H] [ModObj H X]
    {D : EquivariantCoherent.ActionGroupoidModel H X}
    (M : Scheme.GroupoidModule (EquivariantCoherent.source H X)
      (EquivariantCoherent.target H X) (EquivariantCoherent.identityArrow H X)
      (EquivariantCoherent.inverseArrow H X) D.comp D.laws) :
    (Scheme.Modules.tensorPullback (ModObj.smul (M := H) (X := X)).left).obj M.moduleObj ≅
      (Scheme.Modules.tensorPullback (snd H X).left).obj M.moduleObj :=
  (EquivariantCoherent.pullbackIso _).symm.app M.moduleObj ≪≫ M.beta ≪≫
    (EquivariantCoherent.pullbackIso _).app M.moduleObj

/-- The existing coordinate coaction equations with the over-scheme base made explicit.
Source: Stacks 022S (blueprint: def-sfb-relative-external-sections). -/
def IsRational {R : CommRingCat.{u}} (H : Over (Spec R)) [GrpObj H] [IsAffine H.left]
    {M : Type u} [AddCommGroup M] [Module R M] (ρ : M →ₗ[R] M ⊗[R] Γ(H.left, ⊤)) : Prop :=
  @BorelDistributions.IsCoordinateCoaction R H.left ⟨H.hom⟩
    (inferInstanceAs (GrpObj H)) inferInstance M _ _ ρ

/-- The antipode of the canonical coordinate Hopf algebra, with the over-scheme base explicit.
Source: Stacks 022S; Mathlib Group/Affine (blueprint: def-sfb-relative-external-sections). -/
def coordinateAntipode {R : CommRingCat.{u}} (H : Over (Spec R)) [GrpObj H] [IsAffine H.left] :
    Γ(H.left, ⊤) →ₗ[R] Γ(H.left, ⊤) :=
  letI : HopfAlgebra R Γ(H.left, ⊤) :=
    @BorelDistributions.coordinateHopfInstance R H.left ⟨H.hom⟩
      (inferInstanceAs (GrpObj H)) inferInstance
  HopfAlgebra.antipode R

/-- A rational coaction is induced by descent if each finite tensor presentation gives
exactly the descended action-pullback section. The action is a left action, so the right
coaction `ρ(s) = ∑ sᵢ ⊗ cᵢ` is the one of `(h·s)(x) = s(h⁻¹x) = ∑ cᵢ(h) sᵢ(x)`: the action
pullback is `∑ S(cᵢ) sᵢ`, with `S` the antipode. Without `S` the coassociativity of
`IsRational` would fail for every noncommutative `H`. No section base-change isomorphism
is assumed.
Source: Stacks 03LF, affine translation (blueprint: def-sfb-relative-external-sections). -/
def IsInduced {R : CommRingCat.{u}} (H X : Over (Spec R)) [GrpObj H] [IsAffine H.left]
    (F : X.left.Modules) (a : (H ⊗ X).left ⟶ X.left)
    (β : (Scheme.Modules.tensorPullback a).obj F ≅
      (Scheme.Modules.tensorPullback (snd H X).left).obj F)
    (ρ : sections R X F →ₗ[R] sections R X F ⊗[R] Γ(H.left, ⊤)) : Prop :=
  IsRational H ρ ∧ ∀ (s : sections R X F) (n : ℕ)
    (si : Fin n → sections R X F) (ci : Fin n → Γ(H.left, ⊤)),
      ρ s = ∑ i, si i ⊗ₜ[R] ci i →
      β.hom.app ⊤ (pullSection a F s) =
        ∑ i, ((fst H X).left.appTop (coordinateAntipode H (ci i))) •
          pullSection (snd H X).left F (si i)

end AlgebraicGeometry.RelativeExternalSections

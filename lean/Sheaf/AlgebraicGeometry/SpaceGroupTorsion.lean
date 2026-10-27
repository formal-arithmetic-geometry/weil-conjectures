module

public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Torsion of commutative group algebraic spaces

Source: Deligne, Le lemme de Gabber, Sections 1.1 and 3.5.2, printed pp.131 and 140.
(blueprint: def-sfb-space-group-torsion)
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj

namespace AlgebraicGeometry.AlgebraicSpace

/-- The given group law, packaged without changing its functor of points.
Source: Deligne 1.1 (blueprint: def-sfb-space-group-torsion). -/
def CommutativeSpaceGroup.points {S : Scheme.{u}} {N : AlgebraicSpace S}
    (H : CommutativeSpaceGroup N) : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} := by
  letI (T : (Over S)ᵒᵖ) : CommGroup (N.obj.obj.obj T) := H.group T
  exact {
    obj := fun T ↦ CommGrpCat.of (N.obj.obj.obj T)
    map := fun f ↦ CommGrpCat.ofHom {
      toFun := N.obj.obj.map f
      map_one' := H.map_one f
      map_mul' := H.map_mul f }
    map_id := fun T ↦ by ext x; exact congrArg (fun f ↦ f x) (N.obj.obj.map_id T)
    map_comp := fun f g ↦ by
      ext x
      exact congrArg (fun k ↦ k x) (N.obj.obj.map_comp f g) }

/-- A semiabelian fibre is a scheme group model with the shared semiabelian predicate.
The model isomorphism preserves the given group law, not only the underlying space.
Source: Deligne 1.1 (blueprint: def-sfb-space-group-torsion). -/
def HasSemiabelianSpaceFibres {S : Scheme.{u}} {N : AlgebraicSpace S}
    (H : CommutativeSpaceGroup N) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    ∃ (G : Grp (Over (Spec (.of K)))) (hc : IsCommMonObj G.X),
      @HasSemiabelianGeometricFibres _ G hc ∧
      Nonempty ((Over.map s).op ⋙ H.points ⋙ forget₂ CommGrpCat GrpCat ≅ yonedaGrpObj G.X)

/-- Over the specified open the group space is represented by an abelian scheme.
Smoothness is already imposed on the ambient space; the model is proper and every
geometric fibre is connected. The isomorphism identifies its actual group law.
Source: Deligne 1.1 and 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
def IsAbelianOn {S V : Scheme.{u}} {N : AlgebraicSpace S}
    (H : CommutativeSpaceGroup N) (j : V ⟶ S) : Prop :=
  ∃ (A : Grp (Over V)), IsProper A.X.hom ∧ Smooth A.X.hom ∧
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (v : Spec (.of K) ⟶ V),
      ConnectedSpace ((Over.pullback v).obj A.X).left) ∧
    Nonempty ((Over.map j).op ⋙ H.points ⋙ forget₂ CommGrpCat GrpCat ≅ yonedaGrpObj A.X)

/-- The canonical cyclic-coefficient module of torsion elements, in the coefficient universe.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
def spaceTorsionModule (n : ℕ) (A : CommGrpCat.{u}) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)) := by
  let B := AddSubgroup.torsionBy (Additive A) (n : ℤ)
  letI := AddSubgroup.torsionBy.zmodModule (A := Additive A) (n := n)
  exact (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{u + 1} (ZMod n) ≃+* ZMod n).toRingHom).obj
    (ModuleCat.of (ZMod n) (ULift.{u + 1} B))

/-- Restriction on torsion elements is the original group homomorphism.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
def spaceTorsionMap (n : ℕ) {A B : CommGrpCat.{u}} (f : A ⟶ B) :
    spaceTorsionModule n A ⟶ spaceTorsionModule n B := by
  letI := AddSubgroup.torsionBy.zmodModule (A := Additive A) (n := n)
  letI := AddSubgroup.torsionBy.zmodModule (A := Additive B) (n := n)
  let g : Additive A →+ Additive B := f.hom.toAdditive
  let k : AddSubgroup.torsionBy (Additive A) (n : ℤ) →+
      AddSubgroup.torsionBy (Additive B) (n : ℤ) :=
    { toFun := fun x ↦ ⟨g x, by
        change (n : ℤ) • g x = 0
        rw [← map_zsmul]
        have hx : (n : ℤ) • (x : Additive A) = 0 := x.property
        rw [hx, map_zero]⟩
      map_zero' := by ext; exact g.map_zero
      map_add' := by intro x y; ext; exact g.map_add x y }
  exact (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{u + 1} (ZMod n) ≃+* ZMod n).toRingHom).map
    (ModuleCat.ofHom
      ((ULift.moduleEquiv : ULift.{u + 1} _ ≃ₗ[ZMod n] _).symm.toLinearMap.comp
        ((k.toZModLinearMap n).comp
          (ULift.moduleEquiv : ULift.{u + 1} _ ≃ₗ[ZMod n] _).toLinearMap)))

/-- The actual torsion-section presheaf on the small etale site.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
def spaceTorsionPresheaf {S : Scheme.{u}} {N : AlgebraicSpace S}
    (H : CommutativeSpaceGroup N) (n : ℕ) :
    S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)) where
  obj T := spaceTorsionModule n (H.points.obj ((Scheme.Etale.forget S).op.obj T))
  map f := spaceTorsionMap n (H.points.map ((Scheme.Etale.forget S).op.map f))
  map_id T := by
    change spaceTorsionMap n (H.points.map (𝟙 _)) = _
    rw [H.points.map_id]
    ext x
    rfl
  map_comp f g := by
    change spaceTorsionMap n (H.points.map
      (((Scheme.Etale.forget S).op.map f) ≫ ((Scheme.Etale.forget S).op.map g))) = _
    rw [H.points.map_comp]
    ext x
    rfl

/-- Torsion sections form a sheaf: the group space is an fppf sheaf, hence an etale
sheaf; torsion sections glue uniquely because the equation n*x=0 is local. The
cyclic scalar action is sectionwise and commutes with every restriction.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
theorem spaceTorsionPresheaf_isSheaf {S : Scheme.{u}} {N : AlgebraicSpace S}
    (H : CommutativeSpaceGroup N) (n : ℕ) :
    Presheaf.IsSheaf S.smallEtaleTopology (spaceTorsionPresheaf H n) := by
  sorry

/-- The sheaf has exactly the torsion sections, with no choice of a sheaf model.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
def spaceTorsionSheaf {S : Scheme.{u}} {N : AlgebraicSpace S}
    (H : CommutativeSpaceGroup N) (n : ℕ) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) :=
  ⟨spaceTorsionPresheaf H n, spaceTorsionPresheaf_isSheaf H n⟩

/-- A group-space isomorphism over a base isomorphism induces its actual map on torsion.
The components apply the given group isomorphism to the torsion element.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
def spaceTorsionTransport {S S' : Scheme.{u}} (h : S ≅ S')
    {N : AlgebraicSpace S} {N' : AlgebraicSpace S'}
    (H : CommutativeSpaceGroup N) (H' : CommutativeSpaceGroup N')
    (e : H.points ≅ (Over.map h.hom).op ⋙ H'.points) (n : ℕ) :
    spaceTorsionSheaf H n ⟶
      (Etale.localizationRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) h.hom inferInstance).obj
          (spaceTorsionSheaf H' n) :=
  ⟨{ app := fun T ↦ spaceTorsionMap n (e.hom.app ((Scheme.Etale.forget S).op.obj T))
     naturality := by
       intro T U f
       ext x
       apply ULift.ext
       apply Subtype.ext
       exact congrArg (fun a ↦ a.hom x.down.val) (e.hom.naturality
         ((Scheme.Etale.forget S).op.map f)) }⟩

/-- The constant rank-r label sheaf; r=0 and n=1 are included.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
abbrev torsionLabels (S : Scheme.{u}) (n r : ℕ) :=
  (constantSheaf S.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))).obj
      (ModuleCat.of (ULift.{u + 1} (ZMod n)) (Fin r → ULift.{u + 1} (ZMod n)))

/-- Restriction of constant labels uses the identity map on their coefficient module.
Source: Deligne 3.5.2 (blueprint: def-sfb-space-group-torsion). -/
def torsionLabelsRestriction {S V : Scheme.{u}} (j : V ⟶ S) [Etale j] (n r : ℕ) :
    (Etale.localizationRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j inferInstance).obj
        (torsionLabels S n r) ≅ torsionLabels V n r :=
  ((Etale.upperStarIsoLocalizationRestriction _ j inferInstance).app
    (torsionLabels S n r)).symm ≪≫
    (Etale.constantSheafCompUpperStarIso (ULift.{u + 1} (ZMod n)) j).app
      (ModuleCat.of (ULift.{u + 1} (ZMod n)) (Fin r → ULift.{u + 1} (ZMod n)))

end AlgebraicGeometry.AlgebraicSpace

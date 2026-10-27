/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationGZero
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # Homogeneous vector bundles with specified coordinates

Source: Andersen, The strong linkage principle (1980), pp.55--56; Milne,
Algebraic Groups (2017), Section 18c and 22.29--22.30, 22.48.
(blueprint: def-sfb-homogeneous-vector-bundle)

## Main definitions

- `System`: homogeneous sheaves, coordinates, maps and inverse-action linearization.
- `cohomology`: existing cohomology with zero in negative degrees.
- `IsNaturalCoaction`: normalization by canonical pullback maps.

All coordinate changes and action maps are specified on arbitrary test schemes.
Existence, finite local freeness and rationality of cohomology are not fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry.HomogeneousVectorBundle
open EquivariantCoherent RationalHighestWeight Scheme.Modules

variable {F : Type u} [Field F]

/-- A linear coordinate trivialization, with the existing section scalar action
explicitly transported to algΓ's bundled ring. The instance is confined to this
expression, so it cannot interfere with unrelated scalar inference.
Source: Milne, Section 18c. (blueprint: def-sfb-homogeneous-vector-bundle) -/
abbrev Coordinates (Z : Over (Spec (.of F))) (L : Z.left.Modules) (V : ModuleCat.{u} F) :=
  letI : Module (RhoSection.Coordinate Z) Γ(L, ⊤) :=
    inferInstanceAs (Module Γ(Z.left, ⊤) Γ(L, ⊤))
  Γ(L, ⊤) ≃ₗ[RhoSection.Coordinate Z] RhoSection.Coordinate Z ⊗[F] V

/-- Pullback of coordinate functions respects the actual structural scalars on
both the canonical Hopf algebra and algΓ. Only the proof of scalar compatibility
is postponed; the function is appTop.
Source: Milne, Section 4a; Mathlib Group/Affine.
(blueprint: def-sfb-homogeneous-vector-bundle)
Proof: apply global sections to b followed by the structure map of B equalling the
structure map of Z. Naturality of the Spec/global-sections isomorphism identifies
the two scalar maps, including the canonical affine identification in the Hopf API. -/
theorem pointEvaluation_commutes {B : Grp (Over (Spec (.of F)))} [IsAffine B.X.left]
    {Z : Over (Spec (.of F))} (b : Z ⟶ B.X) (a : F) :
    b.left.appTop.hom (algebraMap F (coordinateAlgebra B) a) =
      algebraMap F (RhoSection.Coordinate Z) a := by
  sorry

/-- The canonical evaluation map with its exact scalar structures exposed.
Source: Milne, Section 4a. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def pointEvaluation {B : Grp (Over (Spec (.of F)))} [IsAffine B.X.left]
    {Z : Over (Spec (.of F))} (b : Z ⟶ B.X) :
    coordinateAlgebra B →ₐ[F] RhoSection.Coordinate Z :=
  { b.left.appTop.hom with commutes' := pointEvaluation_commutes b }

/-- Evaluate a coaction on a scheme-valued point and extend scalars. This is the
actual tensor action, not a freely chosen matrix representation.
Source: Milne, Section 4a. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def pointAction {B : Grp (Over (Spec (.of F)))} [IsAffine B.X.left]
    (M : Representation F B.X) {Z : Over (Spec (.of F))} (b : Z ⟶ B.X) :
    RhoSection.Coordinate Z ⊗[F] M.space →ₗ[RhoSection.Coordinate Z]
      RhoSection.Coordinate Z ⊗[F] M.space :=
  extendComparison
    (TensorProduct.lift (((TensorProduct.mk F (RhoSection.Coordinate Z) M.space).flip).compl₂
      (pointEvaluation b).toLinearMap) ∘ₗ M.coaction)

/-- Transport sections along an equality of the displayed base maps.
Source: Milne, Section 18c. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def sectionCast {Z Q : Over (Spec (.of F))} {x y : Z ⟶ Q} (h : x = y)
    (L : Q.left.Modules) :
    Γ((Scheme.Modules.pullback x.left).obj L, ⊤) →
      Γ((Scheme.Modules.pullback y.left).obj L, ⊤) :=
  cast (congrArg (fun t : Z ⟶ Q ↦ (Γ((Scheme.Modules.pullback t.left).obj L, ⊤) : Type u)) h)

/-- Pull a coefficient isomorphism back with the canonical composition transports.
Source: Stacks 01F7; Milne, Section 18c.
(blueprint: def-sfb-homogeneous-vector-bundle) -/
def pullIso {Z Y Q : Over (Spec (.of F))} (h : Z ⟶ Y) (a b : Y ⟶ Q)
    (L : Q.left.Modules)
    (e : (Scheme.Modules.pullback a.left).obj L ≅ (Scheme.Modules.pullback b.left).obj L) :
    (Scheme.Modules.pullback (h ≫ a).left).obj L ≅
      (Scheme.Modules.pullback (h ≫ b).left).obj L :=
  ((Scheme.Modules.pullbackComp h.left a.left).app L).symm ≪≫
    (Scheme.Modules.pullback h.left).mapIso e ≪≫
      (Scheme.Modules.pullbackComp h.left b.left).app L

/-- The inverse-action map, so its effect on sections is f(g) mapping to f(s inverse g).
Source: Milne, Definition 22.21. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def inverseAction (S : Grp (Over (Spec (.of F)))) (Q : Over (Spec (.of F)))
    (a : ModObj S.X Q) : S.X ⊗ Q ⟶ Q :=
  lift (fst S.X Q ≫ GrpObj.inv) (snd S.X Q) ≫ a.smul

/-- Pullback in Zariski sheaf cohomology: exact inverse image on Ext, followed by
its canonical adjoint coefficient map. No arbitrary cohomology map is supplied.
Source: Stacks 01F7 and 02KH. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def pullH {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (i : ℕ) (v : L.H i) :
    ((Scheme.Modules.pullback f).obj L).H i :=
  Sheaf.H.map (coeff f ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)) i
    (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj L) i v)

/-- A simultaneous associated-sheaf construction, with its maps and inverse-action
linearization fixed by trivial coordinates. Natural coordinates on every test scheme
are the pullback trivialization; the B-law is exactly f(gb)=b inverse f(g).
Source: Andersen, pp.55--56; Milne, Section 18c and 22.29--22.30.
(blueprint: def-sfb-homogeneous-vector-bundle) -/
structure System (S B : Grp (Over (Spec (.of F)))) [IsAffine B.X.left]
    (iB : B ⟶ S) (Q : Over (Spec (.of F))) (π : S.X ⟶ Q) where
  L : Representation F B.X → Q.left.Modules
  orbit : ∀ (Z : Over (Spec (.of F))) (g : Z ⟶ S.X) (b : Z ⟶ B.X),
    (g * (b ≫ iB.hom.hom)) ≫ π = g ≫ π
  coordinate : ∀ (M : Representation F B.X) (Z : Over (Spec (.of F))) (g : Z ⟶ S.X),
    Coordinates Z ((Scheme.Modules.pullback (g ≫ π).left).obj (L M)) M.space
  coordinate_natural : ∀ (M : Representation F B.X) (Z R : Over (Spec (.of F)))
    (f : R ⟶ Z) (g : Z ⟶ S.X)
    (σ : Γ((Scheme.Modules.pullback (g ≫ π).left).obj (L M), ⊤)),
    coordinate M R (f ≫ g) (AssociatedCharacterLineBundle.pullSection f (g ≫ π) (L M) σ) =
      TensorProduct.map (((algΓ (.of F)).map f).unop.hom.toLinearMap) LinearMap.id
        (coordinate M Z g σ)
  coordinate_orbit : ∀ (M : Representation F B.X) (Z : Over (Spec (.of F)))
    (g : Z ⟶ S.X) (b : Z ⟶ B.X)
    (σ : Γ((Scheme.Modules.pullback (g ≫ π).left).obj (L M), ⊤)),
    coordinate M Z (g * (b ≫ iB.hom.hom)) (sectionCast (orbit Z g b).symm (L M) σ) =
      pointAction M b⁻¹ (coordinate M Z g σ)
  map : ∀ (M N : Representation F B.X) (f : M.space →ₗ[F] N.space),
    IsRepresentationMap M N f → (L M ⟶ L N)
  map_coordinate : ∀ (M N : Representation F B.X) (f : M.space →ₗ[F] N.space)
    (hf : IsRepresentationMap M N f) (Z : Over (Spec (.of F))) (g : Z ⟶ S.X)
    (σ : Γ((Scheme.Modules.pullback (g ≫ π).left).obj (L M), ⊤)),
    coordinate N Z g (((Scheme.Modules.pullback (g ≫ π).left).map (map M N f hf)).app ⊤ σ) =
      f.baseChange (RhoSection.Coordinate Z) (coordinate M Z g σ)
  action : ModObj S.X Q
  action_coordinate : ∀ (Z : Over (Spec (.of F))) (s g : Z ⟶ S.X),
    lift s (g ≫ π) ≫ action.smul = (s * g) ≫ π
  linearization : ∀ M : Representation F B.X,
    (Scheme.Modules.pullback (inverseAction S Q action).left).obj (L M) ≅
      (Scheme.Modules.pullback (snd S.X Q).left).obj (L M)
  linearization_coordinate : ∀ (M : Representation F B.X) (Z : Over (Spec (.of F)))
    (s g : Z ⟶ S.X)
    (h₁ : lift s (g ≫ π) ≫ inverseAction S Q action = (s⁻¹ * g) ≫ π)
    (h₂ : lift s (g ≫ π) ≫ snd S.X Q = g ≫ π)
    (σ : Γ((Scheme.Modules.pullback
      (lift s (g ≫ π) ≫ inverseAction S Q action).left).obj (L M), ⊤)),
    coordinate M Z g (sectionCast h₂ (L M)
      ((pullIso (lift s (g ≫ π)) (inverseAction S Q action) (snd S.X Q)
        (L M) (linearization M)).hom.app ⊤ σ)) =
      coordinate M Z (s⁻¹ * g) (sectionCast h₁ (L M) σ)

/-- Integer-indexed cohomology with negative degrees set to the zero module.
Nonnegative degrees are the existing Zariski sheaf cohomology, with the given
structural scalar map, rather than an arbitrary vector space.
Source: Andersen, p.55. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def cohomology (Q : Over (Spec (.of F))) (L : Q.left.Modules) (i : ℤ) : ModuleCat.{u} F :=
  if i < 0 then ModuleCat.of F (Fin 0 → F) else ModuleCat.of F (HOver Q.hom L i.toNat)

/-- Identity pullback is a bijection on the actual coordinate rings.
Source: Milne, Section 3a. (blueprint: def-sfb-homogeneous-vector-bundle)
Proof: pointEvaluation has underlying function appTop of the identity morphism.
The global-sections functor maps an identity to the identity, so its function
is bijective. The scalar-compatibility proof changes no data. -/
theorem coordinateEquiv_bijective (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left] :
    Function.Bijective (pointEvaluation (𝟙 S.X)) := by
  sorry

/-- The identity on coordinate functions, bridging the existing Hopf and algΓ
scalar structures. Its inverse is determined uniquely by bijectivity.
Source: Milne, Section 3a. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def coordinateEquiv (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left] :
    coordinateAlgebra S ≃ₗ[F] RhoSection.Coordinate S.X :=
  LinearEquiv.ofBijective (pointEvaluation (𝟙 S.X)).toLinearMap (coordinateEquiv_bijective S)

/-- The actual regular left coaction on the existing regular-function space:
comultiplication, inversion in the first factor, and interchange of factors.
The identity coordinate comparison keeps algΓ's scalar structure on functions
and the canonical Hopf structure on coaction coefficients. Evaluation gives f(s inverse g).
Source: Milne, Definition 22.21. (blueprint: def-sfb-homogeneous-vector-bundle) -/
def regularLeftCoaction (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left] :
    RhoSection.Coordinate S.X →ₗ[F] RhoSection.Coordinate S.X ⊗[F] coordinateAlgebra S :=
  (coordinateEquiv S).toLinearMap.rTensor (coordinateAlgebra S) ∘ₗ
    (TensorProduct.comm F (coordinateAlgebra S) (coordinateAlgebra S)).toLinearMap ∘ₗ
    (HopfAlgebra.antipode F (A := coordinateAlgebra S)).rTensor (coordinateAlgebra S) ∘ₗ
      Coalgebra.comul (R := F) (A := coordinateAlgebra S) ∘ₗ (coordinateEquiv S).symm.toLinearMap

/-- The universal-element normalization of the natural cohomology coaction.
The right side is the canonical flat-base-change coefficient map, characterized
on pure tensors. The inverse action fixes the left-action convention.
Source: Andersen, pp.55--56; Stacks 02KH; Milne, Definition 22.21.
(blueprint: def-sfb-homogeneous-vector-bundle) -/
def IsNaturalCoaction {S B : Grp (Over (Spec (.of F)))}
    [IsAffine S.X.left] [IsAffine B.X.left]
    {iB : B ⟶ S} {Q : Over (Spec (.of F))} {π : S.X ⟶ Q}
    (D : System S B iB Q π) (M : Representation F B.X) (i : ℕ)
    (c : HOver Q.hom (D.L M) i →ₗ[F]
      HOver Q.hom (D.L M) i ⊗[F] coordinateAlgebra S) : Prop :=
  ∀ (v : HOver Q.hom (D.L M) i) (n : ℕ)
    (vi : Fin n → HOver Q.hom (D.L M) i) (ai : Fin n → coordinateAlgebra S),
    c v = ∑ j, vi j ⊗ₜ[F] ai j →
    H.map (D.linearization M).hom i (pullH (inverseAction S Q D.action).left (D.L M) i v) =
      ∑ j, H.map (((Scheme.Modules.pullback (snd S.X Q).left).obj (D.L M)).smulHom
        ((fst S.X Q).left.appTop (ai j))) i (pullH (snd S.X Q).left (D.L M) i (vi j))

end AlgebraicGeometry.HomogeneousVectorBundle

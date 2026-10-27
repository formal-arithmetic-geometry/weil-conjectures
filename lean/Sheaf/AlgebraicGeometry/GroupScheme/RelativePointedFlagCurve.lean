module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Relative pointed flag-curve data

Source: Conrad, Reductive group schemes, Proposition 4.2.7, proof, pp.123--124,
and Theorem 2.3.6, pp.72--75 (blueprint: def-sfb-relative-pointed-flag-curve).

The coset criterion and fppf local lifts specify the represented sheafification.
The automorphism clause uses all test schemes, including nonreduced schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The quotient is the fppf sheaf of right cosets: two sections have the same image
exactly when their ratio belongs to B, and every quotient section lifts fppf locally.
Representable functors on schemes are fppf sheaves, so these conditions specify the
sheafification of the pointwise right-coset presheaf.
Source: Conrad, Theorem 2.3.6, pp.72--75
(blueprint: def-sfb-relative-pointed-flag-curve). -/
def IsRelativeRightCosetQuotient {S : Scheme.{u}} {G B : Grp (Over S)}
    (i : B ⟶ G) {X : Over S} (p : G.X ⟶ X) : Prop :=
  (∀ (V : Over S) (g h : V ⟶ G.X),
    g ≫ p = h ≫ p ↔ ∃ b : V ⟶ B.X, g⁻¹ * h = b ≫ i.hom.hom) ∧
  ∀ (V : Over S) (x : V ⟶ X),
    ∃ (I : Type u) (W : I → Over S) (f : ∀ j, W j ⟶ V),
      Presieve.ofArrows (fun j ↦ (W j).left) (fun j ↦ (f j).left) ∈
        Scheme.fppfPrecoverage V.left ∧
      ∀ j, ∃ g : W j ⟶ G.X, g ≫ p = f j ≫ x

/-- On the test scheme V, the action identifies G(V) with all V-automorphisms of X_V.
The displayed formula characterizes the equivalence by the original action on every
further test scheme, hence specifies the induced homomorphism, with its naturality.
The adjunction counit is the first projection X_V → X.
Source: Conrad, Proposition 4.2.7, proof, pp.123--124
(blueprint: def-sfb-relative-pointed-flag-curve). -/
def IsFlagCurveAutomorphismAction {S : Scheme.{u}} (G : Grp (Over S))
    (X : Over S) [ModObj G.X X] {V : Scheme.{u}} (f : V ⟶ S) : Prop :=
  ∃ ρ : (((Over.map f).obj (𝟙_ (Over V))) ⟶ G.X) ≃*
      Aut ((Over.pullback f).obj X),
    ∀ (g : ((Over.map f).obj (𝟙_ (Over V))) ⟶ G.X)
      (W : Over V) (x : W ⟶ (Over.pullback f).obj X),
      (Over.map f).map (x ≫ (ρ g).hom) ≫ (Over.mapPullbackAdj f).counit.app X =
        lift ((Over.map f).map (toUnit W) ≫ g)
          ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app X) ≫
            ModObj.smul (M := G.X) (X := X)

/-- Compatibility of the pulled action with the original action by the first projections.
Source: Conrad, Proposition 4.2.7, proof, pp.123--124
(blueprint: def-sfb-relative-pointed-flag-curve). -/
def IsFlagCurveActionPullback {S : Scheme.{u}} (G : Grp (Over S))
    (X : Over S) [ModObj G.X X] {S' : Scheme.{u}} (f : S' ⟶ S)
    [ModObj ((Over.pullback f).mapGrp.obj G).X ((Over.pullback f).obj X)] : Prop :=
  ∀ (V : Over S') (g : V ⟶ ((Over.pullback f).mapGrp.obj G).X)
    (x : V ⟶ (Over.pullback f).obj X),
    (Over.map f).map (g • x) ≫ (Over.mapPullbackAdj f).counit.app X =
      lift ((Over.map f).map g ≫ (Over.mapPullbackAdj f).counit.app G.X)
        ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app X) ≫
          ModObj.smul (M := G.X) (X := X)

/-- The data and all compatibilities of the pointed relative Borel quotient curve.
The section is the image of the identity. The action is a scheme action, not merely an
abstract action on geometric points. All pullback quotients are specified, and the
pulled action and section are characterized by their first projections.
Source: Conrad, Proposition 4.2.7, proof, pp.123--124; Theorem 2.3.6, pp.72--75
(blueprint: def-sfb-relative-pointed-flag-curve). -/
structure RelativePointedFlagCurve {S : Scheme.{u}} (T G : Grp (Over S)) (iT : T ⟶ G) where
  /-- The smooth closed subgroup. -/
  B : Grp (Over S)
  /-- Its inclusion. -/
  i : B ⟶ G
  /-- Closedness retains the entire scheme structure. -/
  closed : IsClosedImmersion i.hom.hom.left
  /-- The given torus is contained in B. -/
  contains : ∃ j : T ⟶ B, j ≫ i = iT
  /-- Smoothness over the base. -/
  smoothB : Smooth B.X.hom
  /-- Connected, hence nonempty, geometric fibres. -/
  connectedB : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
    ConnectedSpace (((Over.pullback t).mapGrp.obj B).X.left)
  /-- The representing scheme over the base. -/
  X : Over S
  /-- Smoothness of the quotient curve. -/
  smoothX : Smooth X.hom
  /-- Properness of the quotient curve. -/
  properX : IsProper X.hom
  /-- The quotient map. -/
  p : G.X ⟶ X
  /-- The left scheme action, including its unit and associativity identities. -/
  [action : ModObj G.X X]
  /-- The distinguished section. -/
  σ : 𝟙_ (Over S) ⟶ X
  /-- It is the image of the group identity. -/
  identitySection : σ = η[G.X] ≫ p
  /-- Left multiplication induces the action on the quotient. -/
  equivariant : ∀ (V : Over S) (g h : V ⟶ G.X), (g * h) ≫ p = g • (h ≫ p)
  /-- The identity coset is fixed by the whole subgroup on every test scheme. -/
  fixed : ∀ (V : Over S) (b : V ⟶ B.X),
    (b ≫ i.hom.hom) • ((1 : V ⟶ G.X) ≫ p) = (1 : V ⟶ G.X) ≫ p
  /-- The quotient after every base change is the quotient by the pulled subgroup. -/
  quotient : ∀ (S' : Scheme.{u}) (f : S' ⟶ S),
    IsRelativeRightCosetQuotient ((Over.pullback f).mapGrp.map i)
      ((Over.pullback f).map p)
  /-- The canonical pulled action and identity section commute with base change. -/
  baseChange : ∀ (S' : Scheme.{u}) (f : S' ⟶ S),
    ∃ a' : ModObj ((Over.pullback f).mapGrp.obj G).X ((Over.pullback f).obj X),
      @IsFlagCurveActionPullback S G X action S' f a' ∧
      ∃ σ' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj X,
        σ' = η[((Over.pullback f).mapGrp.obj G).X] ≫ (Over.pullback f).map p ∧
        (Over.map f).map σ' ≫ (Over.mapPullbackAdj f).counit.app X =
          toUnit ((Over.map f).obj (𝟙_ (Over S'))) ≫ σ
  /-- Projective-line geometric fibres and the full geometric automorphism sheaf. -/
  geometric : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
    Nonempty ((Over.pullback t).obj X ≅
      (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of Ω))).asOver (Spec (.of Ω))) ∧
    ∀ V : Over (Spec (.of Ω)), @IsFlagCurveAutomorphismAction S G X action
      V.left (V.hom ≫ t)

end AlgebraicGeometry

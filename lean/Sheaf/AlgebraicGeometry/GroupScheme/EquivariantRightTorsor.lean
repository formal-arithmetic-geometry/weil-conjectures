module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Equivariant represented right torsors and fibre isomorphisms

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions,
Section 2, Claim 1 and Lemma 3.6, pp.2, 6.
(blueprint: def-sfb-equivariant-right-torsor-fibre-isomorphism)

The right torsor is the existing `RepresentedRightTorsor`. The extra left action
is Mathlib's `ModObj`. Fibre isomorphisms are actual isomorphisms of pullbacks.
Their equivariance is expressed by preservation of the graphs of the two actions,
using the inclusions into the original torsors. This avoids choosing fibre actions
or trivializations: at an invariant fibre the action graphs determine those actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A represented right H-torsor with a commuting left G-action covering the
specified base-action morphism b. The left action has its unit and associativity
laws in `ModObj`; no trivialization is part of this structure.
Source: Alper--Halpern-Leistner--Heinloth, Section 2, Claim 1, p.2
(blueprint: def-sfb-equivariant-right-torsor-fibre-isomorphism). -/
structure EquivariantRightTorsor {B : Scheme.{u}} (G H : Grp (Over B))
    (Y : Over B) (b : G.X ⊗ Y ⟶ Y) where
  torsor : RepresentedRightTorsor H Y
  leftAction : ModObj G.X torsor.space
  covers : leftAction.smul ≫ torsor.projection = (G.X ◁ torsor.projection) ≫ b
  commutes : ∀ (T : Over B) (z : T ⟶ G.X) (p : T ⟶ torsor.space) (h : T ⟶ H.X),
    lift z (lift p h ≫ torsor.action) ≫ leftAction.smul =
      lift (lift z p ≫ leftAction.smul) h ≫ torsor.action

namespace EquivariantRightTorsor

variable {B : Scheme.{u}} {G H : Grp (Over B)} {Y : Over B} {b : G.X ⊗ Y ⟶ Y}

/-- An isomorphism over Y respecting the given left G- and right H-actions.
Source: Alper--Halpern-Leistner--Heinloth, Section 2, Claim 3 and Lemma 3.6
(blueprint: def-sfb-equivariant-right-torsor-fibre-isomorphism). -/
structure EquivariantIso (P Q : EquivariantRightTorsor G H Y b) where
  iso : P.torsor.space ≅ Q.torsor.space
  over : iso.hom ≫ Q.torsor.projection = P.torsor.projection
  left_equivariant : ∀ (T : Over B) (z : T ⟶ G.X) (p : T ⟶ P.torsor.space),
    (lift z p ≫ P.leftAction.smul) ≫ iso.hom =
      lift z (p ≫ iso.hom) ≫ Q.leftAction.smul
  right_equivariant : ∀ (T : Over B) (p : T ⟶ P.torsor.space) (h : T ⟶ H.X),
    (lift p h ≫ P.torsor.action) ≫ iso.hom =
      lift (p ≫ iso.hom) h ≫ Q.torsor.action

/-- An equivariant isomorphism of the actual fibres at a base point o. The equations
preserve action graphs after the canonical fibre inclusions. If o is fixed by G,
these are exactly equivariance for the induced fibre actions: each translate has
one and only one lift to the fibre, since its inclusion is a monomorphism. The
isomorphism is over B, hence automatically over the terminal object o has as domain.
Source: Alper--Halpern-Leistner--Heinloth, Lemma 3.6, p.6
(blueprint: def-sfb-equivariant-right-torsor-fibre-isomorphism). -/
structure FibreIso (P Q : EquivariantRightTorsor G H Y b)
    (o : 𝟙_ (Over B) ⟶ Y) where
  iso : pullback P.torsor.projection o ≅ pullback Q.torsor.projection o
  left_equivariant : ∀ (T : Over B) (z : T ⟶ G.X)
    (p p' : T ⟶ pullback P.torsor.projection o),
    lift z (p ≫ pullback.fst P.torsor.projection o) ≫ P.leftAction.smul =
      p' ≫ pullback.fst P.torsor.projection o →
    lift z (p ≫ iso.hom ≫ pullback.fst Q.torsor.projection o) ≫ Q.leftAction.smul =
      p' ≫ iso.hom ≫ pullback.fst Q.torsor.projection o
  right_equivariant : ∀ (T : Over B) (h : T ⟶ H.X)
    (p p' : T ⟶ pullback P.torsor.projection o),
    lift (p ≫ pullback.fst P.torsor.projection o) h ≫ P.torsor.action =
      p' ≫ pullback.fst P.torsor.projection o →
    lift (p ≫ iso.hom ≫ pullback.fst Q.torsor.projection o) h ≫ Q.torsor.action =
      p' ≫ iso.hom ≫ pullback.fst Q.torsor.projection o

end EquivariantRightTorsor

namespace ContractingLine

/-- The canonical weight-one scaling map on Spec k[u], given by u ↦ z ⊗ u.
The two schemes and the affine-product identification are the existing standard
ones. Source: Alper--Halpern-Leistner--Heinloth, Lemma 3.6, p.6, interchanging s,t
(blueprint: def-sfb-equivariant-right-torsor-fibre-isomorphism). -/
def scaling (k : Type u) [Field k] :
    StandardGroupSchemes.multiplicative k ⊗ StandardGroupSchemes.additive k ⟶
      StandardGroupSchemes.additive k :=
  letI := braidedAlgSpec (R := .of k)
  Functor.LaxMonoidal.μ (algSpec (.of k))
    (Opposite.op (CommAlgCat.of k (LaurentPolynomial k)))
    (Opposite.op (CommAlgCat.of k (Polynomial k))) ≫
      StandardGroupSchemes.map k
        (Polynomial.aeval ((LaurentPolynomial.T 1) ⊗ₜ[k] (Polynomial.X : Polynomial k)))

/-- The origin of the standard affine line, specified by evaluation u ↦ 0.
Source: Alper--Halpern-Leistner--Heinloth, Lemma 3.6, p.6
(blueprint: def-sfb-equivariant-right-torsor-fibre-isomorphism). -/
def origin (k : Type u) [Field k] :
    𝟙_ (Over (Spec (.of k))) ⟶ StandardGroupSchemes.additive k :=
  StandardGroupSchemes.identitySection k (Polynomial.aeval (0 : k))

end ContractingLine
end AlgebraicGeometry

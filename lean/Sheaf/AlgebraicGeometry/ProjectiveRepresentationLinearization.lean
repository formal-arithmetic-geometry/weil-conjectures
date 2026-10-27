module

public import Sheaf.AlgebraicGeometry.GroupSchemeLinearization
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Coordinate specification of a projective representation linearization

Source: MFK, Geometric Invariant Theory, Chapter 1, §1 and Chapter 2, §1;
Morrison, arXiv:0810.2340, §2.1--2.2.
(blueprint: def-sfb-projective-representation-linearization)

The inverse-matrix formula fixes the dual tautological linearization on every test
scheme. In particular it also imposes equivariance of the projective embedding.
The vector orbit morphism is constructed from its matrix coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ProjectiveRepresentation

variable {k : Type u} [Field k] {G : Grp (Over (Spec (.of k)))}
variable {idx : Type u} [Fintype idx] [DecidableEq idx]
variable {Y : Over (Spec (.of k))}

/-- Matrix coefficients on arbitrary scheme-valued points of a rational representation.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-projective-representation-linearization). -/
def entry (ρ : G.X ⟶ GeneralLinearGroup idx k) (T : Over (Spec (.of k)))
    (g : T ⟶ G.X) (i j : idx) : Γ(T.left, ⊤) :=
  (g ≫ ρ).left.appTop ((Scheme.ΓSpecIso
    (.of (Matrix.GeneralLinearGroup.CoordinateRing idx k))).inv
      (Matrix.GeneralLinearGroup.coord idx k i j))

/-- The dual tautological line restricted along the embedding, by the recorded tensor pullback.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-projective-representation-linearization). -/
def line (j : Y ⟶ (ℙ(idx; Spec (.of k))).asOver (Spec (.of k))) : Y.left.Modules :=
  (Scheme.Modules.tensorPullback j.left).obj (ProjectiveSpace.twist idx (Spec (.of k)) 1)

/-- Restricted homogeneous coordinate sections, using the section-normalized adjunction.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-projective-representation-linearization). -/
def coordinate (j : Y ⟶ (ℙ(idx; Spec (.of k))).asOver (Spec (.of k))) (i : idx) :
    Γ(line j, ⊤) :=
  ((Scheme.Modules.tensorPullbackSectionAdjunction j.left).unit.app
    (ProjectiveSpace.twist idx (Spec (.of k)) 1)).app ⊤
      (ProjectiveSpace.twistOneSection idx (Spec (.of k)) i)

/-- An equivariant projective embedding with its induced dual tautological linearization.
The displayed formula specifies the line action, rather than allowing a character twist.
It is equivalent to the usual equivariance: the coordinate sections generate the line,
and their ratios are the projective affine-chart coordinates. All tests include nilpotents.
Source: MFK, Chapter 1, §1; Morrison §2.1
(blueprint: def-sfb-projective-representation-linearization). -/
structure LinearizedEmbedding (ρ : G.X ⟶ GeneralLinearGroup idx k)
    (j : Y ⟶ (ℙ(idx; Spec (.of k))).asOver (Spec (.of k))) where
  action : ModObj G.X Y
  linearization : GroupSchemeLinearization.Linearization action (line j)
  coordinates : ∀ (T : Over (Spec (.of k))) (g : T ⟶ G.X) (x : T ⟶ Y) (i : idx),
    (linearization.lift T g x).hom.app ⊤
      (pullbackΓ x.left (line j) (coordinate j i)) =
    ∑ l : idx, entry ρ T g⁻¹ i l •
      pullbackΓ (GroupSchemeLinearization.act action T g x).left (line j) (coordinate j l)

/-- A vector spans the embedded point when evaluation on that vector trivializes its
pulled-back dual tautological line with precisely the given coordinate values.
Source: MFK, Chapter 2, §1 (blueprint: def-sfb-projective-representation-linearization). -/
def IsVectorLift {V : Type u} [AddCommGroup V] [Module k V] (b : Module.Basis idx k V)
    (j : Y ⟶ (ℙ(idx; Spec (.of k))).asOver (Spec (.of k)))
    (y : PGLLinearization.fieldTest k k ⟶ Y) (v : V) : Prop :=
  ∃ e : (Scheme.Modules.pullback y.left).obj (line j) ≅
      Scheme.Modules.unit (Spec (.of k)),
    ∀ i : idx, e.hom.app ⊤ (pullbackΓ y.left (line j) (coordinate j i)) =
      (Scheme.ΓSpecIso (.of k)).inv (b.repr v i)

/-- The actual vector orbit morphism, with coordinates the matrix coefficients of g v.
Here affine space in a basis is Spec of the symmetric algebra of the dual vector space.
Source: MFK, Chapter 2, §1 (blueprint: def-sfb-projective-representation-linearization). -/
def vectorOrbit {V : Type u} [AddCommGroup V] [Module k V] (b : Module.Basis idx k V)
    (ρ : G.X ⟶ GeneralLinearGroup idx k) (v : V) :
    G.X.left ⟶ AffineSpace idx (Spec (.of k)) :=
  AffineSpace.homOfVector G.X.hom (fun i ↦
    ∑ l : idx, entry ρ G.X (𝟙 G.X) i l *
      G.X.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv (b.repr v l)))

end AlgebraicGeometry.ProjectiveRepresentation

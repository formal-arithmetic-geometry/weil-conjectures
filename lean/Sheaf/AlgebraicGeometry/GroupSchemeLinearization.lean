module

public import Sheaf.AlgebraicGeometry.PGLLinearizedPolarization
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Topology.KrullDimension

/-! # Linearizations for arbitrary group schemes

Source: Morrison, arXiv:0810.2340, §2.1, and MFK, GIT, Chapter 1, §1.
(blueprint: def-sfb-group-scheme-linearization)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.GroupSchemeLinearization

variable {k : Type u} [Field k] {G : Grp (Over (Spec (.of k)))}
variable {X : Over (Spec (.of k))}

/-- Evaluation of an internal scheme action on all test schemes.
Source: Morrison §2.1 (blueprint: def-sfb-group-scheme-linearization). -/
def act (A : ModObj G.X X) (T : Over (Spec (.of k))) (g : T ⟶ G.X) (x : T ⟶ X) :
    T ⟶ X :=
  lift g x ≫ A.smul

/-- A linearization is a natural system of linear isomorphisms on pulled-back modules,
with the unit and multiplication cocycles. This describes the action on the total line.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-group-scheme-linearization). -/
structure Linearization (A : ModObj G.X X) (L : X.left.Modules) where
  lift : ∀ (T : Over (Spec (.of k))) (g : T ⟶ G.X) (x : T ⟶ X),
    (Scheme.Modules.pullback x.left).obj L ≅
      (Scheme.Modules.pullback (act A T g x).left).obj L
  unit : ∀ (T : Over (Spec (.of k))) (x : T ⟶ X),
    HEq (lift T 1 x) (Iso.refl ((Scheme.Modules.pullback x.left).obj L))
  mul : ∀ (T : Over (Spec (.of k))) (g h : T ⟶ G.X) (x : T ⟶ X),
    HEq (lift T (g * h) x) (lift T h x ≪≫ lift T g (act A T h x))
  naturality : ∀ (T U : Over (Spec (.of k))) (f : U ⟶ T) (g : T ⟶ G.X) (x : T ⟶ X),
    HEq (lift U (f ≫ g) (f ≫ x))
      ((Scheme.Modules.pullbackComp f.left x.left).symm.app L ≪≫
        (Scheme.Modules.pullback f.left).mapIso (lift T g x) ≪≫
        (Scheme.Modules.pullbackComp f.left (act A T g x).left).app L)

variable {A : ModObj G.X X} {L : X.left.Modules}

/-- Induced maps on powers, using the existing canonical monoidal comparisons.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-group-scheme-linearization). -/
def Linearization.powerLift (D : Linearization A L) (T : Over (Spec (.of k)))
    (g : T ⟶ G.X) (x : T ⟶ X) (n : ℕ) :
    (Scheme.Modules.pullback x.left).obj (L.tensorPow n) ≅
      (Scheme.Modules.pullback (act A T g x).left).obj (L.tensorPow n) :=
  PGLLinearization.pullbackPowerIso x.left L n ≪≫
    PGLLinearization.powerIso (D.lift T g x) n ≪≫
    (PGLLinearization.pullbackPowerIso (act A T g x).left L n).symm

/-- Invariance is tested on every scheme, including nonreduced schemes.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-group-scheme-linearization). -/
def Linearization.IsInvariant (D : Linearization A L) (n : ℕ)
    (s : Scheme.Modules.SectionRingComponent L n) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : T ⟶ G.X) (x : T ⟶ X),
    (D.powerLift T g x n).hom.app ⊤ (pullbackΓ x.left (L.tensorPow n) s) =
      pullbackΓ (act A T g x).left (L.tensorPow n) s

/-- Geometric semistability is nonvanishing of a positive-degree invariant section.
Source: Morrison §2.1 (blueprint: def-sfb-group-scheme-linearization). -/
def Linearization.IsSemistable (D : Linearization A L) (Ω : Type u) [Field Ω] [Algebra k Ω]
    (x : PGLLinearization.fieldTest k Ω ⟶ X) : Prop :=
  ∃ (n : ℕ) (_ : 0 < n) (s : Scheme.Modules.SectionRingComponent L n),
    D.IsInvariant n s ∧ pullbackΓ x.left (L.tensorPow n) s ≠ 0

/-- The scheme-theoretic stabilizer, as the equalizer of the orbit and constant maps
on G × Spec Ω. Equalizers retain all nilpotents.
Source: MFK, Chapter 1, §1 (blueprint: def-sfb-group-scheme-linearization). -/
def stabilizer (A : ModObj G.X X) (Ω : Type u) [Field Ω] [Algebra k Ω]
    (x : PGLLinearization.fieldTest k Ω ⟶ X) : Scheme.{u} :=
  (equalizer (act A (G.X ⊗ PGLLinearization.fieldTest k Ω)
      (fst _ _) (snd _ _ ≫ x)) (snd _ _ ≫ x)).left

/-- A stable point has a closed orbit in the semistable locus and dimension-zero
scheme-theoretic stabilizer. Closedness is read in the actual geometric base change.
Source: Morrison §2.1; MFK, Chapter 1, §1
(blueprint: def-sfb-group-scheme-linearization). -/
def Linearization.IsStable (D : Linearization A L) (Ω : Type u) [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] (x : PGLLinearization.fieldTest k Ω ⟶ X) : Prop :=
  D.IsSemistable Ω x ∧
    (∃ C : Set (pullback (C := Scheme.{u}) X.hom (PGLLinearization.fieldTest k Ω).hom), IsClosed C ∧
      ∀ y : PGLLinearization.fieldTest k Ω ⟶ X, D.IsSemistable Ω y →
        ((∃ g : PGLLinearization.fieldTest k Ω ⟶ G.X, act A _ g x = y) ↔
          PGLLinearization.geometricImage Ω y ∈ C)) ∧
    topologicalKrullDim (stabilizer A Ω x) = 0

end AlgebraicGeometry.GroupSchemeLinearization

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Twists in flat finitely presented projective families

Source: Stacks Project, Constructions, Tags 01MS, 01MT and 01O3; Morphisms, Tags 01WC,
01QR and 01U3 (blueprint: lem-sfb-flat-projective-twist-base-change-data).

The relative twist is transported through the uniquely normalized comparison with
base-change projective space. All subsequent module pullbacks use the recorded tensor
construction. Local frames specify the power, dual and base-change identifications;
the last equation is their compatibility square, including degree zero and negative degrees.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry.FlatProjectiveTwist

/-- The comparison fixed by its affine polynomial formulas, rather than an arbitrary
isomorphism. Source: Stacks, 01NF and 01O3
(blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def comparison (T : Scheme.{u}) (n : ℕ) :
    RelativeProjectiveSpace.scheme T n ≅ ProjectiveSpace (ULift.{u} (Fin (n + 1))) T :=
  Classical.choose (RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace T n)

/-- O(d) on relative-Proj projective space, with its prescribed affine restrictions.
Source: Stacks, 01MS and 01MT
(blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def relativeTwist (T : Scheme.{u}) (n : ℕ) (d : ℤ) :
    (RelativeProjectiveSpace.scheme T n).Modules :=
  (tensorPullback (comparison T n).hom).obj
    (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) T d)

/-- The actual restricted twist i*O(d); its data is a tensor pullback.
Source: Stacks, 01MT; Sheaves, 0095
(blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def twist {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ RelativeProjectiveSpace.scheme T n) (d : ℤ) : Z.Modules :=
  (tensorPullback i).obj (relativeTwist T n d)

/-- The inverse image of the jth standard projective chart.
Source: Stacks, 01MS (blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def chart {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ RelativeProjectiveSpace.scheme T n) (j : ULift.{u} (Fin (n + 1))) : Z.Opens :=
  i ⁻¹ᵁ ((comparison T n).hom ⁻¹ᵁ ProjectiveSpace.standardOpen _ T j)

/-- The basis e_j^(d), pulled back as 1 tensor e_j^(d) at each stage. On the integral
model it is the fraction x_j^d, with inverse powers when d is negative.
Source: Stacks, 01MS and 01MT
(blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def frame {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ RelativeProjectiveSpace.scheme T n) (d : ℤ)
    (j : ULift.{u} (Fin (n + 1))) : Γ(twist i d, chart i j) :=
  letI := MvPolynomial.gradedAlgebra
    (σ := ULift.{u} (Fin (n + 1))) (R := ULift.{u} ℤ)
  tensorPullbackSection i _ _
    (tensorPullbackSection (comparison T n).hom _ _
      (pullbackSection (ProjectiveSpace.toProjInt _ T)
        (Proj.twistPowSection d (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j))))

/-- Tensor powers of a local basis, with 1 as the zeroth tensor power.
Source: Stacks, 01MT (blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def framePower {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) : (m : ℕ) → Γ(M.tensorPow m, U)
  | 0 => unitSectionsEquiv U 1
  | m + 1 => tmulSection s (framePower s m)

/-- The signed tensor power: ordinary powers in nonnegative degree and powers of the
actual internal-Hom dual in negative degree.
Source: Stacks, 01MT (blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def signedPower {X : Scheme.{u}} (M : X.Modules) : ℤ → X.Modules
  | .ofNat m => M.tensorPow m
  | .negSucc m => (dual M).tensorPow (m + 1)

/-- The prescribed basis in a signed power, using the specified inverse-degree duality.
Source: Stacks, 01MT (blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def powerFrame {T Z : Scheme.{u}} {n : ℕ}
    {i : Z ⟶ RelativeProjectiveSpace.scheme T n}
    (δ : twist i (-1) ≅ dual (twist i 1)) :
    (d : ℤ) → (j : ULift.{u} (Fin (n + 1))) →
      Γ(signedPower (twist i 1) d, chart i j)
  | .ofNat m, j => framePower (frame i 1 j) m
  | .negSucc m, j => framePower (δ.hom.app (chart i j) (frame i (-1) j)) (m + 1)

/-- The canonical power data is specified on every standard local basis. The dual
normalization is evaluation v_j(u_j)=1, which fixes the inverse transition function.
Source: Stacks, 01MS and 01MT
(blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
structure PowerData {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ RelativeProjectiveSpace.scheme T n) where
  /-- O(-1) is the internal-Hom dual of O(1). -/
  dualIso : twist i (-1) ≅ dual (twist i 1)
  /-- The inverse-degree basis evaluates to one on the degree-one basis. -/
  dual_normalized : ∀ j : ULift.{u} (Fin (n + 1)),
    (dualEvaluation (twist i 1)).app (chart i j)
      (tmulSection (frame i 1 j) (dualIso.hom.app (chart i j) (frame i (-1) j))) =
        unitSectionsEquiv (chart i j) 1
  /-- Every signed-degree twist is its indicated tensor power. -/
  iso : ∀ d : ℤ, twist i d ≅ signedPower (twist i 1) d
  /-- Each identification sends the displayed basis to its pure tensor power. -/
  normalized : ∀ (d : ℤ) (j : ULift.{u} (Fin (n + 1))),
    (iso d).hom.app (chart i j) (frame i d j) = powerFrame dualIso d j

/-- Relative projective space's canonical map over a change of base, transported from
its fibre-product model. Source: Stacks, 01O3
(blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def projectiveMap {T T' : Scheme.{u}} (n : ℕ) (h : T' ⟶ T) :
    RelativeProjectiveSpace.scheme T' n ⟶ RelativeProjectiveSpace.scheme T n :=
  (comparison T' n).hom ≫ ProjectiveSpace.map _ h ≫ (comparison T n).inv

/-- Basis normalization for a comparison after base change. Both bases are restricted
to any common subopen; thus no equality of opens is hidden in a cast.
Source: Stacks, 01O3 and 04TN
(blueprint: lem-sfb-flat-projective-twist-base-change-data). -/
def IsFrameComparison {Z Z' : Scheme.{u}} (g : Z' ⟶ Z)
    {M : Z.Modules} {N : Z'.Modules} (e : (tensorPullback g).obj M ≅ N)
    {U : Z.Opens} {V : Z'.Opens} (s : Γ(M, U)) (t : Γ(N, V)) : Prop :=
  ∀ (W : Z'.Opens) (hW : W ≤ g ⁻¹ᵁ U) (hV : W ≤ V),
    e.hom.app W (((tensorPullback g).obj M).presheaf.map (homOfLE hW).op
      (tensorPullbackSection g M U s)) = N.presheaf.map (homOfLE hV).op t

/-- Flat finitely presented projective families have canonical invertible twists, finite
presentation, stalkwise base flatness, signed-power identifications, and arbitrary base
change respecting those identifications.
Source: Stacks Project, Constructions, 01MS, 01MT, 01O3; Morphisms, 01WC, 01QR, 01U3;
Modules, 01BN; Algebra, 00HB (blueprint: lem-sfb-flat-projective-twist-base-change-data).

Proof for stage 3:
1. The uniquely normalized comparison with base-change projective space exhibits f as
H-projective (lem-trf-free-projective-bundle-base-change-space). Quasi-compactness makes
it projective (def-pc-projective-morphism), hence proper (lem-pc-projective-proper).
2. On each affine base restriction, the standard charts have bases e_j^(d), with
transition (x_j/x_k)^d (def-pc-projective-space-twist). Tensor pullback gives bases
1 tensor e_j^(d) (def-pc-module-pullback). The comparison uses the same coordinate maps
on all affine restrictions, so these bases and transitions agree on refinements.
Their cocycle identity glues the modules and the prescribed identifications, uniquely,
by clauses (1) and (2) of lem-weil-pbc-glue-sheaves-of-modules. This identifies the actual
relativeTwist/twist constructions with those glued modules. All ratios are units,
including in negative degree; hence the modules are invertible (def-sc-invertible-module).
3. The local presentation has one generator and no relations, giving finite presentation
(def-weil-pbc-module-finite-type-presentation). Its stalk is O_Z,z with the base action
through f.stalkMap z. Flatness of f gives its base flatness (def-weil-flat-morphism,
def-weil-pbc-flat-ring-map), transported through this rank-one stalk isomorphism.
4. Send the basis in degree m to the mth tensor power of the degree-one basis, including
1 when m=0. In degree -m send it to the mth power of the dual basis. Evaluation forces
the dual transition to be the inverse ratio (def-sc-invertible-module). Identical
transitions glue the maps and inverses, and gluing uniqueness fixes all PowerData.
5. Apply lemma-nagata-relative-proj-base-change-arbitrary to the coefficientwise
polynomial base change (def-nagata-graded-algebra-pullback-data): b tensor sum a_I x^I
maps to sum b*h(a_I)*x^I; its inverse fixes coefficients and variables. These maps
preserve grading and commute with restrictions. Pullback pasting gives the induced
embedding, closed by lem-weil-pbc-closed-immersion-base-change.
6. Send every pulled basis to the corresponding new basis. The transition ratios agree,
so maps and inverses glue for every integer degree. The power comparison is similarly
specified on pure tensors; its degree-zero case is the unit and its negative-degree
case uses the dual basis. Both composites in the displayed square send the same basis
to the same pure tensor. Clause (1) of lem-weil-pbc-glue-sheaves-of-modules proves the
square globally, and its uniqueness proves canonicity. This is also the calculation
(a tensor u) tensor (b tensor v) mapping to ab tensor (u tensor v), and the dual
comparison sending the pulled dual basis to the new dual basis. -/
theorem flat_projective_twist_base_change_data {T Z : Scheme.{u}} (n : ℕ)
    (i : Z ⟶ RelativeProjectiveSpace.scheme T n) [IsClosedImmersion i]
    [Flat (i ≫ RelativeProjectiveSpace.π T n)]
    [LocallyOfFinitePresentation (i ≫ RelativeProjectiveSpace.π T n)]
    [QuasiCompact (i ≫ RelativeProjectiveSpace.π T n)]
    [QuasiSeparated (i ≫ RelativeProjectiveSpace.π T n)] :
    IsProper (i ≫ RelativeProjectiveSpace.π T n) ∧
    (∀ d : ℤ, (twist i d).IsInvertible ∧ (twist i d).IsFinitePresentation ∧
      ∀ z : Z, Module.Flat (T.presheaf.stalk ((i ≫ RelativeProjectiveSpace.π T n) z))
        ((ModuleCat.restrictScalars ((i ≫ RelativeProjectiveSpace.π T n).stalkMap z).hom).obj
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (twist i d)))) ∧
    ∃ D : PowerData i, ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
      ∃ i' : pullback (i ≫ RelativeProjectiveSpace.π T n) h ⟶
          RelativeProjectiveSpace.scheme T' n,
        i' ≫ RelativeProjectiveSpace.π T' n =
          pullback.snd (i ≫ RelativeProjectiveSpace.π T n) h ∧
        IsPullback (pullback.fst (i ≫ RelativeProjectiveSpace.π T n) h) i' i
          (projectiveMap n h) ∧ IsClosedImmersion i' ∧
        ∃ (D' : PowerData i')
          (β : ∀ d : ℤ,
            (tensorPullback (pullback.fst (i ≫ RelativeProjectiveSpace.π T n) h)).obj
              (twist i d) ≅ twist i' d)
          (κ : ∀ d : ℤ,
            (tensorPullback (pullback.fst (i ≫ RelativeProjectiveSpace.π T n) h)).obj
              (signedPower (twist i 1) d) ≅ signedPower (twist i' 1) d),
          (∀ (d : ℤ) (j : ULift.{u} (Fin (n + 1))),
            IsFrameComparison _ (β d) (frame i d j) (frame i' d j)) ∧
          (∀ (d : ℤ) (j : ULift.{u} (Fin (n + 1))),
            IsFrameComparison _ (κ d) (powerFrame D.dualIso d j)
              (powerFrame D'.dualIso d j)) ∧
          (∀ d : ℤ,
            (tensorPullback (pullback.fst (i ≫ RelativeProjectiveSpace.π T n) h)).map
              (D.iso d).hom ≫ (κ d).hom = (β d).hom ≫ (D'.iso d).hom) := by
  sorry

end AlgebraicGeometry.FlatProjectiveTwist

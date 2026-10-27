/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.AffineOpenBoundaryCodimensionOne
import Sheaf.AlgebraicGeometry.AffineSpaceInvertibleTrivial
import Sheaf.AlgebraicGeometry.RegularSpaceDivisorLineDictionary
import Sheaf.TraceFormula.ReducedSchemeImage
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The Schubert boundary basis of the Picard group of a split flag variety

Source: Brion, On Linearization of Line Bundles, Lemma 2.3, printed p.118;
Milne, Algebraic Groups (2017), Lemma 18.21, printed p.392.
(blueprint: lem-sfb-split-flag-schubert-picard-lattice)

The auxiliary predicate packages precisely the boundary and basis clauses. Ideals,
associated lines, Picard groups, affine spaces, and base change are the recorded ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SplitFlagSchubert

/-- The class of the dual Cartier ideal, using the existing scheme Picard group.
Source: Brion, Lemma 2.3, p.118; Milne, Lemma 18.21, p.392
(blueprint: lem-sfb-split-flag-schubert-picard-lattice). -/
def divisorClass {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible) : X.Pic :=
  @Scheme.Pic.ofIsInvertible X I.toModulesᵛ hI.isInvertible_dual_toModules

/-- The boundary supports are precisely the distinct codimension-one irreducible
components of the complement. The isomorphism is the actual tensor-power map;
negative exponents in Pic mean tensor powers of the dual line.
Source: Milne, Lemma 18.21, p.392; Brion, Lemma 2.3, p.118
(blueprint: lem-sfb-split-flag-schubert-picard-lattice). -/
def BoundaryBasis {F : Type u} [Field F]
    (Q U : Over (Spec (.of F))) (j : U ⟶ Q) (s : ℕ)
    (D : Fin s → Q.left.IdealSheafData) (hD : ∀ i, (D i).IsInvertible) : Prop :=
  IsOpenImmersion j.left ∧ DenseRange j.left ∧
    (∀ i, GeometricallyIntegral ((D i).subschemeι ≫ Q.hom)) ∧
    Function.Injective (fun i ↦ ((D i).support : Set Q.left)) ∧
    (∀ Z : Set Q.left,
      (∃ i, Z = ((D i).support : Set Q.left)) ↔
        (∃ C : Set {x : Q.left // x ∉ Set.range j.left},
          C ∈ irreducibleComponents {x : Q.left // x ∉ Set.range j.left} ∧
          Z = Subtype.val '' C ∧
          ∀ xi : Q.left, IsGenericPoint xi Z →
            ringKrullDim (Q.left.presheaf.stalk xi) = 1)) ∧
    ∃ e : Multiplicative (Fin s → ℤ) ≃* Q.left.Pic,
      ∀ m : Fin s → ℤ,
        e (Multiplicative.ofAdd m) = ∏ i, divisorClass (D i) (hD i) ^ m i

/-- The split Schubert boundary gives an integral Picard lattice over any field,
with the same cell and actual Cartier base changes after every extension.
The quotient is specified by its fppf covering map and right-B kernel pair, which
identifies its represented sheaf with the sheafification of the coset presheaf.
The Borel hypothesis is spelled out over F: the existing IsBorelGroupScheme only
accepts algebraically closed fields and is therefore not the interface of this node.

Source: Brion, Lemma 2.3, p.118; Milne, Lemma 18.21, p.392
(blueprint: lem-sfb-split-flag-schubert-picard-lattice).

Proof (the six steps of the node):
1. Use lem-sfb-split-bruhat-affine-stratification for the open dense affine cell.
   Smoothness gives regularity and local Noetherianity by
   lem-weil-pbc-smooth-scheme-over-field-regular. Projectivity gives properness by
   lem-pc-projective-proper and finite type and separatedness by
   def-weil-proper-morphism. Quasi-compactness gives Noetherianity.
2. The maximal distinct closures of the remaining cells are the boundary components.
   Give them reduced structures using lem-trf-reduced-scheme-image. Apply
   lem-sfb-scheme-image-flat-base-change to the affine strata: extension of fields
   is flat, and the reduced closures remain integral and nonempty. Surjectivity of
   the projection reflects inclusions of closures, so the components stay distinct.
3. By lem-sfb-affine-open-boundary-codimension-one the local rings at their generic
   points have dimension one. Use lem-weil-pbc-affine-opens-basis,
   lem-weil-pbc-reduced-induced-closed-subscheme,
   lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-spec-tilde-stalk-localization to identify the stalk ideal with the
   height-one prime in the regular local ring. Apply
   lem-trf-regular-local-ufd-boundary-factorization with no boundary parameters and
   lem-trf-ufd-height-one. Its generator is a nonzerodivisor. Spread it by
   lem-sfb-stalk-nonzerodivisor-cartier-spreading. Repeat after extension of fields.
4. By lem-sfb-affine-space-invertible-trivial every line is trivial on the cell.
   Its generating rational section has divisor supported on the boundary, by
   lem-sfb-regular-space-divisor-line-dictionary. Local equations identify the
   associated line with the tensor product of the dual boundary ideals. This
   proves surjectivity of the displayed tensor-power homomorphism.
5. A relation gives a rational function with divisor supported on the boundary.
   Its restriction to affine space is a polynomial unit and hence a nonzero
   constant, by additivity of polynomial degree (also in dimension zero). Density
   makes the rational function constant, so all its boundary orders vanish.
   Distinct prime divisors are independent formal generators. This proves injectivity.
6. Repeat the arguments for the actual extended cell and ideals. Flat pullback in
   lem-sfb-regular-space-divisor-line-dictionary sends each inverse local equation
   to its inverse image, so Picard pullback sends each generator to its extension.
   If the maximal torus is all of H, the Bruhat cell is Spec F and the boundary
   is empty, giving d = s = 0; this includes the trivial group.
-/
theorem split_flag_schubert_picard_lattice {F : Type u} [Field F]
    (H T B : Grp (Over (Spec (.of F))))
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (iT : T ⟶ H) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ H)
    (hB : IsClosedSubgroupScheme iB.hom.hom ∧ Smooth B.X.hom ∧
      ConnectedSpace B.X.left ∧ SolvableGroupStructure.IsSolvable B ∧
      ∀ (C : Grp (Over (Spec (.of F)))) (iC : C ⟶ H),
        IsClosedSubgroupScheme iC.hom.hom → Smooth C.X.hom → ConnectedSpace C.X.left →
        SolvableGroupStructure.IsSolvable C →
        ∀ f : B ⟶ C, f ≫ iC = iB → IsIso f)
    (hBsplit : IsSplitSolvable B)
    (jT : T ⟶ B) (hjT : jT ≫ iB = iT)
    (Q : Over (Spec (.of F))) (q : H.X ⟶ Q)
    (hqflat : Flat q.left) (hqsurj : Surjective q.left)
    (hqlfp : LocallyOfFinitePresentation q.left)
    (hqtorsor : IsPullback (fst H.X B.X)
      (fst H.X B.X * (snd H.X B.X ≫ iB.hom.hom)) q q) :
    ∃ (d s : ℕ)
      (j : (AffineSpace (ULift.{u} (Fin d)) (Spec (.of F))).asOver (Spec (.of F)) ⟶ Q)
      (D : Fin s → Q.left.IdealSheafData) (hD : ∀ i, (D i).IsInvertible),
      BoundaryBasis Q _ j s D hD ∧
      (IsIso iT → d = 0 ∧ s = 0 ∧ Nonempty (Q ≅ Over.mk (𝟙 (Spec (.of F))))) ∧
      ∀ (L : Type u) [Field L] [Algebra F L],
        ∃ hDL : ∀ i, ((D i).comap
            (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))).IsInvertible,
          BoundaryBasis
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q)
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
              ((AffineSpace (ULift.{u} (Fin d)) (Spec (.of F))).asOver (Spec (.of F))))
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map j) s
            (fun i ↦ (D i).comap
              (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))) hDL ∧
          ∀ i, Scheme.Pic.mapHom
              (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
              (divisorClass (D i) (hD i)) =
            divisorClass ((D i).comap
              (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))) (hDL i) := by
  sorry

end AlgebraicGeometry.SplitFlagSchubert

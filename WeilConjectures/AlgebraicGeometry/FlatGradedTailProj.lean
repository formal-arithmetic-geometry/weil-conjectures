/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.RingTheory.GradedAlgebra.Standard
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.RingTheory.StandardGradedHilbertFunction
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Flat.Basic

/-! # Flatness and Hilbert polynomial from a locally free graded tail

Source: Stacks Project, Constructions, Tags 01M7, 01O3 and 07ZK;
Varieties, Tag 08AE; Coherent, Tag 0AG7
(blueprint: lem-sfb-flat-graded-tail-proj).

The quotient is presented by a surjective morphism from the existing polynomial
algebra sheaf. Its kernel is the homogeneous ideal of equations. In particular,
neither the degree-zero unit map nor any coordinate is required to be injective.
The relative Proj and its coefficient pullbacks use the canonical affine-basis API.
Chart-normalized isomorphisms identify the two existing projective-space models.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.FlatGradedTail

/-- The quotient map on polynomial sections, with the existing ordered coordinates.
Source: Stacks, Tag 07ZK (blueprint: lem-sfb-flat-graded-tail-proj). -/
def polynomialMap {U : Scheme.{u}} {n : ℕ} {B : RelativeProjAlgebra U}
    (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)
    (V : U.affineOpens) : MvPolynomial (Fin (n + 1)) Γ(U, V.1) →+* B.sections V :=
  (q.app V).toRingHom.comp (RelativeProjectiveSpace.affinePolynomialEquiv U n V).toRingHom

/-- The homogeneous equations on an affine base open are the kernel of the quotient.
This uses an ordinary ideal and imposes no saturation condition.
Source: Stacks, Tags 07ZK and 0AG7 (blueprint: lem-sfb-flat-graded-tail-proj). -/
def equations {U : Scheme.{u}} {n : ℕ} {B : RelativeProjAlgebra U}
    (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)
    (V : U.affineOpens) : Ideal (MvPolynomial (Fin (n + 1)) Γ(U, V.1)) :=
  RingHom.ker (polynomialMap q V)

/-- The quotient's canonical map to the affine-basis relative Proj of the polynomial algebra.
Source: Stacks, Tag 07ZK (blueprint: lem-sfb-flat-graded-tail-proj). -/
def embedding {U : Scheme.{u}} {n : ℕ} {B : RelativeProjAlgebra U}
    (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)
    (hq : ∀ V : U.affineOpens, Function.Surjective (q.app V)) :
    B.affineData.relProj ⟶ (RelativeProjectiveSpace.algebra U n).affineData.relProj :=
  Scheme.GradedAlgebraData.relProjMap q
    (Scheme.GradedAlgebraData.irrelevantLE_of_surjective q hq)

/-- The normalization identifying the two existing projective-space realizations:
both maps on an affine base chart are the specified Proj chart inclusion.
Source: Stacks, Tag 01LH (blueprint: lem-sfb-flat-graded-tail-proj). -/
def IsProjectiveSpaceIdentification (U : Scheme.{u}) (n : ℕ)
    (e : (RelativeProjectiveSpace.algebra U n).affineData.relProj ≅
      RelativeProjectiveSpace.scheme U n) : Prop :=
  ∀ V : U.affineOpens,
    (RelativeProjectiveSpace.algebra U n).affineData.relProjι V ≫ e.hom =
      ((RelativeProjectiveSpace.algebra U n).gradeIso V).inv ≫
        ((RelativeProjectiveSpace.construction U n).localIso V).inv ≫
          colimit.ι (RelativeProjectiveSpace.construction U n).gluing.functor V

/-- Euler characteristic of the actual twisting module on the Proj over an affine open
of a field spectrum. The scalar action is given by its structural map to that spectrum.
Source: Stacks, Tags 01M7 and 08AE (blueprint: lem-sfb-flat-graded-tail-proj). -/
def affineFieldEuler (k : Type u) [Field k]
    (B : (Spec (CommRingCat.of k)).GradedAlgebraData)
    (V : (Spec (CommRingCat.of k)).affineOpens) (d : ℕ) : ℤ :=
  @Scheme.Modules.eulerChar k _ (Proj (B.grading V))
    ⟨B.toOpen V ≫ V.1.ι⟩ (Proj.twist (B.grading V) (d : ℤ))

/-- Euler characteristic of O(d) on a graded algebra's Proj over its coefficient field.
Source: Stacks, Tags 01M7 and 08AE (blueprint: lem-sfb-flat-graded-tail-proj). -/
def fieldEuler {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (a : ℕ → Submodule k A) [GradedAlgebra a] (d : ℕ) : ℤ :=
  @Scheme.Modules.eulerChar k _ (Proj a) ⟨Proj.toSpecOfAlgebra a⟩ (Proj.twist a (d : ℤ))

/-- A locally free graded tail gives the asserted embedded flat finitely presented family,
its geometric-fibre polynomial, and its equations after every coefficient pullback.
The map q presents B as the polynomial algebra modulo its homogeneous kernel J.
Local finite generation of J is expressed on an affine neighbourhood of each base point.
The two projective-space realizations are identified by their fixed affine charts.

Source: Stacks, Constructions, Tags 01M7, 01O3 and 07ZK; Varieties, Tag 08AE;
Coherent, Tag 0AG7 (blueprint: lem-sfb-flat-graded-tail-proj).

Proof:
1. Apply prop-nagata-relative-proj-functoriality to the surjective graded quotient q.
   Its local models are the quotient polynomial Proj charts. The projective-space
   definition identifies the target with P^n_U, including degree-zero equations.
   Affine cokernels are computed by lem-weil-pbc-quasi-coherent-module-cokernel-image.
2. This is a projective morphism, hence proper by lem-kun-projective-implies-proper.
   The locally Noetherian base and pqf-lem-lft-fp-locnoeth give local finite presentation.
   Properness gives quasi-compactness and separatedness; the closed diagonal is proper
   by lem-weil-pbc-closed-immersion-proper, hence quasi-compact, giving quasi-separatedness.
3. For each degree separately, lem-pc-finite-flat-affine-sections-projective identifies
   affine sections of the given finite locally free piece as a projective module.
   Apply lem-weil-pbc-projective-module-flat. No simultaneous frame in all degrees is used.
4. For a coordinate x, its degree-zero localization is the module colimit of the tail,
   with transition multiplication by x and cocone b mapping to b/x^d. A compatible
   family sends this fraction to the image of x^(D-d)b at any D at least max(d,m).
   Independence uses compatibility; equality of two fractions is tested after a further
   power of x, so works without cancellation even for zero or nilpotent coordinates.
   Addition at a common denominator proves linearity; the tail is cofinal, giving uniqueness.
5. Apply lem-weil-pbc-filtered-colimit-flat-modules to this nonempty directed tail.
   Lemma lem-weil-pbc-flat-ring-map-iff-flat-affine gives flatness on the charts.
   Open restriction preserves local rings, so def-weil-flat-morphism gives global flatness.
6. Lemma lemma-nagata-relative-proj-base-change-arbitrary gives the canonical pullback.
   Lemma lem-weil-pbc-tilde-pullback-base-change identifies its sections with tensor
   coefficient extension. The universal property of a quotient gives the polynomial
   quotient by the image ideal, not an injection of the tensor pullback of J. Both
   embeddings agree on fractions b/x^d, giving the displayed cartesian embedding square.
7. Over a field apply lem-trf-standard-graded-hilbert-function to the polynomial ring
   and its cyclic graded quotient module, not to a quotient assumed to have B_0=k.
   Lemma lem-sfb-projective-coordinate-ring-euler-polynomial identifies this eventual
   function with twisted Euler characteristic, without a saturation hypothesis.
8. After passage to an algebraic closure of a residue field, a local free frame for
   each B_d tensors to a basis of size P(d). Step 7 identifies the Hilbert polynomial
   with P on all large integers. The finite-root property of rational polynomials
   makes them equal. This includes P=0 and empty fibres. -/
theorem flat_finitePresentation_geometricHilbertPolynomial
    (U : Scheme.{u}) [IsLocallyNoetherian U] (n : ℕ) (B : RelativeProjAlgebra U)
    (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)
    (hq : ∀ V : U.affineOpens, Function.Surjective (q.app V))
    (hJ : ∀ x : U, ∃ V : U.affineOpens, x ∈ V.1 ∧ (equations q V).FG)
    (m : ℕ) (P : Polynomial ℚ)
    (hP : ∀ d : ℕ, m ≤ d → ∃ r : ℕ, P.eval (d : ℚ) = (r : ℚ))
    (htail : ∀ (d : ℕ), m ≤ d → ∀ r : ℕ, P.eval (d : ℚ) = (r : ℚ) →
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (B.piece d) r) :
    ∃ e : (RelativeProjectiveSpace.algebra U n).affineData.relProj ≅
        RelativeProjectiveSpace.scheme U n,
      IsProjectiveSpaceIdentification U n e ∧
      IsClosedImmersion (embedding q hq ≫ e.hom) ∧
      (embedding q hq ≫ e.hom ≫ RelativeProjectiveSpace.π U n = B.affineData.relProjHom) ∧
      Flat B.affineData.relProjHom ∧ LocallyOfFinitePresentation B.affineData.relProjHom ∧
      QuasiCompact B.affineData.relProjHom ∧ QuasiSeparated B.affineData.relProjHom ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ U),
        ∃ (B' : RelativeProjAlgebra T)
          (D : Scheme.GradedAlgebraData.PullbackData g B.affineData B'.affineData)
          (DP : Scheme.GradedAlgebraData.PullbackData g
            (RelativeProjectiveSpace.algebra U n).affineData
            (RelativeProjectiveSpace.algebra T n).affineData)
          (q' : (RelativeProjectiveSpace.algebra T n).affineData ⟶ B'.affineData)
          (hq' : ∀ V' : T.affineOpens, Function.Surjective (q'.app V'))
          (e' : (RelativeProjectiveSpace.algebra T n).affineData.relProj ≅
            RelativeProjectiveSpace.scheme T n),
          IsProjectiveSpaceIdentification T n e' ∧
          (∀ (V' : T.affineOpens) (V : U.affineOpens) (h : V'.1 ≤ g ⁻¹ᵁ V.1)
            (p : MvPolynomial (Fin (n + 1)) Γ(U, V.1)),
            DP.map h (RelativeProjectiveSpace.affinePolynomialEquiv U n V p) =
              RelativeProjectiveSpace.affinePolynomialEquiv T n V'
                (MvPolynomial.map (g.appLE V.1 V'.1 h).hom p)) ∧
          (∀ (V' : T.affineOpens) (V : U.affineOpens) (h : V'.1 ≤ g ⁻¹ᵁ V.1)
            (p : MvPolynomial (Fin (n + 1)) Γ(U, V.1)),
            D.map h (polynomialMap q V p) =
              polynomialMap q' V' (MvPolynomial.map (g.appLE V.1 V'.1 h).hom p)) ∧
          (∀ (V' : T.affineOpens) (V : U.affineOpens) (h : V'.1 ≤ g ⁻¹ᵁ V.1),
            equations q' V' = (equations q V).map
              (MvPolynomial.map (g.appLE V.1 V'.1 h).hom)) ∧
          IsPullback (embedding q' hq') D.relProjComparison DP.relProjComparison
            (embedding q hq)) ∧
      (∀ s : U,
        ∃ (B' : (Spec (CommRingCat.of (AlgebraicClosure (U.residueField s)))).GradedAlgebraData)
          (D : Scheme.GradedAlgebraData.PullbackData
            (Spec.map (CommRingCat.ofHom
              (algebraMap (U.residueField s) (AlgebraicClosure (U.residueField s)))) ≫
                U.fromSpecResidueField s) B.affineData B')
          (V : (Spec (CommRingCat.of (AlgebraicClosure (U.residueField s)))).affineOpens),
          V.1 = ⊤ ∧
          ∃ j : Proj (B'.grading V) ≅ pullback B.affineData.relProjHom
              (Spec.map (CommRingCat.ofHom
                (algebraMap (U.residueField s) (AlgebraicClosure (U.residueField s)))) ≫
                  U.fromSpecResidueField s),
            j.hom = B'.relProjι V ≫ D.relProjIsoPullback.hom ∧
            ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              (affineFieldEuler (AlgebraicClosure (U.residueField s)) B' V d : ℚ) =
                P.eval (d : ℚ)) := by
  sorry

/-- The eventual graded Hilbert polynomial of a finitely generated homogeneous polynomial
quotient is the Hilbert polynomial of its embedded Proj. A surjective graded k-algebra
map presents precisely such a quotient, with homogeneous ideal ker(q); its grading and
ordered polynomial variables fix the embedding and its O(d). No saturation is assumed.

Source: Stacks, Coherent, Tag 0AG7 and Varieties, Tag 08AE
(blueprint: lem-sfb-flat-graded-tail-proj).

Proof: apply lem-trf-standard-graded-hilbert-function with S=k[x_0,...,x_n] and its
cyclic graded quotient module A. This gives eventual polynomiality of dim A_d, including
the zero quotient. By lem-sfb-projective-coordinate-ring-euler-polynomial, high-degree
sections of the associated O(d) are A_d (Tag 0AG7), and higher coherent cohomology
vanishes in sufficiently high degree (Tag 08AE). Their Euler characteristic is therefore
the same dimension. Take a common bound for these two eventual equalities. Uniqueness
of a rational polynomial from its values on all large integers identifies the two
polynomials. The unit ideal and irrelevant-primary ideals have zero eventual polynomial
and empty Proj, so require no exception. -/
theorem field_eventualHilbertPolynomial_eq_proj
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] (n : ℕ)
    (a : ℕ → Submodule k A) [GradedAlgebra a]
    (q : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k →+*ᵍ a)
    (hq : Function.Surjective q)
    (hscalar : ∀ c : k, q (MvPolynomial.C c) = algebraMap k A c)
    (hI : (RingHom.ker q.toRingHom).FG) :
    ∃ Q : Polynomial ℚ, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      (Module.finrank k (a d) : ℚ) = Q.eval (d : ℚ) ∧
        (fieldEuler a d : ℚ) = Q.eval (d : ℚ) := by
  sorry

end AlgebraicGeometry.FlatGradedTail

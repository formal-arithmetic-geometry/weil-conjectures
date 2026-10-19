/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Projective completion of a vector bundle

Source: Stacks Project, Constructions, Tag 01OA (projective bundles), Tags 01OB,
01OE and 01NG; blueprint `sec-smooth-purity/sk-prop-an`, the first sentence of
`thm-amb-vector-bundle-purity.proof.md` (blueprint: lem-amb-vector-projective-completion).

The affine presentation below specifies the actual symmetric algebra of O plus F,
its symmetric grading and its restriction maps. No projective scheme or compactification
is selected from an uncharacterized existence assertion. All witnesses, including the
chart equivalences, are characterized in the theorem by their coefficients and generators.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise

noncomputable section

namespace AlgebraicGeometry.VectorProjectiveCompletion

/-- Affine-basis presentation of Sym(O_S ⊕ F), with its symmetric grading and its
actual restriction maps. A finite direct sum has section module R × F(V).
Source: Stacks Tag 01OA (blueprint: lem-amb-vector-projective-completion). -/
structure Presentation (S : Scheme.{u}) (F : S.Modules) where
  algebra : S.GradedAlgebraData
  equiv (V : S.affineOpens) :
    SymmetricAlgebra Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1)) ≃ₐ[Γ(S, V.1)] algebra.obj V
  grade_eq (V : S.affineOpens) (n : ℕ) :
    algebra.grading V n =
      ((LinearMap.range (SymmetricAlgebra.ι Γ(S, V.1)
        (Γ(S, V.1) × F.val.obj (op V.1)))) ^ n).map (equiv V).toLinearMap
  restriction (U V : S.affineOpens) (h : U.1 ≤ V.1)
      (a : Γ(S, V.1)) (m : F.val.obj (op V.1)) :
    algebra.res h (equiv V (SymmetricAlgebra.ι _ _ (a, m))) =
      equiv U (SymmetricAlgebra.ι _ _
        (S.presheaf.map (homOfLE h).op a, F.val.map (homOfLE h).op m))

/-- The degree-one coordinate from the first summand, namely t = j(1,0).
Source: Stacks Tag 01OA (blueprint: lem-amb-vector-projective-completion). -/
def t {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) (V : S.affineOpens) :
    P.algebra.obj V :=
  P.equiv V (SymmetricAlgebra.ι _ _ (1, 0))

/-- The degree-one coordinate from a section of F, namely x(m) = j(0,m).
Source: Stacks Tag 01OA (blueprint: lem-amb-vector-projective-completion). -/
def x {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) (V : S.affineOpens)
    (m : F.val.obj (op V.1)) : P.algebra.obj V :=
  P.equiv V (SymmetricAlgebra.ι _ _ (0, m))

/-- D_+(t), formed from the canonical local Proj opens, over the affine basis of S.
Source: Stacks Tags 01OA and 01NG (blueprint: lem-amb-vector-projective-completion). -/
def chartOpen {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) :
    P.algebra.relProj.Opens :=
  ⨆ V : S.affineOpens,
    (P.algebra.relProjι V).opensFunctor.obj (Proj.basicOpen (P.algebra.grading V) (t P V))

/-- The whole affine open V, viewed as an affine open of its own scheme.
Source: Stacks Tag 01OA (blueprint: lem-amb-vector-projective-completion). -/
def affineTop {S : Scheme.{u}} (V : S.affineOpens) : V.1.toScheme.affineOpens :=
  ⟨⊤, isAffineOpen_top V.1.toScheme⟩

/-- The canonical local Proj embedding into the recorded relative projective space
on an affine base. Its charts are RelativeProjectiveSpace.localChart.
Source: Stacks Tags 01OA and 01NG (blueprint: lem-amb-vector-projective-completion). -/
def projectiveChart {S : Scheme.{u}} (V : S.affineOpens) (d : ℕ) :
    (RelativeProjectiveSpace.algebra V.1.toScheme d).localProj (affineTop V) ⟶
      RelativeProjectiveSpace.scheme V.1.toScheme d :=
  ((RelativeProjectiveSpace.construction V.1.toScheme d).restrictionIso (affineTop V)).inv ≫
    (RelativeProjectiveSpace.π V.1.toScheme d ⁻¹ᵁ ⊤).ι

/-- The local map from Spec Sym(F(V)) to the completion, induced by dehomogenization,
then the recorded homogeneous-localization Proj chart and the relative Proj embedding.
Source: Stacks Tag 01NG (blueprint: lem-amb-vector-projective-completion). -/
def chartMap {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F)
    (ht : ∀ V : S.affineOpens, t P V ∈ P.algebra.grading V 1)
    (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
      HomogeneousLocalization.Away (P.algebra.grading V) (t P V))
    (V : S.affineOpens) :
    Spec (.of (SymmetricAlgebraSheaf.sections F (op V.1))) ⟶ P.algebra.relProj :=
  Spec.map (CommRingCat.ofHom (a V).symm.toRingHom) ≫
    Proj.awayι (P.algebra.grading V) (t P V) (ht V) Nat.one_pos ≫
      P.algebra.relProjι V

/-- The projective completion of a constant finite rank vector bundle has its canonical
frame-independent affine chart, is proper and Noetherian, and compactifies the bundle.
The algebraic chart clauses express x_i ↦ x_i/t on every affine frame, including all
restriction maps and changes of frame. The final clause identifies the rank-zero
compactification with the identity via its structural isomorphisms.
Source: Stacks Tags 01OA, 01OB, 01OE, 01NG; blueprint, vector-bundle purity, first proof
sentence (blueprint: lem-amb-vector-projective-completion).

Proof:
1. Form F' = O_S ⊕ F and its symmetric algebra, using
lem-weil-pbc-quasi-coherent-symmetric-algebra. The symmetric grading of
lem-weil-pbc-symmetric-algebra-graded is the power of the degree-one image. Restriction
preserves generators and their products. Apply lemma-nagata-relative-proj-exists to this
quasi-coherent graded algebra. On any affine frame, the basis-to-polynomial isomorphism
lem-weil-pbc-symmetric-algebra-free-module-polynomial sends (1,0) to t and (0,e_i) to x_i.
prop-nagata-relative-proj-functoriality identifies its Proj with the local projective space.
2. In its t-chart define alpha: Sym(F(V)) → C_(t),0 by m ↦ x(m)/t and fixing scalars.
The inverse sends a homogeneous fraction f(t,x)/t^n to f(1,y). Localization relations
remain equal after setting t=1, so this is well-defined. The identities follow from
homogeneity, f(t,x)/t^n = f(1,x/t).
3. If e'_j = sum_i g_ij e_i then t'=t and x'_j=sum_i g_ij x_i, so division by t
commutes with this same frame change. Restriction restricts only the coefficients.
Use lem-weil-pbc-scheme-morphism-gluing on affine refinements of overlaps to glue these
maps and their inverses. They lie over S, and give j with image D_+(t). The local chart
characterization determines j uniquely.
4. Apply lem-pur-projective-bundle-tautological-geometry to F', of rank d+1: the actual
relative Proj projection r is proper. Then lem-weil-pbc-finite-type-over-noetherian makes
its source Noetherian. The open chart E is Noetherian by
lem-weil-pbc-noetherian-open-subscheme-noetherian. Its inclusion is quasi-compact;
lem-weil-pbc-qc-open-immersion-finite-type and
lem-sfb-finite-type-composition-base-change make pi finite type. Its diagonal is the
base change of the closed diagonal of r; lem-weil-pbc-proper-fp-permanence makes it
closed, so pi is separated.
5. Package j and r as the recorded Compactification. At rank zero, the local ring is
R[t], all Proj points lie in D_+(t), and its degree-zero localization is R. The bundle's
local ring is also R. These structural isomorphisms glue, including for the empty base
and zero ring; under them j and r are identities. -/
theorem exists_projective_completion (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    ∃ (P : Presentation S F)
      (ht : ∀ V : S.affineOpens, t P V ∈ P.algebra.grading V 1)
      (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
        HomogeneousLocalization.Away (P.algebra.grading V) (t P V)),
      IsNoetherian P.algebra.relProj ∧ IsProper P.algebra.relProjHom ∧
      (∀ (V : S.affineOpens) (m : F.val.obj (op V.1)),
        (a V (SymmetricAlgebra.ι _ _ m)).val =
          algebraMap (P.algebra.obj V) (Localization.Away (t P V)) (x P V m) *
            IsLocalization.Away.invSelf (t P V)) ∧
      (∀ (V : S.affineOpens) (r : Γ(S, V.1)),
        (a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r)).val =
          algebraMap (P.algebra.obj V) (Localization.Away (t P V))
            (algebraMap Γ(S, V.1) (P.algebra.obj V) r)) ∧
      (∀ (V : S.affineOpens) (e : VectorBundleZeroSection.Trivialization S d F V.1),
        ∃ q : MvPolynomial (Fin (d + 1)) Γ(S, V.1) ≃ₐ[Γ(S, V.1)] P.algebra.obj V,
          q (MvPolynomial.X 0) = t P V ∧
          (∀ i : Fin d, q (MvPolynomial.X i.succ) =
            x P V (VectorBundleZeroSection.frameSection S d F V.1 e i)) ∧
          (∀ (n : ℕ) (f : MvPolynomial (Fin (d + 1)) Γ(S, V.1)),
            q f ∈ P.algebra.grading V n ↔
              f ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) n) ∧
          ∃ (g : (RelativeProjectiveSpace.algebra V.1.toScheme d).sectionGrade
                (affineTop V) →+*ᵍ P.algebra.grading V) (hg : Function.Bijective g)
              (b : Proj (P.algebra.grading V) ≅ RelativeProjectiveSpace.scheme V.1.toScheme d),
            (∀ r : Γ(V.1.toScheme, ⊤),
              g ((RelativeProjectiveSpace.algebra V.1.toScheme d).algebra.obj.hom.hom.app
                (op ⊤) r) = algebraMap Γ(S, V.1) (P.algebra.obj V) (V.1.topIso.hom r)) ∧
            (∀ i : Fin (d + 1),
              g (RelativeProjectiveSpace.coordinate V.1.toScheme d (affineTop V) i) =
                q (MvPolynomial.X i)) ∧
            b.hom = Proj.map g (GradedRingHom.irrelevant_le_map_of_surjective hg.surjective) ≫
              projectiveChart V d ∧
            b.hom ≫ RelativeProjectiveSpace.π V.1.toScheme d = P.algebra.toOpen V ∧
            b.hom ⁻¹ᵁ RelativeProjectiveSpace.standardOpen V.1.toScheme d 0 =
              Proj.basicOpen (P.algebra.grading V) (t P V)) ∧
      (∀ (U V : S.affineOpens) (h : U.1 ≤ V.1),
        Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.restriction F (homOfLE h).op)) ≫
          chartMap P ht a V = chartMap P ht a U) ∧
      (∀ (V : S.affineOpens) (e e' : VectorBundleZeroSection.Trivialization S d F V.1)
          (G : Matrix (Fin d) (Fin d) Γ(S, V.1)),
        (∀ j : Fin d, VectorBundleZeroSection.frameSection S d F V.1 e' j =
          ∑ i : Fin d, G i j • VectorBundleZeroSection.frameSection S d F V.1 e i) →
        ∀ j : Fin d,
          a V (SymmetricAlgebra.ι _ _ (VectorBundleZeroSection.frameSection S d F V.1 e' j)) =
            ∑ i : Fin d,
              a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) (G i j)) *
                a V (SymmetricAlgebra.ι _ _
                  (VectorBundleZeroSection.frameSection S d F V.1 e i))) ∧
      IsSeparated (VectorBundleZeroSection.π S d F) ∧
      LocallyOfFiniteType (VectorBundleZeroSection.π S d F) ∧
      QuasiCompact (VectorBundleZeroSection.π S d F) ∧
      IsNoetherian (VectorBundleZeroSection.scheme S d F) ∧
      ∃ c : Compactification (VectorBundleZeroSection.π S d F),
        ∃ hZ : c.Z = P.algebra.relProj,
          c.g = eqToHom hZ ≫ P.algebra.relProjHom ∧
          (c.i ≫ eqToHom hZ).opensRange = chartOpen P ∧
          (∀ V : S.affineOpens,
            VectorBundleZeroSection.affineChart S d F V ≫ chartMap P ht a V =
              ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V.1).ι ≫ c.i ≫ eqToHom hZ) ∧
          (∀ j : VectorBundleZeroSection.scheme S d F ⟶ P.algebra.relProj,
            (∀ V : S.affineOpens,
              VectorBundleZeroSection.affineChart S d F V ≫ chartMap P ht a V =
                ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V.1).ι ≫ j) →
            j = c.i ≫ eqToHom hZ) ∧
          (d = 0 → ∃ (eE : VectorBundleZeroSection.scheme S d F ≅ S)
              (eP : P.algebra.relProj ≅ S),
            eE.hom = VectorBundleZeroSection.π S d F ∧
            eP.hom = P.algebra.relProjHom ∧
            c.i ≫ eqToHom hZ = eE.hom ≫ eP.inv) := by
  sorry

end AlgebraicGeometry.VectorProjectiveCompletion

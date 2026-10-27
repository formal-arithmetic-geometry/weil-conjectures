/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Topology.KrullDimension
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Polynomial
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The projective matrix quotient and its special-linear central cover

Source: Milne, Algebraic Groups, Example 5.49, Propositions 5.23--5.25, Corollary 5.26,
Example 2.42 and Proposition 7.15; the explicit chart proof in the DAG.
(blueprint: lem-sfb-projective-matrix-central-cover)

`Presentation` groups the clauses of the statement, using the already constructed GL, SL,
and roots-of-unity schemes. The quotient is specified by its universal property for fpqc
sheaves, on all test schemes: this is the universal property of the sheafification of the
presheaf of scalar orbits. No scheme is selected from a bare existence theorem.
`CompatibleExtension` specifies the coordinate-normalized field-extension comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open MonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.ProjectiveMatrixCentralCover

variable (k : Type u) [Field k] (r : ℕ)

/-- The scalar inclusion Gm → GL, obtained by evaluating the GL coordinates at tI.
Source: Milne Example 5.49 (blueprint: lem-sfb-projective-matrix-central-cover). -/
def scalar : StandardGroupSchemes.multiplicative k ⟶
    GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k :=
  StandardGroupSchemes.map k
    (A := Matrix.GeneralLinearGroup.CoordinateRing (LinearGroupSchemes.Index.{u} r) k)
    (B := LaurentPolynomial k)
    (Matrix.GeneralLinearGroup.evalAlgHom
      (Matrix.GeneralLinearGroup.scalar (LinearGroupSchemes.Index.{u} r)
        (LaurentPolynomial.isUnit_T (R := k) 1).unit))

/-- The canonical scalar map μr → GL, using the recorded Laurent quotient and scalar map.
The proof of positivity only supplies the existing roots inclusion's NeZero instance.
Source: Milne Example 5.49 (blueprint: lem-sfb-projective-matrix-central-cover). -/
def rootsScalar (hr : 2 ≤ r) : StandardGroupSchemes.roots k r ⟶
    GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k :=
  @StandardGroupSchemes.rootsInclusion k _ r
    ⟨Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_two hr)⟩ ≫ scalar k r

/-- All the quotient, torsor, kernel and geometric clauses for a proposed PGL presentation.
The sheaf clause is the sheafification universal property after passing to scalar orbits:
natural maps out of that orbit presheaf are exactly scalar-invariant natural maps out of GL.
The quantifier includes nonaffine and nonreduced test schemes.
Source: Milne Example 5.49, Propositions 5.23--5.25 and 7.15, Example 2.42, and the DAG's
normalized-entry and cofactor charts (blueprint: lem-sfb-projective-matrix-central-cover). -/
structure Presentation (hr : 2 ≤ r) (G : Grp (Over (Spec (.of k))))
    (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k ⟶ G.X)
    (j : StandardGroupSchemes.roots k r ⟶ LinearGroupSchemes.specialLinear k r) : Prop where
  affine : IsAffine G.X.left
  quotient_hom : IsMonHom π
  quotient_sheaf : Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (.of k)))
    (yoneda.obj G.X)
  quotient_universal : ∀ (F : Sheaf (Scheme.fpqcTopology.over (Spec (.of k))) (Type u))
    (a : yoneda.obj (GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k) ⟶ F.obj),
    (∀ (T : Over (Spec (.of k)))
      (g : T ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k)
      (z : T ⟶ StandardGroupSchemes.multiplicative k),
      a.app (op T) (g * (z ≫ scalar k r)) = a.app (op T) g) →
    ∃! b : yoneda.obj G.X ⟶ F.obj, yoneda.map π ≫ b = a
  gl_flat : Flat π.left
  gl_surjective : Surjective π.left
  gl_torsor : ∃ e :
    GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k ⊗
      StandardGroupSchemes.multiplicative k ≅ pullback π π,
    e.hom ≫ pullback.fst π π = fst _ _ ∧
    e.hom ≫ pullback.snd π π = fst _ _ * (snd _ _ ≫ scalar k r)
  scalar_kernel : j ≫ LinearGroupSchemes.inclusion k r = rootsScalar k r hr
  sl_hom : IsMonHom (LinearGroupSchemes.inclusion k r ≫ π)
  sl_finite_locally_free :
    (LinearGroupSchemes.inclusion k r ≫ π).left.IsFiniteLocallyFreeOfDegree r
  sl_affine : IsAffineHom (LinearGroupSchemes.inclusion k r ≫ π).left
  sl_structure_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Scheme.Modules.pushforward (LinearGroupSchemes.inclusion k r ≫ π).left).obj
      (SheafOfModules.unit (LinearGroupSchemes.specialLinear k r).left.ringCatSheaf)) r
  sl_surjective : Surjective (LinearGroupSchemes.inclusion k r ≫ π).left
  sl_fpqc : Presieve.singleton (LinearGroupSchemes.inclusion k r ≫ π).left ∈
    Scheme.fpqcPrecoverage G.X.left
  kernel : ∃ e : StandardGroupSchemes.roots k r ≅
    GrpObj.ker (LinearGroupSchemes.inclusion k r ≫ π),
    e.hom ≫ GrpObj.kerι (LinearGroupSchemes.inclusion k r ≫ π) = j
  central : ∀ (T : Over (Spec (.of k)))
    (g : T ⟶ LinearGroupSchemes.specialLinear k r)
    (z : T ⟶ StandardGroupSchemes.roots k r), Commute g (z ≫ j)
  sl_torsor : ∃ e : LinearGroupSchemes.specialLinear k r ⊗
    StandardGroupSchemes.roots k r ≅
      pullback (LinearGroupSchemes.inclusion k r ≫ π) (LinearGroupSchemes.inclusion k r ≫ π),
    e.hom ≫ pullback.fst _ _ = fst _ _ ∧
    e.hom ≫ pullback.snd _ _ = fst _ _ * (snd _ _ ≫ j)
  sl_smooth : Smooth (LinearGroupSchemes.specialLinear k r).hom
  pgl_smooth : Smooth G.X.hom
  sl_finite_type : LocallyOfFiniteType (LinearGroupSchemes.specialLinear k r).hom ∧
    QuasiCompact (LinearGroupSchemes.specialLinear k r).hom
  pgl_finite_type : LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom
  sl_geometrically_connected : GeometricallyConnected (LinearGroupSchemes.specialLinear k r).hom
  pgl_geometrically_connected : GeometricallyConnected G.X.hom
  sl_dimension : topologicalKrullDim (LinearGroupSchemes.specialLinear k r).left =
    ((r ^ 2 - 1 : ℕ) : WithBot ℕ∞)
  pgl_dimension : topologicalKrullDim G.X.left = ((r ^ 2 - 1 : ℕ) : WithBot ℕ∞)

variable (K : Type u) [Field K] [Algebra k K]

/-- Restriction of scalars on bases, as the canonical Spec of the coefficient map.
Source: Milne Example 5.49, base extension (blueprint: lem-sfb-projective-matrix-central-cover).
-/
def extension : Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The coefficient extension comparisons, normalized on every matrix coordinate and the
Laurent/roots coordinates. Commutation with π, SL inclusion, scalars and the kernel inclusion
makes q and the two torsor isomorphisms the same maps after extension: their two projection
formulas determine them uniquely. These are comparisons with the actual polynomial,
localized-polynomial and quotient presentations, not abstract isomorphisms of group schemes.
Source: Milne Example 5.49 and DAG step 10
(blueprint: lem-sfb-projective-matrix-central-cover). -/
def CompatibleExtension (G : Grp (Over (Spec (.of k))))
    (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k ⟶ G.X)
    (j : StandardGroupSchemes.roots k r ⟶ LinearGroupSchemes.specialLinear k r)
    (H : Grp (Over (Spec (.of K))))
    (ρ : GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) K ⟶ H.X)
    (jK : StandardGroupSchemes.roots K r ⟶ LinearGroupSchemes.specialLinear K r) : Prop :=
  ∃ (α : (Over.pullback (extension k K)).obj
        (GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k) ≅
      GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) K)
    (β : (Over.pullback (extension k K)).obj (LinearGroupSchemes.specialLinear k r) ≅
      LinearGroupSchemes.specialLinear K r)
    (γ : (Over.pullback (extension k K)).obj (StandardGroupSchemes.roots k r) ≅
      StandardGroupSchemes.roots K r)
    (δ : (Over.pullback (extension k K)).obj G.X ≅ H.X)
    (ε : (Over.pullback (extension k K)).obj (StandardGroupSchemes.multiplicative k) ≅
      StandardGroupSchemes.multiplicative K),
    (Over.pullback (extension k K)).map π ≫ δ.hom = α.hom ≫ ρ ∧
    (Over.pullback (extension k K)).map (LinearGroupSchemes.inclusion k r) ≫ α.hom =
      β.hom ≫ LinearGroupSchemes.inclusion K r ∧
    (Over.pullback (extension k K)).map j ≫ β.hom = γ.hom ≫ jK ∧
    (Over.pullback (extension k K)).map (scalar k r) ≫ α.hom = ε.hom ≫ scalar K r ∧
    (∀ a b : LinearGroupSchemes.Index.{u} r,
      (α.inv.left ≫ pullback.fst _ _).appTop.hom
        ((Scheme.ΓSpecIso (.of (Matrix.GeneralLinearGroup.CoordinateRing
          (LinearGroupSchemes.Index.{u} r) k))).inv.hom
          (Matrix.GeneralLinearGroup.coord (LinearGroupSchemes.Index.{u} r) k a b)) =
      (Scheme.ΓSpecIso (.of (Matrix.GeneralLinearGroup.CoordinateRing
        (LinearGroupSchemes.Index.{u} r) K))).inv.hom
          (Matrix.GeneralLinearGroup.coord (LinearGroupSchemes.Index.{u} r) K a b)) ∧
    (∀ a b : LinearGroupSchemes.Index.{u} r,
      (β.inv.left ≫ pullback.fst _ _).appTop.hom
        ((Scheme.ΓSpecIso (.of (LinearGroupSchemes.SpecialAlgebra k r))).inv.hom
          (LinearGroupSchemes.specialMatrix k r a b)) =
      (Scheme.ΓSpecIso (.of (LinearGroupSchemes.SpecialAlgebra K r))).inv.hom
        (LinearGroupSchemes.specialMatrix K r a b)) ∧
    (γ.inv.left ≫ pullback.fst _ _).appTop.hom
      ((Scheme.ΓSpecIso (.of (StandardGroupSchemes.rootsAlgebra k r))).inv.hom
        (StandardGroupSchemes.rootsCoordinate k r)) =
      (Scheme.ΓSpecIso (.of (StandardGroupSchemes.rootsAlgebra K r))).inv.hom
        (StandardGroupSchemes.rootsCoordinate K r) ∧
    (ε.inv.left ≫ pullback.fst _ _).appTop.hom
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv.hom (LaurentPolynomial.T 1)) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv.hom (LaurentPolynomial.T 1)

/-- PGL is the affine fpqc scalar quotient of GL, and SL → PGL is the finite locally free,
surjective central μr cover of rank r, with its canonical torsor identity. SL and PGL are
smooth, finite type, geometrically connected and have dimension r²-1. The whole presentation
commutes with field extension, including characteristics dividing r.
Source: Milne Example 5.49, Propositions 5.23--5.25 and 7.15, Corollary 5.26, Example 2.42
(blueprint: lem-sfb-projective-matrix-central-cover).

Proof (the ten steps of the DAG):
1. Construct P as D_+(det) in projective matrix space, using
lem-sfb-projective-frames-pgl and prop-nagata-proj-standard-open. The Leibniz determinant is
homogeneous of degree r>0, so P is affine.
2. On the entry chart U_ab normalize that entry to 1. Write the matrix g=sA, where det A=d
is invertible and s is a unit. The inverse g ↦ (g_ab,g/g_ab) identifies GL over U_ab with
U_ab × Gm. Affine-space smoothness, open-immersion composition and source locality show
that the quotient is smooth, hence flat. These charts have sections, proving surjectivity.
3. Equal projective matrices differ by a unique scalar. Thus (g,z) ↦ (g,gz) is the GL torsor
isomorphism. Representable fpqc descent glues scalar-invariant maps to any fpqc sheaf,
uniquely; this is the sheafification universal property, on nonaffine tests as well.
4. On U_ab, SL has coordinates B_ab[t]/(t^r-d^(-1)), by det(tA)=t^r d. The inverse
substitutions are g_ij=t y_ij and y_ij=g_ij/g_ab, with t^(-1)=d t^(r-1).
5. The monic-quotient basis 1,t,...,t^(r-1) makes the map finite locally free of rank r.
Descend through the chart cover and use lem-pc-flf-properties for the direct-image rank.
A root of t^r-d(u)^(-1) in an algebraic closure of each residue field gives surjectivity.
An affine flat surjection is an fpqc covering.
6. The kernel consists exactly of scalar matrices zI with z^r=1, including nilpotents.
Scalars commute with all matrices; restricting step 3 gives the SL torsor identity and
the kernel isomorphism respecting j.
7. P's charts are opens of affine (r²-1)-space. For SL, cofactor expansion solves for x_ij
on D(c_ij); the adjugate identity says these opens cover. Hence both are smooth and finite
type, using the finite polynomial presentations and the finite chart cover.
8. GL is integral after any extension because its coordinates localize a polynomial domain
at the nonzero determinant. Determinant normalization retracts GL onto SL, whose coordinate
ring therefore embeds in that domain. GL surjects onto P, proving irreducibility; identity
sections give nonemptiness. This proves geometric connectedness.
9. The identity belongs to the cofactor chart D(c_11) of SL and the entry chart U_11 of P.
These nonempty opens of affine (r²-1)-space have dimension r²-1. The dimension theorem for
nonempty opens of integral locally algebraic schemes gives the asserted global dimensions.
10. Every displayed coordinate and inverse substitution commutes with coefficient extension.
Affine tensor-product base change gives the normalized comparisons in CompatibleExtension;
the projection formulas fix both torsor isomorphisms. All arguments hold in every field,
without dividing by r, even when μr is nonreduced. -/
theorem exists_presentation (hr : 2 ≤ r) :
    ∃ (G : Grp (Over (Spec (.of k))))
      (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k ⟶ G.X)
      (j : StandardGroupSchemes.roots k r ⟶ LinearGroupSchemes.specialLinear k r),
      Presentation k r hr G π j ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∃ (H : Grp (Over (Spec (.of K))))
          (ρ : GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) K ⟶ H.X)
          (jK : StandardGroupSchemes.roots K r ⟶ LinearGroupSchemes.specialLinear K r),
          Presentation K r hr H ρ jK ∧ CompatibleExtension k r K G π j H ρ jK := by
  sorry

end AlgebraicGeometry.ProjectiveMatrixCentralCover

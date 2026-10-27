/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.NodalDualizingDatum
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

import Sheaf.TraceFormula.TwoTermPerfectDeterminant
import WeilConjectures.RingTheory.RegularSequenceConormal
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# The presentation-compatible fundamental class of an lci curve

Source: Stacks Project, Duality, Tags 0E9Y and 0E9Z, with the intrinsic determinant
comparisons of Tags 0FJX and 0FJY
(blueprint: lem-sfb-lci-curve-fundamental-class).

The Jacobian formula is written in its coordinate-independent conormal form, and
also as a matrix determinant. In a regular affine presentation, take the conormal
basis to be the ordered equations and the ambient basis to be the ordered coordinate
differentials. The rows of the matrix are then the partial derivatives of the
relations followed by those of the polynomial being differentiated. The trivialization
sends the specified dual-conormal tensor coordinate-volume orientation to one.
Thus it is the adjunction trivialization, rather than an unspecified generator.
The repaired dependency uses the composition-compatible kernel-first convention,
including the cone rank factor `(-1)^(a*(b+1))`. With this convention the sign
`ε_c` is explicitly +1 for all c, as recorded by `flatLCICurveFundamentalSign`.
This is forced by the smooth comparison: the cone differential `-δ` contributes
`(-1)^c` and the rank factor contributes another `(-1)^c`, which cancel.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The sign fixed by the kernel-first adjunction convention, for each codimension.
The corrected exact-cone rank factor cancels the sign from the negative conormal
inclusion. Hence the conormal-first wedge needs no further sign in any codimension.
On adjoining r variables to a rank-(c,c+1) presentation, both the determinant
transition and the cofactor orientation change by `(-1)^r`, so this choice glues.
Source: Stacks, More on Algebra, Tag 0FJM, kernel-first exact-sequence determinant;
Duality, Tag 0E9Y, displayed conormal-first wedge
(blueprint: lem-sfb-lci-curve-fundamental-class). -/
def flatLCICurveFundamentalSign (_c : ℕ) : ℤ := 1

/-- The local cofactor formula, in the actual adjunction line. A conormal basis is
wedged first, followed by the lifted differential. This specifies the normalization
on every open, including the empty open and codimension zero.
Source: Stacks, Tag 0E9Y, displayed wedge formula
(blueprint: lem-sfb-lci-curve-fundamental-class). -/
def FlatLCIPresentation.IsCurveCofactorMap {X S : Scheme.{u}} {p : X ⟶ S}
    {U : X.Opens} (C : FlatLCIPresentation p 1 U) (K : U.toScheme.Modules)
    (e : C.line ≅ K) (δ : C.conormal ⟶ C.differentials)
    (β : C.differentials ⟶ (U.ι ≫ p).relativeDifferentials)
    (α : (U.ι ≫ p).relativeDifferentials ⟶ K) : Prop :=
  ∀ (O : U.toScheme.Opens)
    (a : Module.Basis (Fin C.c) Γ(U.toScheme, O) Γ(C.conormal, O))
    (ρ : Γ(SheafOfModules.homObj (R := U.toScheme.sheaf)
      (Scheme.Modules.exteriorSheaf C.conormal C.c)
        (SheafOfModules.unit U.toScheme.ringCatSheaf), O)),
    ρ.app (op (Over.mk (𝟙 O)))
      (Scheme.Modules.exteriorSheafSection C.conormal C.c O a) =
        (1 : Γ(U.toScheme, O)) →
    ∀ v : Γ(C.differentials, O),
      α.app O (β.app O v) = flatLCICurveFundamentalSign C.c • e.hom.app O
        (Scheme.Modules.tmulSection (X := U.toScheme)
          (M := SheafOfModules.homObj (R := U.toScheme.sheaf)
            (Scheme.Modules.exteriorSheaf C.conormal C.c)
              (SheafOfModules.unit U.toScheme.ringCatSheaf))
          (N := Scheme.Modules.exteriorSheaf C.differentials C.n) ρ
          (Scheme.Modules.exteriorSheafSection C.differentials C.n O
            (fun j ↦ Fin.snoc (α := fun _ ↦ Γ(C.differentials, O))
              (fun k ↦ δ.app O (a k)) v (Fin.cast C.rank_eq j))))

/-- The scalar Jacobian formula in every ordered basis, with its trivialization fixed
by the actual adjunction orientation. In a polynomial presentation `a` consists of
`[f_i]`, `b` of `dx_j`, and `v = da`; hence `M` is exactly the augmented Jacobian.
The determinant uses rows in the order relations, then the final differential.
Source: Stacks, Tag 0E9Y, expansion of the displayed wedge formula
(blueprint: lem-sfb-lci-curve-fundamental-class). -/
def FlatLCIPresentation.IsCurveJacobianMap {X S : Scheme.{u}} {p : X ⟶ S}
    {U : X.Opens} (C : FlatLCIPresentation p 1 U) (K : U.toScheme.Modules)
    (e : C.line ≅ K) (δ : C.conormal ⟶ C.differentials)
    (β : C.differentials ⟶ (U.ι ≫ p).relativeDifferentials)
    (α : (U.ι ≫ p).relativeDifferentials ⟶ K) : Prop :=
  ∀ (O : U.toScheme.Opens)
    (a : Module.Basis (Fin C.c) Γ(U.toScheme, O) Γ(C.conormal, O))
    (b : Module.Basis (Fin C.n) Γ(U.toScheme, O) Γ(C.differentials, O))
    (ρ : Γ(SheafOfModules.homObj (R := U.toScheme.sheaf)
      (Scheme.Modules.exteriorSheaf C.conormal C.c)
        (SheafOfModules.unit U.toScheme.ringCatSheaf), O)),
    ρ.app (op (Over.mk (𝟙 O)))
      (Scheme.Modules.exteriorSheafSection C.conormal C.c O a) =
        (1 : Γ(U.toScheme, O)) →
    ∃ e₀ : Γ(K, O) ≃ₗ[Γ(U.toScheme, O)] Γ(U.toScheme, O),
      e₀ (e.hom.app O (Scheme.Modules.tmulSection (X := U.toScheme)
        (M := SheafOfModules.homObj (R := U.toScheme.sheaf)
          (Scheme.Modules.exteriorSheaf C.conormal C.c)
            (SheafOfModules.unit U.toScheme.ringCatSheaf))
        (N := Scheme.Modules.exteriorSheaf C.differentials C.n) ρ
        (Scheme.Modules.exteriorSheafSection C.differentials C.n O b))) = 1 ∧
      ∀ (v : Γ(C.differentials, O))
        (M : Matrix (Fin C.n) (Fin C.n) Γ(U.toScheme, O)),
        (∀ i, Fin.snoc (α := fun _ ↦ Γ(C.differentials, O))
          (fun k ↦ δ.app O (a k)) v (Fin.cast C.rank_eq i) =
          ∑ j : Fin C.n, M i j • b j) →
        e₀ (α.app O (β.app O v)) = flatLCICurveFundamentalSign C.c • M.det

/-- A fundamental class in the specified adjunction system. Local maps on all
presentation charts are restrictions of the single global map, and are normalized by
the conormal wedge and Jacobian formulas. In particular their restrictions agree on
arbitrary overlaps. The last equation states arbitrary base-change compatibility on
universal differential generators, so it fixes the canonical comparison square without
introducing an arbitrary differential comparison. Isomorphisms over the base are
included by taking a cartesian square whose base map is the identity.
Source: Stacks, Tags 0E9Y, 0E9Z; cotangent/determinant comparisons, Tags 08QQ, 0FJY
(blueprint: lem-sfb-lci-curve-fundamental-class). -/
def FlatLCIAdjunctionSystem.IsCurveFundamentalClass {X S : Scheme.{u}} {p : X ⟶ S}
    (F : FlatLCIAdjunctionSystem p 1)
    (α : ∀ B : FlatLCIBaseChange p, B.p'.relativeDifferentials ⟶ F.line B) : Prop :=
  (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens) (C : FlatLCIPresentation B.p' 1 U),
    ∃ αU : (U.ι ≫ B.p').relativeDifferentials ⟶
        (Scheme.Modules.tensorPullback U.ι).obj (F.line B),
      (∀ (O : B.X'.Opens) (a : Γ(B.X', O)),
        αU.app (U.ι ⁻¹ᵁ O)
          ((U.ι ≫ B.p').relativeDifferentialsDerivation.d (X := op (U.ι ⁻¹ᵁ O))
            (U.ι.app O a)) =
          Scheme.Modules.tensorPullbackSection U.ι (F.line B) O
            ((α B).app O (B.p'.relativeDifferentialsDerivation.d (X := op O) a))) ∧
      (∀ (δ : C.conormal ⟶ C.differentials)
        (β : C.differentials ⟶ (U.ι ≫ B.p').relativeDifferentials),
        C.IsConormalDifferential δ → C.IsSourceDifferentialMap β →
          C.IsCurveCofactorMap _ (F.localIso B U C) δ β αU ∧
          C.IsCurveJacobianMap _ (F.localIso B U C) δ β αU)) ∧
  (∀ (B : FlatLCIBaseChange p) (x : B.X'),
    IsIso ((RingedSpace.moduleStalkFunctor B.X'.toRingedSpace x).map (α B)) ↔
      ∃ U : B.X'.Opens, x ∈ U ∧ Smooth (U.ι ≫ B.p')) ∧
  (∀ (B D : FlatLCIBaseChange p) (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S')
    (hc : IsPullback g D.p' B.p' b) (hg : g ≫ B.g = D.g) (hb : b ≫ B.b = D.b)
    (O : B.X'.Opens) (a : Γ(B.X', O)),
    (F.baseChange B D g b hc hg hb).hom.app (g ⁻¹ᵁ O)
      (Scheme.Modules.tensorPullbackSection g (F.line B) O
        ((α B).app O (B.p'.relativeDifferentialsDerivation.d (X := op O) a))) =
      (α D).app (g ⁻¹ᵁ O)
        (D.p'.relativeDifferentialsDerivation.d (X := op (g ⁻¹ᵁ O)) (g.app O a)))

/-- A flat finitely presented lci curve over a Noetherian base has a unique
presentation-compatible fundamental class in its canonically normalized adjunction
line, simultaneously on all changes of base. The base changes need not be Noetherian
or flat. The cover is by actual regular affine polynomial presentations; formulas
hold for every presentation, rather than just those in the cover. No properness,
separatedness, nodality, marking, polarization, or reconstruction is assumed.

Source: Stacks, Duality, Tags 0E9Y and 0E9Z; More on Algebra, Tag 0FJM; Perfect,
Tags 0FJX and 0FJY (blueprint: lem-sfb-lci-curve-fundamental-class).

Proof, following the eight steps of the DAG:
1. The regular relations give the conormal basis and a Koszul-regular immersion
   (lem-weil-pbc-regular-sequence-conormal-free and
   lem-weil-pbc-regular-sequence-koszul-regular). The coordinate differentials give
   the ambient basis. Identify the conormal complex with the intrinsic cotangent
   complex by lem-trf-lci-cotangent-presentation. Its determinant is the specified
   adjunction line, by lem-sfb-adjunction-cotangent-determinant-normalization.
2. The cokernel of the conormal differential is the differential module, by its
   universal derivation property (def-weil-pbc-kahler-differentials). Send a lifted
   differential v to the dual conormal orientation tensor the wedge of the images
   of the ordered conormal basis followed by v. Altering the lift adds repeated
   wedge factors and hence zero. Basis changes cancel between the dual and wedge
   factors (def-weil-pbc-exterior-algebra).
3. Expand in the ordered coordinate basis to obtain the augmented Jacobian
   determinant. The rank-corrected kernel-first normalization fixes the explicit
   sign flatLCICurveFundamentalSign c to +1: for the conormal-to-differentials
   quasi-isomorphism the negative cone inclusion gives (-1)^c and the rank sign
   gives (-1)^c again. The scalar trivialization sends the displayed orientation
   to one. Stabilization by r variables changes both transition and cofactor
   orientations by (-1)^r, proving consistency also across codimensions.
4. On affine covers of arbitrary intersections, both conormal models identify
   with the intrinsic cotangent complex. Apply lem-sfb-two-term-cofactor-naturality
   and lem-sfb-adjunction-cotangent-determinant-normalization to the comparisons.
   Their local maps agree. The sheaf axiom glues them to the global morphism.
   The same comparison proves the formula in every additional presentation and
   uniqueness, because differentials of polynomial sections generate locally.
5. On the smooth locus, lem-sc-smooth-omega-finite-locally-free gives a line of
   differentials, and the conormal sequence is split exact locally. Wedging a
   conormal basis and a lift of its differential generator gives a generator of
   the ambient determinant. Thus the morphism is an isomorphism there.
6. Conversely, surjectivity on a stalk makes the maximal Jacobian minors generate
   the unit ideal. A minor is invertible nearby. Adjoin z with equation zh-1;
   the resulting minor is h squared, a unit. Apply
   lem-weil-pbc-standard-smooth-is-smooth and
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine. This includes c=0, whose minor is 1.
7. Restriction and transport by an isomorphism preserve the wedge formulas and
   the specified adjunction comparisons, so uniqueness gives their compatibility.
8. By lem-weil-pbc-flat-morphism-affine-criterion, the chart quotient is flat over
   the base. Base change is Tor-independent; lem-trf-lci-cotangent-presentation
   pulls back its projective two-term model, and lem-trf-two-term-perfect-determinant
   gives the specified determinant comparison. Wedges and partial derivatives
   commute with coefficient extension. The local equality glues, respects
   composition, and needs no flatness or Noetherianity of the new base. -/
theorem existsUnique_lciCurveFundamentalClass {X S : Scheme.{u}} (p : X ⟶ S)
    [IsNoetherian S] [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p] (hpure : HasPureFlatLCIGeometricFibres p 1)
    (hcharts : ∀ x : X, ∃ A : NodalCanonicalPresentation p, x ∈ A.U.1)
    (F : FlatLCIAdjunctionSystem p 1) (hF : F.IsNormalized) :
    ∃! α : ∀ B : FlatLCIBaseChange p, B.p'.relativeDifferentials ⟶ F.line B,
      F.IsCurveFundamentalClass α := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.TraceFormula.SpaceLineModuleProjMap
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.TraceFormula.ProjectiveBundleSeparated
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Projective bundles classify invertible quotients

Source: Stacks Project, Constructions, Tags 01OA, 01OB, 01O4, 01O9, 01OD and 01OE
(blueprint: lem-trf-projective-bundle-quotient-geometry).

The auxiliary records below spell out the conclusion for the fixed canonical symmetric
algebra. Existence and all geometric properties are asserted by the final theorem.
The classification uses the equivalent unique-morphism formulation, avoiding a choice
of representatives for isomorphism classes of quotient pairs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]

/-- The global degree-one twist and quotient, normalized on every affine base chart.
The chart equation sends the pulled-back section m to iota(m)/1 in the affine twist.
Source: Stacks, Tags 01OB, 01NR, 01O4
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
structure TautologicalQuotient where
  line : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules
  quotient : (Scheme.Modules.tensorPullback
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj E ⟶ line
  invertible : line.IsInvertible
  surjective : Epi quotient
  chart (U : S.affineOpens) :
    (Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj line ≅
      Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1
  generator (U : S.affineOpens) (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1) :
    (chart U).hom.app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (Scheme.Modules.tensorPullbackSection
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) line
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (((Scheme.Modules.tensorPullbackSectionAdjunction
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E line
              quotient).app U.1 m)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist
        (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)))

variable {E}

/-- The actual pullback quotient along an S-morphism, using the section-normalized
composition comparison of tensor pullbacks.
Source: Stacks, Tag 01OA (blueprint: lem-trf-projective-bundle-quotient-geometry). -/
noncomputable def pulledQuotient (D : TautologicalQuotient E) {T : Scheme.{u}}
    (h : T ⟶ S) (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h) :
    (Scheme.Modules.tensorPullback h).obj E ⟶
      (Scheme.Modules.tensorPullback a).obj D.line :=
  (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj E) ha)).inv ≫
    (Scheme.Modules.tensorPullbackSectionComp a
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
    (Scheme.Modules.tensorPullback a).map D.quotient

/-- A quotient pair corresponds to a exactly when the pullback of the universal
quotient is isomorphic to that pair, with the quotient map preserved.
Source: Stacks, Tag 01OA (blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def Classifies (D : TautologicalQuotient E) {T : Scheme.{u}} (h : T ⟶ S)
    (L : T.Modules) (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∃ ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h,
    ∃ v : (Scheme.Modules.tensorPullback a).obj D.line ≅ L,
      pulledQuotient D h a ha ≫ v.hom = q

/-- The scheme specialization of the canonical map of Tag 01O9. A frame of L turns
q into coefficients. The unique ring map fixing scalars and those coefficients is
Sym(E) to the tensor powers of L in that frame. The displayed map is precisely the
usual homogeneous-fraction construction, also used in GradedLineMap.IsCanonicalMap.
The ring map and its irrelevant-ideal condition are asserted to exist, not assumed.
Source: Stacks, Tags 01O9, 01OA; def-trf-space-line-module-proj-input
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def IsCanonicalMap {T : Scheme.{u}} (h : T ⟶ S) (L : T.Modules)
    (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∀ (V : S.affineOpens) (W : T.affineOpens) (hWV : W.1 ≤ h ⁻¹ᵁ V.1)
    (e : (Scheme.Modules.tensorPullback W.1.ι).obj L ≅
      SheafOfModules.unit W.1.toScheme.ringCatSheaf),
    ∃ α : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V →+*
        Γ(W.1.toScheme, ⊤),
      (∀ r : Γ(S, V.1), α (algebraMap Γ(S, V.1)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) r) =
          W.1.ι.appLE W.1 ⊤ (by simp) (h.appLE V.1 W.1 hWV r)) ∧
      (∀ m : E.val.obj (op V.1),
        α (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1)) m) =
          (Scheme.Modules.unitSectionsEquiv ⊤).symm
            (e.hom.app ⊤
              (((Scheme.Modules.tensorPullback W.1.ι).obj L).presheaf.map
                (homOfLE (show (⊤ : W.1.toScheme.Opens) ≤ W.1.ι ⁻¹ᵁ W.1 by simp)).op
                (Scheme.Modules.tensorPullbackSection W.1.ι L W.1
                  (L.presheaf.map (homOfLE hWV).op
                    (q.app (h ⁻¹ᵁ V.1)
                      (Scheme.Modules.tensorPullbackSection h E V.1 m))))))) ∧
      ∃ hα : Ideal.map α
          (HomogeneousIdeal.irrelevant
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)).toIdeal = ⊤,
        W.1.ι ≫ a = Proj.fromOfGlobalSections
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) α hα ≫
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V

/-- Restricting the canonical projective bundle to an arbitrary open of its base.
The map exhibits the fibre product and the line isomorphism preserves the quotient.
Source: Stacks, Tags 01NQ, 01NR, 01OA
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def HasOpenCompatibility (D : TautologicalQuotient E) : Prop :=
  ∀ V : S.Opens,
    ∃ hE : ((Scheme.Modules.tensorPullback V.ι).obj E).IsQuasicoherent,
      ∃ DV : @TautologicalQuotient V.toScheme
          ((Scheme.Modules.tensorPullback V.ι).obj E) hE,
        ∃ j : (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
            ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProj ⟶
              (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
          ∃ hj : IsPullback j
            (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
              ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProjHom
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom V.ι,
          ∃ w : (Scheme.Modules.tensorPullback j).obj D.line ≅ DV.line,
            (Scheme.Modules.tensorPullbackSectionComp j
              (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
              (Scheme.Modules.tensorPullback j).map D.quotient ≫ w.hom =
            (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj E)
              hj.w)).hom ≫
            (Scheme.Modules.tensorPullbackSectionComp
              (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
                ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProjHom V.ι).hom.app E ≫
              DV.quotient


/-- Over an affine base chart, the ordered basis gives exactly the standard graded
polynomial algebra. Both projective-space identifications use these polynomial charts,
and the degree-one twists correspond by a section-preserving isomorphism.
The local instance is only the specified Mathlib polynomial grading inside this definition.
Source: Stacks, Tags 01OE, 01OB, 01MN
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def AffineFreeComparison (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r) (V : S.affineOpens) : Prop := by
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (r + 1))) (R := Γ(S, V.1))
  exact ∃ β : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V,
    Function.Bijective β ∧
    (∀ x : Γ(S, V.1), β (MvPolynomial.C x) = algebraMap Γ(S, V.1)
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) x) ∧
    (∀ i : ULift.{u} (Fin (r + 1)), β (MvPolynomial.X i) =
      SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))
        (b.hom.app V.1 ((SheafOfModules.ιFree
          (R := S.ringCatSheaf) i).val.app (op V.1) (1 : Γ(S, V.1))))) ∧
    ∃ (hβ : HomogeneousIdeal.irrelevant
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map β)
      (eC : Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≅
        Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1)),
      eC.hom = Proj.map β hβ ∧
      (∃ t : (Scheme.Modules.tensorPullback eC.hom).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) 1) ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1,
        ∀ (s : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
          (hs : s ∈ MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1) 1),
          (Scheme.Modules.tensorPullback eC.hom).map (Proj.unitToTwist
            (𝒜 := MvPolynomial.homogeneousSubmodule
              (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) hs) ≫ t.hom =
          ((Scheme.Modules.boundaryPullbackComparison eC.hom).app
              (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eC.hom).hom ≫
            Proj.unitToTwist
              (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
              (β.map_mem hs)) ∧
      ∃ (γ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
            (RelativeProjectiveSpace.algebra S r).sectionGrade V)
        (hγ : HomogeneousIdeal.irrelevant
            ((RelativeProjectiveSpace.algebra S r).sectionGrade V) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule
              (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map γ)
        (eR : (RelativeProjectiveSpace.algebra S r).localProj V ≅
          Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1)),
        (∀ x, γ x = RelativeProjectiveSpace.affinePolynomialEquiv S r V
          (MvPolynomial.rename (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down) x)) ∧
        eR.hom = Proj.map γ hγ ∧
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ≫ eRel.hom =
          eC.hom ≫ eR.inv ≫ ((RelativeProjectiveSpace.construction S r).restrictionIso V).inv ≫
            (RelativeProjectiveSpace.π S r ⁻¹ᵁ V.1).ι

/-- The finite free case, with its ordered coordinate quotients and affine polynomial
models. ULift changes only the index universe, retaining all r+1 basis elements.
Source: Stacks, Tag 01OE; ProjectiveSpace.twist and its coordinate sections
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def HasFreeCompatibility (D : TautologicalQuotient E) : Prop :=
  ∀ (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E),
    ∃ (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        RelativeProjectiveSpace.scheme S r)
      (eStd : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        ℙ(ULift.{u} (Fin (r + 1)); S))
      (t : (Scheme.Modules.tensorPullback eStd.hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line),
      eRel.hom ≫ RelativeProjectiveSpace.π S r =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      eStd.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      (∀ i : ULift.{u} (Fin (r + 1)),
        (Scheme.Modules.tensorPullback
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
          (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
        ((Scheme.Modules.boundaryPullbackComparison
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
              (Scheme.Modules.unit S) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
        ((Scheme.Modules.boundaryPullbackComparison eStd.hom).app
            (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eStd.hom).inv ≫
        (Scheme.Modules.tensorPullback eStd.hom).map
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom) ∧
      ∀ V : S.affineOpens, AffineFreeComparison r b eRel V

/-- Projective bundles of arbitrary quasi-coherent modules represent invertible
quotients, naturally under arbitrary scheme pullback, with the prescribed twists,
open-base identifications, separated projection and free-module polynomial models.

Source: Stacks Project, Constructions, Tags 01OA, 01OB, 01O4, 01O9, 01OD and 01OE
(blueprint: lem-trf-projective-bundle-quotient-geometry).

Proof:
1. On an affine base U, the canonical symmetric grading is generated in degree one
(def-trf-canonical-symmetric-graded-algebra). The standard opens D_+(iota(m)) cover
relative Proj by lemma-nagata-relative-proj-exists and prop-nagata-proj-standard-open;
refine base intersections with lem-weil-pbc-affine-opens-basis.
2. On D_+(e), multiplication by e trivializes the degree-one twist, with inverse
x/e^k mapping to x/e^(k+1). On overlaps e=(e/f)f and (e/f)(f/g)=e/g. These are the
homogeneous-localization restrictions of def-weil-pbc-proj-twisting-sheaf and
lem-weil-pbc-proj-basic-open-intersection. Base restrictions preserve them. Glue by
lem-weil-pbc-site-module-sheaf-gluing, obtaining an invertible line.
3. The local section m maps to iota(m)/1. Adjunction
lem-pc-module-pullback-adjunction gives the quotient. It hits the frame e on each
D_+(e), hence is surjective. Its arbitrary tensor pullbacks remain surjective onto
invertible modules (def-pc-module-pullback).
4. Given q, extend its degree-one map by
lem-weil-pbc-quasi-coherent-symmetric-algebra to the graded map into powers of L.
The generation locus is all T, so lem-trf-space-line-module-proj-map supplies its
canonical map. The next steps explicitly verify its quotient and inverse property.
5. Trivialize L on affine W over affine U. By
lem-weil-pbc-module-pullback-affine-sections write q(m)=b_m l. The opens D(b_m)
cover W. On D(b_m), a/e^d maps to b(a)/b_m^d. This is a ring map by localization
and gives a scheme map by def-weil-affine-spectrum.
6. The fraction maps agree on overlaps by lem-weil-pbc-proj-basic-open-intersection.
Replacing l by u*l scales degree d by u^(-d), which cancels in every degree-zero
fraction. Canonical algebra restrictions and relative-Proj charts give the same
maps on base refinements. Glue by lem-weil-pbc-scheme-morphism-gluing. These are
exactly the maps of lem-trf-space-line-module-proj-map, proving IsCanonicalMap.
7. Send the pulled-back frame e to b_m*l. The coefficient of v is b_v/b_m, so this
isomorphism carries the universal quotient to q. Transition equations agree,
including on base refinements; hence these line isomorphisms glue.
8. Starting from a map a, use its pulled-back e frame. The coefficients of the
quotient are a^*(v/e), recovering a on all homogeneous fractions. Equality on
affine charts (def-weil-affine-spectrum) and scheme gluing prove uniqueness.
A compatible isomorphism of quotient pairs preserves all these coefficients.
Thus the correspondence is exactly the claimed bijection on isomorphism classes.
9. Pullback by u sends b(a)/b_m^d to u^*b(a)/(u^*b_m)^d. Thus the composite u;a
classifies the pulled-back quotient, with its pulled-back line isomorphism. Open
base restriction identifies both canonical affine algebras, hence their relative
Projs by lemma-nagata-relative-proj-exists. The twist and quotient agree on each
chart; def-pc-fibre-product identifies this restriction with the fibre product.
10. Apply lem-trf-projective-bundle-separated without a finiteness assumption.
11. For the ordered free basis, the symmetric algebra is the standard polynomial
algebra. Def-nagata-relative-projective-space supplies the same relative charts.
Their twist frames T_i have transitions T_i=(T_i/T_j)T_j, giving exactly
def-pc-projective-space-twist. The affine model is Proj of the polynomial algebra
with twist the shifted module. This includes r=0 and empty charts. -/
theorem projective_bundle_quotient_geometry (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] :
    ∃ D : TautologicalQuotient E,
      IsSeparated (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L),
        L.IsInvertible → Epi q →
        ∃! a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
          Classifies D h L q a) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
        (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h),
        ((Scheme.Modules.tensorPullback a).obj D.line).IsInvertible ∧
          Epi (pulledQuotient D h a ha)) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        L.IsInvertible → Epi q → Classifies D h L q a → IsCanonicalMap h L q a) ∧
      (∀ (T T' : Scheme.{u}) (h : T ⟶ S) (u : T' ⟶ T) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        L.IsInvertible → Epi q → Classifies D h L q a →
          Classifies D (u ≫ h) ((Scheme.Modules.tensorPullback u).obj L)
            ((Scheme.Modules.tensorPullbackSectionComp u h).hom.app E ≫
              (Scheme.Modules.tensorPullback u).map q) (u ≫ a)) ∧
      HasOpenCompatibility D ∧ HasFreeCompatibility D := by
  sorry

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry

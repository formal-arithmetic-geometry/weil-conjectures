/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent
import WeilConjectures.AlgebraicGeometry.ProperFlatSingleNoetherianDescent
import Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # A Noetherian comparison before choosing a finite-free resolution

Source: Stacks Project, Tag 0A1H, Noetherian approximation paragraph, and Tag 081F.
(blueprint: lem-pc-proper-flat-single-open-noetherian-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem isFinitePresentation_of_isZero (X : Scheme.{u})
    (N : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hN : CategoryTheory.Limits.IsZero N) :
    N.IsFinitePresentation := by
  let M := SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}
  have hz : CategoryTheory.Limits.IsZero M :=
    (CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mpr (by
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro i
      exact i.elim)
  let q : M.LocalGeneratorsData :=
    (SheafOfModules.free.generatingSections
      (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  have hf : q.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite PEmpty.{u + 1}
    infer_instance
  have : M.IsFiniteLocallyFree := by
    constructor
    exact ⟨q, hq, hf⟩
  have : N.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} (hz.iso hN)
  infer_instance

/-- Local approximation and transport data, without any finite-free resolution of the image.
Source: Stacks Project, Tag 0A1H, approximation paragraph; Tags 081F, 08E5 and 08E7.

Proof: Choose an affine neighbourhood V of x in U. Its ring is the filtered colimit of
its finitely generated Z-subalgebras. Restrict f and F to this neighbourhood. Apply
Noetherian approximation to the tensor data O_X and F[0], enlarging the stage to descend
relative flatness, properness of the morphism and proper term supports. Take T to be
that stage's affine spectrum and W its total open; replacing the stage by W.toScheme
only changes the data by the
canonical total-open isomorphism. Use standard localizations in universe u+1 at all
auxiliary stages. Denote the source by Y, its map by p, and the descended tensor by A.
The descended source is Noetherian: its morphism is finitely presented over a Noetherian
base. Its finitely presented terms are coherent. The perfect-tensor bounded-coherent
lemma gives the boundedness and coherence hypotheses on A. This supplies the
two source cohomology hypotheses below; it does not assert coherence or pseudo-coherence of Rp_*A.

Let g be the comparison from V to W and let L be tensor pullback along g followed by
W.ι, transported to the localized site of V. Tensor pullback is a left adjoint, hence
additive; it preserves finite free modules with their ranks, as does the localized-site
equivalence. For any bounded-above finite-free P representing Rp_*A after restriction
to W, P is K-flat. Termwise tensor pullback therefore computes derived pullback.
Relatively flat derived base change identifies this pullback with the original single
image on V. Compose with open base change and the exact localized-site equivalence.
To compare independent localizations, use their localization universal properties on
Q and compute both direct images by the same K-injective resolution. This proves the
comparison for every such P, without choosing P here. Empty U has no x; F=0 descends
to zero A, and the same comparison applies. No arbitrary existence witness defines
an object: all data below are used only in a theorem proof.
(blueprint: lem-pc-proper-flat-single-open-noetherian-comparison). -/
theorem properFlat_single_open_noetherian_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f) (U : S.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (x : U.toScheme) :
    ∃ V : U.toScheme.Opens, x ∈ V ∧
      ∃ (T Y : Scheme.{u}) (W : T.Opens),
        IsAffine T ∧ IsCompact (W : Set T) ∧ IsNoetherian W.toScheme ∧
        ∃ (dT : HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)))
          (dW : HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)))
          (dY : HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
          (dO : ∀ B : W.toScheme.Opens, HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over B))),
          letI := dT
          letI := dW
          letI := dY
          letI := dO
          ∃ p : Y ⟶ W.toScheme,
            IsProper p ∧ ∃ A : schemeDerivedCategory Y,
            (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
              IsZero ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) ∧
            (∀ i : ℤ, RingedSpace.IsCoherent Y.toRingedSpace
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) ∧
            ∃ (g : V.toScheme ⟶ W.toScheme)
              (L : T.Modules ⥤ SheafOfModules.{u}
                ((moduleRings U.toScheme.toRingedSpace).over V)),
              Nonempty (L ≅ Scheme.Modules.tensorPullback (g ≫ W.ι) ⋙
                (Scheme.Modules.overEquiv V).inverse) ∧
              ∃ hL : L.Additive,
                letI := hL
                (∀ P : CochainComplex T.Modules ℤ,
                  (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)) →
                  (∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
                    (R := moduleRings T.toRingedSpace) (ULift.{u} (Fin r)))) →
                  Nonempty ((schemeOpenRestriction T W).mapDerivedCategory.obj
                    (DerivedCategory.Q.obj P) ≅ (schemeDerivedDirectImage p).obj A) →
                  Nonempty ((SheafOfModules.overFunctor.{u}
                    (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
                    ((schemeOpenRestriction S U).mapDerivedCategory.obj
                      ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
                        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) ≅
                    DerivedCategory.Q.obj
                      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) := by
  classical
  obtain ⟨V, hx, T, Y, W, hT, hW, hnoethW, hnoethY, p, hp, M, hM, hflat,
    g, q, sq, eM⟩ := properFlat_single_noetherian_descent f F hF U x
  let : IsNoetherian Y := hnoethY
  let : IsProper p := hp
  let : M.IsFinitePresentation := hM
  let dT := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings T.toRingedSpace))
  let dW := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  let dY := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let dO := fun B : W.toScheme.Opens ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over B))
  let := dT
  let := dW
  let := dY
  let := dO
  let A := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  have hzero (i : ℤ) (hi : i < 0 ∨ 0 < i) :
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A) := by
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff A 0).mp inferInstance i hi
    · exact (DerivedCategory.isLE_iff A 0).mp inferInstance i hi
  have hcoh (i : ℤ) : RingedSpace.IsCoherent Y.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A) := by
    apply (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mpr
    have hfin : ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A).IsFinitePresentation := by
      by_cases hi : i = 0
      · subst i
        exact (SheafOfModules.isFinitePresentation (moduleRings Y.toRingedSpace)).prop_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).app M).symm hM
      · exact isFinitePresentation_of_isZero Y _ (hzero i (by omega))
    let := hfin
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction (g ≫ W.ι)
  let : (Scheme.Modules.tensorPullback (g ≫ W.ι)).Additive := adj.left_adjoint_additive
  let : (Scheme.Modules.overEquiv V).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let L := Scheme.Modules.tensorPullback (g ≫ W.ι) ⋙ (Scheme.Modules.overEquiv V).inverse
  refine ⟨V, hx, T, Y, W, hT, hW, hnoethW, dT, dW, dY, dO, p, hp, A,
    ⟨0, 0, hzero⟩, hcoh, g, L, ⟨Iso.refl _⟩, inferInstance, ?_⟩
  intro P hP hfree eP
  exact cartesian_flat_single_termwise_comparison f F U V W p M hflat g q sq eM
    L ⟨Iso.refl _⟩ P hP hfree eP

end AlgebraicGeometry

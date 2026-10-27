/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups F4 and J2
-/
module

public import Sheaf.SixFunctors.ProperImageLocalizingProper
import Sheaf.Paper.ContinuousAlgClLocalFree
import all Sheaf.Paper.ProperHeartConstructibleCohomology
import Sheaf.Paper.ContinuousAlgClProperLisseStratum
import Sheaf.Paper.BoundedFiniteModelGeneration
import all Sheaf.Paper.CoefficientHeartClosure
import all Sheaf.Paper.CoefficientHeartLisseRestriction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Proper direct image for the continuous-map algebraic-closure coefficient

Source: blueprint main-20261015, det-sf-comp-coherence-single, proper-image paragraph.
(blueprint: det-sf-comp-continuous-algcl-heart-finiteness).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Functor.rightDerivedFunctor upperStarFromPoint
  upperStar lowerStar IsLisseCoefficientModule


private theorem finiteModel_heart_image
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
      (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)),
      IsLocallyFinitelyPresented (condensedRingObj Λ T) L →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i,
        Mod.IsFree ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (U.f i)).obj
          (condensedRingObj Λ T))
          (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod
            (condensedRingObj Λ T)).obj L))
    (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      IsLisseCoefficientModule Λ L → ∀ n : ℤ, IsConstantModelConstructible Λ Y
        ((DerivedCategory.homologyFunctor _ n).obj
          (F.obj ((DerivedCategory.singleFunctor _ 0).obj
            ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj L))))))
    (M : ConstantModelConstructible Λ X) :
    ∀ n : ℤ, IsConstantModelConstructible Λ Y
      ((DerivedCategory.homologyFunctor _ n).obj
        (F.obj ((DerivedCategory.singleFunctor _ 0).obj M.obj))) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  let P : ObjectProperty B := IsConstantModelConstructible Λ Y
  have hclosure := (heart_closure_generic Λ hLF).2 Y
  have : P.IsClosedUnderKernels := hclosure.1
  have : P.IsClosedUnderCokernels := hclosure.2.1
  have : P.IsClosedUnderExtensions := hclosure.2.2.1
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ constantModelConstructible_of_iso Λ Y e h⟩
  have : P.ContainsZero := by
    obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject B).zero
    exact ⟨⟨Z, hZ, constantModelConstructible_of_isZero Λ Y Z hZ⟩⟩
  let Q := DerivedCategory.homologyProperty P
  let R := Q.inverseImage F
  have : R.IsClosedUnderIsomorphisms := inferInstance
  have : R.IsTriangulated := inferInstance
  have hM := constantModelConstructible_single Λ X M.obj M.property
  apply (bounded_finiteModel_generation Λ X R ?_
    ((DerivedCategory.singleFunctor A 0).obj M.obj) hM).1
  intro V S v hv t ht hS L hL
  have : TopologicalSpace.NoetherianSpace S :=
    (t ≫ v).isEmbedding.isInducing.noetherianSpace
  exact hgen V S v t L (heart_lisse_of_free Λ (hLF S L (constantModel_lfp Λ S L hL)))

/-- Higher proper direct images of one constructible sheaf have constructible cohomology
for the full continuous-map algebraic-closure coefficient.

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change, assertion (1),
in degree zero, as used in det-sf-comp-coherence-single's proper-image paragraph.
(blueprint: det-sf-comp-continuous-algcl-heart-finiteness).

Proof: the local finite-free theorem identifies finite constant-model constructibility
with stratified local finite presentation. The generic coefficient-heart closure theorem
therefore gives a weak Serre class on Y. Complexes with cohomology in that class form a
replete triangulated subcategory; take its inverse image under the proper derived
pushforward. The bounded finite-model generation theorem builds M[0] from reduced
locally closed stratum extensions by zero, using a finite sheaf filtration and its
short-exact-sequence triangles. The finite constant model on each stratum is locally
finitely presented, hence locally finite free by continuousAlgCl_lf. The separate
lisse-stratum finiteness theorem puts each such generator in the inverse-image class.
Finite extension closure gives the assertion for M[0]. Zero objects and empty strata
are covered by the zero object of the triangulated class. No uniform bound, finite Tor
amplitude or identification of the two algebraic-closure coefficient rings is used. -/
theorem continuousAlgCl_proper_heart_finiteness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (M : ConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X) :
    ∀ n : ℤ, IsConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y
      ((DerivedCategory.homologyFunctor _ n).obj
        ((lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) p).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M.obj))) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  exact finiteModel_heart_image _ (continuousAlgCl_lf ℓ) X Y
    (lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) p).rightDerivedFunctor
    (continuousAlgCl_proper_lisse_stratum ℓ k p) M

end AlgebraicGeometry.ProEtale.CondensedRing

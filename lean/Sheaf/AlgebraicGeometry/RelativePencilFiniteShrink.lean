/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts

/-!
# Shrinking a section pencil to a finite surjection

Source: de Jong, Families of curves and alterations, §3.4, printed p.606;
Stacks Project, Tags 01CY, 01NE, 01W4, 01W6, 02UP, 01WI, 01WL and 01NG.
(blueprint: lem-sfb-relative-pencil-finite-shrink).

The two homogeneous coordinates are indexed by `ULift (Fin 2)`. The helpers only package
ordinary pullback of sections and the recorded projective-coordinate construction.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Pull back the two ordinary global sections, retaining the existing section API.
Source: Stacks Project, Tags 0095 and 01NE; de Jong §3.4, p.606.
(blueprint: lem-sfb-relative-pencil-finite-shrink). -/
noncomputable def relativePencilSections {Y T : Scheme.{u}} (j : T ⟶ Y) (B : Y.Modules)
    (a : ULift.{u} (Fin 2) → B.sections) :
    ULift.{u} (Fin 2) → ((Scheme.Modules.pullback j).obj B).sections :=
  fun i ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
    (pullbackTopSection j ((a i).val (Opposite.op ⊤))))

/-- The existing coordinate morphism of the pulled-back pair, over the prescribed base.
Source: Stacks Project, Tag 01NE and the paragraph following Definition 01NF.
(blueprint: lem-sfb-relative-pencil-finite-shrink). -/
noncomputable def relativePencilHom {Y T S : Scheme.{u}} (j : T ⟶ Y) (q : T ⟶ S)
    (B : Y.Modules) [B.IsInvertible] (a : ULift.{u} (Fin 2) → B.sections)
    (h : Epi (((Scheme.Modules.pullback j).obj B).freeHomEquiv.symm
      (relativePencilSections j B a))) : T ⟶ ℙ(ULift.{u} (Fin 2); S) :=
  ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2)) q
    ((Scheme.Modules.pullback j).obj B) (relativePencilSections j B a) h

/-- A pencil finite on one fibre and finite surjective on the generic fibre spreads to
an affine neighbourhood, preserving its specified fibres, invariance and generic etaleness.

Source: de Jong §3.4, printed p.606; the quotient-free section-pencil argument extracted
from the local-pencil construction, with Stacks Tags 01CY, 01NE, 01W4, 01W6, 02UP, 01WI,
01WL and 01NG. (blueprint: lem-sfb-relative-pencil-finite-shrink).

Proof:
1. The union W of the two nonvanishing loci is open by
lem-weil-pbc-nonvanishing-section-trivializes. The fibre generation criterion
lem-weil-pbc-invertible-generating-sections-fibre shows it contains both specified fibres.
The proper image of its closed complement misses s. Choose a principal neighbourhood V
of s in the complement of that image. Its defining element is nonzero, so V contains the
generic point, and the pair generates over V.
2. The projective-coordinate construction and
lem-weil-pbc-projective-space-functor-of-points identify the restrictions of the resulting
V-map with the specified fibre maps, by pullback compatibility and relative uniqueness.
3. Proper base change (lem-weil-pbc-proper-fp-permanence), properness of projective space
(lemma-nagata-projective-space-base-change-proper), and
lem-weil-pbc-proper-over-separated make this V-map proper.
4. Over every point of the projective special fibre its set-fibre is finite, including
empty fibres, by lem-weil-pbc-finite-closed-map-finite-fibres and the fibre-product
identifications. Apply lem-trf-proper-finite-fibre-finite-near. The union O of the resulting
target opens contains that whole special fibre; lem-weil-pbc-finite-local-on-target makes
the map finite over O.
5. Remove the proper image under the projective-line projection of its closed complement.
Choose a principal affine neighbourhood U of s there. Its generic point remains present.
The projective line over U factors through O, so lem-weil-pbc-finite-morphism-permanence
makes the restricted pencil finite. Generation and the two fibre identifications persist.
6. The generic projective line is dense: lem-weil-pbc-projective-space-standard-charts gives
the two polynomial charts over a localization of the domain A. Each chart is a domain,
and its zero prime lies over the generic point and meets every nonempty basic open.
7. The finite image is closed by lem-weil-pbc-finite-closed-map-finite-fibres and contains
the entire generic projective line. Density therefore gives surjectivity.
8. Pullback compatibility and relative uniqueness identify the pencil with the restriction
of the coordinate map on W. Restrict the assumed group invariance to obtain invariance
over U. The generic fibre is the specified map itself, so every nonempty open on which
that map is etale remains the same etale open for the final generic pencil.
-/
theorem exists_relative_pencil_finite_shrink
    (A K : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (s : Spec (.of A)) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    (B : Y.Modules) [B.IsInvertible] (a : ULift.{u} (Fin 2) → B.sections)
    (hs : Epi (((Scheme.Modules.pullback (p.fiberι s)).obj B).freeHomEquiv.symm
      (relativePencilSections (p.fiberι s) B a)))
    (hK : Epi (((Scheme.Modules.pullback
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj B).freeHomEquiv.symm
        (relativePencilSections
          (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K)))) B a)))
    (hfiniteS : IsFinite (relativePencilHom (p.fiberι s) (p.fiberToSpecResidueField s) B a hs))
    (hfiniteK : IsFinite (relativePencilHom
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A K)))) B a hK))
    (hsurjK : Surjective (relativePencilHom
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A K)))) B a hK)) :
    ∃ (U : (Spec (.of A)).Opens), s ∈ U ∧ IsAffineOpen U ∧
    ∃ (is : Spec ((Spec (.of A)).residueField s) ⟶ U.toScheme)
      (iK : Spec (.of K) ⟶ U.toScheme)
      (his : is ≫ U.ι = (Spec (.of A)).fromSpecResidueField s)
      (hiK : iK ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap A K)))
      (hU : Epi (((Scheme.Modules.pullback (pullback.fst p U.ι)).obj B).freeHomEquiv.symm
        (relativePencilSections (pullback.fst p U.ι) B a)))
      (ψ : pullback p U.ι ⟶ ℙ(ULift.{u} (Fin 2); U.toScheme))
      (ψK : pullback p (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⟶
        ℙ(ULift.{u} (Fin 2); Spec (.of K))),
      ψ = relativePencilHom (pullback.fst p U.ι) (pullback.snd p U.ι) B a hU ∧
      IsFinite ψ ∧ Surjective ψ ∧
      baseChangeMap p (Over.homMk is his :
        Over.mk ((Spec (.of A)).fromSpecResidueField s) ⟶ Over.mk U.ι) ≫ ψ =
        relativePencilHom (p.fiberι s) (p.fiberToSpecResidueField s) B a hs ≫
          ProjectiveSpace.map (ULift.{u} (Fin 2)) is ∧
      baseChangeMap p (Over.homMk iK hiK :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⟶ Over.mk U.ι) ≫ ψ =
        ψK ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) iK ∧
      ψK = relativePencilHom
        (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K))))
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A K)))) B a hK ∧
      (∀ (G : Type v) [Group G] (ρ : G →* Aut (Over.mk p)) (W : Y.Opens)
        (hW : Epi (((Scheme.Modules.pullback W.ι).obj B).freeHomEquiv.symm
          (relativePencilSections W.ι B a))),
        (∀ W' : Y.Opens, Epi (((Scheme.Modules.pullback W'.ι).obj B).freeHomEquiv.symm
          (relativePencilSections W'.ι B a)) → W' ≤ W) →
        ∀ (ρW : G →* Aut W.toScheme),
          (∀ g : G, (ρW g).hom ≫ W.ι = W.ι ≫ ((ρ g).hom).left) →
          (∀ g : G, (ρW g).hom ≫ relativePencilHom W.ι (W.ι ≫ p) B a hW =
            relativePencilHom W.ι (W.ι ≫ p) B a hW) →
          ∀ g : G, ((Over.pullback U.ι).map (ρ g).hom).left ≫ ψ = ψ) ∧
      (∀ V : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap A K)))).Opens,
        Nonempty V →
        Etale (V.ι ≫ relativePencilHom
          (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A K))))
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A K)))) B a hK) →
        Etale (V.ι ≫ ψK)) := by
  sorry

end AlgebraicGeometry

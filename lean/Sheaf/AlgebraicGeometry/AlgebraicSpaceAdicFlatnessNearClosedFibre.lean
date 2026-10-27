module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.OpenFlatLocus
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.RingTheory.Flat.FlatModulePowers

/-! # Adic flatness along the closed fibre of an algebraic space

Source: Stacks Project, spaces-more-morphisms.tex, Tag 08VP,
lemma-flatness-over-Noetherian-ring, including openness in its proof
(blueprint: lem-sfb-space-adic-flatness-near-closed-fibre).

The helpers construct the quotient-spectrum maps and their actual sheaf fibre products.
The flat locus tests ordinary module stalks on every etale scheme chart. No completion,
separation, quasi-compactness, or support properness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical map Spec(A/I^n) → Spec(A), with the specified map to S.
Source: Stacks, Tag 08VP, definition of S_n
(blueprint: lem-sfb-space-adic-flatness-near-closed-fibre). -/
def adicQuotientSpectrumMap {S : Scheme.{u}} {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ≫ a)) ⟶
      schemeSpace (Over.mk a) :=
  ObjectProperty.homMk ⟨yoneda.map (Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) rfl)⟩

/-- The actual sheaf fibre product Y_n = Y ×_A Spec(A/I^n).
Its algebraic-space property is supplied by the recorded fibre-product theorem.
Source: Stacks, Tag 08VP, definition of X_n
(blueprint: lem-sfb-space-adic-flatness-near-closed-fibre). -/
def adicFibre {S : Scheme.{u}} {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ S) {Y : AlgebraicSpace S}
    (p : Y ⟶ schemeSpace (Over.mk a)) (I : Ideal A) (n : ℕ) : AlgebraicSpace S :=
  ⟨Limits.pullback p.hom (adicQuotientSpectrumMap a I n).hom,
    (fibreProduct_isAlgebraicSpace _ _ _ p (adicQuotientSpectrumMap a I n)).1⟩

/-- The canonical projection Y_n → Y, along which F_n is tensor pullback.
Source: Stacks, Tag 08VP, definition of F_n
(blueprint: lem-sfb-space-adic-flatness-near-closed-fibre). -/
def adicFibreInclusion {S : Scheme.{u}} {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ S) {Y : AlgebraicSpace S}
    (p : Y ⟶ schemeSpace (Over.mk a)) (I : Ideal A) (n : ℕ) :
    adicFibre a p I n ⟶ Y :=
  ObjectProperty.homMk (Limits.pullback.fst p.hom (adicQuotientSpectrumMap a I n).hom)

/-- The canonical projection Y_n → Spec(A/I^n).
Source: Stacks, Tag 08VP, structural morphism of X_n
(blueprint: lem-sfb-space-adic-flatness-near-closed-fibre). -/
def adicFibreProjection {S : Scheme.{u}} {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ S) {Y : AlgebraicSpace S}
    (p : Y ⟶ schemeSpace (Over.mk a)) (I : Ideal A) (n : ℕ) :
    adicFibre a p I n ⟶
      schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ≫ a)) :=
  ObjectProperty.homMk (Limits.pullback.snd p.hom (adicQuotientSpectrumMap a I n).hom)

/-- The locus where the ordinary module stalk on every etale chart is flat over the
local ring of its image in Spec(A). Scalars are restricted along the actual stalk map.
Source: Stacks, Tag 08VP, flat locus in the proof; Tag 05VU, chartwise flatness
(blueprint: lem-sfb-space-adic-flatness-near-closed-fibre). -/
def moduleFlatLocusOverSpectrum {S : Scheme.{u}} {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ S) {Y : AlgebraicSpace S}
    (p : Y ⟶ schemeSpace (Over.mk a)) (F : Y.Modules) : Set (Point Y.obj.obj) :=
  {z | ∀ (T : Y.EtaleSite) (t : Y.etaleForget.obj T), schemePointMap T.obj.hom t = z →
    Module.Flat
      ((Spec (CommRingCat.of A)).presheaf.stalk
        ((yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left t))
      ((ModuleCat.restrictScalars
        (((yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left).stalkMap t).hom).obj
        ((RingedSpace.moduleStalkFunctor (Y.etaleForget.obj T).toRingedSpace t).obj
          ((Y.schemeRestriction T).obj F)))}

/-- The relative module-flatness locus is open and contains the closed inverse image
when all positive ideal-power reductions are flat.
Source: Stacks, Tag 08VP, lemma-flatness-over-Noetherian-ring, and its proof
(blueprint: lem-sfb-space-adic-flatness-near-closed-fibre).

Proof:
1. On an affine etale chart Spec(B) → Y, the quasi-coherent chart calculus
   (lem-sfb-space-qcoh-affine-chart-calculus) identifies F with a finitely presented
   B-module M. Local finite presentation of p makes B finitely presented over A
   (lem-weil-pbc-lfp-affine-opens-finite-presentation), hence B is Noetherian
   (lem-weil-pbc-finite-type-algebra-noetherian); M is finite.
2. The tilde stalk formula (lem-weil-pbc-spec-tilde-stalk-localization), flatness
   over a localization (lem-weil-pbc-flat-over-localization), and pointwise chart
   independence (lem-sfb-space-module-flat-point-chart-independence) identify the
   inverse image of the locus with {q | M_q is A-flat}. It is open by
   lem-weil-pbc-openness-of-flatness. The affine basis and final point topology
   (lem-weil-pbc-affine-opens-basis, def-a1-space-point-topology) imply openness on Y.
3. Base change of the chart gives Spec(B/I^n B) → Y_n, still etale by
   lem-trf-space-fibre-products-etale-covers. The affine fibre-product formula
   (lem-weil-pbc-fibre-product-affine-spectra), tensor-pullback composition
   (def-sfb-space-module-tensor-composition), the Zariski/etale comparison
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence), and tilde base change
   (lem-weil-pbc-tilde-pullback-base-change) identify the restricted F_n with
   M/I^n M. Explicitly b-bar tensor m maps to bm modulo I^n M, with inverse
   m-bar mapping to 1 tensor m. Thus the assumed relative flatness gives flatness
   of these modules over A/I^n by def-pc-scheme-module-flat-over.
4. Apply lem-weil-pbc-flat-module-powers to A → B and M. It gives A-flatness
   of M_q for each q containing IB. These are precisely the chart points mapping
   into V(I), since I is contained in the inverse-image prime iff IB is in q.
   Every point lifts to an affine etale chart (def-trf-algebraic-space and
   lem-weil-pbc-affine-opens-basis), proving containment. No completion, separatedness,
   quasi-compactness, or proper support enters this argument. -/
theorem isOpen_moduleFlatLocusOverSpectrum_and_closedFibre_subset
    {S : Scheme.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a : Spec (CommRingCat.of A) ⟶ S) (I : Ideal A) (Y : AlgebraicSpace S)
    (p : Y ⟶ schemeSpace (Over.mk a)) (hp : MapIsLocallyOfFinitePresentation p)
    (F : Y.Modules) (hF : F.IsFinitePresentation) (hFqc : F.IsQuasicoherent) :
    IsOpen (moduleFlatLocusOverSpectrum a p F) ∧
      ((∀ n : ℕ, 1 ≤ n → ModuleIsFlatOver (adicFibreProjection a p I n)
        ((moduleTensorPullback (adicFibreInclusion a p I n)).obj F)) →
        ∀ (T : Y.EtaleSite) (t : Y.etaleForget.obj T),
          I ≤ ((yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left t).asIdeal →
            schemePointMap T.obj.hom t ∈ moduleFlatLocusOverSpectrum a p F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.AlgebraicGeometry.RelativeH1ImmersionUniversalKoszul
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Sheaf.AlgebraicGeometry.FieldExtensionImmersionKoszulPoints
import Sheaf.RingTheory.FlatQuotientFiberRegularSequence
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular

/-!
# Koszul points of a relative scheme morphism under parameter base change

Source: Stacks Project, More on Morphisms, Tag 06B8, `lemma-base-change-lci-fibres`;
Tag 069F, `definition-lci`
(blueprint: lem-sfb-scheme-relative-lci-base-change-points).

The existing `RelativeFiniteHilbert.SchemeLci` expresses the finite Koszul-regular
closed-immersion and smooth factorization, including the empty sequence. Koszul
regularity at a point is expressed by an open neighbourhood on which this holds.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For flat locally finitely presented families, an arbitrary parameter base change
preserves and reflects Koszul regularity at each lifted source point.

Source: Stacks Project, More on Morphisms, Tag 06B8; the local convention is Tag 069F
(blueprint: lem-sfb-scheme-relative-lci-base-change-points).

Proof plan, following the six steps of the DAG node:
1. At the image point choose affine charts over the base and a finite polynomial
   presentation of the source over the target. The finite-presentation cancellation
   lemma `lem-a1-map-over-base-finite-presentation` applies to the structural maps.
   This embeds the source chart into affine space over the target chart. Its ambient
   projection is smooth and flat, and its composite to the base is flat and finitely
   presented. The affine flatness criterion identifies both relevant flat algebras.
2. If the original map is Koszul at the image, smooth-ambient independence makes this
   polynomial-chart immersion Koszul-regular near the point. Apply
   `lem-sfb-relative-h1-immersion-universal-koszul` to its H1-regularity and flat source.
   It stays Koszul-regular under the arbitrary parameter change. Pullbacks of open
   charts are open and smoothness survives base change and composition with opens,
   giving the required lci neighbourhood upstairs.
3. Conversely, upstairs Koszul regularity and smooth-ambient independence make the
   pulled-back polynomial immersion Koszul-regular near the lifted point. Its source
   is flat over the new base by `lem-sfb-pointwise-flatness-base-change`, and its
   ambient is locally finitely presented. The relative H1 immersion lemma then gives
   Koszul regularity on the residue-field fibre at the new parameter point.
4. `lem-weil-pbc-fibre-of-base-change` identifies this fibre immersion with the old
   fibre immersion after the induced residue-field extension. The old ambient fibre
   is locally of finite type over a field. Apply
   `lem-sfb-field-extension-immersion-koszul-points` to descend regularity at the point.
5. By `lem-sfb-koszul-closed-immersion-affine-criterion`, the fibre-local ideal has
   finite Koszul-regular generators. The fibre algebra and its localization are
   Noetherian, and these germs lie in the maximal ideal of the nonzero local ring.
   `lem-per-noetherian-local-koszul-criterion` makes them a regular sequence, including
   the empty sequence.
6. `lem-pur-flat-quotient-fiber-regular-sequence` applies to the flat finitely presented
   ambient algebra, its finitely generated ideal and its flat quotient. It gives
   regular generators on a principal neighbourhood of the original point. They are
   Koszul-regular by `lem-weil-pbc-regular-sequence-koszul-regular`; the affine criterion
   and restriction of the smooth ambient projection give the lci neighbourhood
   downstairs. Empty base-changed sources have no point to check. -/
theorem scheme_relative_lci_base_change_points
    {B X Y : Scheme.{u}} (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y)
    (h : p = f ≫ q) [Flat p] [Flat q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    {T : Scheme.{u}} (g : T ⟶ B) (xT : (pullback p g : Scheme.{u})) :
    (∃ U : (pullback p g).Opens, xT ∈ U ∧
      RelativeFiniteHilbert.SchemeLci
        (U.ι ≫ pullback.map p g q g f (𝟙 T) (𝟙 B)
          ((Category.comp_id p).trans h)
          ((Category.comp_id g).trans (Category.id_comp g).symm))) ↔
    ∃ V : X.Opens, (pullback.fst p g) xT ∈ V ∧
      RelativeFiniteHilbert.SchemeLci (V.ι ≫ f) := by
  sorry

end AlgebraicGeometry

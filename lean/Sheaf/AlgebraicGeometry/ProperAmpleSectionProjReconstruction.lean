/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
import Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Proper ample reconstruction by the full relative section algebra

Source: Stacks Project, Morphisms, Tags 01VJ and 0C6J; Constructions, Tags 01MY and 01MZ
(blueprint: lem-sfb-proper-ample-section-proj-reconstruction).

The auxiliary predicates unpack the affine fraction formula, compatibility of the maps
and their inverses on affine refinements, and the normalized polarized section map.
They introduce no alternative section algebra, pullback, tensor power or relative Proj.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The local reconstruction formula: the inverse image of a standard open is the
nonvanishing locus, and the pullback of t/s^a multiplied by s^a is t. Evaluation uses
actual tensor-section pullback, including degree zero. The denominator section is a
power in the full section algebra, with the multiplication fixed by `A.mul`.
The affine algebra is identified with the existing full invertible section ring by
the evaluated homogeneous sections. Its products are fixed by `A.mul`; the additive
identification therefore identifies tensor-product multiplication as well.
Source: Stacks, Properties, Tag 01PZ; Constructions, Tags 01N8 and 01O9
(blueprint: lem-sfb-proper-ample-section-proj-reconstruction). -/
def RelativeSectionAlgebra.HasReconstructionChart {X S : Scheme.{u}} {f : X ⟶ S}
    {L : X.Modules} (A : RelativeSectionAlgebra f L) (V : S.affineOpens)
    (q : (f ⁻¹ᵁ V.1).toScheme ≅ Proj (A.data.grading V)) : Prop :=
  ∀ h : (⊤ : (f ⁻¹ᵁ V.1).toScheme.Opens) ≤ (f ⁻¹ᵁ V.1).ι ⁻¹ᵁ (f ⁻¹ᵁ V.1),
    (∃ e : A.data.obj V ≃+
        InvertibleSectionRing ((tensorPullback (f ⁻¹ᵁ V.1).ι).obj L),
      ∀ (n : ℕ) (a : A.data.grading V n),
        e a = DirectSum.of (SectionRingComponent
          ((tensorPullback (f ⁻¹ᵁ V.1).ι).obj L)) n
            (A.evaluate (f ⁻¹ᵁ V.1).ι V h n a)) ∧
    ∀ (d : ℕ), 0 < d → ∀ s : A.data.grading V d,
      (q.hom ⁻¹ᵁ Proj.basicOpen (A.data.grading V) s.val :
          Set (f ⁻¹ᵁ V.1).toScheme) =
        nonvanishingLocus (((tensorPullback (f ⁻¹ᵁ V.1).ι).obj L).tensorPow d)
          (A.evaluate (f ⁻¹ᵁ V.1).ι V h d s) ∧
      ∀ (a : ℕ) (t : A.data.grading V (a • d)),
        (q.hom.app (Proj.basicOpen (A.data.grading V) s.val)
          (Proj.awayToSection (A.data.grading V) s.val
            (HomogeneousLocalization.Away.mk (A.data.grading V) s.property a
              t.val t.property))) •
          (((tensorPullback (f ⁻¹ᵁ V.1).ι).obj L).tensorPow (a • d)).val.map
            (homOfLE (le_top : q.hom ⁻¹ᵁ Proj.basicOpen (A.data.grading V) s.val ≤ ⊤)).op
            (A.evaluate (f ⁻¹ᵁ V.1).ι V h (a • d)
              ⟨s.val ^ a, SetLike.pow_mem_graded a s.property⟩) =
        (((tensorPullback (f ⁻¹ᵁ V.1).ι).obj L).tensorPow (a • d)).val.map
          (homOfLE (le_top : q.hom ⁻¹ᵁ Proj.basicOpen (A.data.grading V) s.val ≤ ⊤)).op
          (A.evaluate (f ⁻¹ᵁ V.1).ι V h (a • d) t)

/-- Reconstruction includes the canonical evaluation map, its isomorphisms on every
affine base open, and the compatibility of both directions on every affine refinement.
`RelativeSectionAlgebra.data` encodes quasi-coherence, while its `sectionEquiv`, `one`,
`mul` and `restriction` fix the full tensor section algebra; its zeroth piece is the
sections of L^0 = O_X, with no identification with O_S.
Source: Stacks, Morphisms, Tags 01VJ and 0C6J
(blueprint: lem-sfb-proper-ample-section-proj-reconstruction). -/
def RelativeSectionAlgebra.IsProperAmpleReconstruction {X S : Scheme.{u}}
    {f : X ⟶ S} {L : X.Modules} (A : RelativeSectionAlgebra f L)
    (r : X ≅ A.data.relProj) : Prop :=
  (∐ fun n : ℕ ↦ (pushforward f).obj (L.tensorPow n)).IsQuasicoherent ∧
    A.IsCanonicalMap r.hom ∧
    ∃ q : ∀ V : S.affineOpens, (f ⁻¹ᵁ V.1).toScheme ≅ Proj (A.data.grading V),
      (∀ V, (q V).hom ≫ A.data.relProjι V = (f ⁻¹ᵁ V.1).ι ≫ r.hom) ∧
      (∀ V, (q V).hom ≫ A.data.toOpen V = f ∣_ V.1) ∧
      (∀ V, A.HasReconstructionChart V (q V)) ∧
      (∀ (V W : S.affineOpens) (h : W ≤ V),
        X.homOfLE (f.preimage_mono h) ≫ (q V).hom =
          (q W).hom ≫ Proj.map (A.data.res h) (A.data.irrelevant_le_map_res h)) ∧
      (∀ (V W : S.affineOpens) (h : W ≤ V),
        (q W).inv ≫ X.homOfLE (f.preimage_mono h) =
          Proj.map (A.data.res h) (A.data.irrelevant_le_map_res h) ≫ (q V).inv)

/-- The degreewise characterization of the polarized graded algebra isomorphism.
A homogeneous section is pulled back by the normalized 1-tensor-section map, then
transported along the canonical tensor-power comparison and the tensor power of lambda.
The inclusion proof merely restricts that section to the appropriate inverse-image open;
for an isomorphism over S these opens are equal.
Source: Stacks, Modules, Tag 01CD; Constructions, Tag 01MY
(blueprint: lem-sfb-proper-ample-section-proj-reconstruction). -/
def RelativeSectionAlgebra.IsPolarizedIso {X X' S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} {L : X.Modules} {L' : X'.Modules}
    (A : RelativeSectionAlgebra f L) (A' : RelativeSectionAlgebra f' L')
    (h : X' ≅ X) (lam : (tensorPullback h.hom).obj L ≅ L')
    (phi : A.data ≅ A'.data) : Prop :=
  ∀ (V : S.affineOpens) (n : ℕ) (a : A.data.grading V n)
    (hle : f' ⁻¹ᵁ V.1 ≤ h.hom ⁻¹ᵁ (f ⁻¹ᵁ V.1)),
    A'.sectionEquiv V n ⟨phi.hom.app V a, (phi.hom.app V).map_mem a.property⟩ =
      (boundaryPullbackPowIso h.hom L n ≪≫ boundaryTensorPowIso lam n).hom.app
        (f' ⁻¹ᵁ V.1)
        (((tensorPullback h.hom).obj (L.tensorPow n)).val.map (homOfLE hle).op
          (tensorPullbackSection h.hom (L.tensorPow n) (f ⁻¹ᵁ V.1)
            (A.sectionEquiv V n a)))

/-- Polarized naturality for any other reconstruction. The algebra isomorphism is
uniquely fixed by its action on homogeneous sections; the Proj isomorphism is the
existing contravariant `relProjIsoOfIso`, not an arbitrarily chosen comparison.
Source: Stacks, Constructions, Tags 01MY and 01MZ
(blueprint: lem-sfb-proper-ample-section-proj-reconstruction). -/
def RelativeSectionAlgebra.HasPolarizedNaturality {X S : Scheme.{u}}
    {f : X ⟶ S} {L : X.Modules} (A : RelativeSectionAlgebra f L)
    (r : X ≅ A.data.relProj) : Prop :=
  ∀ (X' : Scheme.{u}) (f' : X' ⟶ S) (L' : X'.Modules)
    (A' : RelativeSectionAlgebra f' L') (r' : X' ≅ A'.data.relProj),
    A'.IsProperAmpleReconstruction r' →
      ∀ (h : X' ≅ X), h.hom ≫ f = f' →
        ∀ lam : (tensorPullback h.hom).obj L ≅ L',
          ∃! phi : A.data ≅ A'.data,
            A.IsPolarizedIso A' h lam phi ∧
              r'.hom ≫ (GradedAlgebraData.relProjIsoOfIso phi).hom = h.hom ≫ r.hom

/-- Identity and composition for the specified section maps and their contravariant
Proj isomorphisms. The composite polarization uses the normalized pullback composition
comparison. Equality of the algebra maps is tested on the actual tensor-power sections,
so these laws retain the degree-zero and scalar normalization.
Source: Stacks, Constructions, Tag 01MZ; Sheaves, Tag 0097
(blueprint: lem-sfb-proper-ample-section-proj-reconstruction). -/
def RelativeSectionAlgebra.PolarizedCoherence {X S : Scheme.{u}}
    {f : X ⟶ S} {L : X.Modules} (A : RelativeSectionAlgebra f L) : Prop :=
  (∀ phi : A.data ≅ A.data,
    A.IsPolarizedIso A (Iso.refl X) ((tensorPullbackSectionId X).app L) phi →
      phi = Iso.refl A.data ∧
        GradedAlgebraData.relProjIsoOfIso phi = Iso.refl A.data.relProj) ∧
  (∀ (X' X'' : Scheme.{u}) (f' : X' ⟶ S) (f'' : X'' ⟶ S)
    (L' : X'.Modules) (L'' : X''.Modules)
    (A' : RelativeSectionAlgebra f' L') (A'' : RelativeSectionAlgebra f'' L'')
    (h : X' ≅ X) (k : X'' ≅ X'), h.hom ≫ f = f' → k.hom ≫ f' = f'' →
    ∀ (lam : (tensorPullback h.hom).obj L ≅ L')
      (mu : (tensorPullback k.hom).obj L' ≅ L'')
      (phi : A.data ≅ A'.data) (psi : A'.data ≅ A''.data)
      (omega : A.data ≅ A''.data),
      A.IsPolarizedIso A' h lam phi → A'.IsPolarizedIso A'' k mu psi →
      A.IsPolarizedIso A'' (k ≪≫ h)
        ((tensorPullbackSectionComp k.hom h.hom).app L ≪≫
          (tensorPullback k.hom).mapIso lam ≪≫ mu) omega →
      omega = phi ≪≫ psi ∧
        GradedAlgebraData.relProjIsoOfIso omega =
          GradedAlgebraData.relProjIsoOfIso psi ≪≫ GradedAlgebraData.relProjIsoOfIso phi)

/-- A proper scheme with a relatively ample invertible module is canonically the
relative Proj of its full tensor section algebra. The quasi-coherent affine-basis
presentation includes the actual degree-zero direct image, all affine chart formulas,
compatibility of both inverses on refinements, and polarized naturality with its
identity and composition laws.

Source: Stacks, Morphisms, Tags 01VJ and 0C6J; Constructions, Tags 01MY and 01MZ
(blueprint: lem-sfb-proper-ample-section-proj-reconstruction).

Proof, following the eight steps of the node:
1. Proper implies finite type, quasi-compact and separated, hence quasi-separated
(def-weil-proper-morphism, def-weil-finite-type-morphism,
lem-pc-separated-quasi-separated). The qcqs section-algebra evaluation construction
(lem-trf-qcqs-line-section-algebra-evaluation) gives the quasi-coherent algebra of all
powers with tensor multiplication. The relative ampleness criterion
(lem-trf-scheme-ample-canonical-proj-criterion, 01VJ) gives the canonical open immersion.
Degree zero is f_*O_X throughout.
2. On an affine base open, use the ordinary canonical map of the full section ring
(lem-sc-ample-proj-canonical-map). Its standard-open preimage and fraction formulas
are exactly `HasReconstructionChart`, with the fraction expressed by multiplication
by the invertible denominator section.
3. The image is dense. If D_+(s) misses it, X_s is empty. Section localization
(lem-sc-section-ring-localization-bijective) makes the chart ring zero, contradicting
nonemptiness of D_+(s). Quasi-separatedness follows from ampleness and separatedness
(lem-weil-pbc-ample-scheme-separated, lem-pc-separated-quasi-separated).
4. Restrict properness to the affine base (lem-pc-proper-base-change). The target Proj
is separated (lem-trf-proj-separated, lem-weil-pbc-separated-cancellation), so the
canonical map is proper (lem-weil-pbc-proper-over-separated). Its image is closed,
and hence all of the target by density. A surjective open immersion is an isomorphism.
5. On affine refinements the evaluation descriptions agree. The local inverses agree
by uniqueness, and glue (lem-weil-pbc-scheme-morphism-gluing) to the inverse of r.
The trivialized evaluation formula verifies `IsCanonicalMap`.
6. A polarized isomorphism acts by lambda^n h^* in degree n. The normalized pullback
unit and tensor comparisons preserve multiplication, scalars, the degree-zero unit
and restrictions (lem-weil-pbc-invertible-pullback-tensor). Pullback by h inverse gives
the inverse graded map. Homogeneous sections determine it uniquely.
7. Apply the graded-isomorphism Proj chart formula
(lem-trf-local-proj-isomorphism-compatibility). Both composites in naturality have the
same standard-open preimages and pull back t/s^a to the same quotient. Glue equality.
8. For identities the homogeneous section maps are identities. For composition,
the normalized pullback composition comparison makes the section maps compose.
The fraction formula gives the reversed composition of Proj maps (01MZ), and
substituting the two naturality equalities gives naturality for the composite.
No empty-scheme, nonreduced or non-Noetherian case is excluded. -/
theorem proper_ample_section_proj_reconstruction {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (L : X.Modules) [L.IsInvertible]
    (hample : ∀ V : S.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj L).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) h) :
    ∃ (A : RelativeSectionAlgebra f L) (r : X ≅ A.data.relProj),
      A.IsProperAmpleReconstruction r ∧ A.HasPolarizedNaturality r ∧
        A.PolarizedCoherence := by
  sorry

end AlgebraicGeometry.Scheme.Modules

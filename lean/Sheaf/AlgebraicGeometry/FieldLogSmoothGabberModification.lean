module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Sheaf.AlgebraicGeometry.DivisorialLogCoverBoundary
public import Sheaf.AlgebraicGeometry.GabberModificationData
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.TraceFormula.ProjectiveBundleSeparated
import Sheaf.AlgebraicGeometry.GabberAbsoluteEquivariantModification
import Sheaf.AlgebraicGeometry.VeryTameLogQuotient
import Sheaf.AlgebraicGeometry.GabberAbelianStageToricChart
import Sheaf.TraceFormula.LogRegularDivisorialStructure

/-! # Gabber's log-smooth modification over a fixed field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X Theorem 1.1,
printed pp.135--136, and its proof, 1.3--1.8, pp.139--148; VI 3.2--3.5
(blueprint: lem-sfb-field-log-smooth-gabber-modification).

The trivial field log structure is presented by an fs log structure whose triviality
locus is the whole spectrum. Its log unit condition identifies it with the units.
The open `U` represents the complement of the original closed boundary. The output
open `V` is exactly the inverse image of `U` intersected with the largest free open;
its complement is therefore precisely the inverse image of the old boundary union
the nonfree locus. All divisorial identifications use the existing structural maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A tame generically free finite group action on a quasi-projective fs log regular
pair, log smooth over the trivial log field, admits a projective birational modification
with very tame action. Both the modified pair and its invariant divisorial quotient
remain log smooth over the same field. No perfectness or nonempty-boundary assumption
is made. The dense-open isomorphism expresses birationality of this particular map.
Source: ILO X Theorem 1.1, pp.135--136; X 1.3--1.8, pp.139--148; VI 3.2--3.5
(blueprint: lem-sfb-field-log-smooth-gabber-modification).

Proof (the seven steps of the DAG):

1. A field is excellent (lem-exc-fields-excellent), so finite type gives a Noetherian
quasi-excellent source (lem-per-quasi-excellent-finite-type-stability). Quasi-projectivity
and separatedness of projective space (lem-trf-projective-bundle-separated) give the
separatedness required by ILO X 1.1. The trivial field log structure is log regular.
Inertia orders divide the invertible group order, giving tameness.

2. Use the four-stage tower of lem-per-gabber-absolute-equivariant-modification over
Spec F. Its composite is integral, equivariant and H-projective, with quasi-projective
finite-type source. It is an isomorphism over the dense intersection of the original
triviality and free opens. Its boundary is the inverse image of B union T, and its
final action is very tame. This step alone does not assert log smoothness.

3. The first two stages are saturated log blowup towers and hence log etale.
By lem-per-log-smooth-composition-strict-base-change they preserve log smoothness
over the same field, as well as the regular strict boundary needed for stage three.

4. For each third-stage fixed-locus blowup use lem-per-gabber-fixed-locus-log-chart.
The z_i chart changes the monoid group map by a unipotent automorphism. The y_i
chart adds a free rank-one cokernel. Thus injectivity and invertible-order torsion
of the chart group cokernel are preserved. The remaining variables are polynomial,
so the scheme comparisons are smooth. The chart criterion def-per-fs-log-smooth-etale
and strict etale locality from lem-per-log-smooth-composition-strict-base-change give
log smoothness of every actual blowup. Iterate through the finite procedure.

5. The quasi-projective finite-group quotient exists by
lem-per-projective-finite-group-quotient. It is integral, quasi-projective of finite
type, finite surjective, categorical, and has invariant structure sheaf and geometric
orbit fibres. Its affine inverse images give admissibility. Apply
lem-per-very-tame-log-quotient to obtain the invariant fs log regular quotient and
its Kummer etale projection, with the invariant map to the fixed field base.

6. Apply lem-per-gabber-abelian-stage-toric-chart to stage three. It is Noetherian,
quasi-excellent and separated by the finite-type and projectivity arguments of step 1.
For the retained-boundary quotient chart, Q^gp injects into R'^gp, and the torsion of
its cokernel embeds into the old invertible-order torsion plus a free group. The
comparison of the enlarged and retained-boundary models is an affine-space projection.
Thus the chart criterion and strict etale locality give log smoothness of the quotient;
composition with its log etale projection gives log smoothness of the modified source.

7. The injective Kummer characteristic maps identify triviality on source and quotient:
a sharp saturated monoid has torsion-free group completion, so one characteristic
monoid is zero exactly when the other is. Orbit fibres and invariance identify the
quotient nontriviality locus with the image of the exact modified boundary. Apply
lem-trf-log-regular-divisorial-structure to both log regular schemes to recover their
divisorial sheaves for precisely these complements. The charts used only local base
changes, so all global maps remain over F. Empty B is permitted, and for trivial G
the identity modification suffices.
-/
theorem exists_field_logSmooth_gabber_modification
    (F : Type u) [Field F]
    (N : EtaleLogStructure (Spec (.of F))) (hN : N.IsFineSaturated)
    (htrivial : N.trivialityLocus = Set.univ)
    (X : FineSaturatedLogScheme.{u}) [IsIntegral X.scheme]
    (f : EtaleLogHom X ⟨Spec (.of F), inferInstance, N, hN⟩)
    [LocallyOfFiniteType f.base] [QuasiCompact f.base]
    (hprojective : IsQuasiProjective f.base)
    (U : X.scheme.Opens) (hdense : Dense (U : Set X.scheme))
    (hdivisorial : X.logStructure.IsDivisorialFor U)
    (hboundary : X.logStructure.trivialityLocus = (U : Set X.scheme))
    (hregular : X.IsLogRegular) (hsmooth : f.IsLogSmooth)
    (G : Type v) [Group G] [Finite G] (horder : IsUnit (Nat.card G : F))
    (a : FSLogGroupAction G X)
    (hover : ∀ g : G, (a.baseAction g).hom ≫ f.base = f.base)
    (hfree : a.IsGenericallyFree) :
    ∃ (Y : FineSaturatedLogScheme.{u}) (b : FSLogGroupAction G Y)
      (h : EtaleLogHom Y X)
      (g : EtaleLogHom Y ⟨Spec (.of F), inferInstance, N, hN⟩),
      IsIntegral Y.scheme ∧ LocallyOfFiniteType g.base ∧ QuasiCompact g.base ∧
      IsQuasiProjective g.base ∧ IsHProjective h.base ∧ b.IsEquivariant a h ∧
      h.CompEq f g ∧
      (∃ (V₀ : Y.scheme.Opens) (W₀ : X.scheme.Opens),
        Dense (V₀ : Set Y.scheme) ∧ Dense (W₀ : Set X.scheme) ∧
        ∃ e : V₀.toScheme ≅ W₀.toScheme, e.hom ≫ W₀.ι = V₀.ι ≫ h.base) ∧
      ∃ V : Y.scheme.Opens,
        (V : Set Y.scheme) =
          h.base ⁻¹' ((U : Set X.scheme) ∩ (GabberModification.freeLocus a : Set X.scheme)) ∧
        Y.logStructure.IsDivisorialFor V ∧
        Y.logStructure.trivialityLocus = (V : Set Y.scheme) ∧
        Y.IsLogRegular ∧ g.IsLogSmooth ∧ b.IsVeryTame ∧
        ∃ (P : FineSaturatedLogScheme.{u}) (q : EtaleLogHom Y P)
          (r : EtaleLogHom P ⟨Spec (.of F), inferInstance, N, hN⟩),
          IsFinite q.base ∧ Surjective q.base ∧ b.IsQuotient q ∧
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (y z : Spec (.of Ω) ⟶ Y.scheme),
            y ≫ q.base = z ≫ q.base ↔ ∃ k : G, y ≫ (b.baseAction k).hom = z) ∧
          IsIntegral P.scheme ∧ LocallyOfFiniteType r.base ∧ QuasiCompact r.base ∧
          IsQuasiProjective r.base ∧ q.CompEq r g ∧
          ∃ W : P.scheme.Opens,
            (W : Set P.scheme) = (q.base '' (V : Set Y.scheme)ᶜ)ᶜ ∧
            P.logStructure.IsDivisorialFor W ∧
            P.logStructure.trivialityLocus = (W : Set P.scheme) ∧
            P.IsLogRegular ∧ r.IsLogSmooth := by
  sorry

end AlgebraicGeometry

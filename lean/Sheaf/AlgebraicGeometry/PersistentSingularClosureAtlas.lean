module

public import Sheaf.AlgebraicGeometry.PersistentNormalizationAtlas
public import Sheaf.TraceFormula.NodalOpenLocus
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionSmoothJacobian
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Sheaf.RingTheory.AnnihilatorFiniteFlatBaseChange

/-! # Horizontal singular closure and two-branch conductor atlas

Source: Stacks Project, models.tex, Tag 0CDD; morphisms.tex, Tag 081I;
coherent.tex, Tag 02OG; the supplied atlas and explicit kernel/conductor calculations
(blueprint: lem-sfb-persistent-singular-closure-atlas).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
namespace PersistentNormalization

/-- The reduced closed nonsmooth locus on the generic fibre. This is the vanishing
ideal of the complement of the existing smooth open, not an independently chosen scheme.
Source: Stacks Project, Tag 0CDD, generic singular locus
(blueprint: lem-sfb-persistent-singular-closure-atlas). -/
noncomputable def genericSingularIdeal {X S T : Scheme.{u}} (f : X ⟶ S) (η : T ⟶ S)
    [LocallyOfFinitePresentation f] : (pullback (C := Scheme.{u}) f η).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (pullback.snd f η).smoothLocus.compl

/-- The immersion of the reduced generic singular locus into the total space.
Source: Stacks Project, Tag 081I, closure as scheme-theoretic image
(blueprint: lem-sfb-persistent-singular-closure-atlas). -/
noncomputable def genericSingularMap {X S T : Scheme.{u}} (f : X ⟶ S) (η : T ⟶ S)
    [LocallyOfFinitePresentation f] : (genericSingularIdeal f η).subscheme ⟶ X :=
  (genericSingularIdeal f η).subschemeι ≫ pullback.fst f η

/-- The actual kernel ideal defining the scheme-theoretic closure `N`.
Source: Stacks Project, Tag 081I
(blueprint: lem-sfb-persistent-singular-closure-atlas). -/
noncomputable def closureIdeal {X S T : Scheme.{u}} (f : X ⟶ S) (η : T ⟶ S)
    [LocallyOfFinitePresentation f] : X.IdealSheafData :=
  (genericSingularMap f η).ker

/-- The local ideal and diagonal two-branch descriptions, including empty charts.
The isomorphisms commute with the projections to the chart and to its singular locus.
Source: Stacks Project, Tag 0CDD, explicit persistent chart computation
(blueprint: lem-sfb-persistent-singular-closure-atlas). -/
def ChartConclusion {R K : CommRingCat.{u}} {η : Spec K ⟶ Spec R}
    {X : Scheme.{u}} {f : X ⟶ Spec R} [LocallyOfFinitePresentation f]
    (c : Chart R K η f) : Prop :=
  (∀ h : c.model = .nodal 0,
    (closureIdeal f η).comap c.toX = (originIdeal c.A).comap
      (c.toModel ≫ eqToHom (congrArg StrictSemistableModel.scheme h)) ∧
    ∃ n : pullback (C := Scheme.{u}) (closureIdeal f η).subschemeι c.toX ≅
        pullback (C := Scheme.{u}) (originMap c.A)
          (c.toModel ≫ eqToHom (congrArg StrictSemistableModel.scheme h)),
      n.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      ∃ b : pullback (C := Scheme.{u}) (pullback.snd X.fromReducedNormalization (closureIdeal f
        η).subschemeι)
            (pullback.fst (closureIdeal f η).subschemeι c.toX) ≅
          pullback (C := Scheme.{u}) (diagonalMap c.A) (n.hom ≫ pullback.fst _ _),
        b.hom ≫ pullback.snd _ _ = pullback.snd _ _) ∧
  (c.model ≠ .nodal 0 →
    (closureIdeal f η).comap c.toX = ⊤ ∧
    IsEmpty (pullback (C := Scheme.{u}) (closureIdeal f η).subschemeι c.toX) ∧
    IsEmpty (pullback (C := Scheme.{u})
      (pullback.snd X.fromReducedNormalization (closureIdeal f η).subschemeι)
      (pullback.fst (closureIdeal f η).subschemeι c.toX)))

/-- The conductor formula on every affine open of the generic fibre. Membership in
`a T̄ ⊆ T` is written using the image of the canonical normalization ring map, so it
also makes sense for the empty affine open without choosing embeddings or components.
Source: Stacks Project, Tags 035P and 0CDD, generic conductor calculation
(blueprint: lem-sfb-persistent-singular-closure-atlas). -/
def GenericConductor {X S T : Scheme.{u}} (f : X ⟶ S) (η : T ⟶ S)
    [LocallyOfFinitePresentation f] : Prop :=
  ∀ (U : (pullback (C := Scheme.{u}) f η).affineOpens) (a : Γ(pullback (C := Scheme.{u}) f η, U.1)),
    a ∈ ((closureIdeal f η).comap (pullback.fst f η)).ideal U ↔
    ∀ b : Γ((pullback (C := Scheme.{u}) f η).reducedNormalization,
        (pullback (C := Scheme.{u}) f η).fromReducedNormalization ⁻¹ᵁ U.1),
      ∃ t : Γ(pullback (C := Scheme.{u}) f η, U.1),
        (pullback (C := Scheme.{u}) f η).fromReducedNormalization.app U.1 t =
          (pullback (C := Scheme.{u}) f η).fromReducedNormalization.app U.1 a * b

/-- Horizontal singular closure and its unordered two-branch conductor atlas.

Source: Stacks Project, models.tex, Tag 0CDD; morphisms.tex, Tag 081I;
coherent.tex, Tag 02OG (blueprint: lem-sfb-persistent-singular-closure-atlas).

Proof plan (the twelve steps of the DAG node):
1. On `uv=0` the Jacobian row `(v,u)` gives precisely the reduced generic singular
   origin; on smoothing charts it is empty. Use the relative-global-CI Jacobian
   criterion, the affine smoothness criterion, étale source smoothness and geometric
   smoothness base change; étale pullbacks preserve the reduced structures.
2. Projectivity gives properness; finite type over the Noetherian DVR makes `X`
   Noetherian. The quasi-compact generic singular immersion factors densely through
   its kernel subscheme, the actual scheme-theoretic image.
3. Pull this dense factorization through each flat étale chart, using
   `lemma-nagata-dense-flat-pullback`. Its ideal is the generic restriction kernel.
4. On persistent charts `H=P/(u,v)P` is flat over the coefficient DVR, so its
   uniformizer is a nonzerodivisor and `H → H[1/π]` is injective. The kernel is
   `(u,v)P`. Generic-only persistent charts need no localization; other kernels are `P`.
5. The split-node normalization/conductor calculation identifies `N_U=Spec H` and
   `B_U=Spec(H×H)` with diagonal ring map. These are pullbacks of the model origins.
6. Descend étaleness of `N→S` and `B→N` through the jointly surjective étale charts;
   use étale composition, base change and source descent.
7. `N→S` is proper with finite zero-dimensional Noetherian fibres, hence finite by
   the proper finite-fibres criterion. `B→N` is the finite base change of normalization.
8. The displayed two-copy covers have rank two, preserved under base change. The
   branch inclusion is a closed immersion and its points are smooth, since they lie
   on the two smooth affine-line branches; descend smoothness through the charts.
9. Off the origins localization at `u` or `v` makes the split normalization an
   isomorphism; the other charts are identities. Faithfully flat kernel/cokernel
   descent gives the canonical complement isomorphism.
10. Localizing the closure ideals at the uniformizer gives exactly the original
    generic singular ideal. Faithfully flat ideal comparison gives canonical equality.
11. Reduced geometric fibres and flatness imply that `X_K` and `X` are reduced.
    Normalization commutes with localization. On every generic affine, the conductor
    is the annihilator of the finite normalization quotient. Annihilators of finite
    modules commute with flat base change (`lem-trf-annihilator-finite-flat-base-change`);
    the split-node computation gives `(u,v)` and identity charts give the unit ideal.
    Faithfully flat ideal descent identifies this with the actual generic ideal.
12. All steps are local on the supplied cover. They need no global branch ordering;
    empty singular loci and nonsplit nodes are included.
-/
theorem persistent_singular_closure_atlas
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (_hπ : Irreducible π)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] [IsFinite X.fromReducedNormalization]
    (_hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      Nonempty (pullback (C := Scheme.{u}) f g) ∧ IsReduced (pullback (C := Scheme.{u}) f g) ∧
      (pullback (C := Scheme.{u}) f g).IsPureDimension 1 ∧
      ∀ x : pullback (C := Scheme.{u}) f g, x ∈ closedPoints (pullback (C := Scheme.{u}) f g) →
        x ∉ (pullback.snd f g).smoothLocus → IsOrdinaryNode Ω (pullback (C := Scheme.{u}) f g) x)
    (_atlas : Atlas (.of R) (.of K)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) f) :
    (∀ x : X, ChartConclusion (_atlas.chart x)) ∧
    IsFinite ((closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι ≫ f) ∧
    Etale ((closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι ≫ f) ∧
    IsFinite (pullback.snd X.fromReducedNormalization
      (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι) ∧
    Etale (pullback.snd X.fromReducedNormalization
      (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι) ∧
    IsFinite (pullback.snd X.fromReducedNormalization
      (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι ≫
      (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι ≫ f) ∧
    Etale (pullback.snd X.fromReducedNormalization
      (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι ≫
      (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι ≫ f) ∧
    (∀ n : (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subscheme,
      (pullback.snd X.fromReducedNormalization
        (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι).finrank n =
          2) ∧
    IsClosedImmersion (pullback.fst X.fromReducedNormalization
      (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι) ∧
    (∀ b : pullback (C := Scheme.{u}) X.fromReducedNormalization
        (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι,
      ∃ U : X.reducedNormalization.Opens,
        pullback.fst X.fromReducedNormalization
          (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).subschemeι b ∈ U ∧
        Smooth (U.ι ≫ X.fromReducedNormalization ≫ f)) ∧
    IsIso (pullback.snd X.fromReducedNormalization
      (Scheme.Opens.ι
        (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).support.compl)) ∧
    (closureIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).comap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) =
      genericSingularIdeal f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
    GenericConductor f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  sorry

end PersistentNormalization
end AlgebraicGeometry

module

public import Sheaf.AlgebraicGeometry.BlowupSquarePullbackMaps
public import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.AlgebraicGeometry.ModuleStrictTransformFlatPullback
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Blowup.AdmissibleBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import Sheaf.RingTheory.EtaleIdealLocalFactor
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Finite affine refinement of etale local module flatifications

Source: Stacks Project, `flat.tex`, Tag 0814, `lemma-flatten-module-etale-localize`,
second proof paragraph, and Tag 0813, `lemma-push-ideal`
(blueprint: lem-trf-etale-flatification-affine-refinement).

The finite refinement is indexed by `Σ i, Fin (n i)`, with projection to the old index.
The inverse-image open `g i ⁻¹ᵁ W` represents `X_i ×[S_i] W`.
All displayed cokernels are the existing `moduleStrictTransform` unfolded; this avoids
adding hypotheses asserting quasi-coherence of tensor pullbacks or finite type of
restricted ideals, which follow from the original hypotheses. The comparison is
normalized by the quotient maps, rather than an unspecified isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The quotient-normalized canonical comparison for one open refining base.
This is the clause of the refinement conclusion, factored out so projection types do not
repeatedly expand the large pullback expressions. It uses exactly the existing transform
quotients and normalized tensor-pullback comparison.
Source: Stacks Tags 0814, 0805 and 080D
(blueprint: lem-trf-etale-flatification-affine-refinement). -/
def EtaleFlatificationTransformRestriction {S X Y : Scheme.{u}} (g : Y ⟶ S)
    (j : Y ⟶ X) (J : S.IdealSheafData) (F : X.Modules) (W : S.Opens) : Prop :=
    ∃! θ : (tensorPullback (moduleStrictTransformFlatPullbackMap
          g W.ι (g ∣_ W) (g ⁻¹ᵁ W).ι
          (morphismRestrict_ι g W).symm J)).obj
        (cokernel (kernel.ι
          (moduleStrictTransformRestriction g J ((tensorPullback j).obj F)))) ≅
      cokernel (kernel.ι (moduleStrictTransformRestriction (g ∣_ W)
        (J.comap W.ι)
        ((tensorPullback (g ⁻¹ᵁ W).ι).obj ((tensorPullback j).obj F)))),
      (tensorPullback (moduleStrictTransformFlatPullbackMap
          g W.ι (g ∣_ W) (g ⁻¹ᵁ W).ι
          (morphismRestrict_ι g W).symm J)).map
        (cokernel.π (kernel.ι
          (moduleStrictTransformRestriction g J ((tensorPullback j).obj F)))) ≫
          θ.hom =
        (moduleStrictTransformFlatPullbackSourceIso
          g W.ι (g ∣_ W) (g ⁻¹ᵁ W).ι
          (morphismRestrict_ι g W).symm J ((tensorPullback j).obj F)).hom ≫
        cokernel.π (kernel.ι (moduleStrictTransformRestriction (g ∣_ W)
          (J.comap W.ι)
          ((tensorPullback (g ⁻¹ᵁ W).ι).obj ((tensorPullback j).obj F))))

/-- The conclusion data of the finite affine refinement in Stacks Tag 0814, paragraph 2.
The retained centres are `J i` restricted by `comap`. Their blowups are identified with
restrictions of the old blowups by `blowupFlatBaseChangeIso (W i r).ι`, the comparison used
inside `moduleStrictTransformFlatPullbackMap`. The latter is consequently an open inclusion.
Admissibility retains precisely that restricted centre; its specified blowup morphism is
`((J i).comap (W i r).ι).blowupMap`, so its identification with the retained blowup is identity.
Source: Stacks Tags 0814, 0805 and 080D
(blueprint: lem-trf-etale-flatification-affine-refinement). -/
structure EtaleFlatificationAffineRefinement {S X : Scheme.{u}} (U : S.Opens)
    {I : Type v} (Si Xi : I → Scheme.{u}) (g : ∀ i, Xi i ⟶ Si i)
    (e : ∀ i, Si i ⟶ S) (j : ∀ i, Xi i ⟶ X)
    (J : ∀ i, (Si i).IdealSheafData) (F : X.Modules) where
  /-- The finite number of affine opens over each old index. -/
  n : I → ℕ
  /-- The affine open subschemes of the old bases. -/
  W : ∀ i, Fin (n i) → (Si i).Opens
  /-- Every old base is covered, including the empty-base case. -/
  covers : ∀ i, iSup (W i) = ⊤
  /-- Every refining open is affine. -/
  affine : ∀ i r, IsAffineOpen (W i r)
  /-- Every refining base is quasi-compact. -/
  compact : ∀ i r, CompactSpace (W i r).toScheme
  /-- Every refining base is quasi-separated. -/
  quasiSeparated : ∀ i r, QuasiSeparatedSpace (W i r).toScheme
  /-- The refined base maps are quasi-compact. -/
  quasiCompact_map : ∀ i r, QuasiCompact ((W i r).ι ≫ e i)
  /-- The refined base maps are etale. -/
  etale_base : ∀ i r, Etale ((W i r).ι ≫ e i)
  /-- The refined source maps are etale. -/
  etale_source : ∀ i r, Etale (((g i) ⁻¹ᵁ W i r).ι ≫ j i)
  /-- Joint surjectivity of the refined base family. -/
  surjective_base : ∀ s : S, ∃ (i : I) (r : Fin (n i)) (t : (W i r).toScheme),
    ((W i r).ι ≫ e i) t = s
  /-- Joint surjectivity of the refined source family. -/
  surjective_source : ∀ x : X,
    ∃ (i : I) (r : Fin (n i)) (y : ((g i) ⁻¹ᵁ W i r).toScheme),
      (((g i) ⁻¹ᵁ W i r).ι ≫ j i) y = x
  /-- The preserved open on each refining base is quasi-compact. -/
  compact_preserved : ∀ i r,
    IsCompact ((W i r).ι ⁻¹ᵁ ((e i) ⁻¹ᵁ U) : Set (W i r).toScheme)
  /-- The admissible blowup retains exactly the restricted given centre. -/
  admissible : ∀ i r, ∃ B : IsAdmissible (W i r).toScheme
      ((W i r).ι ⁻¹ᵁ ((e i) ⁻¹ᵁ U)), B.I = (J i).comap (W i r).ι
  /-- The canonical base-change blowup comparison exhibits an open restriction. -/
  blowup_open : ∀ i r, IsOpenImmersion
    (((J i).blowupFlatBaseChangeIso (W i r).ι).hom ≫
      pullback.fst (J i).blowupMap (W i r).ι)
  /-- On the blown-up sources, the specified comparison is also an open restriction. -/
  transform_open : ∀ i r, IsOpenImmersion (moduleStrictTransformFlatPullbackMap
    (g i) (W i r).ι (g i ∣_ W i r) ((g i) ⁻¹ᵁ W i r).ι
    (morphismRestrict_ι (g i) (W i r)).symm (J i))
  /-- The canonical restriction comparison is uniquely fixed by the quotient maps. -/
  transform_comparison : ∀ i r,
    EtaleFlatificationTransformRestriction (g i) (j i) (J i) F (W i r)
  /-- The refined strict transform remains flat over the restricted blowup. -/
  flat_transform : ∀ i r,
    (cokernel (kernel.ι (moduleStrictTransformRestriction (g i ∣_ W i r)
      ((J i).comap (W i r).ι)
      ((tensorPullback ((g i) ⁻¹ᵁ W i r).ι).obj ((tensorPullback (j i)).obj F))))).IsFlatOver
        (pullback.snd (g i ∣_ W i r) ((J i).comap (W i r).ι).blowupMap)

/-- Finite affine refinement of the specified etale local flattenings.
Source: Stacks Tag 0814, paragraph 2
(blueprint: lem-trf-etale-flatification-affine-refinement).

Proof: (1) Each `Si i` is quasi-compact by quasi-compactness of `e i`. Choose a finite affine
open cover using lem-weil-pbc-quasi-compact-morphism-preimage-qc-open and
lem-weil-pbc-qcqs-finite-affine-open-cover. This is steps 1 and 4 of the node in the general
case. Empty bases contribute no opens.
(2) These affine opens are qcqs by lem-weil-pbc-affine-scheme-qcqs. Their maps to `S` are
quasi-compact by lemma-nagata-open-immersion-qc-over-separated-target, applied to the
quasi-separated structure morphism of `S`. Open restriction preserves etaleness by
lem-weil-pbc-etale-composition-cancellation. The inverse-image opens on `Xi i` cover it,
so both refined families are jointly surjective (step 5).
(3) Apply lem-trf-module-strict-transform-flat-pullback to the open inclusions on source
and base. The blowup is the canonical flat base change and the quotient-normalized
comparison identifies its transform with the restriction of the original one. The
normalized tensor-pullback composition identifies the iterated pullback with that along
the composite to `X`. Flatness is preserved by this open restriction, either on affine
sections or stalks, by def-pc-scheme-module-flat-over (step 6).
(4) The restricted centre is finite type, quasi-coherent and unit on the inverse image of
`U`. That inverse image is quasi-compact by quasi-compactness of the refined map.
These give def-nagata-admissible-blowup, with exactly the restricted centre (step 7). -/
theorem exists_etaleFlatificationAffineRefinement
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) (hU : IsCompact (U : Set S)) (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {I : Type v} [Finite I]
    (Si Xi : I → Scheme.{u}) (g : ∀ i, Xi i ⟶ Si i)
    (e : ∀ i, Si i ⟶ S) (j : ∀ i, Xi i ⟶ X)
    (hcomm : ∀ i, g i ≫ e i = j i ≫ f)
    (he : ∀ i, QuasiCompact (e i)) (heEtale : ∀ i, Etale (e i))
    (hjEtale : ∀ i, Etale (j i))
    (hcoverS : ∀ s : S, ∃ (i : I) (t : Si i), e i t = s)
    (hcoverX : ∀ x : X, ∃ (i : I) (y : Xi i), j i y = x)
    (J : ∀ i, (Si i).IdealSheafData) (hJ : ∀ i, (J i).ofFiniteType)
    (hunit : ∀ i, (J i).comap ((e i) ⁻¹ᵁ U).ι = ⊤)
    (hflat : ∀ i, (cokernel (kernel.ι
      (moduleStrictTransformRestriction (g i) (J i) ((tensorPullback (j i)).obj F)))).IsFlatOver
        (pullback.snd (g i) (J i).blowupMap)) :
    Nonempty (EtaleFlatificationAffineRefinement U Si Xi g e j J F) := by
  sorry

/-- Over `Spec A`, with preserved open `D(a)` for a nonzerodivisor, the refinement can
simultaneously be chosen with finitely generated base ideal factors.
Source: Stacks Tags 0814 (second paragraph) and 0813
(blueprint: lem-trf-etale-flatification-affine-refinement).

Proof: (1) Start with finite affine covers of the quasi-compact `Si i` as in step 1 of the
node. On each affine chart, the centre corresponds to a finitely generated ideal `J` by
lem-weil-pbc-affine-tilde-gamma-adjunction and lem-weil-pbc-quasi-coherent-finite-type-affine.
Its zero locus is contained in `V(aB)` by lem-weil-pbc-basic-open-pullback and
lem-weil-pbc-quasi-coherent-ideal-zero-set-affine (step 2).
(2) For each prime, apply lem-trf-etale-ideal-local-factor (Stacks 0813) to obtain a
principal open containing it and finitely generated ideals `K` in `A` and `J'` on the
localization, with `V(K) ⊆ V(a)` and `K B_g = (J B_g) J'`. The principal localization is an
affine open by lem-weil-pbc-principal-localization-open-immersion. The associated ideal
sheaf is finite type; the equality of ideal sheaves follows from
lem-weil-pbc-quasi-coherent-affine-section-base-change,
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and affine reconstruction (step 3).
(3) Quasi-compactness of each preliminary chart selects finitely many of these opens.
The finite disjoint union of all their index sets gives the refinement (step 4).
(4) Steps 5--7 are exactly the etaleness, joint-surjectivity, qcqs, admissibility and
canonical restriction argument of exists_etaleFlatificationAffineRefinement above. -/
theorem exists_etaleFlatificationAffineRefinement_baseFactors
    (A : Type u) [CommRing A] (a : A)
    (ha : Function.Injective (fun x : A ↦ a * x))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (F : X.Modules) [F.IsQuasicoherent] {I : Type v} [Finite I]
    (Si Xi : I → Scheme.{u}) (g : ∀ i, Xi i ⟶ Si i)
    (e : ∀ i, Si i ⟶ Spec (.of A)) (j : ∀ i, Xi i ⟶ X)
    (hcomm : ∀ i, g i ≫ e i = j i ≫ f)
    (he : ∀ i, QuasiCompact (e i)) (heEtale : ∀ i, Etale (e i))
    (hjEtale : ∀ i, Etale (j i))
    (hcoverS : ∀ s : Spec (.of A), ∃ (i : I) (t : Si i), e i t = s)
    (hcoverX : ∀ x : X, ∃ (i : I) (y : Xi i), j i y = x)
    (J : ∀ i, (Si i).IdealSheafData) (hJ : ∀ i, (J i).ofFiniteType)
    (hunit : ∀ i, (J i).comap ((e i) ⁻¹ᵁ PrimeSpectrum.basicOpen a).ι = ⊤)
    (hflat : ∀ i, (cokernel (kernel.ι
      (moduleStrictTransformRestriction (g i) (J i) ((tensorPullback (j i)).obj F)))).IsFlatOver
        (pullback.snd (g i) (J i).blowupMap)) :
    ∃ D : EtaleFlatificationAffineRefinement (PrimeSpectrum.basicOpen a) Si Xi g e j J F,
      ∀ (i : I) (r : Fin (D.n i)), ∃ (K : Ideal A) (J' : (D.W i r).toScheme.IdealSheafData),
        K.FG ∧ J'.ofFiniteType ∧
        PrimeSpectrum.zeroLocus (K : Set A) ⊆
          PrimeSpectrum.zeroLocus (Ideal.span ({a} : Set A) : Set A) ∧
        (Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap
          ((D.W i r).ι ≫ e i) = (J i).comap (D.W i r).ι * J' := by
  sorry

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleProEtale
import WeilConjectures.AlgebraicGeometry.Open.OpenProjectionComparisonSquare
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-! # Finite-ring compactification projections and restricted transposes

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, the comparison of the ordered affine-line
adjoints with the same integration and the final canonical reassociations.
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison).

The coefficient category is the fixed-ring presentation of constant-A modules. The maps
are the published proper counit mate, open comparison, projections and ordinary adjunction.
The restricted transpose is the published comparison Hom chain followed by the inverse
of its comparison-unit normalization. No ambient pro-etale exceptional adjoint is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteCompactificationTranspose

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Notation for the recorded ordinary etale derived category.
Source: def-weil-pbc-derived-categories
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev E (X : Scheme.{u}) := Etale.DerivedCategoryModule A X

/-- Notation for its strictly full bounded-below subcategory.
Source: def-weil-pbc-derived-categories
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev EPlus (X : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- Notation for the fixed-ring pro-etale derived category.
Source: def-weil-pbc-proetale-modules, fixed-ring realization
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev P (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- The existing exact comparison, localized termwise.
Source: def-weil-pbc-site-comparison-morphism
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev C (X : Scheme.{u}) : E A X ⥤ P A X :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The recorded ordinary compact-support functor for c.
Source: def-amb-etale-compact-support
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev Fe {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The actual pro-etale proper/open compact-support functor.
Source: lem-sp-finite-compact-site-coherence
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev Fp {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- B is precisely the proper counit mate followed by direct image of the canonical
open comparison, with the bounded-below inclusion identifications inserted.
Source: def-sf-compact-support-site-comparison-construction, compactSupportSiteComparison
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev B {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (J : EPlus A X) : (C A Y).obj ((Fe A c).obj J.obj) ≅
      (Fp A c).obj ((C A X).obj J.obj) :=
  (compactSupportSiteComparison A c).symm.app J

/-- The existing tensor input; its boundedness is required explicitly, not inferred
from boundedness of the two factors. Source: the displayed projection square
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev tensorInput {X Y : Scheme.{u}} (f : X ⟶ Y) (M : E A X) (H : E A Y) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)

/-- The actual counit-defined ordinary compactification projection.
Source: def-exchange-projection, proper projection followed by inverse open projection
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev pe {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : E A X) (H : E A Y) :=
  projectionComparisonEtaleArrow A c M H

/-- The corresponding actual pro-etale projection, on the comparison objects.
Source: def-exchange-projection, the same proper/open construction on the pro-etale site
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev pp {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : E A X) (H : E A Y) :=
  projectionComparisonProEtaleArrow A c M H

/-- Source identification in the projection square: comparison tensor, then B tensor 1.
Source: the displayed projection square
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev projectionSource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : EPlus A X) (H : E A Y) :=
  projectionComparisonSourceBoundary A c M H

/-- Target identification: B at the tensor input, then compact support of the
canonical tensor/pullback comparison. Source: the displayed projection square
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev projectionTarget {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : EPlus A X) (H : E A Y)
    (ht : DerivedCategory.TStructure.t.plus (tensorInput A f M.obj H)) :=
  projectionComparisonTargetBoundary A c M H ht

/-- The projection square and the asserted conditional inverse square.
Source: the two displayed projection clauses of the node
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def ProjectionLaw {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∀ (M : EPlus A X) (H : EPlus A Y)
    (ht : DerivedCategory.TStructure.t.plus (tensorInput A f M.obj H.obj)),
    (C A Y).map (pe A c M.obj H.obj) ≫ (projectionTarget A c M H.obj ht).hom =
      (projectionSource A c M H.obj).hom ≫ pp A c M.obj H.obj ∧
    ∀ h : IsIso (pe A c M.obj H.obj),
      IsIso (pp A c M.obj H.obj) ∧
      ∀ hp : IsIso (pp A c M.obj H.obj),
        letI := h
        letI := hp
        (C A Y).map (inv (pe A c M.obj H.obj)) =
          (projectionTarget A c M H.obj ht).hom ≫
            inv (I := hp) (pp A c M.obj H.obj) ≫ (projectionSource A c M H.obj).inv

/-- The restricted transpose, normalized to C_X(GH). The raw Hom chain is the existing
boundedSiteTranspose. Its final factor is C_XG applied to the inverse comparison unit
at the bounded-below target H. The inverse exists by the recorded site comparison theorem.
Source: the node's explicit Hom chain and rho normalization
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def transpose {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : E A Y ⥤ E A X) (adj : Fe A c ⊣ G) (J : EPlus A X) (H : EPlus A Y)
    (z : (Fp A c).obj ((C A X).obj J.obj) ⟶ (C A Y).obj H.obj) :
    (C A X).obj J.obj ⟶ (C A X).obj (G.obj H.obj) :=
  letI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) Y H.obj H.property
  boundedSiteTranspose A c G adj J ((C A Y).obj H.obj) z ≫
    (C A X).map (G.map (inv
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H.obj)))

/-- The restricted counit, transported from the ordinary counit by precisely B inverse.
Source: the counit specialization of the node's Hom-chain calculation
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def counit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : E A Y ⥤ E A X) (adj : Fe A c ⊣ G) (H : EPlus A Y)
    (hG : DerivedCategory.TStructure.t.plus (G.obj H.obj)) :=
  (B A c ⟨G.obj H.obj, hG⟩).inv ≫ (C A Y).map (adj.counit.app H.obj)

/-- Bijection, compatible transposes, and its counit normalization. The compatibility
quantifies over every ordinary map, so it includes inverse projections and integrations.
Source: restricted-adjunction and counit paragraphs of the node
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def TransposeLaw {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∀ (G : E A Y ⥤ E A X) (adj : Fe A c ⊣ G) (J : EPlus A X) (H : EPlus A Y)
    (hG : DerivedCategory.TStructure.t.plus (G.obj H.obj)),
    Function.Bijective (transpose A c G adj J H) ∧
    (∀ (ae : (Fe A c).obj J.obj ⟶ H.obj)
      (ap : (Fp A c).obj ((C A X).obj J.obj) ⟶ (C A Y).obj H.obj),
      (B A c J).hom ≫ ap = (C A Y).map ae →
        transpose A c G adj J H ap = (C A X).map (adj.homEquiv J.obj H.obj ae)) ∧
    (B A c ⟨G.obj H.obj, hG⟩).hom ≫ counit A c G adj H hG =
      (C A Y).map (adj.counit.app H.obj) ∧
    transpose A c G adj ⟨G.obj H.obj, hG⟩ H (counit A c G adj H hG) =
      𝟙 ((C A X).obj (G.obj H.obj))

/-- Naturality and independence of both bounded-below etale representatives. The unique
lift b of the change of target representative supplies the target identification C_XG(b).
Source: representative-independence paragraph of the node
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def RepresentativeLaw {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∀ (G : E A Y ⥤ E A X) (adj : Fe A c ⊣ G)
    (J J' : EPlus A X) (H H' : EPlus A Y)
    (_hG : DerivedCategory.TStructure.t.plus (G.obj H.obj))
    (_hG' : DerivedCategory.TStructure.t.plus (G.obj H'.obj))
    (K : P A X) (L : P A Y) (w : (C A X).obj J.obj ≅ K)
    (w' : (C A X).obj J'.obj ≅ K) (v : (C A Y).obj H.obj ≅ L)
    (v' : (C A Y).obj H'.obj ≅ L) (z : (Fp A c).obj K ⟶ L),
    (∃! a : J.obj ⟶ J'.obj, (C A X).map a ≫ w'.hom = w.hom) ∧
    ∃! b : H.obj ⟶ H'.obj,
      (C A Y).map b ≫ v'.hom = v.hom ∧
      w.inv ≫ transpose A c G adj J H ((Fp A c).map w.hom ≫ z ≫ v.inv) ≫
          (C A X).map (G.map b) =
        w'.inv ≫ transpose A c G adj J' H' ((Fp A c).map w'.hom ≫ z ≫ v'.inv)

/-- The very same bounded-below ordinary compositor as in the site square, with
only the canonical inclusions into the unbounded categories inserted.
Source: def-pur-chosen-compactification-compositors, coherenceEtaleCompositor
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def ordinaryCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (J : EPlus A X) :
    (Fe A d).obj ((Fe A c).obj J.obj) ≅ (Fe A e).obj J.obj :=
  let FJ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} A) c).obj J
  (Fe A d).mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).app J).symm ≪≫
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).app FJ).symm ≪≫
    DerivedCategory.Plus.ι.mapIso ((coherenceEtaleCompositor A c d e).app J) ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) e).app J

/-- The pro-etale compositor is transposed twice through the restricted Hom chains.
It is exactly finiteCompactSiteCompositionPlus from the site square, transported along
the canonical bounded-below inclusions. The only right adjoints are ordinary ones.
Source: final compositor clause and mate-pasting proof step of the node
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def proRightCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsNoetherian Y] [IsNoetherian Z] [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (Gf : E A Y ⥤ E A X) (Gg : E A Z ⥤ E A Y) (Gh : E A Z ⥤ E A X)
    (af : Fe A c ⊣ Gf) (ag : Fe A d ⊣ Gg) (ah : Fe A e ⊣ Gh)
    (H : EPlus A Z) (hH : DerivedCategory.TStructure.t.plus (Gh.obj H.obj))
    (hg : DerivedCategory.TStructure.t.plus (Gg.obj H.obj)) :=
  let J : EPlus A X := ⟨Gh.obj H.obj, hH⟩
  let FJ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} A) c).obj J
  let q := (C A Y).mapIso
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app J)
  let NJ := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj J
  let PJ := (rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} A) c).obj NJ
  let kc := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c).app NJ
  let kd := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) d).app PJ
  let ke := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) e).app NJ
  let alpha := (Fp A d).map kc.inv ≫ kd.inv ≫
    DerivedCategory.Plus.ι.map (finiteCompactSiteCompositionPlus A c d e T J) ≫ ke.hom
  transpose A c Gf af J ⟨Gg.obj H.obj, hg⟩
    ((B A c J).inv ≫ q.inv ≫
      transpose A d Gg ag FJ H
        ((Fp A d).map (q.hom ≫ (B A c J).hom) ≫
          alpha ≫ counit A e Gh ah H hH))

/-- The site squares for actual proper refinements and normalized compact-support
composition, together with the equality of their conjugate right-adjoint compositors.
Source: lem-sp-finite-compact-site-coherence and the last paragraph of the node
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def CoherenceLaw (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (aY : Y ⟶ Spec (.of k))
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  (∀ (d : Compactification f) (r : c.Refinement d) (J : EPlus A X),
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).hom.app J) ≫
      (compactSupportSiteComparisonPlus A c).hom.app J =
    (compactSupportSiteComparisonPlus A d).hom.app J ≫
      (properTransportRefinementPlus A r J).inv) ∧
  ∀ (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of k))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (g : Y ⟶ Z) (_hg : g ≫ aZ = aY)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g),
    letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType aZ
    (∀ J : EPlus A X,
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
          ((coherenceEtaleCompositor A c d e).hom.app J) ≫
        (compactSupportSiteComparisonPlus A e).hom.app J =
      (compactSupportSiteComparisonPlus A d).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} A) c).obj J) ≫
        (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).map
          ((compactSupportSiteComparisonPlus A c).hom.app J) ≫
        finiteCompactSiteCompositionPlus A c d e T J) ∧
    ∀ (Gf : E A Y ⥤ E A X) (Gg : E A Z ⥤ E A Y) (Gh : E A Z ⥤ E A X)
      (af : Fe A c ⊣ Gf) (ag : Fe A d ⊣ Gg) (ah : Fe A e ⊣ Gh)
      (H : EPlus A Z) (hH : DerivedCategory.TStructure.t.plus (Gh.obj H.obj))
      (hg : DerivedCategory.TStructure.t.plus (Gg.obj H.obj))
      (_hfg : DerivedCategory.TStructure.t.plus (Gf.obj (Gg.obj H.obj))),
      proRightCompositor A c d e T Gf Gg Gh af ag ah H hH hg =
        (C A X).map ((af.comp ag).homEquiv (Gh.obj H.obj) H.obj
          ((ordinaryCompositor A c d e ⟨Gh.obj H.obj, hH⟩).hom ≫
            ah.counit.app H.obj))

private theorem transport_projection
    {D : Type*} [Category D] {Q : Type*} [Category Q]
    (F : D ⥤ Q) {U V : D} {S T : Q} (p : U ⟶ V) (q : S ⟶ T)
    (s : F.obj U ≅ S) (t : F.obj V ≅ T) (h : q ≫ t.inv = s.inv ≫ F.map p) :
    F.map p ≫ t.hom = s.hom ≫ q ∧
      ∀ he : IsIso p, IsIso q ∧ ∀ hq : IsIso q,
        letI := he
        letI := hq
        F.map (inv p) = t.hom ≫ inv q ≫ s.inv := by
  have hs : F.map p ≫ t.hom = s.hom ≫ q := by
    apply (cancel_epi s.inv).1
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [h.symm, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨hs, ?_⟩
  intro he
  letI := he
  have hq_eq : q = s.inv ≫ F.map p ≫ t.hom := by
    apply (cancel_epi s.hom).1
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hs.symm
  have hq : IsIso q := by rw [hq_eq]; infer_instance
  refine ⟨hq, ?_⟩
  intro hq'
  letI := hq'
  apply (cancel_mono (F.map p)).1
  simp only [Category.assoc, ← h]
  simp [← CategoryTheory.Functor.map_comp]

private def projection_inverse_square
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : EPlus A X) (H : EPlus A Y)
    (ht : DerivedCategory.TStructure.t.plus (tensorInput A f M.obj H.obj)) :
    pp A c M.obj H.obj ≫ (projectionTarget A c M H.obj ht).inv =
      (projectionSource A c M H.obj).inv ≫ (C A Y).map (pe A c M.obj H.obj) := by
  exact projectionComparison_equation_of_plus A c M.obj H.obj M.property ht

private theorem projection_law_proof
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : ProjectionLaw A c := by
  intro M H ht
  exact transport_projection (D := E A Y) (Q := P A Y) (C A Y)
    (pe A c M.obj H.obj) (pp A c M.obj H.obj)
    (projectionSource A c M H.obj) (projectionTarget A c M H.obj ht)
    (projection_inverse_square A c M H ht)

private theorem normalized_projection_law
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : ProjectionLaw A c :=
  projection_law_proof A c

private theorem normalized_transpose_compatible
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : E A Y ⥤ E A X) (adj : Fe A c ⊣ G) (J : EPlus A X) (H : EPlus A Y)
    (ae : (Fe A c).obj J.obj ⟶ H.obj)
    (ap : (Fp A c).obj ((C A X).obj J.obj) ⟶ (C A Y).obj H.obj)
    (h : (B A c J).hom ≫ ap = (C A Y).map ae) :
    transpose A c G adj J H ap = (C A X).map (adj.homEquiv J.obj H.obj ae) := by
  letI := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y H.obj H.property
  have hraw : boundedSiteTranspose A c G adj J ((C A Y).obj H.obj) ap =
      (C A X).map (adj.homEquiv J.obj H.obj ae) ≫
        (C A X).map (G.map
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H.obj)) := by
    unfold boundedSiteTranspose
    change (C A X).map ((adj.homEquiv J.obj _)
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _
        ((B A c J).hom ≫ ap))) = _
    rw [h]
    have he : (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _
        ((C A Y).map ae) =
        ae ≫ (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H.obj := by
      rw [Adjunction.homEquiv_unit]
      exact ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.naturality ae).symm
    rw [he, Adjunction.homEquiv_naturality_right, Functor.map_comp]
  unfold transpose
  rw [hraw, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  simp

private theorem normalized_transpose_law
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : TransposeLaw A c := by
  intro G adj J H hG
  have hcompat := normalized_transpose_compatible A c G adj
  have hmapY := bijective_comparisonUpperStar_mapDerivedCategory_map
    (A := ModuleCat.{u + 1} A) ((Fe A c).obj J.obj) H.obj H.property
  have hmapX := bijective_comparisonUpperStar_mapDerivedCategory_map
    (A := ModuleCat.{u + 1} A) J.obj (G.obj H.obj) hG
  have hbij : Function.Bijective (transpose A c G adj J H) := by
    constructor
    · intro ap₁ ap₂ heq
      obtain ⟨ae₁, h₁⟩ := hmapY.2 ((B A c J).hom ≫ ap₁)
      obtain ⟨ae₂, h₂⟩ := hmapY.2 ((B A c J).hom ≫ ap₂)
      have hm : (C A X).map (adj.homEquiv J.obj H.obj ae₁) =
          (C A X).map (adj.homEquiv J.obj H.obj ae₂) := by
        rw [← hcompat J H ae₁ ap₁ h₁.symm, ← hcompat J H ae₂ ap₂ h₂.symm]
        exact heq
      have hae : ae₁ = ae₂ := (adj.homEquiv J.obj H.obj).injective (hmapX.1 hm)
      apply (cancel_epi (B A c J).hom).1
      rw [← h₁, ← h₂, hae]
    · intro z
      obtain ⟨b, hb⟩ := hmapX.2 z
      let ae := (adj.homEquiv J.obj H.obj).symm b
      refine ⟨(B A c J).inv ≫ (C A Y).map ae, ?_⟩
      rw [hcompat J H ae _ (by simp), Equiv.apply_symm_apply]
      exact hb
  have hc : (B A c ⟨G.obj H.obj, hG⟩).hom ≫ counit A c G adj H hG =
      (C A Y).map (adj.counit.app H.obj) := by
    simp [counit]
  refine ⟨hbij, hcompat J H, hc, ?_⟩
  rw [hcompat ⟨G.obj H.obj, hG⟩ H (adj.counit.app H.obj) _ hc]
  rw [← adj.homEquiv_symm_id H.obj, Equiv.apply_symm_apply]
  exact (C A X).map_id _

private theorem normalized_transpose_left
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : E A Y ⥤ E A X) (adj : Fe A c ⊣ G) (J J' : EPlus A X) (H : EPlus A Y)
    (a : J'.obj ⟶ J.obj)
    (z : (Fp A c).obj ((C A X).obj J.obj) ⟶ (C A Y).obj H.obj) :
    transpose A c G adj J' H ((Fp A c).map ((C A X).map a) ≫ z) =
      (C A X).map a ≫ transpose A c G adj J H z := by
  unfold transpose
  rw [boundedSiteTranspose_left]
  simp only [Category.assoc]

private theorem normalized_transpose_right
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : E A Y ⥤ E A X) (adj : Fe A c ⊣ G) (J : EPlus A X) (H H' : EPlus A Y)
    (b : H.obj ⟶ H'.obj)
    (z : (Fp A c).obj ((C A X).obj J.obj) ⟶ (C A Y).obj H.obj) :
    transpose A c G adj J H' (z ≫ (C A Y).map b) =
      transpose A c G adj J H z ≫ (C A X).map (G.map b) := by
  letI := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y H.obj H.property
  letI := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y H'.obj H'.property
  have hn : (R(ν_*(Y)[ModuleCat.{u + 1} A])).map ((C A Y).map b) ≫
      inv ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H'.obj) =
      inv ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H.obj) ≫ b := by
    apply (cancel_epi
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H.obj)).1
    have hη := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.naturality b
    change b ≫ (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H'.obj =
      (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H.obj ≫
        (R(ν_*(Y)[ModuleCat.{u + 1} A])).map ((C A Y).map b) at hη
    rw [← Category.assoc, ← hη]
    simp
  unfold transpose
  rw [boundedSiteTranspose_right]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, hn]

private theorem normalized_representative_law
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : RepresentativeLaw A c := by
  intro G adj J J' H H' hG hG' K L w w' v v' z
  have hmapX := bijective_comparisonUpperStar_mapDerivedCategory_map
    (A := ModuleCat.{u + 1} A) J.obj J'.obj J'.property
  have hmapY := bijective_comparisonUpperStar_mapDerivedCategory_map
    (A := ModuleCat.{u + 1} A) H.obj H'.obj H'.property
  obtain ⟨a, ha⟩ := hmapX.2 (w.hom ≫ w'.inv)
  obtain ⟨b, hb⟩ := hmapY.2 (v.hom ≫ v'.inv)
  change (C A X).map a = w.hom ≫ w'.inv at ha
  change (C A Y).map b = v.hom ≫ v'.inv at hb
  have ha' : (C A X).map a ≫ w'.hom = w.hom := by rw [ha]; simp
  have hb' : (C A Y).map b ≫ v'.hom = v.hom := by rw [hb]; simp
  have hw : w.inv ≫ (C A X).map a = w'.inv := by rw [ha]; simp
  have hv : v.inv ≫ (C A Y).map b = v'.inv := by rw [hb]; simp
  refine ⟨⟨a, ha', ?_⟩, b, ⟨hb', ?_⟩, ?_⟩
  · intro a' ha''
    apply hmapX.1
    apply (cancel_mono w'.hom).1
    exact ha''.trans ha'.symm
  · let z₁ := (Fp A c).map w.hom ≫ z ≫ v.inv
    let z₂ := (Fp A c).map w'.hom ≫ z ≫ v'.inv
    have hz : z₁ ≫ (C A Y).map b = (Fp A c).map ((C A X).map a) ≫ z₂ := by
      calc
        z₁ ≫ (C A Y).map b = (Fp A c).map w.hom ≫ z ≫ v'.inv := by
          simp only [z₁, Category.assoc, hv]
        _ = (Fp A c).map ((C A X).map a) ≫ z₂ := by
          rw [← ha', CategoryTheory.Functor.map_comp]
          simp only [z₂, Category.assoc]
    have ht := congrArg (fun t ↦ transpose A c G adj J H' t) hz
    rw [normalized_transpose_right A c G adj J H H' b z₁,
      normalized_transpose_left A c G adj J' J H' a z₂] at ht
    change w.inv ≫ transpose A c G adj J H z₁ ≫ (C A X).map (G.map b) =
      w'.inv ≫ transpose A c G adj J' H' z₂
    rw [ht, ← Category.assoc, hw]
  · intro b' hb''
    apply hmapY.1
    apply (cancel_mono v'.hom).1
    exact hb''.1.trans hb'.symm

private def ambientSiteCompositor
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsNoetherian Y] [IsNoetherian Z] [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) (J : EPlus A X) :=
  let NJ := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj J
  let PJ := (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj NJ
  let kc := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c).app NJ
  let kd := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) d).app PJ
  let ke := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) e).app NJ
  (Fp A d).map kc.inv ≫ kd.inv ≫
    DerivedCategory.Plus.ι.map (finiteCompactSiteCompositionPlus A c d e T J) ≫ ke.hom

private theorem boundary_hom
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (J : EPlus A X) :
    (B A c J).hom =
      (C A Y).map ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).inv.app J) ≫
      DerivedCategory.Plus.ι.map ((compactSupportSiteComparisonPlus A c).hom.app J) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj J) := by
  simp [B, compactSupportSiteComparison,
    CategoryTheory.Functor.mapDerivedCategoryPlusCompatibility, Category.assoc]

private theorem ambient_site_composition
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) (J : EPlus A X) :
    let FJ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} A) c).obj J
    let rc := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app J
    (B A d FJ).hom ≫ (Fp A d).map ((C A Y).map rc.hom ≫ (B A c J).hom) ≫
        ambientSiteCompositor A c d e T J =
      (C A Z).map ((Fe A d).map rc.hom ≫ (ordinaryCompositor A c d e J).hom) ≫
        (B A e J).hom := by
  dsimp only
  let FJ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} A) c).obj J
  let NJ := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj J
  let PJ := (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj NJ
  let rc := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c).app J
  let rd := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) d).app FJ
  let re := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) e).app J
  let kc := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c).app NJ
  let kd := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) d).app PJ
  let kd' := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) d).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.obj FJ)
  let ke := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) e).app NJ
  let bc := (compactSupportSiteComparisonPlus A c).hom.app J
  let bd := (compactSupportSiteComparisonPlus A d).hom.app FJ
  let be := (compactSupportSiteComparisonPlus A e).hom.app J
  let ae := (coherenceEtaleCompositor A c d e).hom.app J
  let ap := finiteCompactSiteCompositionPlus A c d e T J
  have hq : (C A Y).map rc.hom ≫ (B A c J).hom =
      DerivedCategory.Plus.ι.map bc ≫ kc.hom := by
    rw [boundary_hom]
    simp [rc, bc, kc, NJ, Category.assoc, ← CategoryTheory.Functor.map_comp]
  have ho : (Fe A d).map rc.hom ≫ (ordinaryCompositor A c d e J).hom =
      rd.inv ≫ DerivedCategory.Plus.ι.map ae ≫ re.hom := by
    simp [ordinaryCompositor, rc, rd, re, FJ, ae, Category.assoc,
      ← CategoryTheory.Functor.map_comp_assoc]
  have hnat := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) d).hom.naturality bc
  change DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).map bc) ≫
      kd.hom = kd'.hom ≫ (Fp A d).map (DerivedCategory.Plus.ι.map bc) at hnat
  have hk : kd'.hom ≫ (Fp A d).map (DerivedCategory.Plus.ι.map bc) ≫ kd.inv =
      DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).map bc) := by
    rw [← Category.assoc, ← hnat]
    simp
  have hkc : (Fp A d).map kc.hom ≫ (Fp A d).map kc.inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp]
    simp
  have hree : (C A Z).map re.hom ≫ (C A Z).map re.inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp]
    simp
  have hplus := congrArg (fun t ↦ DerivedCategory.Plus.ι.map t)
    (finiteCompactSiteCoherence A c d e T J)
  simp only [CategoryTheory.Functor.map_comp] at hplus
  change (C A Z).map (DerivedCategory.Plus.ι.map ae) ≫
      DerivedCategory.Plus.ι.map be =
    DerivedCategory.Plus.ι.map bd ≫ DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).map bc) ≫
      DerivedCategory.Plus.ι.map ap at hplus
  rw [hq, ho, boundary_hom A d FJ, boundary_hom A e J]
  simp only [Category.assoc]
  change (C A Z).map rd.inv ≫ DerivedCategory.Plus.ι.map bd ≫ kd'.hom ≫
      (Fp A d).map (DerivedCategory.Plus.ι.map bc ≫ kc.hom) ≫
      ((Fp A d).map kc.inv ≫ kd.inv ≫ DerivedCategory.Plus.ι.map ap ≫ ke.hom) =
    (C A Z).map (rd.inv ≫ DerivedCategory.Plus.ι.map ae ≫ re.hom) ≫
      (C A Z).map re.inv ≫ DerivedCategory.Plus.ι.map be ≫ ke.hom
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [reassoc_of% hkc, reassoc_of% hk, reassoc_of% hree]
  erw [← reassoc_of% hplus]

private theorem normalized_compositor
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (Gf : E A Y ⥤ E A X) (Gg : E A Z ⥤ E A Y) (Gh : E A Z ⥤ E A X)
    (af : Fe A c ⊣ Gf) (ag : Fe A d ⊣ Gg) (ah : Fe A e ⊣ Gh)
    (H : EPlus A Z) (hH : DerivedCategory.TStructure.t.plus (Gh.obj H.obj))
    (hg : DerivedCategory.TStructure.t.plus (Gg.obj H.obj)) :
    proRightCompositor A c d e T Gf Gg Gh af ag ah H hH hg =
      (C A X).map ((af.comp ag).homEquiv (Gh.obj H.obj) H.obj
        ((ordinaryCompositor A c d e ⟨Gh.obj H.obj, hH⟩).hom ≫ ah.counit.app H.obj)) := by
  let J : EPlus A X := ⟨Gh.obj H.obj, hH⟩
  let FJ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} A) c).obj J
  let rc := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c).app J
  let q := (C A Y).mapIso rc
  let az := (ordinaryCompositor A c d e J).hom ≫ ah.counit.app H.obj
  let ae := (Fe A d).map rc.hom ≫ az
  let ap := (Fp A d).map (q.hom ≫ (B A c J).hom) ≫
    ambientSiteCompositor A c d e T J ≫ counit A e Gh ah H hH
  have hsite := ambient_site_composition A c d e T J
  have hd : (B A d FJ).hom ≫ ap = (C A Z).map ae := by
    calc
      (B A d FJ).hom ≫ ap =
          ((B A d FJ).hom ≫ (Fp A d).map (q.hom ≫ (B A c J).hom) ≫
            ambientSiteCompositor A c d e T J) ≫ counit A e Gh ah H hH := by
        simp only [ap, Category.assoc]
      _ = ((C A Z).map
          ((Fe A d).map rc.hom ≫ (ordinaryCompositor A c d e J).hom) ≫
            (B A e J).hom) ≫ counit A e Gh ah H hH := by
        exact congrArg (fun t ↦ t ≫ counit A e Gh ah H hH) hsite
      _ = (C A Z).map ae := by
        simp [counit, ae, az, J, Category.assoc, ← CategoryTheory.Functor.map_comp]
  have htd := normalized_transpose_compatible A d Gg ag FJ H ae ap hd
  have hc : (B A c J).hom ≫
      ((B A c J).inv ≫ q.inv ≫ transpose A d Gg ag FJ H ap) =
      (C A Y).map (ag.homEquiv ((Fe A c).obj J.obj) H.obj az) := by
    rw [htd]
    simp only [Iso.hom_inv_id_assoc]
    dsimp only [ae]
    rw [Adjunction.homEquiv_naturality_left]
    simp [q, Category.assoc, ← CategoryTheory.Functor.map_comp]
  change transpose A c Gf af J ⟨Gg.obj H.obj, hg⟩
      ((B A c J).inv ≫ q.inv ≫ transpose A d Gg ag FJ H ap) = _
  rw [normalized_transpose_compatible A c Gf af J ⟨Gg.obj H.obj, hg⟩
    (ag.homEquiv ((Fe A c).obj J.obj) H.obj az) _ hc]
  rw [Adjunction.comp_homEquiv]
  rfl

private theorem normalized_coherence_law
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (aY : Y ⟶ Spec (.of k))
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : CoherenceLaw A k aY c := by
  constructor
  · intro d r J
    exact finiteCompactSite_refinement A f r J
  · intro Z aZ _ _ _ g hg _ _ _ d e T
    letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType aZ
    constructor
    · intro J
      exact finiteCompactSiteCoherence A c d e T J
    · intro Gf Gg Gh af ag ah H hH hg hfg
      exact normalized_compositor A c d e T Gf Gg Gh af ag ah H hH hg

/-- Finite-ring comparison preserves compactification projections, their inverses,
restricted exceptional transposes and counits, representatives, and normalized compositors.
Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, the two sentences
identifying the affine-line adjoints with the same integration, and final reassociations.
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison).

Proof:
1. Use the existing compactification projection equation for the given bounded-below
witnesses. Its two sides are pp followed by projectionTarget inverse and
projectionSource inverse followed by C(pe). Cancel the invertible boundaries to get
the forward square. If pe is invertible, pp is conjugate to C(pe); cancellation also
gives the claimed inverse formula.
2. At bounded-below H the comparison unit eta_H is invertible. Unit naturality and
target naturality of the ordinary adjunction show that the raw boundedSiteTranspose
of a compatible ap is C_X(adj_e ae) followed by C_XG(eta_H). Postcomposing with
C_XG(eta_H inverse), as prescribed in transpose, gives normalized compatibility.
3. Comparison on maps into bounded-below H uniquely lifts B followed by any ap to
ae. The ordinary adjunction Hom equivalence and comparison on maps into bounded-below
GH give a bijection. The compatibility just computed proves injectivity and
surjectivity of transpose directly, without a separate estimate for F_eJ or for G at
other targets. For J = GH the ordinary counit transposes to the identity; cancellation
of B and functoriality prove both counit clauses.
4. Naturality of the raw Hom chain and of its comparison-unit normalization gives
source and target naturality of transpose. Bounded-below full faithfulness uniquely
lifts the changes of source and target representatives. Substitute these equations
and cancel the representative isomorphisms to prove independence.
5. Apply finiteCompactSite_refinement and finiteCompactSiteCoherence. Expand B using
the ordinary and pro-etale bounded-below inclusion compatibilities. Naturality of
the latter transports the plus-category composition square to ambient_site_composition;
each intermediate inclusion boundary cancels.
6. Compose this square with the specified counit for e. Apply normalized compatibility
to d, cancel the c inclusion boundary by left naturality of the ordinary adjunction,
and apply normalized compatibility to c. Adjunction.comp_homEquiv identifies these
two transposes with the transpose for the composite ordinary adjunction. This is the
specified conjugate compositor.
These constructions impose neither a presentation of A nor a nonempty scheme; they
apply to the zero ring, empty schemes and identity compactifications.
-/
theorem finiteRingCompactificationTransposeComparison
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) (_hell : ell.Prime) (_hp : (ringChar k).Prime)
    (_hne : ringChar k ≠ ell) (_hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f) :
    letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType aX
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    (Fe A c).IsLeftAdjoint ∧ ProjectionLaw A c ∧ TransposeLaw A c ∧
      RepresentativeLaw A c ∧ CoherenceLaw A k aY c := by
  letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType aX
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  exact ⟨AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c,
    normalized_projection_law A c, normalized_transpose_law A c,
    normalized_representative_law A c, normalized_coherence_law A k aY c⟩

end AlgebraicGeometry.ProEtale.FiniteCompactificationTranspose

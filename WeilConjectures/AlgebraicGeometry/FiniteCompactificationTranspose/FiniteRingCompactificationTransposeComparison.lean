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
  ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app H

/-- The corresponding actual pro-etale projection, on the comparison objects.
Source: def-exchange-projection, the same proper/open construction on the pro-etale site
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev pp {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : E A X) (H : E A Y) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
    ((C A X).obj M)).app ((C A Y).obj H)

/-- Source identification in the projection square: comparison tensor, then B tensor 1.
Source: the displayed projection square
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def projectionSource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : EPlus A X) (H : E A Y) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) ((Fe A c).obj M.obj)).app H ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).mapIso (B A c M)).app ((C A Y).obj H)

/-- Target identification: B at the tensor input, then compact support of the
canonical tensor/pullback comparison. Source: the displayed projection square
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
def projectionTarget {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : EPlus A X) (H : E A Y)
    (ht : DerivedCategory.TStructure.t.plus (tensorInput A f M.obj H)) :=
  B A c ⟨tensorInput A f M.obj H, ht⟩ ≪≫
    (Fp A c).mapIso (projectionComparisonTargetIso A f M.obj H).symm

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

/-- Finite-ring comparison preserves compactification projections, their inverses,
restricted exceptional transposes and counits, representatives, and normalized compositors.
Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, the two sentences
identifying the affine-line adjoints with the same integration, and final reassociations.
(blueprint: lem-pur-finite-ring-compactification-transpose-comparison).

Proof:
1. Expand both compactification projections into proper counit projection followed by
inverse open tensor comparison and pullback composition. Paste the proper projection
comparison square with the arbitrary-object open square. Naturality of the proper mate
moves the open comparison to the B factor. All vertical factors are invertible; solve
this square for the pro-etale projection and then take inverses.
2. Exact open extension and derived direct image preserve bounded-below objects. For H
bounded below the comparison unit eta_H is invertible. Thus C_XG(eta_H) identifies
C_XGH with Q_H = C_XGU_YC_YH; the explicit hypothesis that GH is bounded below makes
GU_YC_YH bounded below as well. No estimate on G at other targets is needed.
3. Precomposition by B, the comparison adjunction at Y, the ordinary exceptional
adjunction, and full faithfulness of C_X on bounded-below targets are bijections.
Their composite is boundedSiteTranspose; postcomposition by C_XG(eta_H inverse)
gives transpose. If B a_p = C_Y a_e, naturality of eta and of the ordinary adjunction
gives raw transpose = C_X(adj_e a_e) followed by C_XG(eta_H). Cancel the last factor.
4. For J = GH and a_e the ordinary counit its transpose is the identity. The inverse
Hom chain therefore gives precisely B inverse followed by the image of that counit.
Every compatible inverse-projection or integration morphism is covered by the same
calculation with arbitrary a_e.
5. Every arrow of the Hom chain is natural. Full faithfulness uniquely lifts the
changes of source and target representatives. Naturality identifies their conjugated
transposes, proving independence of both representatives, also for zero objects.
6. Apply the proper-refinement and computed proper/open composition equations of
finiteCompactSiteCoherence. Use those exact two bounded-below compositors in the
conjugate clause, inserting only their canonical inclusion compatibilities. Evaluating
the ordinary mate means composing its component with the counit of ah and applying
the composite ordinary adjunction Hom equivalence. Mate pasting under these adjunctions,
and the just computed restricted Hom chains, identifies their conjugates. The two
successive transposes defining proRightCompositor are exactly this pasted mate.
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
  sorry

end AlgebraicGeometry.ProEtale.FiniteCompactificationTranspose

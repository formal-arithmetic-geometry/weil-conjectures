module

public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.CoefficientTowerShriekInterfaces
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.SmoothPurityTowerGammaData
public import Sheaf.Paper.SmoothPurityCoordinateRightComparisons
public import Sheaf.Paper.TowerClassDiagonal
public import Sheaf.Paper.TowerClassPullback
public import Sheaf.Paper.SmoothPurityTowerChartData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Sheaf.Paper.TowerGeometricPurityData
import Sheaf.Paper.TowerGeometricPurityAssembly

/-! # Geometric Frobenius and the strict-tower purity mate

Source: latest blueprint equivariance of purity and trace, Steps 1 and 5.
(blueprint: lem-pur-tower-geometric-purity-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry AlgebraicGeometry.ProEtale

/-- Specialize the whole-tower conclusion to the actual geometric-Frobenius maps
of the model schemes. Noetherian and compactification instances below are consequences
of finite type or of the displayed open/proper factorization, not extra hypotheses.
All operation data are the recorded normalized presentations. The result supplies
closure and root witnesses for every presentation of the given purity isomorphism.
Source: equivariance Steps 1 and 5
(blueprint: lem-pur-tower-geometric-purity-mate). -/
@[irreducible] def TowerGeometricPurityConclusion (S : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (.of S.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (d : ℕ) (c : Compactification (S.frobeniusMap f₀)) : Prop :=
  let β := Spec.map (CommRingCat.ofHom (algebraMap S.field.k₀ S.field.k))
  letI : LocallyOfFiniteType (S.frobeniusFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom β))
  letI : QuasiCompact (S.frobeniusFiber X₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom β))
  letI : IsSeparated (S.frobeniusFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom β))
  letI : LocallyOfFiniteType (S.frobeniusFiber Y₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom β))
  letI : QuasiCompact (S.frobeniusFiber Y₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom β))
  letI : IsSeparated (S.frobeniusFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom β))
  letI : LocallyOfFiniteType ((S.frobeniusFiber X₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (S.frobeniusFiber X₀).hom)
  letI : QuasiCompact ((S.frobeniusFiber X₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (QuasiCompact (S.frobeniusFiber X₀).hom)
  letI : IsSeparated ((S.frobeniusFiber X₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (IsSeparated (S.frobeniusFiber X₀).hom)
  letI : LocallyOfFiniteType ((S.frobeniusFiber Y₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (S.frobeniusFiber Y₀).hom)
  letI : QuasiCompact ((S.frobeniusFiber Y₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (QuasiCompact (S.frobeniusFiber Y₀).hom)
  letI : IsSeparated ((S.frobeniusFiber Y₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (IsSeparated (S.frobeniusFiber Y₀).hom)
  letI : IsSeparated (S.frobeniusMap f₀) :=
    MorphismProperty.overPullbackMap (P := @IsSeparated) β f₀ inferInstance
  letI : LocallyOfFiniteType (S.frobeniusMap f₀) :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) β f₀ inferInstance
  letI : QuasiCompact (S.frobeniusMap f₀) :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) β f₀ inferInstance
  letI : IsNoetherian (S.frobeniusFiber X₀).left :=
    isNoetherian_of_locallyOfFiniteType (S.frobeniusFiber X₀).hom
  letI : IsNoetherian (S.frobeniusFiber Y₀).left :=
    isNoetherian_of_locallyOfFiniteType (S.frobeniusFiber Y₀).hom
  letI : QuasiCompact (c.i ≫ c.g) := c.comm ▸ inferInstance
  letI : (c.i ≫ c.g).IsOver (Spec (.of S.field.k)) := c.comm ▸
    (inferInstanceAs ((S.frobeniusMap f₀).IsOver (Spec (.of S.field.k))))
  letI : HasCompactification (c.i ≫ c.g) :=
    ⟨⟨SpTowerGamma.factorization c.i c.g⟩⟩
  ∀ (b : SpTowerShriek.Base S.coefficients.l S.extension)
    (o : SpTowerShriek.Operations S.coefficients.l S.extension b)
    (x : SpTowerShriek.OpenExchange S.coefficients.l S.extension b o),
    SpTowerShriek.Laws S.coefficients.l S.extension b o x →
    ∀ (q : SpTowerCalculus.Coordinates S.coefficients.l S.extension b)
    (z : SpTowerCalculus.FiniteCoordinates S.coefficients.l S.extension)
    (h : SpTowerCalculus.Preservation S.coefficients.l S.extension S.field.k b o q)
    (cal : SpTowerCalculus.Calculus S.coefficients.l S.extension S.field.k b o q z h)
    (w : SpChartAdmissibility.Twists S.coefficients.l S.extension (S.frobeniusFiber X₀).left)
    (hF : ∀ K : SpTowerCalculus.C S.coefficients.l S.extension b q
        (S.frobeniusFiber X₀).left,
      spConstructibleTorTowers S.coefficients.l S.extension (S.frobeniusFiber Y₀).left
        (q.abelian (S.frobeniusFiber Y₀).left)
        ((SpTowerCalculus.F S.coefficients.l S.extension b o q
          (SpTowerGamma.factorization c.i c.g)).obj K.obj))
    (G : SpTowerCalculus.C S.coefficients.l S.extension b q (S.frobeniusFiber Y₀).left ⥤
      SpTowerCalculus.C S.coefficients.l S.extension b q (S.frobeniusFiber X₀).left)
    (adj : SpTowerGluing.support S.coefficients.l S.extension b o q
      (SpTowerGamma.factorization c.i c.g) hF ⊣ G)
    (lv : SpTowerGluing.Levels S.coefficients.l S.extension b o q
      (SpTowerGamma.factorization c.i c.g) hF G adj)
    (a : SpTowerGamma.Purity S.coefficients.l S.extension b o q c.i c.g d w hF G adj lv),
    ∃ sq : IsPullback (S.frobeniusGaloisMap X₀) (c.i ≫ c.g) (c.i ≫ c.g)
        (S.frobeniusGaloisMap Y₀),
      Nonempty (SpGeometricPurity.Result S.coefficients.l S.extension b o q
        c.i c.g d w hF G adj lv a S.field.k
        (S.frobeniusGaloisMap X₀) (S.frobeniusGaloisMap Y₀) sq z h cal x)

/-- Semilinear purity exchange is the compact-support counit mate on unnormalized
uniformly bounded constructible finite-Tor towers. It is a natural isomorphism,
restricts to normalized towers, and both displayed whole-tower purity identities hold.
The retagging assertion includes orientation and the actual tensor-map transpose.
Source: latest blueprint, equivariance proof Steps 1 and 5, and purity-bc-factors (1)--(2)
(blueprint: lem-pur-tower-geometric-purity-mate).

Proof:
1. The Frobenius-square lemma gives compatible scheme isomorphisms and a Cartesian
square. The projection equation a_T g_T = Spec(gamma) a_T makes it k-linear after
retagging. Retagging preserves separatedness, finite type and smooth pure dimension.
2. Tower-operations ground-field retagging identifies sites, quotient transitions,
pullback, tensor, twists and the same-compactification support functor before deriving.
Orientation retagging identifies the whole orientation. Tensor-transpose retagging
identifies inverse projection followed by the counit and its actual transpose, under
the unique counit-preserving comparison of right adjoints. Hence Gamma also agrees.
3. Apply tower exceptional base change to the retagged square. Proper/open exchange,
followed by canonical compactification refinement, is exchange above. Transposing its
inverse and the pulled-back counit gives mate. Injectivity of the adjunction Hom
bijection identifies it with the retagged exceptional exchange, proving invertibility.
4. Apply purity-bc-factors (1)--(2) to orientation and tensor transpose, then insert
both identities into the recorded factorization of tower Gamma. The strict root map
and its tensor powers, with composition and shifts, give sourceComparison. This is
the purity_square identity in the ordinary derived category of whole towers. No
faithfulness of derived finite evaluation is asserted or used for an equality.
5. Tower Gamma preserves normalized towers for both adjoints. Exact inverse image
along a scheme isomorphism preserves flat resolutions and every coefficient quotient,
so it preserves the canonical derived reduction arrows and their invertibility.
This gives both normalized preservation fields. Finally cancel the invertible pulled
purity map in purity_square to obtain conjugation, including d=0 and the empty scheme.
-/
theorem tower_geometric_purity_mate (S : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (.of S.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (d : ℕ) [SmoothOfRelativeDimension d (S.frobeniusMap f₀)]
    (c : Compactification (S.frobeniusMap f₀)) :
    S.TowerGeometricPurityConclusion X₀ Y₀ f₀ d c := by
  classical
  let β := Spec.map (CommRingCat.ofHom (algebraMap S.field.k₀ S.field.k))
  let : LocallyOfFiniteType (S.frobeniusFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom β))
  let : QuasiCompact (S.frobeniusFiber X₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom β))
  let : IsSeparated (S.frobeniusFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom β))
  let : LocallyOfFiniteType (S.frobeniusFiber Y₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom β))
  let : QuasiCompact (S.frobeniusFiber Y₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom β))
  let : IsSeparated (S.frobeniusFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom β))
  let : LocallyOfFiniteType ((S.frobeniusFiber X₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (S.frobeniusFiber X₀).hom)
  let : QuasiCompact ((S.frobeniusFiber X₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (QuasiCompact (S.frobeniusFiber X₀).hom)
  let : IsSeparated ((S.frobeniusFiber X₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (IsSeparated (S.frobeniusFiber X₀).hom)
  let : LocallyOfFiniteType ((S.frobeniusFiber Y₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (S.frobeniusFiber Y₀).hom)
  let : QuasiCompact ((S.frobeniusFiber Y₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (QuasiCompact (S.frobeniusFiber Y₀).hom)
  let : IsSeparated ((S.frobeniusFiber Y₀).left ↘ Spec (.of S.field.k)) :=
    inferInstanceAs (IsSeparated (S.frobeniusFiber Y₀).hom)
  let : IsSeparated (S.frobeniusMap f₀) :=
    MorphismProperty.overPullbackMap (P := @IsSeparated) β f₀ inferInstance
  let : LocallyOfFiniteType (S.frobeniusMap f₀) :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) β f₀ inferInstance
  let : QuasiCompact (S.frobeniusMap f₀) :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) β f₀ inferInstance
  let : IsNoetherian (S.frobeniusFiber X₀).left :=
    isNoetherian_of_locallyOfFiniteType (S.frobeniusFiber X₀).hom
  let : IsNoetherian (S.frobeniusFiber Y₀).left :=
    isNoetherian_of_locallyOfFiniteType (S.frobeniusFiber Y₀).hom
  let : QuasiCompact (c.i ≫ c.g) := c.comm ▸ inferInstance
  let : (c.i ≫ c.g).IsOver (Spec (.of S.field.k)) := c.comm ▸
    (inferInstanceAs ((S.frobeniusMap f₀).IsOver (Spec (.of S.field.k))))
  let : HasCompactification (c.i ≫ c.g) :=
    ⟨⟨SpTowerGamma.factorization c.i c.g⟩⟩
  have hsm : SmoothOfRelativeDimension d (c.i ≫ c.g) := c.comm ▸ inferInstance
  let := hsm
  obtain ⟨hX, hY, hsq, _⟩ := S.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d
  let := hX
  let := hY
  have sq : IsPullback (S.frobeniusGaloisMap X₀) (c.i ≫ c.g) (c.i ≫ c.g)
      (S.frobeniusGaloisMap Y₀) := c.comm ▸ hsq
  unfold TowerGeometricPurityConclusion
  dsimp only
  intro b o x laws q z h cal w hF G adj lv a
  refine ⟨sq, ?_⟩
  exact SpGeometricPurity.isomorphism_purity_result S b o q c.i c.g d w hF G adj lv a
    (S.frobeniusGaloisMap X₀) (S.frobeniusGaloisMap Y₀) sq z h cal x laws

end WeilConjectures.PurityFiniteSetting

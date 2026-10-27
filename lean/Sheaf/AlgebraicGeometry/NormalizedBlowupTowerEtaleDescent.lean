/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedTowerDescentData
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.Blowup.FlatBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.CategoryTheory.Limits.MorphismProperty
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationSmoothPullback
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import Sheaf.AlgebraicGeometry.ProjectiveBundleComposition
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Blowup.Complement

/-! # Étale descent and geometry of finite normalized blowup towers

Source: ILO, Travaux de Gabber, VIII 2.2.1--2.2.11, 3.4.8 and 5.5.3--5.5.5;
Stacks Project, Tags 035S, 02NS and 0C4P
(blueprint: lem-per-normalized-blowup-tower-etale-descent).

The clauses are stated separately so that both towers already over X and towers
obtained by descent use precisely the same geometry theorem. No covers are needed for
that theorem. The descent theorem preserves the supplied datum, not just the local schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Monoscheme.NormalizedTower

/-- Geometry of a finite normalized blowup tower on a Noetherian quasi-excellent normal
separated base, without any covering assumption. All normalization maps are finite; every
level is Noetherian, normal and quasi-excellent; the final composite is projective in the
projective-bundle sense and of finite type. Every level is the identity over the complement
of the images of the centers. In the integral case the generic-stalk map is an isomorphism:
together with the common-open identity this identifies all function fields by the identity.

Source: ILO VIII 2.2.1--2.2.5; Stacks Tags 035S, 02NS, 0B3I and 0C4P
(blueprint: lem-per-normalized-blowup-tower-etale-descent).

Proof (node steps 1--4):
1. By lem-weil-pbc-noetherian-finitely-many-components and
lem-sfb-normal-locally-finite-components, the base has finitely many open integral
components. The nowhere-dense center contains no generic point. On each component use
lem-sfb-integral-blowup-projective-geometry; thm-nagata-blowup-flat-base-change restricts to
components. Globally lem-sfb-blowup-rees-symmetric-presentation and
prop-nagata-relative-proj-functoriality embed the blowup in P(I).
2. Apply lem-trf-projective-bundle-proper and
lem-per-quasi-excellent-finite-type-stability to the ordinary blowup. Its affine rings are
Nagata by lem-exc-quasi-excellent-nagata. The definition of Nagata and the degree-one
Japanese normalization assertion, together with
lem-per-componentwise-normalization-affine-charts, make the normalization finite.
3. A finite map is projective by lem-trf-finite-projective-bundle. Apply finite-type
stability again and lem-sfb-componentwise-normalization-generic-properties for normality.
Induct, using lem-sfb-projective-bundle-composition on the qcqs bases; local Noetherianity
implies quasi-separatedness. The identity handles length zero.
4. thm-nagata-global-blowup-complement, normalization on a normal scheme and its open
restriction identify every arrow off its center. The center images are closed by
properness and miss generic points. Their finite union has dense open complement. The
integral-blowup lemma and normalization give integral levels and unchanged generic stalks.
These are exactly the function fields of def-sc-function-field, and their maps restrict
to the identity on the same dense open. Empty schemes and unit centers are included. -/
theorem normalizedBlowupTower_geometry {n : ℕ} (T : NormalizedTower.{u} n)
    [IsNoetherian (T.level 0)] [(T.level 0).IsSeparated]
    (hNormal : ∀ x : T.level 0,
      IsDomain ((T.level 0).presheaf.stalk x) ∧
        IsIntegrallyClosed ((T.level 0).presheaf.stalk x))
    (hQE : ∀ V : (T.level 0).affineOpens, IsQuasiExcellent Γ(T.level 0, V))
    (hCenters : T.HasNowhereDenseCenters) :
    (∀ i : Fin (n + 1), IsNoetherian (T.level i) ∧
      (∀ x : T.level i, IsDomain ((T.level i).presheaf.stalk x) ∧
        IsIntegrallyClosed ((T.level i).presheaf.stalk x)) ∧
      ∀ V : (T.level i).affineOpens, IsQuasiExcellent Γ(T.level i, V)) ∧
    (∀ i : Fin n, IsFinite (T.center i).blowup.fromReducedNormalization) ∧
    IsProjectiveBundle (T.toFirst (Fin.last n)) ∧
    LocallyOfFiniteType (T.toFirst (Fin.last n)) ∧ QuasiCompact (T.toFirst (Fin.last n)) ∧
    (∃ V : (T.level 0).Opens, (V : Set (T.level 0)) = T.centerImagesᶜ ∧
      Dense (V : Set (T.level 0)) ∧
      ∀ i : Fin (n + 1), IsIso (pullback.snd (T.toFirst i) V.ι)) ∧
    (IsIntegral (T.level 0) → (∀ i : Fin (n + 1), IsIntegral (T.level i)) ∧
      ∀ (i : Fin (n + 1)) (x : T.level i), x ∈ genericPoints (T.level i) →
        T.toFirst i x ∈ genericPoints (T.level 0) ∧ IsIso ((T.toFirst i).stalkMap x)) := by
  sorry

/-- Étale pullback commutes with every normalized blowup, with all stages and ideal
centers retained. The comparison consists of actual cartesian squares. The base need not
be separated (it may be the cover U or its overlaps), and the arbitrary étale source need
not be quasi-compact, separated, or globally Noetherian.

Source: ILO VIII 2.2.7--2.2.11; Stacks Tags 0805 and 07TD
(blueprint: lem-per-normalized-blowup-tower-etale-descent).

Proof (node step 6): thm-nagata-blowup-flat-base-change gives the ordinary comparison,
whose map is itself étale. The locally Noetherian hypotheses hold on both ordinary
blowups by finite-type stability. Apply
lem-sfb-componentwise-normalization-smooth-pullback in its étale case to get the
normalized cartesian comparison. Repeating this construction gives the tower, with
center equality by ideal extension. Normality ascends étale locally by
lem-sfb-smooth-normal-ascent, and the inverse image of the dense center complement
is dense because étale maps are open. No arbitrary-flat normalization assertion is used.
The coefficient-pullback construction and the unique normalization comparisons give
the identity and composition normalizations, with no stage contraction. -/
theorem normalizedBlowupTower_etalePullback {n : ℕ} (T : NormalizedTower.{u} n)
    [IsNoetherian (T.level 0)]
    (hNormal : ∀ x : T.level 0,
      IsDomain ((T.level 0).presheaf.stalk x) ∧
        IsIntegrallyClosed ((T.level 0).presheaf.stalk x))
    (hQE : ∀ V : (T.level 0).affineOpens, IsQuasiExcellent Γ(T.level 0, V))
    (hCenters : T.HasNowhereDenseCenters) (Y : Scheme.{u}) (f : Y ⟶ T.level 0)
    [Etale f] :
    ∃ (S : NormalizedTower.{u} n) (e : S.level 0 ≅ Y) (c : CenterMap S T),
      S.HasNowhereDenseCenters ∧ c.map 0 = e.hom ≫ f ∧ c.IsCartesian := by
  sorry

/-- A tower with center-preserving étale descent datum descends uniquely, including the
chosen datum. The cover's source is only required Noetherian, not separated. The same
number of ordered stages is used in the descended tower and every comparison.

Source: ILO VIII 2.2.11 and 5.5.5; Stacks Tag 023T
(blueprint: lem-per-normalized-blowup-tower-etale-descent).

Proof (node steps 5, 8--9, using steps 1--4 and 6--7):
1. Normalized blowups have no nonidentity automorphisms over the base: on each affine
base open the source is separated and its integral components contain the dense
center complement. This open is schematically dense, so lem-chow-agree-on-dense-open
makes an automorphism the identity. Glue by lem-weil-pbc-scheme-morphism-gluing and
induct. This works for nonseparated U as well (step 5).
2. Suppose X_i has been constructed. The comparison U_i -> X_i is the base change of
uMap, hence a singleton fpqc cover by lem-galois-fpqc-covering-base-change. Apply
lem-pc-fpqc-descent to the next center and its inclusion in O. Stalkwise faithful-flat
injectivity (step 7) makes the descended map injective. Its image is the descended
quasi-coherent ideal. The Noetherian-submodule lemma and pqf-lem-coherent-ft-locnoeth
make it coherent. Its zero set misses generic points: a point over a generic point of
X_i is generic in the étale source, by the zero-dimensional-fiber lemma (step 8).
3. Set X_(i+1) to the actual normalized blowup of that ideal. Steps 1--4 give the
required geometry and step 6 gives the cartesian comparison with U_(i+1). The given
and reconstructed overlap identifications differ by an automorphism, hence agree by
step 5. Iterate without deleting identity stages (step 9).
4. Fully faithful module descent makes each ideal and its inclusion unique. Functorial
blowup and normalization then compare any two global towers, and the same rigidity
makes their compatible isomorphism unique. The argument starts at n=0 and includes
empty schemes. -/
theorem normalizedBlowupTower_etaleDescent {n : ℕ} (X : Scheme.{u})
    [IsNoetherian X] [X.IsSeparated]
    (hNormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (hQE : ∀ V : X.affineOpens, IsQuasiExcellent Γ(X, V))
    (T : NormalizedTower.{u} n) [IsNoetherian (T.level 0)]
    (uMap : T.level 0 ⟶ X) [Etale uMap] [QuasiCompact uMap] [Surjective uMap]
    (hCenters : T.HasNowhereDenseCenters) (D : DescentData T uMap) :
    ∃ (S : NormalizedTower.{u} n) (e : S.level 0 ≅ X) (c : CenterMap T S),
      S.HasNowhereDenseCenters ∧ D.Realizes S e c ∧
      ∀ (S' : NormalizedTower.{u} n) (e' : S'.level 0 ≅ X) (c' : CenterMap T S'),
        S'.HasNowhereDenseCenters → D.Realizes S' e' c' →
        ∃! E : CenterIso S S', (E.iso 0).hom ≫ e'.hom = e.hom ∧
          ∀ i : Fin (n + 1), c.map i ≫ (E.iso i).hom = c'.map i := by
  sorry

/-- Equality of ideal centers is detected by any jointly surjective flat family at a
stage. No quasi-compactness or size bound is imposed on that family.

Source: ILO VIII 5.5.3; Stacks Tags 00HR and 05CK
(blueprint: lem-per-normalized-blowup-tower-etale-descent).

Proof (node step 7): at each point choose a lift to one covering scheme. Its flat
local stalk map is faithfully flat (lem-weil-pbc-flat-local-hom-faithfully-flat).
Universal injectivity for A/J shows that equality IB=JB implies I subset J; reverse
I and J. Flat module pullback identifies these extensions with the pulled ideal
submodules by lem-weil-pbc-flat-module-pullback-exact-pushforward-injective. Equality
at every stalk gives equality of the ideal subsheaves, by locality of membership. -/
theorem normalizedBlowupTower_flatCenterDetection {n : ℕ} (T : NormalizedTower.{u} n)
    (i : Fin n) (I J : (T.level i.castSucc).IdealSheafData)
    (A : Type v) (Y : A → Scheme.{u}) (f : ∀ a, Y a ⟶ T.level i.castSucc)
    (hFlat : ∀ a, Flat (f a))
    (hSurj : ∀ x : T.level i.castSucc, ∃ a, ∃ y : Y a, f a y = x) :
    (∀ a, I.comap (f a) = J.comap (f a)) ↔ I = J := by
  sorry

/-- For synchronized towers, ideal equality tested on a flat cover of each stage makes
the supplied stage identifications a center-preserving tower isomorphism, with arrow
equality tested on the covers too. The stages
are never contracted, even when a center is the unit ideal.

Source: ILO VIII 5.5.3 (blueprint: lem-per-normalized-blowup-tower-etale-descent).

Proof (node step 10): apply the faithful-flat ideal test of step 7 to the first pair
of centers, and then to each next pair under the given synchronized stage
identifications. The normalized blowup constructions agree under these identifications.
Equality of the arrow maps is detected by the same flat covers, since representable
functors are fpqc sheaves and morphism equality is local even for flat families without
a quasi-compactness condition. The resulting center-preserving isomorphism has exactly
the prescribed stage isomorphisms, so equality of its data makes it unique. This is a test on ideal
pullbacks, not a claim about normalization under arbitrary flat base change. -/
theorem normalizedBlowupTower_flatTowerDetection {n : ℕ} (T S : NormalizedTower.{u} n)
    (e : ∀ i : Fin (n + 1), T.level i ≅ S.level i)
    (A : Fin (n + 1) → Type v) (Y : ∀ i, A i → Scheme.{u})
    (f : ∀ i a, Y i a ⟶ T.level i)
    (hFlat : ∀ i a, Flat (f i a))
    (hSurj : ∀ i (x : T.level i), ∃ a, ∃ y : Y i a, f i a y = x)
    (hArrows : ∀ (i : Fin n) a,
      f i.succ a ≫ T.arrow i ≫ (e i.castSucc).hom =
        f i.succ a ≫ (e i.succ).hom ≫ S.arrow i)
    (hCenters : ∀ (i : Fin n) a, (T.center i).comap (f i.castSucc a) =
      ((S.center i).comap (e i.castSucc).hom).comap (f i.castSucc a)) :
    ∃! E : CenterIso T S, E.iso = e := by
  sorry

/-- Every action compatible with the given datum descends to any realization. Actions
are expressed naturally on all test schemes, covering both arbitrary abstract groups
and scheme-valued groups; the descended action retains arrows and actual ideals.

Source: ILO VIII 5.5.5 (blueprint: lem-per-normalized-blowup-tower-etale-descent).

Proof (node step 10): for a test scheme W and a group section on W, base change the
cover and the action to W. Compatibility says precisely that the action respects
the given descent relation. Apply lem-weil-pbc-fpqc-representable-descent to the action
map, and likewise to its inverse. Uniqueness descends the multiplication and identity
laws and the arrow equations. Step 7 descends preservation of the center ideals.
For representable groups do this on the parameter product; Yoneda gives the actual
scheme action. For a constant group this descends each automorphism. Faithfulness
gives uniqueness on every test scheme, and naturality follows by the same uniqueness. -/
theorem normalizedBlowupTower_actionDescent {n : ℕ} {X : Scheme.{u}}
    (T : NormalizedTower.{u} n) (uMap : T.level 0 ⟶ X)
    [Etale uMap] [QuasiCompact uMap] [Surjective uMap]
    (D : DescentData T uMap) (S : NormalizedTower.{u} n) (e : S.level 0 ≅ X)
    (c : CenterMap T S) (hc : D.Realizes S e c)
    (G : Scheme.{u}ᵒᵖ ⥤ GrpCat.{w}) (A : Action G T) (hA : A.Compatible D) :
    ∃! B : Action G S, ∀ (i : Fin (n + 1)) (W : Scheme.{u}) (g : G.obj (op W))
      (x : W ⟶ T.level i), A.act i W g x ≫ c.map i = B.act i W g (x ≫ c.map i) := by
  sorry

end AlgebraicGeometry.Monoscheme.NormalizedTower

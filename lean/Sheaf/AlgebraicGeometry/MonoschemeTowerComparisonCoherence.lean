/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Mathlib.Algebra.Field.ULift
import Sheaf.AlgebraicGeometry.ToricMonoidComparison
import Sheaf.RingTheory.AffineMonoidAlgebraNormalization
import Sheaf.AlgebraicGeometry.ToricRealizationFiniteType
import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus

/-! # Coherence of descended centered monoscheme towers

Source: ILO, Travaux de Gabber, Exposé VIII 3.2.19--3.2.20, p.106,
and 3.1.21--3.1.23, pp.101--102
(blueprint: lem-trf-monoscheme-tower-comparison-coherence).

The auxiliary records spell out the supplied rule, its unique centered lifts, and the
comparisons in this lemma. They impose no desingularization or normality of the base.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Monoscheme.TowerComparison

/-- Inputs include every fine torsion-free finite-covered monoscheme, including the empty
one and finite disjoint unions. Source: ILO VIII 3.2.19--3.2.20
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
abbrev Input := {M : Fine.{u} // M.IsTorsionFree}

/-- A finite centered normalized tower, with its actual base identified with the toric
realization. Coherence of each ideal is part of `NormalizedTower.blowup`.
Source: ILO VIII 2.2.5, 3.2.19
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure SchemeTower (M : Input.{u}) where
  length : ℕ
  tower : NormalizedTower.{u} length
  base : tower.level 0 ≅ realization (ULift.{u} ℚ) M.val

/-- A supplied contracted recursive smooth pullback, preserving actual ordered ideals.
Source: ILO VIII 2.2.8, 2.3.4, 3.2.19
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure SchemeComparison {M N : Input.{u}} (T : SchemeTower M) (S : SchemeTower N)
    (a : realization (ULift.{u} ℚ) N.val ⟶ realization (ULift.{u} ℚ) M.val) where
  pulled : NormalizedTower.{u} T.length
  base : pulled.level 0 ≅ realization (ULift.{u} ℚ) N.val
  pullback : NormalizedPullback T.tower pulled
  baseMap : pullback.lift 0 ≫ T.base.hom = base.hom ≫ a
  contraction : NormalizedContraction pulled S.tower
  baseIso : (contraction.iso 0).hom ≫
    eqToHom (congrArg S.tower.level contraction.first) ≫ S.base.hom = base.hom

/-- Undo the contraction identification to obtain the comparison's map to an original
level. Source: ILO VIII 3.1.22--3.1.23
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
noncomputable def SchemeComparison.levelMap {M N : Input.{u}}
    {T : SchemeTower M} {S : SchemeTower N}
    {a : realization (ULift.{u} ℚ) N.val ⟶ realization (ULift.{u} ℚ) M.val}
    (c : SchemeComparison T S a) (i : Fin (T.length + 1)) :
    S.tower.level (c.contraction.index i) ⟶ T.tower.level i :=
  (c.contraction.iso i).inv ≫ c.pullback.lift i

/-- The supplied scheme rule and all its smooth-scheme comparisons, including morphisms
which are not monomial. Identity and composition include the contraction index maps.
Source: ILO VIII 3.2.19--3.2.20
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure SchemeRule where
  tower : ∀ M : Input.{u}, SchemeTower M
  comparison : ∀ (M N : Input.{u})
    (a : realization (ULift.{u} ℚ) N.val ⟶ realization (ULift.{u} ℚ) M.val),
    Smooth a → SchemeComparison (tower M) (tower N) a
  identityIndex : ∀ (M : Input.{u}) (h : Smooth (𝟙 (realization (ULift.{u} ℚ) M.val)))
    (i : Fin ((tower M).length + 1)),
    (comparison M M (𝟙 _) h).contraction.index i = i
  identityMap : ∀ (M : Input.{u}) (h : Smooth (𝟙 (realization (ULift.{u} ℚ) M.val)))
    (i : Fin ((tower M).length + 1)),
    HEq ((comparison M M (𝟙 _) h).levelMap i) (𝟙 ((tower M).tower.level i))
  compositionIndex : ∀ (M N P : Input.{u})
    (a : realization (ULift.{u} ℚ) N.val ⟶ realization (ULift.{u} ℚ) M.val)
    (b : realization (ULift.{u} ℚ) P.val ⟶ realization (ULift.{u} ℚ) N.val)
    (c : realization (ULift.{u} ℚ) P.val ⟶ realization (ULift.{u} ℚ) M.val)
    (ha : Smooth a) (hb : Smooth b) (hc : Smooth c) (_eq : c = b ≫ a)
    (i : Fin ((tower M).length + 1)),
    (comparison M P c hc).contraction.index i =
      (comparison N P b hb).contraction.index ((comparison M N a ha).contraction.index i)
  compositionMap : ∀ (M N P : Input.{u})
    (a : realization (ULift.{u} ℚ) N.val ⟶ realization (ULift.{u} ℚ) M.val)
    (b : realization (ULift.{u} ℚ) P.val ⟶ realization (ULift.{u} ℚ) N.val)
    (c : realization (ULift.{u} ℚ) P.val ⟶ realization (ULift.{u} ℚ) M.val)
    (ha : Smooth a) (hb : Smooth b) (hc : Smooth c) (_eq : c = b ≫ a)
    (i : Fin ((tower M).length + 1)),
    HEq ((comparison M P c hc).levelMap i)
      ((comparison N P b hb).levelMap ((comparison M N a ha).contraction.index i) ≫
        (comparison M N a ha).levelMap i)

/-- A centered saturated lift through the canonical monomial maps. The centers are
identified as ideals, not merely by support. All intermediate objects are fine,
torsion-free and finitely covered. Source: ILO VIII 3.2.14--3.2.19
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure Lift (M : Fine.{u}) {n : ℕ} (S : NormalizedTower.{u} n)
    (e : realization (ULift.{u} ℚ) M ≅ S.level 0) where
  tower : Tower.{u} n
  base : tower.level 0 = M
  torsionFree : ∀ i, (tower.level i).IsTorsionFree
  iso : ∀ i, realization (ULift.{u} ℚ) (tower.level i) ≅ S.level i
  baseIso : (iso 0).hom = eqToHom (congrArg (realization (ULift.{u} ℚ)) base) ≫ e.hom
  arrows : ∀ i : Fin n,
    realizationMap (ULift.{u} ℚ) (tower.arrow i) ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ S.arrow i
  centers : ∀ i : Fin n, ringIdeal (ULift.{u} ℚ) (tower.center i) =
    (S.center i).comap (iso i.castSucc).hom

/-- Uniqueness of lifts means a unique centered isomorphism over the identity, compatible
with their specified realization identifications. Localness in both directions makes
these actual monoscheme isomorphisms. Source: ILO VIII 3.2.19--3.2.20
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure LiftIso {M : Fine.{u}} {n : ℕ} {S : NormalizedTower.{u} n}
    {e : realization (ULift.{u} ℚ) M ≅ S.level 0} (T U : Lift M S e) where
  iso : ∀ i, (T.tower.level i).space ≅ (U.tower.level i).space
  localHom : ∀ i, FineFan.IsLocalMorphism (iso i).hom
  localInv : ∀ i, FineFan.IsLocalMorphism (iso i).inv
  base : (iso 0).hom = eqToHom (congrArg Fine.space (T.base.trans U.base.symm))
  arrows : ∀ i : Fin n,
    (T.tower.arrow i).map ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ (U.tower.arrow i).map
  centers : ∀ i : Fin n,
    T.tower.center i = pullbackAlong (iso i.castSucc).hom (U.tower.center i)
  realizes : ∀ i, IsRealizationMap (ULift.{u} ℚ) ⟨(iso i).hom, localHom i⟩
    ((T.iso i).hom ≫ (U.iso i).inv)

/-- The assumed lifts of the scheme rule, unique up to their centered realization-preserving
isomorphisms. Torus invariance is tested on the identified intermediate toric schemes.
Source: ILO VIII 3.2.15, 3.2.19--3.2.20
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure LiftRule (F : SchemeRule.{u}) where
  lift : ∀ M : Input.{u}, Lift M.val (F.tower M).tower (F.tower M).base.symm
  unique : ∀ (M : Input.{u})
    (T : Lift M.val (F.tower M).tower (F.tower M).base.symm),
    Nonempty (LiftIso (lift M) T) ∧ Subsingleton (LiftIso (lift M) T)
  invariant : ∀ (M : Input.{u}) (i : Fin (F.tower M).length),
    IsTorusEquivariant (ULift.{u} ℚ) ((lift M).tower.level i.castSucc)
      (((F.tower M).tower.center i).comap ((lift M).iso i.castSucc).hom)

/-- A descended comparison realizes precisely the supplied scheme comparison. Its full
pullback retains all original indices; its contraction retains the actual ordered ideals.
The two deletion tests are compared separately, so a nonidentity saturation stays.
Source: ILO VIII 3.1.21--3.1.23, 3.2.19--3.2.20
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure Comparison {F : SchemeRule.{u}} (T : LiftRule F) {M N : Input.{u}}
    (a : Hom N.val M.val) (c : SchemeComparison (F.tower M) (F.tower N)
      (realizationMap (ULift.{u} ℚ) a)) where
  pulled : Lift N.val c.pulled c.base.symm
  pullback : PullbackTower (T.lift M).tower pulled.tower
  smooth : ∀ i, (pullback.lift i).IsSmooth
  baseMap : (pullback.lift 0).map =
    eqToHom (congrArg Fine.space pulled.base) ≫ a.map ≫
      eqToHom (congrArg Fine.space (T.lift M).base.symm)
  contraction : Contraction pulled.tower (T.lift N).tower
  baseIso : (contraction.iso 0).hom =
    eqToHom (congrArg Fine.space (pulled.base.trans (T.lift N).base.symm)) ≫
      eqToHom (congrArg (fun j ↦ ((T.lift N).tower.level j).space)
        contraction.first.symm)
  index : contraction.index = c.contraction.index
  contractionLocal : ∀ i, FineFan.IsLocalMorphism (contraction.iso i).hom ∧
    FineFan.IsLocalMorphism (contraction.iso i).inv
  pullbackRealizes : ∀ i, IsRealizationMap (ULift.{u} ℚ) (pullback.lift i)
    ((pulled.iso i).hom ≫ c.pullback.lift i ≫ ((T.lift M).iso i).inv)
  contractionRealizes : ∀ i, IsRealizationMap (ULift.{u} ℚ)
    ⟨(contraction.iso i).hom, (contractionLocal i).1⟩
    ((pulled.iso i).hom ≫ (c.contraction.iso i).hom ≫
      eqToHom (congrArg (F.tower N).tower.level (congrArg (fun f ↦ f i) index.symm)) ≫
        ((T.lift N).iso (contraction.index i)).inv)
  unitCenter : ∀ i : Fin (F.tower M).length,
    pulled.tower.center i = wholeIdeal (pulled.tower.level i.castSucc) ↔
      c.pulled.center i = ⊤
  isoStage : ∀ i : Fin (F.tower M).length,
    IsIso (pulled.tower.arrow i).map ↔ IsIso (c.pulled.arrow i)

/-- The underlying level maps include the canonical identification with the contracted
pullback. Source: ILO VIII 3.1.22--3.1.23, 3.2.20
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
noncomputable def Comparison.levelMap {F : SchemeRule.{u}} {T : LiftRule F}
    {M N : Input.{u}} {a : Hom N.val M.val}
    {c : SchemeComparison (F.tower M) (F.tower N) (realizationMap (ULift.{u} ℚ) a)}
    (d : Comparison T a c) (i : Fin ((F.tower M).length + 1)) :
    ((T.lift N).tower.level (d.contraction.index i)).space ⟶
      ((T.lift M).tower.level i).space :=
  (d.contraction.iso i).inv ≫ (d.pullback.lift i).map

/-- A simultaneous choice of descended comparisons with identity and composition equations
on both original indices and level maps. The index equation identifies successive
contractions with the single contraction. Source: ILO VIII 3.1.22--3.1.23, 3.2.20
(blueprint: lem-trf-monoscheme-tower-comparison-coherence). -/
structure CoherentComparisons {F : SchemeRule.{u}} (T : LiftRule F) where
  realizationSmooth : ∀ {M N : Input.{u}} (a : Hom N.val M.val),
    a.IsSmooth → Smooth (realizationMap (ULift.{u} ℚ) a)
  comparison : ∀ {M N : Input.{u}} (a : Hom N.val M.val) (ha : a.IsSmooth),
    Comparison T a
      (F.comparison M N (realizationMap (ULift.{u} ℚ) a) (realizationSmooth a ha))
  unique : ∀ {M N : Input.{u}} (a : Hom N.val M.val) (ha : a.IsSmooth)
    (d e : Comparison T a
      (F.comparison M N (realizationMap (ULift.{u} ℚ) a) (realizationSmooth a ha)))
    (i : Fin ((F.tower M).length + 1)), HEq (d.levelMap i) (e.levelMap i)
  identityIndex : ∀ (M : Input.{u}) (a : Hom M.val M.val) (ha : a.IsSmooth)
    (_eq : a.map = 𝟙 M.val.space) (i : Fin ((F.tower M).length + 1)),
    (comparison a ha).contraction.index i = i
  identityMap : ∀ (M : Input.{u}) (a : Hom M.val M.val) (ha : a.IsSmooth)
    (_eq : a.map = 𝟙 M.val.space) (i : Fin ((F.tower M).length + 1)),
    HEq ((comparison a ha).levelMap i) (𝟙 ((T.lift M).tower.level i).space)
  compositionIndex : ∀ {M N P : Input.{u}}
    (a : Hom N.val M.val) (b : Hom P.val N.val) (c : Hom P.val M.val)
    (ha : a.IsSmooth) (hb : b.IsSmooth) (hc : c.IsSmooth) (_eq : c.map = b.map ≫ a.map)
    (i : Fin ((F.tower M).length + 1)),
    (comparison c hc).contraction.index i =
      (comparison b hb).contraction.index ((comparison a ha).contraction.index i)
  compositionMap : ∀ {M N P : Input.{u}}
    (a : Hom N.val M.val) (b : Hom P.val N.val) (c : Hom P.val M.val)
    (ha : a.IsSmooth) (hb : b.IsSmooth) (hc : c.IsSmooth) (_eq : c.map = b.map ≫ a.map)
    (i : Fin ((F.tower M).length + 1)),
    HEq ((comparison c hc).levelMap i)
      ((comparison b hb).levelMap ((comparison a ha).contraction.index i) ≫
        (comparison a ha).levelMap i)
  successiveContraction : ∀ {M N P : Input.{u}}
    (a : Hom N.val M.val) (b : Hom P.val N.val) (c : Hom P.val M.val)
    (ha : a.IsSmooth) (hb : b.IsSmooth) (hc : c.IsSmooth) (_eq : c.map = b.map ≫ a.map),
    ∃ e : ∀ i : Fin ((F.tower M).length + 1),
      ((comparison c hc).pulled.tower.level i).space ≅
        ((comparison b hb).pulled.tower.level ((comparison a ha).contraction.index i)).space,
      (∀ i, HEq ((comparison c hc).contraction.iso i).hom
        ((e i).hom ≫
          ((comparison b hb).contraction.iso ((comparison a ha).contraction.index i)).hom)) ∧
      ∀ i, (e i).hom ≫
        ((comparison b hb).pullback.lift ((comparison a ha).contraction.index i)).map ≫
          ((comparison a ha).contraction.iso i).inv ≫
            ((comparison a ha).pullback.lift i).map = ((comparison c hc).pullback.lift i).map

/-- Coherent smooth scheme comparisons descend to the unique centered saturated lifts.
Source: ILO VIII 3.2.19 (second half), Theorem 3.2.20, p.106; 3.1.21--3.1.23
(blueprint: lem-trf-monoscheme-tower-comparison-coherence).

Proof plan (the node's seven steps).
1. A smooth monoscheme map realizes to a smooth map by lem-trf-toric-monoid-comparison.
   Extend each nonempty coherent center recursively; the smooth product charts
   P × N^r × Z^t stay smooth after saturated blowup, so this induction can continue.
   The monoid/ring ideal comparison and normalized chart comparison identify the full
   pullback towers, including every original index and their torsion-free finite covers.
2. Unit ideals correspond by monomial independence. For a whole monoid ideal the map
   is saturation, and the ring map is normalization by lem-trf-affine-monoid-algebra-
   normalization. Its being an isomorphism is exactly equality with saturation, again
   by independence of monomials. Thus precisely the same indices are contracted;
   nonidentity saturations and proper principal centers are retained.
3. At each retained center, injectivity of the ideal comparison identifies the actual
   monoid ideals. The saturated blowup universal property
   (lem-trf-saturated-monoscheme-blowup-universal) constructs the unique next-level
   isomorphism, preserving both center and index order.
4. The realization is the specified scheme isomorphism: toric realizations are reduced
   of finite type with integral components (lem-trf-toric-realization-finite-type),
   nonempty monoid centers are nonzero on every component, and the normalized blowup
   has no nonidentity automorphism over its base (lem-trf-normalized-blowup-calculus).
5. Uniqueness of each saturated blowup lift gives uniqueness of the comparison over
   the base and centers. Apply it to the identity comparison; no stage is deleted.
6. For a composite, recursive ideal extensions agree. The saturated blowup universal
   property identifies full successive pullbacks. Deleted whole-center isomorphisms
   remain such after smooth pullback, so successive contraction has exactly the same
   ordered subsequence as single contraction, even across consecutive deleted stages.
7. Both composite comparisons preserve these centers and indices over the identity
   base. Uniqueness gives equality of their level maps. Their realizations are the
   prescribed scheme composites. The argument admits zero-length and empty towers. -/
theorem exists_coherentComparisons (F : SchemeRule.{u}) (T : LiftRule F) :
    Nonempty (CoherentComparisons T) := by
  sorry

end AlgebraicGeometry.Monoscheme.TowerComparison

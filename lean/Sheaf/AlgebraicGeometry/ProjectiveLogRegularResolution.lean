/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.AlgebraicGeometry.MonoidalResolutionTower
import Sheaf.AlgebraicGeometry.FSLogSmoothCompositionStrictBaseChange
import Sheaf.AlgebraicGeometry.LogSmoothPreservesLogRegularity
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.AlgebraicGeometry.SaturatedLogTowerProjectivity
import Sheaf.AlgebraicGeometry.SaturatedLogTowerDenseOpen
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.ULift

/-!
# Projective resolution of an excellent-base log regular scheme

Source: ILO, Travaux de Gabber, VIII 3.4.6(i), 3.4.8--3.4.9, pp.111--112;
VI 1.7--1.8, p.70; XVI 3.7, pp.254--255
(blueprint: lem-per-log-regular-projective-log-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem sharp_fs_torsionFree {P : Type u} [CommMonoid P]
    (hP : IsFineSaturatedMonoid P) (hsharp : ∀ p : P, IsUnit p → p = 1)
    (g : Algebra.GrothendieckGroup P) (n : ℕ) (hn : n ≠ 0) (hg : g ^ n = 1) :
    g = 1 := by
  obtain ⟨a, ha⟩ := hP.2.2 g n (Nat.pos_of_ne_zero hn) ⟨1, by simp [hg]⟩
  obtain ⟨b, hb⟩ := hP.2.2 g⁻¹ n (Nat.pos_of_ne_zero hn) ⟨1, by simp [hg]⟩
  have hab : a * b = 1 := hP.2.1 (by rw [map_mul, ha, hb, map_one]; exact mul_inv_cancel g)
  have hua : IsUnit a := isUnit_iff_exists.mpr ⟨b, hab, by simpa [mul_comm] using hab⟩
  rw [← ha, hsharp a hua, map_one]

private theorem identity_eq {X : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X X) (hf : f.IsIdentity) : f = EtaleLogHom.id X := by
  have he : f.toLogMap = (EtaleLogHom.id X).toLogMap := by
    apply EtaleLogMap.ext _ _ hf.1
    intro W V k hk
    have hk' : k ≫ W.hom = V.hom := by
      change k ≫ W.hom = V.hom ≫ f.base at hk
      exact hk.trans ((congrArg (V.hom ≫ ·) hf.1).trans (Category.comp_id _))
    exact hf.2 W V k hk hk'
  exact congrArg EtaleLogMap.toFSHom he

private theorem smooth_comp_of_etale {X Y Z : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (g : EtaleLogHom Y Z)
    (hf : f.IsLogEtale) (hg : g.IsLogSmooth) : (f.comp g).IsLogSmooth := by
  obtain ⟨c, hc, hs⟩ := fsLogSmooth_composition_strictBaseChange.{u, u}.2.2.1 X Y Z f g hf hg
  have hc' : f.toLogMap.CompEq g.toLogMap c.toLogMap := hc
  have he : c = f.comp g := congrArg EtaleLogMap.toFSHom
    (EtaleLogMap.eq_comp_of_compEq hc')
  exact he ▸ hs

private theorem integral_of_dense_open_iso {X Y : Scheme.{u}} [IsIntegral Y]
    (hX : IsRegularScheme X) (U : X.Opens) (W : Y.Opens)
    (e : U.toScheme ≅ W.toScheme) (hU : Dense (U : Set X)) (hW : Dense (W : Set Y)) :
    IsIntegral X := by
  have : Nonempty W := hW.nonempty.to_subtype
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hUi : IrreducibleSpace U.toScheme :=
    (Scheme.homeoOfIso e).irreducibleSpace_iff.mpr inferInstance
  have hi : IsIrreducible (U : Set X) := by
    have hir := (IrreducibleSpace.isIrreducible_univ U.toScheme).image U.ι
      U.ι.continuous.continuousOn
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using hir
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr (by
    simpa only [hU.closure_eq, Set.top_eq_univ] using hi.closure)
  have : IsRegular X := hX.2
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun _ ↦ inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- An integral log regular scheme quasi-projective over an excellent affine base admits
one finite saturated log blowup tower with projective birational regular integral total
space. Its composite is log etale and preserves every supplied log-smooth map to a locally
Noetherian fs log scheme. The initial identity and recursive `CompEq` equations specify
that the maps `p` are the actual composites of the tower, including for length zero.

Source: ILO VIII 3.4.6(i), 3.4.8--3.4.9; VI 1.7--1.8; XVI 3.7
(blueprint: lem-per-log-regular-projective-log-resolution).

Proof:
1. Sharp saturated characteristics have torsion-free group completions: saturation
   puts both a torsion element and its inverse in the monoid, so sharpness kills it.
   Quasi-compactness follows from the given morphism to the affine base. Apply
   `exists_monoidal_resolution_tower` to obtain one tower with free terminal stalks.
2. The finite-tower clause of `fsLogSmooth_composition_strictBaseChange` supplies
   its actual composite maps and log etaleness. Its identity condition determines
   the initial map, including on relative etale sections and for length zero.
3. Log etale implies log smooth. Apply `EtaleLogHom.isLogRegular_of_isLogSmooth`
   (ILO VI 1.8) to obtain terminal log regularity. Convert the free characteristics
   from the ULift/finitely-supported presentation to finite tuples, and apply
   `FineSaturatedLogScheme.free_characteristic_regular_boundary` (ILO VI 1.7).
4. `saturatedLogTower_isHProjective` proves projectivity for this fixed tower from
   the quasi-projective affine-base hypothesis. `saturatedLogTower_denseOpen`
   gives the dense-open isomorphism of the same tower, using its log regular endpoints.
5. The target dense open is nonempty and integral. Its isomorphic source open is
   irreducible, hence its dense closure is the whole irreducible terminal scheme.
   The terminal regular stalks are domains, hence reduced. The reduced irreducible
   terminal scheme is integral.
6. The mixed composition clause of the log calculus makes the terminal composite
   followed by any supplied log-smooth map log smooth. Its CompEq equations identify
   this map with the explicitly constructed composite in the conclusion.

The geometric arguments in step 4 are the two named remaining subproblems; neither
constructs a resolution tower or asserts terminal regularity. -/
theorem exists_projective_log_regular_resolution
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsExcellent A)
    (V : FineSaturatedLogScheme.{u}) [IsIntegral V.scheme] (hV : V.IsLogRegular)
    (f : V.scheme ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hqp : ∃ (n : ℕ) (i : V.scheme ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))),
      IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A) = f) :
    ∃ (T : SaturatedLogBlowupTower.{u})
      (p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) V),
      T.level 0 = V ∧ HEq (p 0) (EtaleLogHom.id V) ∧
      (∀ i : Fin T.length, (T.arrow i).CompEq (p i.castSucc) (p i.succ)) ∧
      IsHProjective (p (Fin.last T.length)).base ∧
      (∃ (U : (T.level (Fin.last T.length)).scheme.Opens) (W : V.scheme.Opens)
        (e : U.toScheme ≅ W.toScheme),
        Dense (U : Set (T.level (Fin.last T.length)).scheme) ∧ Dense (W : Set V.scheme) ∧
        U.ι ≫ (p (Fin.last T.length)).base = e.hom ≫ W.ι) ∧
      IsIntegral (T.level (Fin.last T.length)).scheme ∧
      IsRegularScheme (T.level (Fin.last T.length)).scheme ∧
      (p (Fin.last T.length)).IsLogEtale ∧
      ∀ (D : FineSaturatedLogScheme.{u}) (g : EtaleLogHom V D), g.IsLogSmooth →
        ((p (Fin.last T.length)).comp g).IsLogSmooth := by
  have _hExcellent := hA
  have : CompactSpace V.scheme := QuasiCompact.compactSpace_of_compactSpace f
  have ht : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ V.scheme),
      ∀ g : Algebra.GrothendieckGroup (V.logStructure.characteristic t),
        ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1 := by
    intro Ω _ _ t
    obtain ⟨hfs, hsharp, _⟩ := exists_sharp_chart_of_logRegular V hV t
    exact sharp_fs_torsionFree hfs hsharp
  obtain ⟨_, T, _, hzero, hfree⟩ := exists_monoidal_resolution_tower ht
  have hzero' : T.level 0 = V := hzero
  clear hzero
  subst V
  obtain ⟨p, hpidentity, hp, hpetale⟩ :=
    fsLogSmooth_composition_strictBaseChange.{u, u}.2.2.2.2.2.2.2 T
  have hp0 : p 0 = EtaleLogHom.id (T.level 0) := identity_eq (p 0) hpidentity
  have hlogsmooth : (p (Fin.last T.length)).IsLogSmooth :=
    fsLogSmooth_composition_strictBaseChange.{u, u}.2.1 _ _ _ hpetale
  have hlog := (p (Fin.last T.length)).isLogRegular_of_isLogSmooth hlogsmooth hV
  have hregular : IsRegularScheme (T.level (Fin.last T.length)).scheme := by
    refine (((T.level (Fin.last T.length)).free_characteristic_regular_boundary hlog).2
      ?_).1
    intro Ω _ _ t
    obtain ⟨r, ⟨e⟩⟩ := hfree Ω t
    exact ⟨r, ⟨e.trans (MulEquiv.ulift.trans
      (AddEquiv.toMultiplicative Finsupp.addEquivFunOnFinite))⟩⟩
  obtain ⟨U, W, e, hU, hW, he⟩ := saturatedLogTower_denseOpen T p hp0 hp hV hlog
  have hprojective : IsHProjective (p (Fin.last T.length)).base := by
    apply saturatedLogTower_isHProjective T p hp0 hp A
    obtain ⟨n, i, hi, _⟩ := hqp
    exact ⟨n, i, hi⟩
  refine ⟨T, p, rfl, hp0.heq, hp, hprojective, ⟨U, W, e, hU, hW, he⟩,
    integral_of_dense_open_iso hregular U W e hU hW, hregular, hpetale, ?_⟩
  intro D g hg
  exact smooth_comp_of_etale _ g hpetale hg

end AlgebraicGeometry

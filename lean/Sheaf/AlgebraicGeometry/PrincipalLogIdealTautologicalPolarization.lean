/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Sheaf.AlgebraicGeometry.LogInfinitesimalLifting
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.Sites.UnitsTorsor
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # The tautological polarization of a principal log ideal

Source: ILO, Exposé VIII 3.3.8, printed pp. 107--108, expanded generator-torsor
construction; Stacks Tags 00AM, 00AN, 01PS, 01VJ and 0893
(blueprint: lem-trf-principal-log-ideal-tautological-polarization).

Monoids are written multiplicatively: `a * m = b` expresses `m = b - a`.
The auxiliary interfaces record the actual generators and local section formulas;
they introduce no choices of a line bundle or of a log pullback.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Generation of a log ideal on an étale object, tested on geometric stalks.
Source: ILO VIII 3.3.8
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
def logIdealGenerates {X : Scheme.{u}} (M : EtaleLogStructure X)
    (J : M.IdealFamily) (W : X.Etale) (a : M.monoidSheaf.obj.obj (op W)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (w : (Scheme.pointSmallEtale t).fiber.obj W),
    M.idealStalk J t = {b | ∃ m : M.toEtalePrelogStructure.stalk t,
      M.toEtalePrelogStructure.germ t W w a * m = b}

/-- Sections of the log sheaf on a Zariski open, by restriction of its étale sheaf.
Source: ILO VI 1.1, VIII 3.3.8
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
abbrev logOpenSections {X : Scheme.{u}} (M : EtaleLogStructure X) (U : X.Opens) :=
  M.monoidSheaf.obj.obj (op (Scheme.Etale.mk U.ι))

/-- The structural scalar on the original open of X, using its canonical top-section iso.
Source: ILO VIII 3.3.8
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
noncomputable def logOpenAlpha {X : Scheme.{u}} (M : EtaleLogStructure X)
    (U : X.Opens) (a : logOpenSections M U) : Γ(X, U) :=
  U.topIso.hom (M.alpha.app (op (Scheme.Etale.mk U.ι)) a)

/-- Restriction of the original monoid sheaf along an inclusion of Zariski opens.
Source: ILO VI 1.1
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
noncomputable def logOpenRestrict {X : Scheme.{u}} (M : EtaleLogStructure X)
    {U V : X.Opens} (h : V ≤ U) : logOpenSections M U →* logOpenSections M V :=
  (M.monoidSheaf.obj.map
    (MorphismProperty.Over.homMk (X.homOfLE h) (by simp)).op).hom

/-- The geometric-stalk generator locus of a global section of a log ideal.
Source: ILO VIII 3.3.8
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
def logIdealGeneratorLocus {X : Scheme.{u}} (M : EtaleLogStructure X)
    (J : M.IdealFamily) (a : logOpenSections M ⊤) : Set X :=
  {x | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk (⊤ : X.Opens).ι)),
    (Scheme.SpecToEquivOfField Ω X t).1 = x →
    M.idealStalk J t = {b | ∃ m : M.toEtalePrelogStructure.stalk t,
      M.toEtalePrelogStructure.germ t _ w a * m = b}}

/-- A realization of the generator sheaf as the existing étale Gm-torsor notion.
The embedding identifies its sections exactly, and the action is multiplication by
that unique log unit whose structural scalar is the given ring unit.
Source: ILO VIII 3.3.8
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
structure LogIdealEtaleGeneratorTorsor {X : Scheme.{u}} (M : EtaleLogStructure X)
    (J : M.IdealFamily) where
  torsor : Sheaf.Torsor X.gmSheaf
  embed : ∀ W : X.Etale, torsor.sheaf.obj.obj (op W) → M.monoidSheaf.obj.obj (op W)
  injective : ∀ W : X.Etale, Function.Injective (embed W)
  range : ∀ (W : X.Etale) (s : M.monoidSheaf.obj.obj (op W)),
    (∃ t, embed W t = s) ↔ s ∈ J W ∧ logIdealGenerates M J W s
  naturality : ∀ (V W : X.Etale) (f : V ⟶ W) (t : torsor.sheaf.obj.obj (op W)),
    embed V (torsor.sheaf.obj.map f.op t) = M.monoidSheaf.obj.map f.op (embed W t)
  action : ∀ (W : X.Etale) (g : X.gmSheaf.obj.obj (op W))
    (t : torsor.sheaf.obj.obj (op W)),
    ∃! m : M.monoidSheaf.obj.obj (op W), IsUnit m ∧
      M.alpha.app (op W) m = (Additive.toMul g.down : Γ(W.left, ⊤)ˣ).val ∧
      embed W (torsor.vadd (op W) g t) = embed W t * m

/-- The same generator sheaf on the Zariski site, as an O-units torsor.
Source: ILO VIII 3.3.8
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
structure LogIdealZariskiGeneratorTorsor {X : Scheme.{u}} (M : EtaleLogStructure X)
    (J : M.IdealFamily) where
  torsor : Sheaf.Torsor X.unitsSheaf
  embed : ∀ U : X.Opens, torsor.sheaf.obj.obj (op U) → logOpenSections M U
  injective : ∀ U : X.Opens, Function.Injective (embed U)
  range : ∀ (U : X.Opens) (s : logOpenSections M U),
    (∃ t, embed U t = s) ↔ s ∈ J (Scheme.Etale.mk U.ι) ∧
      logIdealGenerates M J (Scheme.Etale.mk U.ι) s
  naturality : ∀ (U V : X.Opens) (h : V ≤ U) (t : torsor.sheaf.obj.obj (op U)),
    embed V (torsor.sheaf.obj.map (homOfLE h).op t) = logOpenRestrict M h (embed U t)
  action : ∀ (U : X.Opens) (g : X.unitsSheaf.obj.obj (op U))
    (t : torsor.sheaf.obj.obj (op U)),
    ∃! m : logOpenSections M U, IsUnit m ∧
      logOpenAlpha M U m = (Scheme.unitsSheaf.toUnits g).val ∧
      embed U (torsor.vadd (op U) g t) = embed U t * m

/-- The canonical associated line bundle, characterized by all local ideal sections.
In a generator frame a, the value of a*m is alpha(m) times that frame. Encoding local
sections makes the characterization independent of a finite generating family.
Source: ILO VIII 3.3.8, expanded construction; Stacks Tags 00AM and 00AN
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
structure LogIdealPolarization {X : Scheme.{u}} (M : EtaleLogStructure X)
    (J : M.IdealFamily) where
  line : X.Modules
  invertible : line.IsInvertible
  value : ∀ U : X.Opens, {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)} → Γ(line, U)
  naturality : ∀ (U V : X.Opens) (h : V ≤ U)
    (s : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)})
    (hs : logOpenRestrict M h s.val ∈ J (Scheme.Etale.mk V.ι)),
    line.presheaf.map (homOfLE h).op (value U s) =
      value V ⟨logOpenRestrict M h s.val, hs⟩
  frame : ∀ (U : X.Opens) (s : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)}),
    logIdealGenerates M J (Scheme.Etale.mk U.ι) s.val → IsFreeGenerator (value U s)
  formula : ∀ (U : X.Opens)
    (a b : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)})
    (m : logOpenSections M U), logIdealGenerates M J (Scheme.Etale.mk U.ι) a.val →
    a.val * m = b.val → value U b = logOpenAlpha M U m • value U a
  nonvanishing : ∀ h : {s : logOpenSections M ⊤ // s ∈ J (Scheme.Etale.mk (⊤ : X.Opens).ι)},
    nonvanishingLocus line (value ⊤ h) = logIdealGeneratorLocus M J h.val

attribute [instance] LogIdealPolarization.invertible

/-- Pullback of a log section on an open using the actual relative étale test square.
Source: ILO VI 1.1, VIII 3.3.8
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
noncomputable def logIdealPullSection {Y X : Scheme.{u}} {N : EtaleLogStructure Y}
    {M : EtaleLogStructure X} (q : EtaleLogMap N M) (U : X.Opens) :
    logOpenSections M U →* logOpenSections N (q.base ⁻¹ᵁ U) :=
  q.sectionMap (Scheme.Etale.mk U.ι) (Scheme.Etale.mk (q.base ⁻¹ᵁ U).ι)
    (q.base ∣_ U) (morphismRestrict_ι q.base U)

/-- The normalization of a comparison: it preserves every local ideal section,
using the section-normalized tensor pullback. Membership is quantified explicitly,
so there is no hidden choice of a proof or of a section outside the ideal.
Source: ILO VIII 3.3.8, expanded frame comparison; Stacks Tag 00AN
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
def LogIdealPolarization.Respects {Y X : Scheme.{u}} {N : EtaleLogStructure Y}
    {M : EtaleLogStructure X} {I : N.IdealFamily} {J : M.IdealFamily}
    (P : LogIdealPolarization M J) (Q : LogIdealPolarization N I) (q : EtaleLogMap N M)
    (e : (tensorPullback q.base).obj P.line ≅ Q.line) : Prop :=
  ∀ (U : X.Opens) (s : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)}),
    ∃ hs : logIdealPullSection q U s.val ∈ I (Scheme.Etale.mk (q.base ⁻¹ᵁ U).ι),
      e.hom.app (q.base ⁻¹ᵁ U) (tensorPullbackSection q.base P.line U (P.value U s)) =
        Q.value (q.base ⁻¹ᵁ U) ⟨logIdealPullSection q U s.val, hs⟩

/-- Relative ampleness over every affine open, using precisely the existing absolute
ampleness predicate and tensor restriction, with its invertibility witness.
Source: Stacks Tags 01VH and 01VJ
(blueprint: lem-trf-principal-log-ideal-tautological-polarization). -/
def LogIdealPolarization.RelativelyAmple {X S : Scheme.{u}} {M : EtaleLogStructure X}
    {J : M.IdealFamily} (P : LogIdealPolarization M J) (p : X ⟶ S) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∃ hi : ((tensorPullback (p ⁻¹ᵁ U).ι).obj P.line).IsInvertible,
      @IsAmple (p ⁻¹ᵁ U).toScheme ((tensorPullback (p ⁻¹ᵁ U).ι).obj P.line) hi

/-- The generator torsors and their tautological polarized line bundle, including
strict affine base change. Frames are values of the prescribed h_e, and the local
formula of `LogIdealPolarization.formula` is v_f=alpha(h_f-h_e)v_e. Its `value` gives
s_h for every global ideal section; `nonvanishing` gives exactly the generator locus.

Source: ILO VIII 3.3.8, printed pp. 107--108, expanded construction; Stacks Tags
00AM, 00AN, 01PS, 01VJ and 0893
(blueprint: lem-trf-principal-log-ideal-tautological-polarization).

Proof:
1. Fine charts are integral: localize P at the elements mapping to ring units and
form the pushout (P_F times B^units)/F^gp. Equality is a unit translation, so cancel
in P^gp and B^units. Use def-trf-fs-log-blowup and def-trf-fine-log-etale-descent-datum.
2. If a and b generate the same ideal, b=a*c and a=b*d give c*d=1 by cancellation.
The unique c is a unit. Local differences glue uniquely. The log unit axiom
identifies them with O^units, giving both torsors of def-sc-gm-torsor.
3. Differences u_ef satisfy u_eg=u_ef*u_fg. Apply
lem-sc-glue-component-transition-cocycle to their structural units with inverse
coordinate maps. This glues the line bundle with frames v_f=alpha(u_ef)v_e.
4. For any ideal section h, its differences m_he satisfy m_he=m_hf*u_ef.
Thus alpha(m_he)v_e glues to its value. The log unit axiom identifies nonvanishing
with generation on geometric stalks (def-weil-pbc-ample-invertible-module).
5. The finite affine generator cover makes X quasi-compact. Its opens are
nonvanishing loci of sections of the line itself, so the line is ample.
6. Each V_e to Spec A is affine, so p is quasi-compact. Apply
lem-trf-scheme-relative-ample-affine-cover to the one-member affine cover of Spec A.
7. Tensor pullback preserves frames, sections and residue values by
lem-weil-pbc-invertible-pullback-tensor. Nonvanishing pulls back because residue
field extensions preserve nonzero elements. Apply lem-trf-scheme-relative-ample-base-change.
8. Associate the inverse-image prelog sheaf. Its pulled charts are the same P
with the pulled structural map. The cancellation of step 1 still applies; the
pulled generators and differences have the pulled structural scalars. This gives
exactly the pulled generator loci and the normalized comparison of line bundles.
9. On common generator charts compare frames by alpha(k_i-h_e). Differences add,
so these maps glue uniquely by lem-weil-pbc-glue-sheaves-of-modules. They preserve
every local ideal section. Their uniqueness proves independence of families and
identity, composition and further-base-change compatibility (def-pc-module-pullback).
-/
theorem principalLogIdeal_tautological_polarization
    {X : Scheme.{u}} (M : EtaleLogStructure X) (hM : M.IsFine)
    (J : M.IdealFamily) (hJ : M.IsInvertibleIdeal J)
    (A : CommRingCat.{u}) (p : X ⟶ Spec A)
    (E : Type v) [Finite E] [Nonempty E]
    (h : E → logOpenSections M ⊤)
    (hmem : ∀ e : E, h e ∈ J (Scheme.Etale.mk (⊤ : X.Opens).ι))
    (hgen : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
      (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk (⊤ : X.Opens).ι)),
      M.idealStalk J t = {b | ∃ e : E, ∃ m : M.toEtalePrelogStructure.stalk t,
        M.toEtalePrelogStructure.germ t _ w (h e) * m = b})
    (V : E → X.Opens) (hV : ∀ e : E, (V e : Set X) = logIdealGeneratorLocus M J (h e))
    (haff : ∀ e : E, IsAffineOpen (V e)) (hcover : iSup V = ⊤) :
    Nonempty (LogIdealEtaleGeneratorTorsor M J) ∧
    Nonempty (LogIdealZariskiGeneratorTorsor M J) ∧
    (∀ (U : X.Opens)
      (a b : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)}),
      logIdealGenerates M J (Scheme.Etale.mk U.ι) a.val →
        ∃! m : logOpenSections M U, a.val * m = b.val) ∧
    ∃ P : LogIdealPolarization M J,
      IsAmple X P.line ∧ P.RelativelyAmple p ∧
      (∀ e : E, nonvanishingLocus P.line (P.value ⊤ ⟨h e, hmem e⟩) = (V e : Set X)) ∧
      (∀ Q : LogIdealPolarization M J,
        ∃! e : P.line ≅ Q.line,
          ∀ (U : X.Opens) (s : {s : logOpenSections M U //
              s ∈ J (Scheme.Etale.mk U.ι)}), e.hom.app U (P.value U s) = Q.value U s) ∧
      (∀ (A' : CommRingCat.{u}) (g : Spec A' ⟶ Spec A),
        ∃ (N : EtaleLogStructure (pullback p g)) (q : EtaleLogMap N M),
          q.base = pullback.fst p g ∧ q.IsStrict ∧ N.IsFine ∧
          N.IsInvertibleIdeal (q.pullbackIdeal J) ∧
          (∃ hi : ((tensorPullback q.base).obj P.line).IsInvertible,
            @IsAmple (pullback p g) ((tensorPullback q.base).obj P.line) hi) ∧
          (∀ s : {s : logOpenSections M ⊤ //
              s ∈ J (Scheme.Etale.mk (⊤ : X.Opens).ι)},
            logIdealGeneratorLocus N (q.pullbackIdeal J) (logIdealPullSection q ⊤ s.val) =
              q.base ⁻¹' logIdealGeneratorLocus M J s.val) ∧
          ∃ Q : LogIdealPolarization N (q.pullbackIdeal J),
            IsAmple (pullback p g) Q.line ∧ Q.RelativelyAmple (pullback.snd p g) ∧
            (∀ s : {s : logOpenSections M ⊤ //
                s ∈ J (Scheme.Etale.mk (⊤ : X.Opens).ι)},
              nonvanishingLocus ((tensorPullback q.base).obj P.line)
                  (tensorPullbackSection q.base P.line ⊤ (P.value ⊤ s)) =
                q.base ⁻¹' logIdealGeneratorLocus M J s.val) ∧
            ∃! e : (tensorPullback q.base).obj P.line ≅ Q.line, P.Respects Q q e) := by
  sorry

/-- Log isomorphisms preserving an ideal give unique normalized identifications of
both generator torsors and the associated line bundle. The normalizations involve
all local sections, so they do not refer to any generating family.

Source: ILO VIII 3.3.8, expanded canonical frame comparison; Stacks Tag 00AN
(blueprint: lem-trf-principal-log-ideal-tautological-polarization).

Proof (node step 9): transport log generators through the log isomorphism. It
preserves their principal ideals, structural scalars and unit translations.
The injective embeddings identifying the torsors with generators give unique
maps on sections; their naturality and compatibility with units follow from those
of the log map. Over a scheme isomorphism these maps are bijective. On common
local generator charts, send the pulled frame to the frame of its image generator.
The scalar is alpha(k_i-h_e), and equality of differences on triple overlaps makes
these local maps agree. Apply lem-weil-pbc-glue-sheaves-of-modules to glue the maps
and their inverses. The equation h-h_e=(h-k_i)+(k_i-h_e) preserves every value.
Generation of the line module on the cover forces uniqueness.
-/
theorem principalLogIdeal_polarization_logIso
    {X Y : Scheme.{u}} {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    {J : M.IdealFamily} (q : EtaleLogMap N M) [IsIso q.base]
    (hq : q.IsStrict) (hM : M.IsFine) (hJ : M.IsInvertibleIdeal J)
    (P : LogIdealPolarization M J)
    (Q : LogIdealPolarization N (q.pullbackIdeal J))
    (T : LogIdealEtaleGeneratorTorsor M J)
    (T' : LogIdealEtaleGeneratorTorsor N (q.pullbackIdeal J))
    (Z : LogIdealZariskiGeneratorTorsor M J)
    (Z' : LogIdealZariskiGeneratorTorsor N (q.pullbackIdeal J)) :
    (∃! e : (tensorPullback q.base).obj P.line ≅ Q.line, P.Respects Q q e) ∧
    (∃! t : ∀ (W : X.Etale) (V : Y.Etale) (k : V.left ⟶ W.left)
        (hk : k ≫ W.hom = V.hom ≫ q.base),
        T.torsor.sheaf.obj.obj (op W) → T'.torsor.sheaf.obj.obj (op V),
      (∀ (W : X.Etale) (V : Y.Etale) (k : V.left ⟶ W.left)
        (hk : k ≫ W.hom = V.hom ≫ q.base) (s : T.torsor.sheaf.obj.obj (op W)),
        T'.embed V (t W V k hk s) = q.sectionMap W V k hk (T.embed W s)) ∧
      ∀ (W : X.Etale) (V : Y.Etale) (k : V.left ⟶ W.left) [IsIso k]
        (hk : k ≫ W.hom = V.hom ≫ q.base), Function.Bijective (t W V k hk)) ∧
    (∃! t : ∀ U : X.Opens,
        Z.torsor.sheaf.obj.obj (op U) → Z'.torsor.sheaf.obj.obj (op (q.base ⁻¹ᵁ U)),
      (∀ (U : X.Opens) (s : Z.torsor.sheaf.obj.obj (op U)),
        Z'.embed (q.base ⁻¹ᵁ U) (t U s) = logIdealPullSection q U (Z.embed U s)) ∧
      ∀ U : X.Opens, Function.Bijective (t U)) := by
  sorry

/-- Any realization of a strict pulled-back ideal is canonically the tensor pullback
of the original polarization. This quantification includes any choices made in
successive affine base changes; the comparison is fixed on all local ideal sections.

Source: ILO VIII 3.3.8, expanded frame comparison; Stacks Tags 00AM and 00AN
(blueprint: lem-trf-principal-log-ideal-tautological-polarization).

Proof (node steps 7--9): choose local generators of J. Their strict pullbacks
generate the image ideal and the associated log structure is integral by the chart
cancellation in step 1. The frames of Q associated to these image generators have
exactly the pulled structural transitions. Send pulled frames to these frames.
The overlap equations agree by compatibility of the log map with structural scalars.
Glue the local maps and their inverses using lem-weil-pbc-glue-sheaves-of-modules.
The local scalar formula proves Respects on every ideal section. Since the frames
generate, the same gluing uniqueness gives a unique such comparison.
-/
theorem principalLogIdeal_polarization_strict_comparison
    {X Y : Scheme.{u}} {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    {J : M.IdealFamily} (hM : M.IsFine) (hJ : M.IsInvertibleIdeal J)
    (q : EtaleLogMap N M) (hq : q.IsStrict)
    (P : LogIdealPolarization M J) (Q : LogIdealPolarization N (q.pullbackIdeal J)) :
    ∃! e : (tensorPullback q.base).obj P.line ≅ Q.line, P.Respects Q q e := by
  sorry

private theorem polarization_hom_ext
    {X : Scheme.{u}} {M : EtaleLogStructure X} {J : M.IdealFamily}
    (P : LogIdealPolarization M J)
    (hcover : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (s : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)}),
      logIdealGenerates M J (Scheme.Etale.mk U.ι) s.val)
    {L : X.Modules} (a b : P.line ⟶ L)
    (h : ∀ (U : X.Opens)
      (s : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)}),
      logIdealGenerates M J (Scheme.Etale.mk U.ι) s.val →
      a.app U (P.value U s) = b.app U (P.value U s)) : a = b := by
  classical
  choose U hx s hs using hcover
  apply hom_ext
  intro W
  ext t
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨L.presheaf, L.isSheaf⟩
  apply F.eq_of_locally_eq' (fun x ↦ W ⊓ U x) W (fun x ↦ homOfLE inf_le_left)
  · intro x hxW
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW, hx x⟩
  · intro x
    change L.presheaf.map (homOfLE inf_le_left).op (a.app W t) =
      L.presheaf.map (homOfLE inf_le_left).op (b.app W t)
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
    obtain ⟨r, hr⟩ := (P.frame (U x) (s x) (hs x) (W ⊓ U x) inf_le_right).surjective
      (P.line.presheaf.map (homOfLE inf_le_left).op t)
    rw [← hr, Hom.app_smul, Hom.app_smul, Hom.app_presheaf_map,
      Hom.app_presheaf_map, h (U x) (s x) (hs x)]

private theorem logIdealPullSection_id {X : Scheme.{u}} (M : EtaleLogStructure X)
    (U : X.Opens) (s : logOpenSections M U) :
    logIdealPullSection (EtaleLogMap.id M) U s = s := by
  change M.monoidSheaf.obj.map
    (MorphismProperty.Over.homMk ((𝟙 X) ∣_ U) _).op s = s
  have hm : (MorphismProperty.Over.homMk ((𝟙 X) ∣_ U)
      (by exact (morphismRestrict_ι (𝟙 X) U).trans (Category.comp_id _)) :
      Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk U.ι) = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    exact morphismRestrict_id U
  rw [hm, op_id]
  exact congrArg (fun z ↦ z s) (M.monoidSheaf.obj.map_id (op (Scheme.Etale.mk U.ι)))

private theorem tensor_unit_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : Y.Modules) (U : Y.Opens) (s : Γ(L, U)) :
    ((tensorPullbackSectionAdjunction g).unit.app L).app U s =
      tensorPullbackSection g L U s :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction g)).1 L U s

private theorem tensor_homEquiv_apply {X Y : Scheme.{u}} (g : X ⟶ Y)
    {L : Y.Modules} {N : X.Modules} (a : (tensorPullback g).obj L ⟶ N)
    (U : Y.Opens) (s : Γ(L, U)) :
    (((tensorPullbackSectionAdjunction g).homEquiv L N) a).app U s =
      a.app (g ⁻¹ᵁ U) (tensorPullbackSection g L U s) := by
  change a.app (g ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction g).unit.app L).app U s) = _
  rw [tensor_unit_section]

private theorem tensor_section_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {L N : Y.Modules} (a : L ⟶ N) (U : Y.Opens) (s : Γ(L, U)) :
    ((tensorPullback g).map a).app (g ⁻¹ᵁ U) (tensorPullbackSection g L U s) =
      tensorPullbackSection g N U (a.app U s) := by
  have h := congrArg (fun z ↦ z.app U s)
    ((tensorPullbackSectionAdjunction g).unit.naturality a)
  simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, pushforward_map_app,
    ConcreteCategory.comp_apply] at h
  simp only [tensor_unit_section] at h
  exact h.symm

private theorem tensor_section_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (L : Z.Modules) (U : Z.Opens) (s : Γ(L, U)) :
    ((tensorPullbackSectionComp g h).hom.app L).app ((g ≫ h) ⁻¹ᵁ U)
        (tensorPullbackSection (g ≫ h) L U s) =
      tensorPullbackSection g ((tensorPullback h).obj L) (h ⁻¹ᵁ U)
        (tensorPullbackSection h L U s) := by
  have hc := (tensorPullbackSectionAdjunction (g ≫ h)).unit_leftAdjointUniq_hom_app
    (((tensorPullbackSectionAdjunction h).comp (tensorPullbackSectionAdjunction g)).ofNatIsoRight
      (pushforwardComp g h)) L
  have hs := congrArg (fun z ↦ z.app U s) hc
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    Adjunction.comp_unit_app] at hs
  change ((tensorPullbackSectionComp g h).hom.app L).app ((g ≫ h) ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction (g ≫ h)).unit.app L).app U s) =
    ((tensorPullbackSectionAdjunction g).unit.app ((tensorPullback h).obj L)).app (h ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction h).unit.app L).app U s) at hs
  simpa only [tensor_unit_section] using hs

/-- Normalized comparisons obey composition, in particular successive affine base
change and compositions of log isomorphisms. The equality of composite log maps
is the existing relative-test-object predicate, and the tensor comparison is the
existing section-normalized one. This is also the compatibility of a log-isomorphism
identification with further base change, applied to the two paths of that square.

Source: ILO VIII 3.3.8, expanded frame comparison; Stacks Tag 00AN
(blueprint: lem-trf-principal-log-ideal-tautological-polarization).

Proof (node step 9): under def-pc-module-pullback, successive pullback sends a
local section to its twice-pulled section. The two log section maps agree by
CompEq. Thus the displayed composite and the direct comparison send every local
ideal section to the same value. Locally these include free generator frames.
Consequently the two maps agree by the uniqueness clause of
lem-weil-pbc-glue-sheaves-of-modules. This works also for a commuting square:
apply the assertion to both paths and use the same direct normalized comparison.
-/
theorem principalLogIdeal_polarization_composition
    {X Y Z : Scheme.{u}} {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    {K : EtaleLogStructure Z} {I : K.IdealFamily} {J : N.IdealFamily}
    {H : M.IdealFamily} (P : LogIdealPolarization M H)
    (Q : LogIdealPolarization N J) (R : LogIdealPolarization K I)
    (f : EtaleLogMap K N) (g : EtaleLogMap N M) (r : EtaleLogMap K M)
    (hcomp : f.CompEq g r)
    (a : (tensorPullback f.base).obj Q.line ≅ R.line)
    (b : (tensorPullback g.base).obj P.line ≅ Q.line)
    (c : (tensorPullback r.base).obj P.line ≅ R.line)
    (ha : Q.Respects R f a) (hb : P.Respects Q g b) (hc : P.Respects R r c)
    (hcover : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (s : {s : logOpenSections M U // s ∈ H (Scheme.Etale.mk U.ι)}),
      logIdealGenerates M H (Scheme.Etale.mk U.ι) s.val) :
    c = eqToIso (congrArg (fun k : Z ⟶ X ↦ (tensorPullback k).obj P.line) hcomp.1.symm) ≪≫
      (tensorPullbackSectionComp f.base g.base).app P.line ≪≫
      (tensorPullback f.base).mapIso b ≪≫ a := by
  rcases r with ⟨rb, rs, rn, rc⟩
  rcases hcomp with ⟨hbase, hsections⟩
  dsimp only at hbase
  subst rb
  simp only [eqToIso_refl, Iso.refl_trans]
  apply Iso.ext
  apply ((tensorPullbackSectionAdjunction (f.base ≫ g.base)).homEquiv _ _).injective
  apply polarization_hom_ext P hcover
  intro U s _
  rw [tensor_homEquiv_apply, tensor_homEquiv_apply]
  obtain ⟨hbs, hbeq⟩ := hb U s
  obtain ⟨has, haeq⟩ := ha (g.base ⁻¹ᵁ U) ⟨logIdealPullSection g U s.val, hbs⟩
  obtain ⟨hcs, hceq⟩ := hc U s
  have hlogs :
      logIdealPullSection f (g.base ⁻¹ᵁ U) (logIdealPullSection g U s.val) =
        logIdealPullSection ⟨f.base ≫ g.base, rs, rn, rc⟩ U s.val := by
    exact congrArg (fun z ↦ z s.val)
      (hsections (Scheme.Etale.mk U.ι) (Scheme.Etale.mk (g.base ⁻¹ᵁ U).ι)
        (Scheme.Etale.mk ((f.base ≫ g.base) ⁻¹ᵁ U).ι)
        (g.base ∣_ U) (f.base ∣_ (g.base ⁻¹ᵁ U)) ((f.base ≫ g.base) ∣_ U)
        (morphismRestrict_ι g.base U) (morphismRestrict_ι f.base (g.base ⁻¹ᵁ U))
        (morphismRestrict_ι (f.base ≫ g.base) U)
        (morphismRestrict_comp f.base g.base U).symm)
  change c.hom.app ((f.base ≫ g.base) ⁻¹ᵁ U)
      (tensorPullbackSection (f.base ≫ g.base) P.line U (P.value U s)) =
    a.hom.app (f.base ⁻¹ᵁ (g.base ⁻¹ᵁ U))
      (((tensorPullback f.base).map b.hom).app (f.base ⁻¹ᵁ (g.base ⁻¹ᵁ U))
        (((tensorPullbackSectionComp f.base g.base).hom.app P.line).app
          ((f.base ≫ g.base) ⁻¹ᵁ U)
          (tensorPullbackSection (f.base ≫ g.base) P.line U (P.value U s))))
  rw [tensor_section_comp, tensor_section_naturality, hbeq, haeq, hceq]
  congr 1
  exact Subtype.ext hlogs.symm

/-- The normalized identity comparison is the identity-pullback comparison already
fixed by the module-pullback dependency.

Source: ILO VIII 3.3.8, expanded frame comparison; Stacks Tag 00AN
(blueprint: lem-trf-principal-log-ideal-tautological-polarization).

Proof (node step 9): the identity log map fixes every ideal section. The normalized
identity tensor comparison does too by def-pc-module-pullback. Both maps therefore
fix every local generator frame, and the uniqueness part of
lem-weil-pbc-glue-sheaves-of-modules identifies them.
-/
theorem principalLogIdeal_polarization_identity
    {X : Scheme.{u}} {M : EtaleLogStructure X} {J : M.IdealFamily}
    (P : LogIdealPolarization M J)
    (e : (tensorPullback (𝟙 X)).obj P.line ≅ P.line)
    (he : P.Respects P (EtaleLogMap.id M) e)
    (hcover : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (s : {s : logOpenSections M U // s ∈ J (Scheme.Etale.mk U.ι)}),
      logIdealGenerates M J (Scheme.Etale.mk U.ι) s.val) :
    e = (tensorPullbackSectionId X).app P.line := by
  apply Iso.ext
  apply ((tensorPullbackSectionAdjunction (𝟙 X)).homEquiv _ _).injective
  apply polarization_hom_ext P hcover
  intro U s _
  have hi := ((tensorPullbackSectionAdjunction (𝟙 X)).ofNatIsoRight
    (pushforwardId X)).unit_leftAdjointUniq_hom_app Adjunction.id P.line
  have hit := congrArg (fun z ↦ z.app U (P.value U s)) hi
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Hom.comp_app, pushforwardId_hom_app_app,
    Adjunction.id_unit, NatTrans.id_app, Hom.id_app] at hit
  change ((tensorPullbackSectionId X).app P.line).hom.app U
    (((tensorPullbackSectionAdjunction (𝟙 X)).unit.app P.line).app U (P.value U s)) =
      P.value U s at hit
  obtain ⟨hmem, heq⟩ := he U s
  have hsid : (⟨logIdealPullSection (EtaleLogMap.id M) U s.val, hmem⟩ :
      {t : logOpenSections M U // t ∈ J (Scheme.Etale.mk U.ι)}) = s := by
    apply Subtype.ext
    exact logIdealPullSection_id M U s.val
  change e.hom.app U (tensorPullbackSection (𝟙 X) P.line U (P.value U s)) =
    P.value U ⟨logIdealPullSection (EtaleLogMap.id M) U s.val, hmem⟩ at heq
  rw [hsid] at heq
  rw [tensor_homEquiv_apply, tensor_homEquiv_apply]
  rw [tensor_unit_section] at hit
  exact heq.trans hit.symm

end AlgebraicGeometry

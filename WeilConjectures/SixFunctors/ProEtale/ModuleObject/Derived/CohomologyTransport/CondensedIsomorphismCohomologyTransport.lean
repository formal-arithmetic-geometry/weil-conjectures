/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.Compactification.Refinement

/-! # Semilinear transport of ordinary condensed cohomology

Source: the first isomorphisms in the ordinary and compact-support composites of
`def-weil-global-geometric-frobenius` in blueprint latest.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport)

All categories below are ordinary unbounded derived categories of internal module
objects. Scalar sections mean actual terminal sections with restriction to Λ(*).
Compactification comparisons are specified by their proper-refinement normalization;
fixed-compactification exchange is specified by its open-adjunction mate. These
normalizations determine the maps, rather than merely asking for some isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Avoid the imported max-universe site-size instance leaving a universe metavariable.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ambient category from the recorded ordinary-derived convention.
Source: blueprint, derived categories of condensed modules.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev D (T : Scheme.{u}) := DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))

/-- Inclusion of complexes with bounded constructible cohomology, without completeness.
Source: blueprint, bounded constructible modules.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev bc (T : Scheme.{u}) := (boundedConstructible (condensedRingObj Λ T)).ι

/-- Published derived tensor inverse image, retaining its canonical coefficient map.
Source: blueprint, module-derived push/pull.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev L {T U : Scheme.{u}} (f : T ⟶ U) := moduleObjectDerivedPullback Λ f

/-- Published total right derived direct image.
Source: blueprint, module-derived push/pull.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev R {T U : Scheme.{u}} (f : T ⟶ U) := moduleObjectDerivedPushforward Λ f

/-- Exact extension by zero applied termwise on the ordinary derived categories.
Source: blueprint, module-derived lower shriek.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev J {T U : Scheme.{u}} (j : T ⟶ U) [IsOpenImmersion j] :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The recorded compactification construction, not the derived composite of j! and g*.
Source: blueprint, module-derived lower shriek.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev C {T U : Scheme.{u}} {a : T ⟶ U} (c : Compactification a) :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- The actual scalar map Λ(*) → Γ(T,Λ_T), induced by the strong monoidal p_T^*.
Source: blueprint, pullback from the point and scalar sections.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def scalarMap (T : Scheme.{u}) : condensedScalarRing Λ →+*
    Evaluation.A.{u} (Scheme.ProEt.topology T) (condensedRingObj Λ T) (ProEt.mk (𝟙 T)) := by
  letI : PreservesFiniteLimits (upperStarFromPoint T) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  letI := Functor.additive_of_preserves_binary_products (upperStarFromPoint T)
  exact (InternalAbelianSheafModule.sectionGlobalEval.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (condensedRingObj Λ T) (ProEt.mk (𝟙 T))).comp
    ((MonObj.Γ.mapFunctor (upperStarFromPoint T)).comp
      (InternalAbelianSheafModule.sectionGlobalEquiv.{u + 1, u + 1, u}
        (coherentTopology Profinite.{u})
        Λ (⊤_ Profinite.{u}) terminalIsTerminal).symm.toRingHom)

/-- Terminal module sections, followed by the specified restriction of scalars.
Source: blueprint, definition of Γ_s in this lemma.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def sections (T : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
      ModuleCat.{u + 1} (condensedScalarRing Λ) :=
  Evaluation.sections.{u} (Scheme.ProEt.topology T) (condensedRingObj Λ T) (ProEt.mk (𝟙 T)) ⋙
    ModuleCat.restrictScalars (scalarMap Λ T)

/-- Derived scalar sections; on an algebraically closed point these are canonically
termwise sections, as asserted by the exactness clause of the theorem below.
Source: blueprint, exact point sections.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev Γ (T : Scheme.{u}) := (sections Λ T).rightDerivedFunctor

/-- The unit/compositor/counit pullback comparison of a commutative square.
Source: the displayed adjoint defining e_* in the node.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def square {T' T U' U : Scheme.{u}} (h : T' ⟶ T) (a' : T' ⟶ U')
    (a : T ⟶ U) (b : U' ⟶ U) (w : h ≫ a = a' ≫ b) :
    L Λ b ⋙ L Λ a' ≅ L Λ a ⋙ L Λ h :=
  (leftDerivedUpperStarComp Λ a' b).symm ≪≫
    eqToIso (congrArg (fun f : T' ⟶ U ↦ L Λ f) w.symm) ≪≫
    leftDerivedUpperStarComp Λ h a

/-- Canonical direct-image exchange, with no arbitrary base-change hypothesis.
Source: the displayed adjoint in the node.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def ordinary {T' T U' U : Scheme.{u}} (h : T' ⟶ T) (a' : T' ⟶ U')
    (a : T ⟶ U) (b : U' ⟶ U) (w : h ≫ a = a' ≫ b) :
    R Λ a ⋙ L Λ b ⟶ L Λ h ⋙ R Λ a' :=
  Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ a)
    (derivedUpperStarLowerStarAdjunction Λ a') (square Λ h a' a b w)

/-- Canonical derived pushforward compositor, the conjugate of the pullback compositor.
Source: the same unit/counit convention used for ordinary exchange.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def pushComp {T U V : Scheme.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    R Λ f ⋙ R Λ g ≅ R Λ (f ≫ g) :=
  (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    ((derivedUpperStarLowerStarAdjunction Λ g).comp
      (derivedUpperStarLowerStarAdjunction Λ f))
    (leftDerivedUpperStarComp Λ f g).symm).symm

/-- Derived j! ⊣ Lj* from the exact underived open-immersion adjunction.
Source: blueprint, open extension by zero.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def openAdj {T U : Scheme.{u}} (j : T ⟶ U) [IsOpenImmersion j] :
    J Λ j ⊣ L Λ j :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryAdjunction.ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

/-- Open reindexing is the mate of the inverse pullback comparison. Its direction is
j'_! Lh* → Lv* j!; the compact exchange below uses its inverse.
Source: blueprint, reindexing of extension by zero.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def openExchange {T' T Z' Z : Scheme.{u}} (h : T' ⟶ T) (j' : T' ⟶ Z')
    (j : T ⟶ Z) (v : Z' ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : h ≫ j = j' ≫ v) : L Λ h ⋙ J Λ j' ⟶ J Λ j ⋙ L Λ v :=
  Adjunction.exchangeLeft (openAdj Λ j) (openAdj Λ j') (square Λ h j' j v w).symm

/-- Restriction along b at the final object, transported by the canonical point
coefficient equivalence. The equivalence p_s^* is fully faithful; its composition
comparison therefore determines the same map as N(s,1) → N(s,b) under the normalized
corresponding-object inverse-image description. This construction is Λ(*)-linear.
Source: blueprint, the specified iota_b and pullback-from-point comparison.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def insertion {k : Type u} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of k)) :
    Γ Λ (Spec (.of k)) ≅ L Λ b ⋙ Γ Λ (Spec (.of k)) :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ b ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed Λ b) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm) _

/-- Transport of a compactification along the two scheme isomorphisms; its middle
scheme is unchanged, j'=h;j and g'=g;b^-1. This is an actual construction.
Source: blueprint, compactification reindexing along b.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def reindex {T' T s : Scheme.{u}} {a : T ⟶ s} {a' : T' ⟶ s}
    (b : s ⟶ s) [IsIso b] (h : T' ⟶ T) [IsIso h]
    (w : h ≫ a = a' ≫ b) (c : Compactification a) : Compactification a' :=
  ((c.precomp h).postcomp (inv b)).copy (by
    rw [w]
    simp [Category.assoc])

/-- The canonical unit path along a proper refinement, after pushforward composition.
It is used to specify the compactification comparison without any arbitrary choice.
Source: blueprint, canonical compactification comparison via refinements.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def refinementUnit {T s : Scheme.{u}} {a : T ⟶ s} (c d : Compactification a)
    (r : d.Z ⟶ c.Z) (wg : r ≫ c.g = d.g) (M : D Λ T) :
    (C Λ c).obj M ⟶ (R Λ d.g).obj ((L Λ r).obj ((J Λ c.i).obj M)) :=
  (R Λ c.g).map ((derivedUpperStarLowerStarAdjunction Λ r).unit.app ((J Λ c.i).obj M)) ≫
    (pushComp Λ r c.g).hom.app _ ≫
    (eqToIso (congrArg (fun f : d.Z ⟶ s ↦ R Λ f) wg)).hom.app _

/-- The open mate for a refinement, after removing pullback along id_T.
Source: blueprint, proper-refinement comparison.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def refinementOpen {T s : Scheme.{u}} {a : T ⟶ s} (c d : Compactification a)
    (r : d.Z ⟶ c.Z) (wi : d.i ≫ r = c.i) (M : D Λ T) :
    (J Λ d.i).obj M ⟶ (L Λ r).obj ((J Λ c.i).obj M) :=
  (J Λ d.i).map ((leftDerivedUpperStarId Λ T).inv.app M) ≫
    (openExchange Λ (𝟙 T) d.i c.i r (by simpa using wi.symm)).app M

/-- Data for the canonical compactification comparison and fixed-square exchanges.
The two equations fix them by the proper-refinement unit and the open-adjunction mate.
The isomorphisms are only required on the stated bounded constructible domain for
comparison; the fixed-square exchanges use isomorphisms of sites.
Source: blueprint, the compact-support normalization in this node.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
structure CompactData (s : Scheme.{u}) where
  compare : ∀ {T : Scheme.{u}} (a : T ⟶ s) [QuasiCompact a] (c d : Compactification a),
    bc Λ T ⋙ C Λ c ≅ bc Λ T ⋙ C Λ d
  compare_refl : ∀ {T : Scheme.{u}} (a : T ⟶ s) [QuasiCompact a] (c : Compactification a),
    compare a c c = Iso.refl _
  compare_trans : ∀ {T : Scheme.{u}} (a : T ⟶ s) [QuasiCompact a] (c d e : Compactification a),
    compare a c d ≪≫ compare a d e = compare a c e
  refinement : ∀ {T : Scheme.{u}} (a : T ⟶ s) [QuasiCompact a] (c d : Compactification a)
    (r : d.Z ⟶ c.Z) [IsProper r] (wi : d.i ≫ r = c.i) (wg : r ≫ c.g = d.g)
    (_ : IsPullback (𝟙 T) d.i c.i r)
    (M : (boundedConstructible (condensedRingObj Λ T)).FullSubcategory),
    (compare a c d).hom.app M ≫ (R Λ d.g).map (refinementOpen Λ c d r wi M.obj) =
      refinementUnit Λ c d r wg M.obj
  exchange : ∀ {T' T : Scheme.{u}} (a : T ⟶ s) (a' : T' ⟶ s)
    (b : s ⟶ s) [IsIso b] (h : T' ⟶ T) [IsIso h]
    (c : Compactification a) (d : Compactification a')
    (v : d.Z ⟶ c.Z) [IsIso v] (_wi : h ≫ c.i = d.i ≫ v)
    (_wg : v ≫ c.g = d.g ≫ b),
    C Λ c ⋙ L Λ b ⟶ L Λ h ⋙ C Λ d
  exchange_normalization : ∀ {T' T : Scheme.{u}} (a : T ⟶ s) (a' : T' ⟶ s)
    (b : s ⟶ s) [IsIso b] (h : T' ⟶ T) [IsIso h]
    (c : Compactification a) (d : Compactification a')
    (v : d.Z ⟶ c.Z) [IsIso v] (wi : h ≫ c.i = d.i ≫ v)
    (wg : v ≫ c.g = d.g ≫ b) (M : D Λ T),
    (exchange a a' b h c d v wi wg).app M ≫
        (R Λ d.g).map ((openExchange Λ h d.i c.i v wi).app M) =
      (ordinary Λ v d.g c.g b wg).app ((J Λ c.i).obj M)
  open_iso : ∀ {T' T Z' Z : Scheme.{u}} (h : T' ⟶ T) [IsIso h]
    (j' : T' ⟶ Z') (j : T ⟶ Z) [IsOpenImmersion j'] [IsOpenImmersion j]
    (v : Z' ⟶ Z) [IsIso v] (wi : h ≫ j = j' ≫ v),
    IsIso (openExchange Λ h j' j v wi)

/-- The normalized exchange to any chosen target compactification. First reindex c
along (b,h), then apply the canonical comparison to c'. No new coefficient action is used.
Source: blueprint, the specified construction of e_!.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def compact {s T' T : Scheme.{u}} (S : CompactData Λ s)
    (a : T ⟶ s) (a' : T' ⟶ s) [QuasiCompact a'] (b : s ⟶ s) [IsIso b]
    (h : T' ⟶ T) [IsIso h] (w : h ≫ a = a' ≫ b)
    (c : Compactification a) (c' : Compactification a')
    (M : (boundedConstructible (condensedRingObj Λ T)).FullSubcategory)
    (hM : boundedConstructible (condensedRingObj Λ T') ((L Λ h).obj M.obj)) :
    (L Λ b).obj ((C Λ c).obj M.obj) ⟶ (C Λ c').obj ((L Λ h).obj M.obj) :=
  let d := reindex b h w c
  let v : d.Z ⟶ c.Z := 𝟙 c.Z
  letI : IsIso v := by
    dsimp [v]
    exact IsIso.id c.Z
  (S.exchange a a' b h c d v
      (by simp [v, d, reindex, Compactification.precomp,
        Compactification.postcomp, Compactification.copy])
      (by simp [v, d, reindex, Compactification.precomp,
        Compactification.postcomp, Compactification.copy])).app M.obj ≫
    (S.compare a' (reindex b h w c) c').hom.app ⟨(L Λ h).obj M.obj, hM⟩

/-- Ordinary scalar cohomology transport, exactly Γ(e_*) after insertion along b.
Source: blueprint, the formula for t_*.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def t {k : Type u} [Field k] [IsAlgClosed k] {T' T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) (a' : T' ⟶ Spec (.of k)) [QuasiCompact a']
    (b : Spec (.of k) ⟶ Spec (.of k)) [IsIso b]
    (h : T' ⟶ T) [IsIso h] (w : h ≫ a = a' ≫ b) (M : D Λ T) :=
  (insertion Λ b).hom.app ((R Λ a).obj M) ≫
    (Γ Λ (Spec (.of k))).map ((ordinary Λ h a' a b w).app M)

/-- Compactly supported scalar cohomology transport, exactly Γ(e_!) after insertion.
Source: blueprint, the formula for t_!.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def tc {k : Type u} [Field k] [IsAlgClosed k] {T' T : Scheme.{u}}
    (S : CompactData Λ (Spec (.of k)))
    (a : T ⟶ Spec (.of k)) (a' : T' ⟶ Spec (.of k)) [QuasiCompact a']
    (b : Spec (.of k) ⟶ Spec (.of k)) [IsIso b]
    (h : T' ⟶ T) [IsIso h] (w : h ≫ a = a' ≫ b)
    (c : Compactification a) (c' : Compactification a')
    (M : (boundedConstructible (condensedRingObj Λ T)).FullSubcategory)
    (hM : boundedConstructible (condensedRingObj Λ T') ((L Λ h).obj M.obj)) :=
  (insertion Λ b).hom.app ((C Λ c).obj M.obj) ≫
    (Γ Λ (Spec (.of k))).map (compact Λ S a a' b h w c c' M hM)

/-- A semilinear isomorphism square with precisely the geometric hypotheses of the node.
The isomorphisms are in schemes, not in Over k.
Source: blueprint, the hypotheses of condensed cohomology transport.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
structure Geometry (k : Type u) [Field k] where
  X : Scheme.{u}
  X' : Scheme.{u}
  a : X ⟶ Spec (.of k)
  a' : X' ⟶ Spec (.of k)
  b : Spec (.of k) ≅ Spec (.of k)
  h : X' ≅ X
  comm : h.hom ≫ a = a' ≫ b.hom
  separated : IsSeparated a
  finiteType : LocallyOfFiniteType a
  quasiCompact : QuasiCompact a
  separated' : IsSeparated a'
  finiteType' : LocallyOfFiniteType a'
  quasiCompact' : QuasiCompact a'

attribute [instance] Geometry.separated Geometry.finiteType Geometry.quasiCompact
  Geometry.separated' Geometry.finiteType' Geometry.quasiCompact'

/-- Reverse the two scheme isomorphisms, with their actual inverse square.
Source: blueprint, inverse-pair compatibility.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def Geometry.symm {k : Type u} [Field k] (q : Geometry k) : Geometry k where
  X := q.X'
  X' := q.X
  a := q.a'
  a' := q.a
  b := q.b.symm
  h := q.h.symm
  comm := by
    apply (cancel_epi q.h.hom).1
    simpa [Category.assoc] using
      (congrArg (fun f : q.X' ⟶ Spec (.of k) ↦ f ≫ q.b.inv) q.comm).symm
  separated := q.separated'
  finiteType := q.finiteType'
  quasiCompact := q.quasiCompact'
  separated' := q.separated
  finiteType' := q.finiteType
  quasiCompact' := q.quasiCompact

/-- The identity semilinear square.
Source: blueprint, identity normalization.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def Geometry.id {k : Type u} [Field k] {T : Scheme.{u}} (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] : Geometry k where
  X := T
  X' := T
  a := a
  a' := a
  b := Iso.refl _
  h := Iso.refl _
  comm := by simp
  separated := inferInstance
  finiteType := inferInstance
  quasiCompact := inferInstance
  separated' := inferInstance
  finiteType' := inferInstance
  quasiCompact' := inferInstance

/-- Ordinary transport for the bundled square; this is only an abbreviation of t.
Source: blueprint, t_h (blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
abbrev ordinaryTransport {k : Type u} [Field k] [IsAlgClosed k]
    (q : Geometry k) (M : D Λ q.X) :=
  t Λ q.a q.a' q.b.hom q.h.hom q.comm M

/-- Compact-support transport for the bundled square; this is only an abbreviation of tc.
Source: blueprint, t_c,h (blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
abbrev compactTransport {k : Type u} [Field k] [IsAlgClosed k]
    (S : CompactData Λ (Spec (.of k))) (q : Geometry k)
    (c : Compactification q.a) (c' : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory)
    (hM : boundedConstructible (condensedRingObj Λ q.X') ((L Λ q.h.hom).obj M.obj)) :=
  tc Λ S q.a q.a' q.b.hom q.h.hom q.comm c c' M hM

set_option maxHeartbeats 0 in
-- This type contains many occurrences of the full published derived-functor interfaces.
/-- The two allowed coefficients, using the finite-subextension-valued condensed
algebraic closure rather than all continuous algebraic-closure-valued maps.
Source: blueprint, condensed E and Ω conventions.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def coefficient (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (closure : Bool) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  if closure then Profinite.padicAlgClRingObj ℓ else Profinite.continuousMapRingObj E

/-- For every algebraically closed field, both allowed condensed coefficients admit
all the normalized semilinear cohomology transports. The first two conjuncts say that
Γ_s is exact and that its universal derived unit is invertible on every complex;
thus the functor used here is canonically the termwise evaluation required by the node.
`CompactData` fixes comparison and exchange by their canonical mates, and `Laws`
spells out every naturality, inverse, identity, compactification, and H^i clause.

Source: the first isomorphism of each displayed composite in blueprint latest,
`def-weil-global-geometric-frobenius`.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport)

Proof: inverse image under an isomorphism is an exact coefficient-compatible
site equivalence; pullback of a finite constructible stratification proves preservation
of bounded constructibility. Conjugating the pullback composition comparison through
the two derived adjunctions gives the ordinary exchange, invertible for a square of
isomorphisms. Reindex a compactification by h and b^-1; the open-adjunction mate
identifies extension by zero and the ordinary exchange identifies its proper direct
image. Along proper cartesian refinements the comparison is characterized by the
adjunction unit; common refinements, their cocycle law, and compatibility of the mates
make the resulting exchange independent of the chosen compactification. Evaluation
at Spec k is exact because this final object is weakly contractible; restriction to
Λ(*) is exact. Its restriction along b is Λ(*)-linear since b preserves the unique
component, and agrees with insertion via the point equivalence. Compose insertion
with the exchanges. Naturality follows from the adjunctions and the site restriction
maps. Restriction along b followed by b^-1 is restriction along the identity; the
compositors and the refinement cocycle give the displayed inverse and identity laws.
Finally apply the ordinary homology functor in every integer degree. None of these
steps replaces the condensed algebraic closure by its larger continuous-map sheaf.
-/
theorem condensedCohomologyTransport (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ringChar k ≠ ℓ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (closure : Bool) :
    (sections (coefficient.{u} ℓ E closure) (Spec (.of k))).PreservesHomology ∧
      IsIso (sections (coefficient.{u} ℓ E closure) (Spec (.of k))).rightDerivedFunctorUnit ∧
      ∃ S : CompactData (coefficient.{u} ℓ E closure) (Spec (.of k)),
        Laws (coefficient.{u} ℓ E closure) S := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

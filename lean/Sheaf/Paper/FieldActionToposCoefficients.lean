/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation
public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.CategoryTheory.InternalActionSitePresentation
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.ProfiniteActionParameters
public import Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Sheaf.Paper.FieldProfiniteGaloisSite
public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The field action topos and its normalized coefficient comparison

Source: Bhatt--Scholze, Examples 4.1.9--4.1.10, pp. 27--28; main-20261015,
six-functors direct-image proof, paragraph (3), normalized free-subsite refinement.
(blueprint: lem-sfb-field-action-topos-coefficients).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction.CoherentPresentation

namespace AlgebraicGeometry.ProEtale.FieldActionTopos

/-- Condensed sets on the original profinite site, with the containing coefficient universe.
Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-sfb-field-action-topos-coefficients). -/
abbrev Cond := Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))

/-- The actual small-model transport of a condensed set and its maps.
Source: the size convention and the recorded `base_transport`
(blueprint: lem-sfb-field-action-topos-coefficients). -/
def transport : Cond.{u} ⥤ Sheaf baseCoverage.toGrothendieck (Type (u + 1)) :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
      (AsSmall.down : Base.{u} ⥤ Profinite.{u}).op)
    (fun F ↦ (base_transport F.obj).2 F.property)

/-- Set sheaves on the small pro-etale site, without changing its universes.
Source: Bhatt--Scholze, Definition 4.1.1
(blueprint: lem-sfb-field-action-topos-coefficients). -/
abbrev FieldSheaves (k : Type u) [Field k] :=
  Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))

/-- The underlying condensed set of the recorded arbitrary commutative condensed ring.
Source: the recorded section-ring equivalence
(blueprint: lem-sfb-field-action-topos-coefficients). -/
abbrev coefficientSet (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] : Cond.{u} :=
  (sheafCompose _ (forget CommRingCat.{u + 1})).obj (coefficient R)

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The arithmetic profinite-test presheaf, functorial in the sheaf.
Source: Bhatt--Scholze, Example 4.1.9
(blueprint: lem-sfb-field-action-topos-coefficients). -/
def arithmetic : FieldSheaves k ⥤ Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (profiniteToProEtOf (Spec (.of k))).op

/-- The complete field equivalence, with every comparison tied to its test restrictions.
The internal action category and its small model are the recorded constructions.
Source: Bhatt--Scholze, Examples 4.1.9--4.1.10 and the free-subsite refinement
(blueprint: lem-sfb-field-action-topos-coefficients). -/
structure Normalization where
  /-- The equivalence of set topoi. -/
  equivalence : FieldSheaves k ≌ Actions (Ω ≃ₐ[k] Ω)
  /-- A normalized realization of the existing action-topos inverse image. -/
  actionTopos : InternalActionSite.GeometricRestriction baseCoverage base_site
  /-- The free dense subsite, embedded in the qcqs field site. -/
  free : InternalActionSite.Object (groupPresheaf (Ω ≃ₐ[k] Ω)) ⥤
    Scheme.ProEt.Qcqs (Spec (.of k))
  /-- The free subsite is full and faithful. -/
  fullyFaithful : free.FullyFaithful
  /-- The free subsite is dense with its induced pro-etale topology. -/
  dense : (free ⋙ Scheme.ProEt.qcqsInclusion (Spec (.of k))).IsDenseSubsite
    ((free ⋙ Scheme.ProEt.qcqsInclusion (Spec (.of k))).inducedTopology
      (Scheme.ProEt.topology (Spec (.of k)))) (Scheme.ProEt.topology (Spec (.of k)))
  /-- The field-site equivalence, used only to specify the free coordinates. -/
  fieldSite : Scheme.ProEt.Qcqs (Spec (.of k)) ≌ ContAction Profinite.{u} (Ω ≃ₐ[k] Ω)
  /-- These really are the free profinite Galois spaces. -/
  coordinates (P : Base.{u}) : fieldSite.functor.obj (free.obj ⟨P⟩) ≅
    (Profinite.ContinuousActionParameter.freeAction (Ω ≃ₐ[k] Ω)).obj (parameter P)
  /-- Every labeled restriction has the prescribed noncommutative multiplication order. -/
  arrow (P T : Base.{u}) (f : T ⟶ P)
      (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op T))
      (g : Ω ≃ₐ[k] Ω) (t : parameter T) :
    ((coordinates T).inv ≫ fieldSite.functor.map (free.map ⟨f, b⟩) ≫
      (coordinates P).hom).hom.hom (g, t) = (g * b.down t, f.down t)
  /-- Each free object is the actual geometric test scheme over s. -/
  geometric (P : Base.{u}) :
    (Scheme.ProEt.qcqsInclusion (Spec (.of k)) ⋙ Scheme.ProEt.forget (Spec (.of k))).obj
        (free.obj ⟨P⟩) ≅
      (profiniteToProEtOf (Spec (.of Ω)) ⋙ Scheme.ProEt.forget (Spec (.of Ω)) ⋙
        Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj (parameter P)
  /-- The geometric identification is natural in profinite parameters. -/
  geometric_naturality (P T : Base.{u}) (f : T ⟶ P) :
    (Scheme.ProEt.qcqsInclusion (Spec (.of k)) ⋙ Scheme.ProEt.forget (Spec (.of k))).map
        (free.map ⟨f, 1⟩) ≫
        (geometric P).hom =
      (geometric T).hom ≫ (profiniteToProEtOf (Spec (.of Ω)) ⋙ Scheme.ProEt.forget (Spec (.of Ω)) ⋙
        Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).map f.down
  /-- The label sigma is the actual Spec.map sigma on the geometric test, with unchanged
  profinite coordinate. On geometric points this is right multiplication g mapped to
  g sigma, so no inverse of sigma occurs. These two pullback coordinates fix the map. -/
  geometric_galois (P : Base.{u}) (σ : Ω ≃ₐ[k] Ω) :
    ((Scheme.ProEt.qcqsInclusion _).map
        (free.map ⟨𝟙 P, ULift.up (ContinuousMap.const (parameter P) σ)⟩)).left ≫
        (geometric P).hom.left ≫
        pullback.fst ((profiniteToProEt.obj (parameter P)).hom) (toSpecZ (Spec (.of Ω))) =
      (geometric P).hom.left ≫
        pullback.fst ((profiniteToProEt.obj (parameter P)).hom) (toSpecZ (Spec (.of Ω))) ∧
    ((Scheme.ProEt.qcqsInclusion _).map
        (free.map ⟨𝟙 P, ULift.up (ContinuousMap.const (parameter P) σ)⟩)).left ≫
        (geometric P).hom.left ≫
        pullback.snd ((profiniteToProEt.obj (parameter P)).hom) (toSpecZ (Spec (.of Ω))) =
      (geometric P).hom.left ≫
        pullback.snd ((profiniteToProEt.obj (parameter P)).hom) (toSpecZ (Spec (.of Ω))) ≫
        Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)
  /-- Free restriction, hence evaluation on bar s[P], is the underlying condensed sheaf. -/
  sections (F : FieldSheaves k) (P : Base.{u}) :
    (equivalence.functor.obj F).X.obj.obj (op P) ≃
      F.obj.obj (op ((Scheme.ProEt.qcqsInclusion _).obj (free.obj ⟨P⟩)))
  /-- The restriction along (f,b) is b acting on f-star, in the recorded convention. -/
  restriction (F : FieldSheaves k) (P T : Base.{u}) (f : T ⟶ P)
      (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op T))
      (x : (equivalence.functor.obj F).X.obj.obj (op P)) :
    sections F T (InternalActionSite.setAction _ _ _ (equivalence.functor.obj F)
        (op T) b ((equivalence.functor.obj F).X.obj.map f.op x)) =
      F.obj.map ((Scheme.ProEt.qcqsInclusion _).map (free.map ⟨f, b⟩)).op (sections F P x)
  /-- The section identifications also commute with all maps of sheaves. -/
  sections_maps {F H : FieldSheaves k} (a : F ⟶ H) (P : Base.{u})
      (x : (equivalence.functor.obj F).X.obj.obj (op P)) :
    sections H P ((equivalence.functor.map a).hom.hom.app (op P) x) =
      a.hom.app _ (sections F P x)
  /-- A finite labeled family covers exactly when its parameter maps jointly surject. -/
  covers (P : Base.{u}) (n : ℕ) (T : Fin n → Base.{u}) (f : ∀ i, T i ⟶ P)
      (b : ∀ i, (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op (T i))) :
    Presieve.ofArrows (fun i ↦ free.obj ⟨T i⟩) (fun i ↦ free.map ⟨f i, b i⟩) ∈
        ((Scheme.ProEt.qcqsInclusion _).inducedTopology
          (Scheme.ProEt.topology (Spec (.of k)))).toPrecoverage (free.obj ⟨P⟩) ↔
      ∀ p : parameter P, ∃ (i : Fin n) (t : parameter (T i)), (f i).down t = p
  /-- The point direct image, pinned below to arithmetic test evaluation. -/
  pointDirect : FieldSheaves k ⥤ Cond.{u}
  /-- Its evaluation is F(s[P]), naturally in P and F. -/
  pointEvaluation : pointDirect ⋙ sheafToPresheaf _ _ ≅ arithmetic k
  /-- This is the adjoint of the recorded geometric point inverse image. -/
  pointAdjunction : profinitePointSetSchemeInverseImage (Spec (.of k)) ⊣ pointDirect
  /-- The action point inverse image, on the original profinite-site encoding. -/
  trivial : Cond.{u} ⥤ Actions (Ω ≃ₐ[k] Ω)
  /-- It is exactly the inverse image of the recorded action-topos geometric morphism. -/
  trivial_eq : trivial = transport ⋙
    InternalActionSite.inflation baseCoverage base_site (groupPresheaf (Ω ≃ₐ[k] Ω))
      (Type (u + 1)) ⋙
    (actionTopos.equivalence (groupPresheaf (Ω ≃ₐ[k] Ω))
      (group_isSheaf (Ω ≃ₐ[k] Ω))).inverse
  /-- Its right adjoint is internal invariants. -/
  invariants : Actions (Ω ≃ₐ[k] Ω) ⥤ Cond.{u}
  /-- The invariants adjunction. -/
  actionAdjunction : trivial ⊣ invariants
  /-- The conjugate right-adjoint comparison. -/
  rightComparison : pointDirect ≅ equivalence.functor ⋙ invariants
  /-- The inclusion of invariant sections into underlying sections. -/
  inclusion : invariants ⋙ transport ⟶ Mod.forget _
  /-- The trivial-action inverse image retains the original underlying sheaf. -/
  trivialUnderlying : trivial ⋙ Mod.forget _ ≅ transport
  /-- Its action is literally trivial under this identification. -/
  trivial_action (A : Cond.{u}) (P : Base.{u})
      (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op P))
      (x : (trivial.obj A).X.obj.obj (op P)) :
    InternalActionSite.setAction _ _ _ (trivial.obj A) (op P) b x = x
  /-- The inclusion is the underlying counit, not an unrelated invariant embedding. -/
  inclusion_counit (M : Actions (Ω ≃ₐ[k] Ω)) :
    inclusion.app M = (trivialUnderlying.inv.app (invariants.obj M)) ≫
      (Mod.forget _).map (actionAdjunction.counit.app M)
  /-- Invariant sections inject. -/
  injective (M : Actions (Ω ≃ₐ[k] Ω)) (P : Base.{u}) :
    Function.Injective ((inclusion.app M).hom.app (op P))
  /-- The image consists of sections fixed after every profinite base change. -/
  image (M : Actions (Ω ≃ₐ[k] Ω)) (P : Base.{u}) (x : M.X.obj.obj (op P)) :
    (∃ y, (inclusion.app M).hom.app (op P) y = x) ↔
      ∀ (T : Base.{u}) (f : T ⟶ P)
        (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op T)),
        InternalActionSite.setAction _ _ _ M (op T) b (M.X.obj.map f.op x) =
          M.X.obj.map f.op x
  /-- The canonical geometric-to-arithmetic cover. -/
  cover (P : Base.{u}) : (Scheme.ProEt.qcqsInclusion _).obj (free.obj ⟨P⟩) ⟶
    (profiniteToProEtOf (Spec (.of k))).obj (parameter P)
  /-- This is a cover in the given pro-etale topology. -/
  covering (P : Base.{u}) :
    Sieve.generate (Presieve.singleton (cover P)) ∈
      Scheme.ProEt.topology (Spec (.of k))
        ((profiniteToProEtOf (Spec (.of k))).obj (parameter P))
  /-- Its scheme map preserves the profinite coordinate, fixing the canonical restriction. -/
  cover_coordinate (P : Base.{u}) :
    (cover P).left ≫ pullback.fst ((profiniteToProEt.obj (parameter P)).hom)
        (toSpecZ (Spec (.of k))) =
      (geometric P).hom.left ≫
        pullback.fst ((profiniteToProEt.obj (parameter P)).hom) (toSpecZ (Spec (.of Ω)))
  /-- The right comparison's invariant inclusion is precisely restriction along this cover. -/
  right_restriction (F : FieldSheaves k) (P : Base.{u})
      (y : (pointDirect.obj F).obj.obj (op (parameter P))) :
    sections F P ((inclusion.app (equivalence.functor.obj F)).hom.app (op P)
      (((rightComparison.hom.app F).hom.app (op (parameter P))) y)) =
      F.obj.map (cover P).op ((pointEvaluation.hom.app F).app (op (parameter P)) y)
  /-- The cover equalizer is exactly the universal fixed-section subobject. -/
  equalizer (F : FieldSheaves k) (P : Base.{u})
      (x : (equivalence.functor.obj F).X.obj.obj (op P)) :
    (∃! y : F.obj.obj (op ((profiniteToProEtOf (Spec (.of k))).obj (parameter P))),
      F.obj.map (cover P).op y = sections F P x) ↔
      ∀ (T : Base.{u}) (f : T ⟶ P)
        (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op T)),
        InternalActionSite.setAction _ _ _ (equivalence.functor.obj F) (op T) b
            ((equivalence.functor.obj F).X.obj.map f.op x) =
          (equivalence.functor.obj F).X.obj.map f.op x
  /-- The normalized left-adjoint comparison. -/
  leftComparison : profinitePointSetSchemeInverseImage (Spec (.of k)) ⋙
    equivalence.functor ≅ trivial
  /-- Both sides are finite-product-preserving inverse images. -/
  point_leftExact : PreservesFiniteLimits
    (profinitePointSetSchemeInverseImage (Spec (.of k)))
  /-- Trivial action is left exact. -/
  trivial_leftExact : PreservesFiniteLimits trivial
  /-- The left comparison is the conjugate of exactly the specified right comparison. -/
  mate (A : Cond.{u}) (F : FieldSheaves k)
      (a : (profinitePointSetSchemeInverseImage (Spec (.of k))).obj A ⟶ F) :
    actionAdjunction.homEquiv A (equivalence.functor.obj F)
        (leftComparison.inv.app A ≫ equivalence.functor.map a) =
      pointAdjunction.homEquiv A F a ≫ rightComparison.hom.app F
  /-- The same comparison transports every finite-arity operation, including all ring
  operations: arity zero is the unit and zero, arity one negation, arity two product and sum.
  The two image cones are product cones, and their comparison has exactly the given
  components. Naturality here also applies to every morphism of condensed rings. -/
  finite_operations (A : Cond.{u}) (n : ℕ) (c : Fan (fun _ : Fin n ↦ A))
      (_hc : IsLimit c) (o : c.pt ⟶ A) :
    Nonempty (IsLimit ((profinitePointSetSchemeInverseImage (Spec (.of k)) ⋙
      equivalence.functor).mapCone c)) ∧ Nonempty (IsLimit (trivial.mapCone c)) ∧
    (profinitePointSetSchemeInverseImage (Spec (.of k)) ⋙ equivalence.functor).map o ≫
        leftComparison.hom.app A = leftComparison.hom.app c.pt ≫ trivial.map o ∧
    (∀ i : Fin n,
      (profinitePointSetSchemeInverseImage (Spec (.of k)) ⋙ equivalence.functor).map
          (c.π.app ⟨i⟩) ≫ leftComparison.hom.app A =
        leftComparison.hom.app c.pt ≫ trivial.map (c.π.app ⟨i⟩))
  /-- The ring comparison uses the same left-adjoint comparison on the underlying set.
  Its operation compatibility is `finite_operations`, for the actual ring operations.
  In particular it is an isomorphism of ring objects, not a chosen ring structure. -/
  coefficientComparison (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :
    equivalence.functor.obj
      ((profinitePointSetSchemeInverseImage (Spec (.of k))).obj (coefficientSet R)) ≅
        trivialCoefficient (Ω ≃ₐ[k] Ω) R
  /-- The coefficient comparison is precisely alpha_R, including its product and unit
  comparisons; the target is the recorded trivial action on the original ring. -/
  coefficient_underlying (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :
    (coefficientComparison R).hom.hom =
      (Mod.forget _).map (leftComparison.hom.app (coefficientSet R)) ≫
        trivialUnderlying.hom.app (coefficientSet R)
  /-- Naturality is required for every ring-sheaf morphism, including multiplication and
  unit compatibility inherited from the finite-operation comparison. -/
  coefficient_maps (R R' : Profinite.CondensedRing.{u})
      [IsCommMonObj R.X] [IsCommMonObj R'.X] (a : coefficient R ⟶ coefficient R') :
    (Mod.forget _).map (equivalence.functor.map
        ((profinitePointSetSchemeInverseImage (Spec (.of k))).map
          ((sheafCompose _ (forget CommRingCat.{u + 1})).map a))) ≫
        (coefficientComparison R').hom.hom =
      (coefficientComparison R).hom.hom ≫
        transport.map ((sheafCompose _ (forget CommRingCat.{u + 1})).map a)
  /-- Equivariant maps between free objects have unique continuous coordinates. -/
  free_arrows (P T : Base.{u})
      (v : (Profinite.ContinuousActionParameter.freeAction (Ω ≃ₐ[k] Ω)).obj (parameter T) ⟶
        (Profinite.ContinuousActionParameter.freeAction (Ω ≃ₐ[k] Ω)).obj (parameter P)) :
    ∃! fb : (T ⟶ P) × (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op T),
      ∀ (g : Ω ≃ₐ[k] Ω) (t : parameter T),
        v.hom.hom (g, t) = (g * fb.2.down t, fb.1.down t)
  /-- The kernel-pair coordinates are (g,h,p), with projections (g,p) and (gh,p). -/
  kernel_pair (P : Base.{u}) :
    ∃ (T : Base.{u}) (e : parameter T ≃ₜ ((Ω ≃ₐ[k] Ω) × parameter P))
      (f : T ⟶ P) (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op T)),
      (∀ t, f.down t = (e t).2 ∧ b.down t = (e t).1) ∧
      IsPullback
        ((Scheme.ProEt.qcqsInclusion _).map (free.map ⟨f, 1⟩))
        ((Scheme.ProEt.qcqsInclusion _).map (free.map ⟨f, b⟩)) (cover P) (cover P)

/-- The field pro-etale topos is the topos of internal condensed Galois actions,
with its free-test, point-adjunction, universal-invariants and ring normalization.

Source: Bhatt--Scholze, Examples 4.1.9--4.1.10, pp. 27--28; main-20261015,
six-functors direct-image proof paragraph (3), agent normalized refinement.
(blueprint: lem-sfb-field-action-topos-coefficients).

Proof:
1. Restrict to the dense qcqs field subsite using field_profinite_galois_site and
   the dense-subsite sheaf equivalence. This identifies the arithmetic and geometric
   test schemes with trivial P and free G times P.
2. Every free equivariant arrow is (g,t) mapped to (g b(t),f(t)), uniquely by evaluation
   at (1,t). Composing labels gives c times h-star b, also for noncommutative G.
   Under the canonical Galois fibre functor, Spec.map sigma acts on an embedding g by
   precomposition with sigma, hence by g sigma. Choose the geometric identifications
   from this fibre functor; the label (identity, constant sigma) is exactly this scheme
   automorphism on bar s[P], preserving P. This pins the Galois labels themselves.
3. A finite labeled family surjects exactly when its parameter maps jointly surject;
   normalize a preimage using b(t) inverse. Every action space has the free cover
   G times its underlying space. Thus this free subsite is dense with the action topology.
4. Apply the recorded internal-action equivalence and transport by AsSmall. Restriction
   is b acting on f-star. These identities commute with all maps and all profinite tests.
5. The free cover of the trivial parameter has kernel pair G times G times P,
   with projections (g,h,p) mapped to (g,p) and (gh,p). Its sheaf equalizer says precisely
   that a section is fixed after every profinite base change; conversely test on G times P.
6. Such fixed sections form a sheaf and represent maps out of trivial actions. The
   inclusion is the adjunction counit. Hence restriction on s[P] is the specified
   conjugate right-adjoint comparison, including its underlying inclusion.
7. Uniqueness of left adjoints, with the prescribed mate, gives leftComparison. Both
   inverse images preserve finite limits, so this comparison respects finite products.
8. Naturality at each ring operation R^n to R, and the product comparison, gives the
   ring comparison: n=0 gives zero and unit, n=1 negation, n=2 addition and multiplication.
   Naturality at ring morphisms gives its coefficient square. No discreteness, algebraic
   closedness of k, finite Galois group or exactness of invariant sections is assumed.
-/
theorem field_action_topos_coefficients (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] : Nonempty (Normalization k Ω) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldActionTopos

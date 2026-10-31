/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
import WeilConjectures.DeligneLaumon.NativeOpenDirectExchangeIso
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian

/-! # Condensed compactification comparison and target-open restriction

Source: latest blueprint, sec-deligne-laumon-general/sk-l-dl-general-quasifinite/
lem-zl-quasi-finite.proof.md, first paragraph, and sec-six-functors-basics/
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md
(blueprint: lem-zl-condensed-compactification-open-comparison).

The comparison is normalized by the existing native refinement arrows. Open restriction
is the existing proper/open exchange, whose two factors are adjunction mates. All endpoints
are ordinary derived categories of internal modules over the actual condensed coefficient.
The context record only bundles the hypotheses; it imposes no absolute separatedness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Check the native derived proofs sequentially to limit peak memory.
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactificationOpenComparison

open CompactificationReindexing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp pullbackSquareComparison


/-- The finite-type quasi-separated models and the separated finite-type morphism between
 them. Neither structure morphism is assumed separated.
Source: latest blueprint quasi-finite proof, first paragraph, and the node's opening setting
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
structure Model (D : WeilConjectures.FiniteFieldDatum.{u}) where
  X₀ : Over (Spec (.of D.k₀))
  Y₀ : Over (Spec (.of D.k₀))
  f₀ : X₀ ⟶ Y₀
  [finiteX : LocallyOfFiniteType X₀.hom]
  [compactX : QuasiCompact X₀.hom]
  [qsX : QuasiSeparatedSpace X₀.left]
  [finiteY : LocallyOfFiniteType Y₀.hom]
  [compactY : QuasiCompact Y₀.hom]
  [qsY : QuasiSeparatedSpace Y₀.left]
  [separated : IsSeparated f₀.left]
  [finite : LocallyOfFiniteType f₀.left]
  [compact : QuasiCompact f₀.left]

attribute [instance] Model.finiteX Model.compactX Model.qsX Model.finiteY Model.compactY
  Model.qsY Model.separated Model.finite Model.compact

/-- The actual base-change functor along the chosen algebraic-closure embedding.
Source: latest blueprint quasi-finite proof, first paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev geometric (D : WeilConjectures.FiniteFieldDatum.{u}) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The middle model has its induced structure morphism over k0.
Source: latest blueprint refinement proof, compactification diagrams
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev middle₀ {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) : Over (Spec (.of D.k₀)) :=
  Over.mk (c.g ≫ M.Y₀.hom)

/-- The open factor is a morphism over the finite base.
Source: latest blueprint refinement proof, compactification diagrams
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: replace i g by f using the compactification triangle, then use the equation
saying that f0 is a morphism over k0. -/
theorem open_over {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) : c.i ≫ (c.g ≫ M.Y₀.hom) = M.X₀.hom := by
  rw [← Category.assoc, ← c.comm]
  exact Over.w M.f₀

/-- The open arrow over k0, with its structure equation named separately.
Source: latest blueprint refinement proof, compactification diagrams
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def open₀ {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) : M.X₀ ⟶ middle₀ M c :=
  Over.homMk c.i (open_over M c)

/-- The proper arrow over k0, with the induced structure morphism on its source.
Source: latest blueprint refinement proof, compactification diagrams
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def proper₀ {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) : middle₀ M c ⟶ M.Y₀ :=
  Over.homMk c.g rfl

/-- Base change preserves the compactification triangle.
Source: latest blueprint refinement proof, base-change clause
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: the two model arrows compose to f0 by the compactification triangle.
Apply the actual base-change functor and take underlying scheme morphisms. -/
theorem geometric_factorization {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) :
    ((geometric D).map M.f₀).left =
      ((geometric D).map (open₀ M c)).left ≫ ((geometric D).map (proper₀ M c)).left := by
  have h : M.f₀ = open₀ M c ≫ proper₀ M c := by
    apply Over.OverMorphism.ext
    exact c.comm
  rw [h, Functor.map_comp]
  rfl

/-- A model compactification pulled back literally on all three vertices. Its middle
scheme is the geometric fibre of the middle model, so its Frobenius is the recorded one.
Source: latest blueprint refinement proof, base-change clause
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def geometricCompactification {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) : Compactification ((geometric D).map M.f₀).left where
  Z := ((geometric D).obj (middle₀ M c)).left
  i := ((geometric D).map (open₀ M c)).left
  g := ((geometric D).map (proper₀ M c)).left
  comm := geometric_factorization M c
  isProper := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) (proper₀ M c) c.isProper
  isOpenImmersion := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) (open₀ M c) c.isOpenImmersion

/-- The source geometric fibre, exactly the one of the finite-field datum.
Source: latest blueprint quasi-finite proof, geometric base change
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev source {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D) :=
  (D.geometricFiber M.X₀).left

/-- The target geometric fibre, exactly the one of the finite-field datum.
Source: latest blueprint quasi-finite proof, geometric base change
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev target {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D) :=
  (D.geometricFiber M.Y₀).left

/-- Bounded constructible inputs in the dependency's ordinary derived category.
Source: latest blueprint refinement proof, bounded constructible inputs
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev Inputs (ell : ℕ) [Fact ell.Prime] {D : WeilConjectures.FiniteFieldDatum.{u}}
    (M : Model D) :=
  BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) (source M))

/-- The given candidate Rp_* D(j_!), restricted only at its source. No preservation
of bounded constructibility by the output is assumed here.
Source: latest blueprint refinement proof, candidate T_c
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev candidate (ell : ℕ) [Fact ell.Prime] {D : WeilConjectures.FiniteFieldDatum.{u}}
    (M : Model D) (c : Compactification M.f₀.left) :=
  (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) (source M))).ι ⋙
    rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell)
      (geometricCompactification M c)

/-- Families of natural derived comparisons; the theorem below fixes them by the
canonical refinement normalization, rather than choosing arbitrary isomorphisms.
Source: latest blueprint refinement proof, independence and cocycle
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev Comparisons (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] :=
  ∀ (M : Model D) (c d : Compactification M.f₀.left), candidate ell M c ≅ candidate ell M d

/-- Naturality of geometric Frobenius for every morphism of finite-field models.
Source: latest blueprint quasi-finite proof, definition over k0
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: the base-changed model morphism changes the model coordinate and geometric
Frobenius changes the closure coordinate. Their composites have identical two pullback
projections, so the fibre-product universal property proves this commuting square. -/
theorem frobenius_naturality (D : WeilConjectures.FiniteFieldDatum.{u})
    {T₀ S₀ : Over (Spec (.of D.k₀))} (a₀ : T₀ ⟶ S₀) :
    CommSq (StrictWeil.modelFrobenius D T₀).hom ((geometric D).map a₀).left
      ((geometric D).map a₀).left (StrictWeil.modelFrobenius D S₀).hom := by
  exact ⟨(D.frobenius_square_cartesian T₀ S₀ a₀).2.2.2.2.1⟩


/-- The Frobenius automorphisms give the two commuting compactification squares.
Source: latest blueprint quasi-finite proof, definition over k0; refinement proof,
Frobenius reindexing
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: on every vertex use id times geometric field Frobenius. Naturality of fibre
products gives both commuting squares. Their horizontal arrows are isomorphisms,
so the open square is Cartesian. No linearity over k is claimed. -/
theorem frobenius_squares {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) :
    IsPullback (StrictWeil.modelFrobenius D M.X₀).hom
      (geometricCompactification M c).i (geometricCompactification M c).i
      (StrictWeil.modelFrobenius D (middle₀ M c)).hom ∧
    CommSq (StrictWeil.modelFrobenius D (middle₀ M c)).hom
      (geometricCompactification M c).g (geometricCompactification M c).g
      (StrictWeil.modelFrobenius D M.Y₀).hom := by
  exact ⟨IsPullback.of_horiz_isIso (frobenius_naturality D (open₀ M c)),
    frobenius_naturality D (proper₀ M c)⟩

/-- The specified geometric-Frobenius diagram, using the recorded semilinear action.
Source: latest blueprint quasi-finite proof, definition over k0
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def frobeniusSquare {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) :
    Square (geometricCompactification M c) (geometricCompactification M c)
      (StrictWeil.modelFrobenius D M.X₀).hom (StrictWeil.modelFrobenius D M.Y₀).hom where
  middle := (StrictWeil.modelFrobenius D (middle₀ M c)).hom
  openSquare := (frobenius_squares M c).1
  properSquare := (frobenius_squares M c).2

/-- Canonical comparisons between the exact and total-derived Frobenius pullbacks.
The strict-pair action is termwise, while the exchange interface uses total pullback.
Source: latest blueprint refinement proof, Frobenius reindexing
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
abbrev frobeniusExactComparison (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀))) :=
  leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ell)
    (StrictWeil.modelFrobenius D T₀).hom

/-- The actual ambient Frobenius structure on T_c K, using the specified exchange and
T_c of the input structure. This is a strict Weil object whenever it lies in Dctf.
Source: latest blueprint refinement proof, last paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def outputWeilArrow (ell : ℕ) [Fact ell.Prime] {D : WeilConjectures.FiniteFieldDatum.{u}}
    (M : Model D) (c : Compactification M.f₀.left)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell) (source M))
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D M.X₀)).obj K ≅ K) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D M.Y₀)).obj
        ((F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).obj K) ⟶
      (F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).obj K :=
  (frobeniusExactComparison ell D M.Y₀).inv.app _ ≫
    (squareExchange (Profinite.padicAlgClRingObj ell) (frobeniusSquare M c)).app K ≫
    (F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).map
      ((frobeniusExactComparison ell D M.X₀).hom.app K ≫ phi.hom)

/-- Normalization on every common dense boundary-preserving refinement. Both comparison
paths are the existing native refinement arrows, not unspecified isomorphisms.
Source: latest blueprint refinement proof, independence calculation
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def Normalized (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (C : Comparisons D ell) : Prop :=
  ∀ (M : Model D) (c d : Compactification M.f₀.left)
    (r : Compactification ((geometric D).map M.f₀).left)
    (_hr : IsSchemeTheoreticallyDominant r.i)
    (a : r.Refinement (geometricCompactification M c))
    (b : r.Refinement (geometricCompactification M d))
    (_ha : a.hom ⁻¹ᵁ (geometricCompactification M c).i.opensRange = r.i.opensRange)
    (_hb : b.hom ⁻¹ᵁ (geometricCompactification M d).i.opensRange = r.i.opensRange)
    (K : Inputs ell M),
    (C M c d).hom.app K ≫ (refinement (Profinite.padicAlgClRingObj ell) b).app K.obj =
      (refinement (Profinite.padicAlgClRingObj ell) a).app K.obj

/-- The canonical natural comparison system is uniquely fixed by every common dense
refinement, including for nonseparated models.
Source: latest blueprint refinement proof, independence and cocycle calculation
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof, following steps 1--4 of the DAG node:
1. Choose a common dense boundary refinement over k0 using
`det-nagata-refinement-common-dense`; its arrows are proper, preserve the boundary,
and become unique after a further dense refinement by `det-nagata-refinement-morphisms`.
Base change these actual diagrams to k, using `prop-nagata-compactification-category`.
2. On the open, normalized derived restriction identifies Rh_* j_d! K with K.
The open adjunction transposes its inverse to e_h, uniquely restricting to id_K
(`lem-sfb-derived-open-restriction-normalization`,
`lem-sfb-condensed-support-derived-localization`). The native refinement is this map
followed by proper image and the canonical direct-image compositor.
3. On the closed complement both sides vanish by
`lem-zl-condensed-proper-support-boundary-zero` and mixed restriction. Joint open/closed
restriction detects that e_h is invertible; this does not assert geometric-stalk
conservativity for arbitrary condensed objects.
4. Both successive refinement arrows restrict to id_K, so the adjunction bijection
and the mixed restriction/composition equation identify them. For a common refinement
r set C_cd = rho_a rho_b^{-1}. A further refinement cancels in this formula. A common
dense refinement of any two choices proves independence. The same normalization
forces uniqueness, and naturality in all ambient derived arrows gives a natural iso. -/
theorem comparisons_existsUnique (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p) :
    ∃! C : Comparisons D ell, Normalized D ell C := by
  sorry

/-- The comparison system selected from a theorem determining it uniquely up to equality.
Source: latest blueprint refinement proof, canonical common-refinement comparisons
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def comparisons (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) : Comparisons D ell :=
  (comparisons_existsUnique D ell hEll).exists.choose

/-- Identity, independence of every common dense refinement, and the cocycle in the
ordinary derived category, as equalities of natural isomorphisms.
Source: latest blueprint refinement proof, independence and cocycle calculation
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: the chosen family satisfies its defining normalization. Use a single common
dense refinement for three compactifications and cancel the middle rho factors.
For c = d the two arrows from the dense common refinement are equal, so the same
cancellation gives identity. This is step 4 of the DAG proof, using compositor coherence. -/
theorem comparison_normalization_id_cocycle (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) :
    Normalized D ell (comparisons D ell hEll) ∧
      (∀ (M : Model D) (c : Compactification M.f₀.left),
        comparisons D ell hEll M c c = Iso.refl _) ∧
      (∀ (M : Model D) (c d e : Compactification M.f₀.left),
        comparisons D ell hEll M c d ≪≫ comparisons D ell hEll M d e =
          comparisons D ell hEll M c e) := by
  sorry

private theorem open_exchange_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsOpenImmersion v]
    (s : Square c c' w v) (hs : IsPullback s.middle c'.g c.g v) :
    IsIso (squareExchange Λ s) := by
  have he : IsIso (baseChangeMap Λ s.properSquare) := nativeOpenDirectExchangeIso Λ hs
  unfold squareExchange
    CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
  rw [← Adjunction.exchangeRight_eq_mateEquiv]
  change IsIso (
    (Functor.associator (J Λ c.i) (R Λ c.g) (P Λ v)).hom ≫
    Functor.whiskerLeft (J Λ c.i) (baseChangeMap Λ s.properSquare) ≫
    (Functor.associator (J Λ c.i) (P Λ s.middle) (R Λ c'.g)).inv ≫
    Functor.whiskerRight (beta Λ s.openSquare).hom (R Λ c'.g) ≫
    (Functor.associator (P Λ w) (J Λ c'.i) (R Λ c'.g)).hom)
  infer_instance


/-- Restriction of any geometric compactification along a target open is an isomorphism
on the entire ordinary derived category. The Cartesian squares retain the actual restricted
compactification; the literal pullback is the specialization `c.baseChange v`.
Source: latest blueprint refinement proof, target-open restriction construction
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: step 5 of the DAG proof. Factor the specified exchange as normalized derived
open restriction of Rp_* followed by RpV_* of the inverse open-unit mate. The first
factor is invertible by `lem-sfb-derived-open-restriction-normalization`; the second
is the arbitrary-coefficient open base-change isomorphism, equivalently
`lem-sf-ring-sheaf-base-change-mates` after the canonical coefficient identifications.
Exact pullback and extension by zero descend it termwise, using
`lem-sfb-exact-derived-natural-iso` and `lem-sfb-exact-derived-composition`.
No boundedness or constructibility of the input is used. -/
theorem open_restriction_isIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p) (M : Model D)
    (c : Compactification ((geometric D).map M.f₀).left)
    {U V : Scheme.{u}} {f' : U ⟶ V} (c' : Compactification f')
    {v : V ⟶ target M} {w : U ⟶ source M} [IsOpenImmersion v]
    (s : Square c c' w v) (_hs : IsPullback s.middle c'.g c.g v) :
    IsIso (squareExchange (Profinite.padicAlgClRingObj ell) s) := by
  exact open_exchange_isIso (Profinite.padicAlgClRingObj ell) s _hs

/-- The actual target-open isomorphism, whose hom is the specified proper/open exchange.
Source: latest blueprint refinement proof, target-open restriction construction
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def openRestrictionIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (M : Model D)
    (c : Compactification ((geometric D).map M.f₀).left)
    {U V : Scheme.{u}} {f' : U ⟶ V} (c' : Compactification f')
    {v : V ⟶ target M} {w : U ⟶ source M} [IsOpenImmersion v]
    (s : Square c c' w v) (hs : IsPullback s.middle c'.g c.g v) :
    F (Profinite.padicAlgClRingObj ell) c ⋙ P (Profinite.padicAlgClRingObj ell) v ≅
      P (Profinite.padicAlgClRingObj ell) w ⋙ F (Profinite.padicAlgClRingObj ell) c' :=
  @asIso _ _ _ _ (squareExchange (Profinite.padicAlgClRingObj ell) s)
    (open_restriction_isIso D ell hEll M c c' s hs)

/-- Model target-open restriction preserves bounded constructible inputs, and the canonical
open comparison commutes with the compactification comparisons. The universal quantifier
on L and its identifying iso includes every representative, including the identity case.
Source: latest blueprint refinement proof, comparison/restriction square
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: step 6 of the DAG proof. Exact inverse image commutes with homology and carries
finite presentations and strata to their inverse images, so gives the first clause.
For a refinement restrict its defining open adjunct to the target open. The arbitrary-ring
open base-change mate and direct-image restriction identify this adjunct with identity
on the restricted K. Open-adjunction uniqueness identifies it with the restricted
refinement arrow. The mixed restriction/composition law makes the proper-image square
commute. Apply this to both arrows of a common dense refinement and cancel them.
Naturality transports this equation to every L and every displayed identifying iso. -/
theorem comparison_open (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (M N : Model D)
    (u₀ : N.X₀ ⟶ M.X₀) (v₀ : N.Y₀ ⟶ M.Y₀) [IsOpenImmersion v₀.left]
    (_sq₀ : IsPullback u₀.left N.f₀.left M.f₀.left v₀.left)
    (c d : Compactification M.f₀.left) (c' d' : Compactification N.f₀.left)
    (s : Square (geometricCompactification M c) (geometricCompactification N c')
      ((geometric D).map u₀).left ((geometric D).map v₀).left)
    (t : Square (geometricCompactification M d) (geometricCompactification N d')
      ((geometric D).map u₀).left ((geometric D).map v₀).left)
    (_hs : IsPullback s.middle (geometricCompactification N c').g
      (geometricCompactification M c).g ((geometric D).map v₀).left)
    (_ht : IsPullback t.middle (geometricCompactification N d').g
      (geometricCompactification M d).g ((geometric D).map v₀).left)
    (K : Inputs ell M) :
    (∃ L : Inputs ell N, Nonempty
      ((P (Profinite.padicAlgClRingObj ell) ((geometric D).map u₀).left).obj K.obj ≅ L.obj)) ∧
    (∀ (L : Inputs ell N)
      (e : (P (Profinite.padicAlgClRingObj ell) ((geometric D).map u₀).left).obj K.obj ≅ L.obj),
      (P (Profinite.padicAlgClRingObj ell) ((geometric D).map v₀).left).map
          ((comparisons D ell hEll M c d).hom.app K) ≫
        (squareExchange (Profinite.padicAlgClRingObj ell) t).app K.obj ≫
        (F (Profinite.padicAlgClRingObj ell) (geometricCompactification N d')).map e.hom =
      (squareExchange (Profinite.padicAlgClRingObj ell) s).app K.obj ≫
        (F (Profinite.padicAlgClRingObj ell) (geometricCompactification N c')).map e.hom ≫
        (comparisons D ell hEll N c' d').hom.app L) := by
  sorry

/-- Successive target-open restrictions agree with the direct restriction, with precisely
the native pullback compositors at the two boundaries. All inputs are allowed.
Source: latest blueprint refinement proof, successive open restrictions
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: step 6 of the DAG proof. The inverse open-extension comparison is defined by the
open unit; direct and pasted comparisons therefore have the same adjunct. For direct
image use `lem-sfb-derived-open-restriction-successive`. Whisker the two equalities,
insert the canonical pullback compositors, and use naturality to obtain this equality. -/
theorem open_restriction_successive (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p) (M : Model D)
    (c : Compactification ((geometric D).map M.f₀).left)
    {U V U' V' : Scheme.{u}} {f' : U ⟶ V} {f'' : U' ⟶ V'}
    {c' : Compactification f'} {c'' : Compactification f''}
    {w : U ⟶ source M} {v : V ⟶ target M} {w' : U' ⟶ U} {v' : V' ⟶ V}
    [IsOpenImmersion v] [IsOpenImmersion v']
    (s : Square c c' w v) (t : Square c' c'' w' v')
    (outer : Square c c'' (w' ≫ w) (v' ≫ v))
    (_hs : IsPullback s.middle c'.g c.g v)
    (_ht : IsPullback t.middle c''.g c'.g v')
    (_hmiddle : outer.middle = t.middle ≫ s.middle)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell) (source M)) :
    (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ell) v' v).hom.app
        ((F (Profinite.padicAlgClRingObj ell) c).obj K) ≫
      (P (Profinite.padicAlgClRingObj ell) v').map
        ((squareExchange (Profinite.padicAlgClRingObj ell) s).app K) ≫
      (squareExchange (Profinite.padicAlgClRingObj ell) t).app
        ((P (Profinite.padicAlgClRingObj ell) w).obj K) =
    (squareExchange (Profinite.padicAlgClRingObj ell) outer).app K ≫
      (F (Profinite.padicAlgClRingObj ell) c'').map
        ((leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ell) w' w).hom.app K) := by
  sorry


/-- Frobenius reindexing preserves the canonical compactification comparisons.
Source: latest blueprint refinement proof, Frobenius reindexing paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: step 7 of the DAG proof. The geometric-Frobenius automorphisms reindex the
entire model diagram, carrying open units, counits and the K-injective-normalized
proper direct-image compositor to their conjugates. Exact inverse equivalences
preserve K-injectives. Thus the adjunct id_K defining each refinement is preserved.
Uniqueness gives the refinement square, and a common-refinement cancellation gives
this comparison square. Frobenius pullback preserves bounded constructibility by
reindexing the finite presentations and stratifications; naturality covers every e. -/
theorem comparison_frobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (M : Model D)
    (c d : Compactification M.f₀.left) (K : Inputs ell M) :
    (∃ L : Inputs ell M, Nonempty
      ((P (Profinite.padicAlgClRingObj ell)
        (StrictWeil.modelFrobenius D M.X₀).hom).obj K.obj ≅ L.obj)) ∧
    (∀ (L : Inputs ell M)
      (e : (P (Profinite.padicAlgClRingObj ell)
        (StrictWeil.modelFrobenius D M.X₀).hom).obj K.obj ≅ L.obj),
      (P (Profinite.padicAlgClRingObj ell) (StrictWeil.modelFrobenius D M.Y₀).hom).map
          ((comparisons D ell hEll M c d).hom.app K) ≫
        (squareExchange (Profinite.padicAlgClRingObj ell) (frobeniusSquare M d)).app K.obj ≫
        (F (Profinite.padicAlgClRingObj ell) (geometricCompactification M d)).map e.hom =
      (squareExchange (Profinite.padicAlgClRingObj ell) (frobeniusSquare M c)).app K.obj ≫
        (F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).map e.hom ≫
        (comparisons D ell hEll M c d).hom.app L) := by
  sorry

/-- Frobenius also commutes with the target-open exchange, with the canonical square
pullback identifications inserted. The middle model map makes this the actual model cube.
Source: latest blueprint refinement proof, Frobenius reindexing paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: step 7 of the DAG proof. Reindex both proper and open factors of the target-open
comparison by Frobenius. Their defining adjunction units and counits are preserved.
Mate pasting for the proper face and the inverse open-unit mate gives the cube equation
with the two native pullback-square comparisons. There is no restriction on K. -/
theorem open_restriction_frobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p) (M N : Model D)
    (u₀ : N.X₀ ⟶ M.X₀) (v₀ : N.Y₀ ⟶ M.Y₀) [IsOpenImmersion v₀.left]
    (c : Compactification M.f₀.left) (c' : Compactification N.f₀.left)
    (s : Square (geometricCompactification M c) (geometricCompactification N c')
      ((geometric D).map u₀).left ((geometric D).map v₀).left)
    (_hs : IsPullback s.middle (geometricCompactification N c').g
      (geometricCompactification M c).g ((geometric D).map v₀).left)
    (m₀ : middle₀ N c' ⟶ middle₀ M c)
    (_hmiddle : s.middle = ((geometric D).map m₀).left)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell) (source M)) :
    (P (Profinite.padicAlgClRingObj ell) (StrictWeil.modelFrobenius D N.Y₀).hom).map
        ((squareExchange (Profinite.padicAlgClRingObj ell) s).app K) ≫
      (squareExchange (Profinite.padicAlgClRingObj ell) (frobeniusSquare N c')).app
        ((P (Profinite.padicAlgClRingObj ell) ((geometric D).map u₀).left).obj K) ≫
      (F (Profinite.padicAlgClRingObj ell) (geometricCompactification N c')).map
        ((pullbackSquareComparison (Profinite.padicAlgClRingObj ell)
          (frobenius_naturality D u₀)).inv.app K) =
    (pullbackSquareComparison (Profinite.padicAlgClRingObj ell)
        (frobenius_naturality D v₀)).inv.app
        ((F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).obj K) ≫
      (P (Profinite.padicAlgClRingObj ell) ((geometric D).map v₀).left).map
        ((squareExchange (Profinite.padicAlgClRingObj ell) (frobeniusSquare M c)).app K) ≫
      (squareExchange (Profinite.padicAlgClRingObj ell) s).app
        ((P (Profinite.padicAlgClRingObj ell)
          (StrictWeil.modelFrobenius D M.X₀).hom).obj K) := by
  sorry

/-- The induced compactification comparison intertwines the exact strict Weil structures.
Whenever the outputs lie in the bounded constructible finite-Tor subcategory this is
precisely the morphism condition in `StrictWeil.Complex`; it already holds ambiently.
Source: latest blueprint refinement proof, final displayed Weil equation
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: compose comparison_frobenius with the image of the input Weil isomorphism.
Naturality of the comparison moves that image across it. Transport from total derived
pullback to the recorded exact strict-pair action with frobeniusExactComparison.
The resulting equality is h phi_c = phi_d P_Y(h), in categorical composition order. -/
theorem comparison_intertwines_weil (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (M : Model D)
    (c d : Compactification M.f₀.left) (K : Inputs ell M)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D M.X₀)).obj K.obj ≅ K.obj) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ell)
        (StrictWeil.modelFrobenius D M.Y₀)).map
        ((comparisons D ell hEll M c d).hom.app K) ≫
      outputWeilArrow ell M d K.obj phi =
    outputWeilArrow ell M c K.obj phi ≫ (comparisons D ell hEll M c d).hom.app K := by
  sorry

/-- The induced output structure is invertible, already in the ambient derived category.
Source: latest blueprint refinement proof, Frobenius reindexing paragraph
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: Frobenius is an isomorphism at each vertex, so its proper base-change mate
and its open-extension mate are isomorphisms. The remaining factors are the exact/total
pullback comparison and the image of phi, hence are isomorphisms too. -/
theorem outputWeilArrow_isIso (ell : ℕ) [Fact ell.Prime]
    {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell) (source M))
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D M.X₀)).obj K ≅ K) :
    IsIso (outputWeilArrow ell M c K phi) := by
  have hm : IsIso (frobeniusSquare M c).middle :=
    (StrictWeil.modelFrobenius D (middle₀ M c)).isIso_hom
  have he := (square_isIso (Profinite.padicAlgClRingObj ell) (frobeniusSquare M c)
    (frobenius_naturality D M.f₀)).2
  unfold outputWeilArrow
  infer_instance

/-- The canonical isomorphism underlying the output strict Weil structure.
Source: latest blueprint refinement proof, induced Weil structures
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def outputWeilIso (ell : ℕ) [Fact ell.Prime]
    {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell) (source M))
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D M.X₀)).obj K ≅ K) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D M.Y₀)).obj
        ((F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).obj K) ≅
      (F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).obj K :=
  @asIso _ _ _ _ (outputWeilArrow ell M c K phi) (outputWeilArrow_isIso ell M c K phi)

/-- Pullback of a Weil structure along a morphism defined over k0. The square comparison
is the recorded native one and not an arbitrary isomorphism of pullback functors.
Source: latest blueprint refinement proof, target-open Weil compatibility
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def pullbackWeilArrow (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {T₀ S₀ : Over (Spec (.of D.k₀))} (a₀ : T₀ ⟶ S₀)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell)
      ((geometric D).obj S₀).left)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D S₀)).obj K ≅ K) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D T₀)).obj
        ((P (Profinite.padicAlgClRingObj ell) ((geometric D).map a₀).left).obj K) ⟶
      (P (Profinite.padicAlgClRingObj ell) ((geometric D).map a₀).left).obj K :=
  (frobeniusExactComparison ell D T₀).inv.app _ ≫
    (pullbackSquareComparison (Profinite.padicAlgClRingObj ell)
      (frobenius_naturality D a₀)).inv.app K ≫
    (P (Profinite.padicAlgClRingObj ell) ((geometric D).map a₀).left).map
      ((frobeniusExactComparison ell D S₀).hom.app K ≫ phi.hom)

/-- Pullback transports an invertible Weil structure to an invertible structure.
Source: latest blueprint refinement proof, target-open Weil compatibility
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: each displayed factor of pullbackWeilArrow is an isomorphism: the exact/total
comparison, the canonical commuting-square comparison, and pullback of phi. -/
theorem pullbackWeilArrow_isIso (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {T₀ S₀ : Over (Spec (.of D.k₀))} (a₀ : T₀ ⟶ S₀)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell)
      ((geometric D).obj S₀).left)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D S₀)).obj K ≅ K) :
    IsIso (pullbackWeilArrow ell D a₀ K phi) := by
  unfold pullbackWeilArrow
  infer_instance

/-- The specified pulled-back Weil isomorphism.
Source: latest blueprint refinement proof, target-open Weil compatibility
(blueprint: lem-zl-condensed-compactification-open-comparison). -/
def pullbackWeilIso (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {T₀ S₀ : Over (Spec (.of D.k₀))} (a₀ : T₀ ⟶ S₀)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell)
      ((geometric D).obj S₀).left)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D S₀)).obj K ≅ K) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D T₀)).obj
        ((P (Profinite.padicAlgClRingObj ell) ((geometric D).map a₀).left).obj K) ≅
      (P (Profinite.padicAlgClRingObj ell) ((geometric D).map a₀).left).obj K :=
  @asIso _ _ _ _ (pullbackWeilArrow ell D a₀ K phi)
    (pullbackWeilArrow_isIso ell D a₀ K phi)

/-- The target-open comparison intertwines the induced strict Weil structures. Together
with invertibility above, this gives maps of the recorded strict pairs whenever their
underlying objects belong to its bounded constructible subcategory.
Source: latest blueprint refinement proof, final Weil compatibility
(blueprint: lem-zl-condensed-compactification-open-comparison).
Proof: compose open_restriction_frobenius with the image of phi. Naturality moves
phi through the open exchange. Insert the two exact/total pullback comparisons;
their naturality and the native square comparison give precisely the displayed
pullbackWeilArrow and outputWeilArrow. Thus the cube equation becomes the strict
pair morphism equation. This argument is ambient and needs no output preservation. -/
theorem open_restriction_intertwines_weil (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p) (M N : Model D)
    (u₀ : N.X₀ ⟶ M.X₀) (v₀ : N.Y₀ ⟶ M.Y₀) [IsOpenImmersion v₀.left]
    (c : Compactification M.f₀.left) (c' : Compactification N.f₀.left)
    (s : Square (geometricCompactification M c) (geometricCompactification N c')
      ((geometric D).map u₀).left ((geometric D).map v₀).left)
    (_hs : IsPullback s.middle (geometricCompactification N c').g
      (geometricCompactification M c).g ((geometric D).map v₀).left)
    (m₀ : middle₀ N c' ⟶ middle₀ M c)
    (_hmiddle : s.middle = ((geometric D).map m₀).left)
    (K : CompactificationReindexing.D (Profinite.padicAlgClRingObj ell) (source M))
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D M.X₀)).obj K ≅ K) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ell)
        (StrictWeil.modelFrobenius D N.Y₀)).map
        ((squareExchange (Profinite.padicAlgClRingObj ell) s).app K) ≫
      outputWeilArrow ell N c'
        ((P (Profinite.padicAlgClRingObj ell) ((geometric D).map u₀).left).obj K)
        (pullbackWeilIso ell D u₀ K phi) =
    pullbackWeilArrow ell D v₀
        ((F (Profinite.padicAlgClRingObj ell) (geometricCompactification M c)).obj K)
        (outputWeilIso ell M c K phi) ≫
      (squareExchange (Profinite.padicAlgClRingObj ell) s).app K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CompactificationOpenComparison

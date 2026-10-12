module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality
import Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! The valuative factorization step in the proof of Tag 0BF0. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorIsoPullback {A B : Scheme.{u}} (g : A ⟶ B) :
    Modules.tensorPullback g ≅ Modules.pullback g :=
  (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction g)

private theorem tensor_invertible {A B : Scheme.{u}} (g : A ⟶ B)
    (M : B.Modules) [M.IsInvertible] :
    ((Modules.tensorPullback g).obj M).IsInvertible :=
  Modules.IsInvertible.of_iso ((tensorIsoPullback g).app M).symm

private theorem appTop_isIso_of_tensor_unit {A B : Scheme.{u}} (g : A ⟶ B)
    (h : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction g)).unit.app
      (SheafOfModules.unit B.ringCatSheaf))) : IsIso g.appTop := by
  have := h
  have := (Modules.tensorPullbackObjUnitToUnit_isIso g).1
  have hs : IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
    rw [← (Modules.tensorPullbackObjUnitToUnit_isIso g).2]
    infer_instance
  have happ := Functor.map_isIso (SheafOfModules.evaluation B.ringCatSheaf
    (Opposite.op ⊤)) (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
  rw [ConcreteCategory.isIso_iff_bijective] at happ ⊢
  exact happ

/--
(blueprint: lem-sc-picard-locus-closed-valuative-factorization)

For a valuative commutative square for the Picard pullback locus, the generic
factorization forces a factorization over the valuation ring.  This is the
valuative argument of Stacks, More on Morphisms, Tag 0BF0, using the generic
fibre triviality result (Tag 0EX8) and the universal property of the locus.
No immersion or finiteness hypothesis on `j` is needed for this local step.

Proof: put `A = sq.R`, `K = sq.K`, and base change `f` along `sq.i₂`, obtaining
`p : X_A ⟶ Spec A` and the invertible pullback `L` of `E`. The hypotheses on
`p` persist under base change; properness also gives quasi-compactness and
quasi-separatedness, hence finite presentation. Geometric integrality gives
an integral, nonempty closed fibre and a nonempty generic fibre. The adjunction
unit hypothesis, applied to the generic map to `S`, identifies the canonical
structure-sheaf map on the generic fibre with an isomorphism. Its global
sections therefore identify `H⁰(X_K, O)` with `K`. Pullback composition and
the associativity isomorphism of fibre products identify these with the
corresponding objects for `p`.

The commutativity of `sq` gives the generic factorization `sq.i₁`. Apply `hj`
to that map to obtain a finite locally free module `N` over `Spec K` whose
pullback is `L_K`. Such an `N` corresponds to a finite-dimensional vector
space. Its dimension is one: the generic fibre is nonempty, and at any of
its points its pullback has rank one because `L_K` is invertible. Thus `N`
is isomorphic to `O_K`, and `L_K` is trivial. Apply
`generic_fibre_triviality_over_valuation_ring` (Tag 0EX8) to `p` and `L` to
make `L` trivial. The unit module `O_A` is finite locally free, and its
pullback is the unit module on `X_A`. Use this trivialization with `N = O_A`
in the reverse direction of `hj` at `sq.i₂` to obtain the desired `l`.
-/
theorem picard_valuative_factorization {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsInvertible]
    {Z : Scheme.{u}} (j : Z ⟶ S)
    (hj : ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ (h : T ⟶ Z), h ≫ j = g) ↔
          ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
            Nonempty (((Scheme.Modules.tensorPullback (pullback.fst f g)).obj E) ≅
              ((Scheme.Modules.tensorPullback (pullback.snd f g)).obj N)))
    [GeometricallyIntegral f] (sq : ValuativeCommSq j) :
    ∃ l : Spec (CommRingCat.of sq.R) ⟶ Z, l ≫ j = sq.i₂ := by
  classical
  let a := sq.i₂
  let t := Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
  let g := t ≫ a
  let q := pullback.fst f a
  let p := pullback.snd f a
  let L := (Modules.tensorPullback q).obj E
  have : L.IsInvertible := tensor_invertible q E
  let : Field (sq.R ⧸ IsLocalRing.maximalIdeal sq.R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal sq.R)
  have hX₀ : IsIntegral (pullback p (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal sq.R))))) := by
    exact pullback_of_geometrically
      (GeometricallyIntegral.geometrically_isIntegral (f := p))
      (sq.R ⧸ IsLocalRing.maximalIdeal sq.R) _
  have hglobal : IsIso (pullback.snd p t).appTop := by
    let b := pullbackLeftPullbackSndIso f a t
    have hg : IsIso (pullback.snd f g).appTop :=
      appTop_isIso_of_tensor_unit _ (hO g)
    have hb : b.hom ≫ pullback.snd f g = pullback.snd p t :=
      pullbackLeftPullbackSndIso_hom_snd f a t
    rw [← hb, Hom.comp_appTop]
    infer_instance
  obtain ⟨N, hN, ⟨e⟩⟩ := (hj g).mp ⟨sq.i₁, sq.commSq.w⟩
  have : ((Modules.tensorPullback (pullback.fst f g)).obj E).IsInvertible :=
    tensor_invertible _ E
  have : ((Modules.tensorPullback (pullback.snd f g)).obj N).IsInvertible :=
    Modules.IsInvertible.of_iso e
  have : Nonempty (CategoryTheory.Limits.pullback f g : Scheme.{u}) := by
    have := pullback_of_geometrically
      (GeometricallyIntegral.geometrically_isIntegral (f := f)) sq.K g
    exact inferInstance
  obtain ⟨eN⟩ := Modules.nonempty_iso_unit_of_invertible_field_pullback sq.K
    (pullback.snd f g) N
  let eK : (Modules.tensorPullback (pullback.fst f g)).obj E ≅
      SheafOfModules.unit _ :=
    e ≪≫ (Modules.tensorPullback (pullback.snd f g)).mapIso eN ≪≫
      (tensorIsoPullback _).app _ ≪≫ Modules.pullbackObjUnitIso _
  have htriv : Nonempty ((Modules.tensorPullback (pullback.fst p t)).obj L ≅
      SheafOfModules.unit _) := by
    let b := pullbackLeftPullbackSndIso f a t
    let r := pullback.fst p t
    obtain ⟨c₁⟩ := Modules.nonempty_tensorPullbackComp r q
    obtain ⟨c₂⟩ := Modules.nonempty_tensorPullbackComp b.hom (pullback.fst f g)
    have hb : b.hom ≫ pullback.fst f g = r ≫ q :=
      pullbackLeftPullbackSndIso_hom_fst f a t
    let d : (Modules.tensorPullback (r ≫ q)).obj E ≅
        (Modules.tensorPullback (b.hom ≫ pullback.fst f g)).obj E :=
      eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj E) hb.symm)
    exact ⟨c₁.symm.app E ≪≫ d ≪≫ c₂.app E ≪≫
      (Modules.tensorPullback b.hom).mapIso eK ≪≫
      (tensorIsoPullback b.hom).app _ ≪≫ Modules.pullbackObjUnitIso _⟩
  obtain ⟨eA⟩ := generic_fibre_triviality_over_valuation_ring sq.R sq.K
    (pullback f a) p L hX₀ hglobal htriv
  let eunit : (Modules.tensorPullback p).obj
      (SheafOfModules.unit (Spec (CommRingCat.of sq.R)).ringCatSheaf) ≅
      SheafOfModules.unit _ :=
    (tensorIsoPullback p).app _ ≪≫ Modules.pullbackObjUnitIso p
  exact (hj a).mpr ⟨SheafOfModules.unit _,
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _, ⟨eA ≪≫ eunit.symm⟩⟩

end AlgebraicGeometry.Scheme

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus
import Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus
import Sheaf.AlgebraicGeometry.PicardPullbackEvaluation

/-!
# Universal locally closed pullback locus for a finite locally free module

Source: Stacks Project, More on Morphisms, Lemma diagonal-picard-flat-proper, Tag 0BDP
(blueprint: lem-sc-picard-diagonal-locally-closed).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-sc-picard-diagonal-locally-closed) For a flat proper morphism with
  universally trivial structure pushforward, the locus on which a finite locally free module
  comes by pullback is represented by an immersion of finite presentation (locally of finite
  presentation, quasi-compact and quasi-separated, def-sbc-locally-finite-presentation).

  Proof steps from Tag 0BDP: the universal structure-sheaf pushforward makes every fibre
  connected and nonempty, so the rank of `E` is constant on each open-and-closed rank
  component of the base; flatness and properness make these components open and closed.
  Apply the perfect direct-image/base-change theorem to `E` and its dual, and apply the
  locally-closed degree-zero locus construction to both perfect complexes.  On their
  intersection, the two direct images are finite locally free and commute with base change.
  The projection formula shows that an isomorphism `q* E ≅ p* N` forces the cup-product
  pairing between the two direct images to be perfect, and conversely a perfect pairing gives
  such an isomorphism locally on `T`.  Finally, the perfect-pairing locus is the open
  determinant locus; taking it on all rank components yields the required finitely presented
  immersion and the stated universal factorization property. -/
theorem picard_diagonal_locally_closed {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsImmersion j ∧ LocallyOfFinitePresentation j ∧
      QuasiCompact j ∧ QuasiSeparated j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ (h : T ⟶ Z), h ≫ j = g) ↔
          ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
            Nonempty (((Scheme.Modules.tensorPullback (pullback.fst f g)).obj E) ≅
              ((Scheme.Modules.tensorPullback (pullback.snd f g)).obj N)) := by
  obtain ⟨W, j, hj, hjfp, hjqc, hjqs, hW⟩ :=
    exists_picardDirectImageRankLocus f hO E
  have : IsImmersion j := hj
  have : LocallyOfFinitePresentation j := hjfp
  have : QuasiCompact j := hjqc
  have : QuasiSeparated j := hjqs
  obtain ⟨Z, k, hk, hkqc, hZ⟩ := exists_picardEvaluationOpenLocus f hO E j
    (fun h ↦ (hW (h ≫ j)).mp ⟨h, rfl⟩)
  have : IsOpenImmersion k := hk
  have : QuasiCompact k := hkqc
  refine ⟨Z, k ≫ j, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro T g
  constructor
  · rintro ⟨l, hl⟩
    have hl' : (l ≫ k) ≫ j = g := (Category.assoc l k j).trans hl
    subst g
    have hP := (hW ((l ≫ k) ≫ j)).mp ⟨l ≫ k, rfl⟩
    have hε := (hZ (l ≫ k)).mp ⟨l, rfl⟩
    let N := (Modules.pushforward (pullback.snd f ((l ≫ k) ≫ j))).obj
      ((Modules.tensorPullback (pullback.fst f ((l ≫ k) ≫ j))).obj E)
    have hN : N.IsFiniteLocallyFree := hP.1
    have e : Nonempty
        ((Modules.tensorPullback (pullback.fst f ((l ≫ k) ≫ j))).obj E ≅
          (Modules.tensorPullback (pullback.snd f ((l ≫ k) ≫ j))).obj N) :=
      ⟨(asIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction
          (pullback.snd f ((l ≫ k) ≫ j)))).counit.app
            ((Modules.tensorPullback (pullback.fst f ((l ≫ k) ≫ j))).obj E))).symm⟩
    exact ⟨N, hN, e⟩
  · rintro ⟨N, hN, e⟩
    have : N.IsFiniteLocallyFree := hN
    obtain ⟨hP, hε⟩ := picard_rankCondition_and_isIso_counit_of_pullback f hO E g N e
    obtain ⟨h, hh⟩ := (hW g).mpr hP
    subst g
    obtain ⟨l, hl⟩ := (hZ h).mpr hε
    exact ⟨l, by rw [← Category.assoc, hl]⟩

end AlgebraicGeometry.Scheme

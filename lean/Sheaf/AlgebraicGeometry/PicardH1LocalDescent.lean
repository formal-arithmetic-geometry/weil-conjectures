/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.PicardH1MultipleLocus
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Local descent from trivial restrictions and joint H¹ injectivity

Source: Stacks Project, Tags 0BDP and 0BF2.
(blueprint: lem-sc-picard-h1-local-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorPullbackIsoPullback {A B : Scheme.{u}} (g : A ⟶ B) :
    Modules.tensorPullback g ≅ Modules.pullback g :=
  (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction g)

private noncomputable def tensorPullbackUnitIso {A B : Scheme.{u}} (g : A ⟶ B) :
    (Modules.tensorPullback g).obj (SheafOfModules.unit B.ringCatSheaf) ≅
      SheafOfModules.unit A.ringCatSheaf :=
  (tensorPullbackIsoPullback g).app _ ≪≫ Modules.pullbackObjUnitIso g

/-- Trivial restrictions with jointly injective fibre H¹ imply local descent to the base.
Source: Stacks Project, Tag 0BF2, applied to the universal locus of Tag 0BDP.
(blueprint: lem-sc-picard-h1-local-descent).

Proof: construct the universal pullback locus Z for L by Tag 0BDP. For each trivial
restriction use S itself as its universal locus: after any base change the restriction
is still the unit, so it is pulled back from the unit on the new base. The trivial fibre
at s gives a factorization of Spec κ(s) through Z, hence s is in its image. Apply Tag
0BF2 to these loci. On the resulting open U all of the restriction loci are S, so U
factors through Z. Evaluate the universal property of Z on U → S to obtain N and the
required pullback isomorphism. Tensor pullback preserves the unit because it is the
unique left adjoint of the ordinary module pushforward. -/
theorem picard_h1_local_descent {P S : Scheme.{u}} (f : P ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{u}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ P) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : P.Modules) [L.IsInvertible]
    (hi : ∀ i, Nonempty ((Modules.tensorPullback (ui i)).obj L ≅
      SheafOfModules.unit (Xi i).ringCatSheaf))
    (s : S)
    (hs : Nonempty ((Modules.tensorPullback (f.fiberι s)).obj L ≅
      SheafOfModules.unit _))
    (hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1 x)) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ N : U.toScheme.Modules,
      N.IsFiniteLocallyFree ∧
      Nonempty ((Modules.tensorPullback (pullback.fst f U.ι)).obj L ≅
        (Modules.tensorPullback (pullback.snd f U.ι)).obj N) := by
  have := Modules.IsInvertible.sheafOfModules_isInvertible L
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree L
  obtain ⟨Z, j, hj, _, _, _, hZ⟩ := picard_diagonal_locally_closed f hO L
  let : IsImmersion j := hj
  let Zi : Fin n → Scheme.{u} := fun _ ↦ S
  let ji : ∀ i, Zi i ⟶ S := fun _ ↦ 𝟙 S
  have hZi : ∀ i, ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ Zi i, h ≫ ji i = g) ↔
        ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
          Nonempty ((Modules.tensorPullback (pullback.fst (fi i) g)).obj
            ((Modules.tensorPullback (ui i)).obj L) ≅
            (Modules.tensorPullback (pullback.snd (fi i) g)).obj N) := by
    intro i T g
    constructor
    · intro _
      obtain ⟨e⟩ := hi i
      refine ⟨SheafOfModules.unit _, inferInstance, ?_⟩
      exact ⟨(Modules.tensorPullback (pullback.fst (fi i) g)).mapIso e ≪≫
        tensorPullbackUnitIso _ ≪≫ (tensorPullbackUnitIso _).symm⟩
    · intro _
      exact ⟨g, by exact Category.comp_id g⟩
  have hsZ : s ∈ Set.range j := by
    obtain ⟨e⟩ := hs
    obtain ⟨h, hh⟩ := (hZ (S.fromSpecResidueField s)).mpr
      ⟨SheafOfModules.unit _, inferInstance,
        ⟨e ≪≫ (tensorPullbackUnitIso _).symm⟩⟩
    refine ⟨h (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
    have he := congrArg (fun k : Spec (S.residueField s) ⟶ S ↦
      k (IsLocalRing.closedPoint (S.residueField s))) hh
    simpa [Hom.comp_apply] using he
  obtain ⟨U, hsU, hU⟩ := picard_h1_multiple_locus f Xi fi ui hui hO hOi L Z j Zi ji
    hZ hZi (fun g _ _ ↦ ⟨g, by exact Category.comp_id g⟩) s hsZ hH
  obtain ⟨h, hh⟩ := (hU (𝟙 U.toScheme)).mpr
    (fun _ ↦ ⟨U.ι, by simpa only [ji, Category.id_comp] using Category.comp_id U.ι⟩)
  obtain ⟨N, hN, e⟩ := (hZ U.ι).mp ⟨h, by simpa using hh⟩
  exact ⟨U, hsU, N, hN, e⟩

end AlgebraicGeometry.Scheme

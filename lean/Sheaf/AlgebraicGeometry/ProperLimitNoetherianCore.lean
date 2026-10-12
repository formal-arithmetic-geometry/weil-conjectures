module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimit
import Sheaf.AlgebraicGeometry.ProperNoetherianStage
import Sheaf.AlgebraicGeometry.ClosedImageLimitSystem
import Mathlib.CategoryTheory.Presentable.Directed

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Core inverse-system construction for a proper morphism.
Source: Stacks limits.tex, Tag 0A0P, proof steps 1--8.
(blueprint: lem-weil-pbc-proper-limit-noetherian-core)
The construction descends a proper finitely presented envelope, forms scheme-theoretic
images, and verifies the two limit cones, affine transitions, proper stage maps, and
finite-type base stages. -/
theorem exists_proper_limit_noetherian_core
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
      (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs)
      (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss),
      Nonempty (IsLimit (Cone.mk X πX)) ∧ Nonempty (IsLimit (Cone.mk S πS)) ∧
      (∀ (i j : Λᵒᵖ) (a : i ⟶ j),
        IsAffineHom (Xs.map a) ∧ IsAffineHom (Ss.map a)) ∧
      (∀ i : Λᵒᵖ, IsProper (fs.app i)) ∧
      (∀ i : Λᵒᵖ,
        LocallyOfFiniteType (specULiftZIsTerminal.from (Ss.obj i)) ∧
          QuasiCompact (specULiftZIsTerminal.from (Ss.obj i))) ∧
      (∀ i : Λᵒᵖ, πX.app i ≫ fs.app i = f ≫ πS.app i) := by
  classical
  obtain ⟨Y, i, g, hi, hg, hfp, hqc, hqs, hw⟩ :=
    (exists_proper_finitePresentation_closedImmersion_limit f).2
  have := hi
  have := hg
  have := hfp
  have := hqc
  have := hqs
  obtain ⟨N⟩ := S.nonempty_noetherianApproximation
  obtain ⟨a, Y₀, p, h, hp, hpfp, hpqc, hpqs, H⟩ := exists_proper_noetherian_stage g N
  have := hp
  have := hpfp
  have := hpqc
  have := hpqs
  let D := baseChangeDiagram N.D p
  let q := baseChangeDiagramπ N.D p
  let πS := Functor.whiskerLeft (Over.forget a) N.π
  let πY := (Functor.const _).map H.isoPullback.hom ≫
    (baseChangeCone N.D (Cone.mk S N.π) p).π
  have hY : IsLimit (Cone.mk Y πY) :=
    (isLimitBaseChangeCone N.D (Cone.mk S N.π) p N.isLimit).ofIsoLimit
      (Cone.ext H.isoPullback.symm fun j ↦ by simp [πY])
  have (j : Over a) : CompactSpace (D.obj j) := by
    dsimp [D, baseChangeDiagram]
    infer_instance
  have (j : Over a) : QuasiSeparatedSpace (D.obj j) := by
    dsimp [D, baseChangeDiagram]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd _ _)
  obtain ⟨Z, k, πX, hX, htrans, hclosed, hfactor⟩ :=
    exists_closed_image_limit_system D i πY hY
  obtain ⟨A, horder, hdir, hne, F, hfinal⟩ :=
    IsFiltered.exists_directed (Over a)ᵒᵖ
  let := horder
  let := hfinal
  let R := F.leftOp
  let fs := Functor.whiskerLeft R (k ≫ q)
  refine ⟨A, horder.toPreorder, hne, hdir, R ⋙ Z,
    R ⋙ Over.forget a ⋙ N.D, fs,
    Functor.whiskerLeft R πX, Functor.whiskerLeft R πS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(Functor.Initial.isLimitWhiskerEquiv R (Cone.mk X πX)).symm hX.some⟩
  · exact ⟨(Functor.Initial.isLimitWhiskerEquiv R (Cone.mk S πS)).symm
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget a) (Cone.mk S N.π)).symm
        N.isLimit)⟩
  · intro j l b
    exact ⟨htrans (R.map b), N.isAffineHom_map _⟩
  · intro j
    change IsProper (k.app (R.obj j) ≫ q.app (R.obj j))
    have := hclosed (R.obj j)
    dsimp [q, baseChangeDiagramπ]
    infer_instance
  · intro j
    change LocallyOfFiniteType (specULiftZIsTerminal.from (N.D.obj (R.obj j).left)) ∧
      QuasiCompact (specULiftZIsTerminal.from (N.D.obj (R.obj j).left))
    exact ⟨N.locallyOfFiniteType_obj _, inferInstance⟩
  · intro j
    change πX.app (R.obj j) ≫ (k.app (R.obj j) ≫ q.app (R.obj j)) =
      f ≫ N.π.app (R.obj j).left
    rw [← Category.assoc, hfactor, Category.assoc]
    have hcomm : πY.app (R.obj j) ≫ q.app (R.obj j) =
        g ≫ N.π.app (R.obj j).left := by
      simp [πY, q, Category.assoc]
    rw [hcomm, ← Category.assoc, hw]

/-- Affine-base refinement of the core inverse-system construction.
Source: Stacks limits.tex, Tag 0A0P, affine clause of the proof.
(blueprint: lem-weil-pbc-proper-limit-noetherian-affine-clause)
For a core system over an affine base, the stages are affine finite-type schemes and
the global-section cocone is a colimit. -/
-- STATEMENT-DISPUTED: arbitrary limit systems over an affine S need not have
-- finite-type stages. Take X = S = Spec Q, f = id, and the constant singleton system.
-- Q is not finite type over Z: finitely many generators invert only finitely many primes.
theorem proper_limit_noetherian_affine_clause
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S]
    (hS : IsAffine S)
    (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
    (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
    (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs)
    (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss)
    (hlimX : Nonempty (IsLimit (Cone.mk X πX)))
    (hlimS : Nonempty (IsLimit (Cone.mk S πS))) :
    (∀ i : Λᵒᵖ, IsAffine (Ss.obj i) ∧
      RingHom.FiniteType (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Ss.obj i))))) ∧
      Nonempty (IsColimit (Scheme.Γ.mapCocone (Cone.mk S πS).op)) := by
  sorry

end AlgebraicGeometry

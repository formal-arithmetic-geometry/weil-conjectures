/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Topology.KrullDimension
public import Submission.WeilConjectures.AlgebraicGeometry.Thickening
import Submission.WeilConjectures.AlgebraicGeometry.ProperBaseChange.UnmarkedCurveDiagramModel
import Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteClosedImmersionLocus

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Descent of a marked finite curve diagram before the final shrinking

Source: Stacks Project, Tag 0GK7, diagram descent and marked-open paragraphs.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Descend the supplied marked diagram, with the required fibre conditions only at
points above the specified component generic point. The global fibre conditions and
surjectivity of the marked opens are deliberately left to a subsequent shrinking.

Source: Stacks Project, Tag 0GK7, proof of `lemma-make-good-curves`, the paragraphs
from reduction of the base through descent of the marked closed immersion.
(blueprint: lem-weil-pbc-marked-curve-diagram-model)

Proof: Reduce an affine neighbourhood of η. Its generic stalk is its residue field.
Apply the prescribed purely inseparable generic-cover theorem, and reduce its source.
The unique point above η has residue field K. Over this reduced cover, take the inverse
system of affine neighbourhoods of this point. Its limit is Spec K. The finite-family
object, arrow and equality descent theorems descend the supplied schemes and their
commuting arrows to one stage. The objects are finitely presented: B is proper smooth
over a field, A is an open in a Noetherian scheme and is quasi-compact, and L/K is finite.
Keep the given model X by the cartesian comparison with its generic fibre. Descend
finiteness and surjectivity of ν, finite etaleness of t, openness of j, and smooth
properness of p to a common later stage. These properties persist under further base
change. The target over K is Noetherian, hence W₀ is quasi-compact. Descent of this
open and of the closed-immersion comparison gives a marked open W on the model.
Surjectivity of ν makes the comparison a thickening. Its generic inverse image in A_i
is nonempty, since it is dense and A_i is nonempty. Thus its image contains the point
of Spec L_i. The cartesian identifications give geometric connectedness and the
one-dimensional bound at every point of T_i above η. Finally descend each shrinking
through the finite radicial cover by removing the closed image of its complement.
For n=0 all component conditions are vacuous; the descended empty-source surjection
forces the target model to be empty. No final shrinking to control other fibres is used.
-/
theorem exists_marked_curve_diagram_model
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (K : Type u) [Field K] [Algebra (S.residueField η) K]
    [Module.Finite (S.residueField η) K] [IsPurelyInseparable (S.residueField η) K]
    (n : ℕ) (L : Fin n → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (A B : Fin n → Scheme.{u}) (j₀ : ∀ i, A i ⟶ B i)
    (q₀ : ∀ i, B i ⟶ Spec (.of (L i)))
    (ν₀ : (∐ A) ⟶ pullback (f.fiberToSpecResidueField η)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))))
    (hν₀ : IsFinite ν₀ ∧ Surjective ν₀)
    (hcomm : ∀ i, Sigma.ι A i ≫ ν₀ ≫ pullback.snd _ _ =
      j₀ i ≫ q₀ i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
    (hL : ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i))
    (hj₀ : ∀ i, IsOpenImmersion (j₀ i) ∧ Nonempty (A i))
    (hq₀ : ∀ i, Smooth (q₀ i) ∧ IsProper (q₀ i) ∧
      GeometricallyIrreducible (q₀ i) ∧ topologicalKrullDim (B i) ≤ 1)
    (W₀ : (pullback (f.fiberToSpecResidueField η)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K)))).Opens)
    (hW₀ : (∀ i, Dense ((Sigma.ι A i ≫ ν₀) ⁻¹' (W₀ : Set _))) ∧
      IsThickening (pullback.snd ν₀ W₀.ι)) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i)) ∧
        (∃ (σK : Spec (.of K) ⟶ V)
          (hA : ∀ i, A i ⟶ Y i) (hB : ∀ i, B i ⟶ Ybar i)
          (hT : ∀ i, Spec (.of (L i)) ⟶ T i),
          σK ≫ g ≫ U.ι = Spec.map (CommRingCat.ofHom
            (algebraMap (S.residueField η) K)) ≫ S.fromSpecResidueField η ∧
          ∀ i,
            IsPullback (hA i) (j₀ i ≫ q₀ i ≫
              Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
              (j i ≫ p i ≫ t i) σK ∧
            IsPullback (hB i) (q₀ i ≫
              Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) (p i ≫ t i) σK ∧
            IsPullback (hT i) (Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
              (t i) σK ∧
            hA i ≫ j i = j₀ i ≫ hB i ∧ hB i ≫ p i = q₀ i ≫ hT i) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          IsThickening (pullback.snd ν W.ι) ∧
          ∀ i (s : T i), (t i ≫ g ≫ U.ι) s = η →
            GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1 ∧
            s ∈ Set.range (((Sigma.ι Y i ≫ ν) ⁻¹ᵁ W).ι ≫ j i ≫ p i) := by
  classical
  obtain ⟨U, hηU, V, g, hgf, hgs, hgr, T, Y, Ybar, t, j, p, ν,
    hνf, hνs, hc, ht, hj, hp, σK, hA, hB, hT, hσ, H, ⟨aX, Hν⟩, hgeom⟩ :=
    exists_unmarked_curve_diagram_model f η hη K n L A B j₀ q₀ ν₀
      hν₀ hcomm hL hj₀ hq₀
  have : IsFinite g := hgf
  have : UniversallyInjective g := hgr
  have : IsFinite ν := hνf
  have : Surjective ν := hνs
  obtain ⟨W, hWci, hWle⟩ :=
    exists_finite_closedImmersion_locus ν ν₀ (Limits.Sigma.map hA) aX Hν W₀ hW₀.2.1
  refine ⟨U, hηU, V, g, hgf, hgs, hgr, T, Y, Ybar, t, j, p, ν,
    hνf, hνs, hc, ht, hj, hp, ⟨σK, hA, hB, hT, hσ, H⟩,
    W, ⟨hWci, inferInstance⟩, ?_⟩
  intro i s hs
  refine ⟨(hgeom i s hs).1, (hgeom i s hs).2, ?_⟩
  obtain ⟨zK⟩ : Nonempty (Spec (.of K)) := inferInstance
  have hσpoint : (g ≫ U.ι) (σK zK) = η := by
    have hz := congrArg (fun a : Spec (.of K) ⟶ S ↦ a zK) hσ
    exact hz.trans (S.fromSpecResidueField_apply η _)
  have hts : t i s = σK zK := by
    apply g.injective
    apply U.ι.isOpenEmbedding.injective
    exact hs.trans hσpoint.symm
  obtain ⟨zL, hzL, _⟩ := Scheme.exists_preimage_of_isPullback (H i).2.2.1
    s zK hts
  have : Nonempty (A i) := (hj₀ i).2
  obtain ⟨a₀, ha₀⟩ := (hW₀.1 i).nonempty
  have hamark : (Sigma.ι Y i ≫ ν) (hA i a₀) ∈ W := by
    have hνeq := congrArg (fun k ↦ Sigma.ι A i ≫ k) Hν.w
    have hνeq' : hA i ≫ Sigma.ι Y i ≫ ν = Sigma.ι A i ≫ ν₀ ≫ aX := by
      simpa only [← Category.assoc, Sigma.ι_map] using hνeq
    rw [← Scheme.Hom.comp_apply, hνeq']
    exact hWle ha₀
  refine ⟨⟨hA i a₀, hamark⟩, ?_⟩
  have heq : hA i ≫ j i ≫ p i = j₀ i ≫ q₀ i ≫ hT i := by
    rw [← Category.assoc, (H i).2.2.2.1, Category.assoc, (H i).2.2.2.2]
  change (j i ≫ p i) (hA i a₀) = s
  rw [← Scheme.Hom.comp_apply, heq]
  simpa only [Scheme.Hom.comp_apply] using
    (congrArg (hT i) (Subsingleton.elim ((q₀ i) ((j₀ i) a₀)) zL)).trans hzL

end AlgebraicGeometry

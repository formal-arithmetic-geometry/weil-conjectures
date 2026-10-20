/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
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
public import WeilConjectures.AlgebraicGeometry.Thickening

/-!
# Spreading a marked curve diagram from a generic fibre

Source: Stacks Project, Tag 0GK7, the radicial-extension, spreading and final
shrinking paragraphs. This is the descent argument with its field diagram supplied.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Spread a specified finite diagram over a finite purely inseparable extension of a
component's generic residue field. The supplied open marks a thickening locus that meets
each normalized component densely. The output keeps the supplied number of components
and identifies their generic fibres with the supplied diagram by cartesian squares.

Source: Stacks Project, Tag 0GK7, proof of `lemma-make-good-curves`, from the paragraph
reducing the inseparable extension through the last paragraph.
(blueprint: lem-weil-pbc-spread-marked-curve-diagram)

Proof:
1. Restrict to an affine neighbourhood of η and reduce the base. Its generic local ring
is the residue field, the filtered colimit of the principal localizations outside the
minimal prime. The spectrum of K is a finitely presented finite radicial surjection over
that field. Apply finite radicial model descent to this inverse system. Reduce the model;
its unique point over η still has local ring K. To make a shrinking of this finite
radicial cover come from the original base, remove the closed image of its closed
complement. This produces the reduced affine finite radicial cover required below.
2. Write its generic field as the filtered colimit of principal localizations outside
the minimal prime. Descend the finitely presented objects A i, B i and Spec (L i), the
arrows j i, q i and the components of ν₀, and their commuting equations to a common
localization. The finite-family object, arrow and equality descent lemmas provide a
common stage, with the displayed cartesian squares and compatibility equations.
All the field objects are finitely presented: proper B i is finite type
over a field, its open subscheme A i is Noetherian and quasi-compact, and L i is finite.
3. Descend finiteness and surjectivity of ν₀, finite etaleness of the constant-field
maps, open immersions j i, smoothness of their composites, and smooth properness of q i.
A finite set of stages has a common refinement. Nonempty smooth field fibres give
surjectivity of A i → Spec (L i); spread this too. Local constancy of proper smooth
geometric component counts and upper semicontinuity of proper fibre dimension give
neighbourhoods on each finite etale constant-field model where its proper smooth fibres
are geometrically connected and have dimension at most one. Delete the finite closed
images of their complements from the base.
4. The generic target is Noetherian, so W₀ is quasi-compact. The scheme-over-limit
lemma realizes it on the limit of the target models. Descend this marked open and
its closed-immersion comparison map.
Surjectivity of ν persists and makes that comparison a thickening. Its inverse image
in each A i is nonempty generically by density and nonemptiness of A i. The smooth
map of this open to the constant-field model is open; deleting finite closed images
of its complement makes it surjective.
Empty families are allowed: the descended surjection from the empty scheme forces
X to be empty. All further shrinkings descend through the finite radicial cover
as in step 1. Fibrewise density follows separately from the supplied surjectivity.
-/
theorem exists_spread_marked_curve_diagram
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
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
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
          (∀ i, Surjective (((Sigma.ι Y i ≫ ν) ⁻¹ᵁ W).ι ≫ j i ≫ p i)) ∧
          IsThickening (pullback.snd ν W.ι) := by
  sorry

end AlgebraicGeometry

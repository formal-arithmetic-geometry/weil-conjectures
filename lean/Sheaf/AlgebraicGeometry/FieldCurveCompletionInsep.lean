/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.GlobalSectionsProperVariety
import Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields
import Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion
import Sheaf.AlgebraicGeometry.FiniteSeparableBaseRefinement
import Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper

/-!
# Smooth projective completions after an inseparable field extension

Source: Stacks Project, Varieties, Tag 0GK5,
`lemma-dim-1-projective-completion-after-insep`, assertions (1)-(5)
(blueprint: lem-weil-pbc-field-curve-completion-insep).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A separated finite type scheme of dimension at most one has, after finite purely
inseparable extension, componentwise normalization with smooth projective geometrically
irreducible completions over finite separable constant fields.
Source: Stacks Project, Varieties, Tag 0GK5
(blueprint: lem-weil-pbc-field-curve-completion-insep).

The integral closed immersions `c i` enumerate the reduced irreducible components of
`X_K`: an integral closed subscheme with a given irreducible-component support is exactly
its reduced induced subscheme, equivalently that of `(X_K)_red`. The isomorphisms `e i`
identify `Y i` with their normalizations. Thus the equation for `ν` specifies the full
componentwise normalization map, including its scheme structure.

Proof:
1. For empty X use the trivial field extension and empty family. Otherwise reduce X;
   reduction after scalar extension is unchanged, since the extended nilradical is nil
   (def-weil-pbc-scheme-reduction, lem-weil-pbc-scheme-coproduct-family).
2. Take a dense projective completion and a finite purely inseparable extension making
   its normalization geometrically normal (lem-weil-pbc-curve-projective-dense-completion,
   lem-weil-pbc-normalization-geonormal-insep). Projectivity survives base change and its
   underlying homeomorphism preserves dimension and the dense open
   (lem-pc-projective-base-change, lem-pc-homeo-pure-insep).
3. Decompose the projective normalization into its finitely many integral components;
   geometric normality and dimension at most one imply smoothness and geometric reducedness
   (lem-weil-pbc-normalization-projective-components, lem-weil-pbc-geonormal-dim-one-smooth).
4. The global sections of each component form a finite separable constant field. The
   Stein map has geometrically connected fibres, and refinement to that field preserves
   smoothness and projectivity (lem-pc-h0-proper-variety,
   lem-pc-proper-geometrically-reduced-global-sections-separable,
   lem-weil-pbc-stein-factorization-affine, lem-weil-pbc-finite-separable-base-refinement).
5. After further extension the base-refinement scheme is an open-and-closed subscheme of
   the original scalar extension: the multiplication section of the finite etale base is
   open and closed (lem-exc-etale-coproduct-etale, lem-weil-pbc-etale-scheme-base-change,
   lem-weil-pbc-etale-section-clopen-immersion). It is therefore geometrically normal;
   geometric connectedness implies geometric irreducibility in dimension at most one
   (lem-weil-pbc-geonormal-dim-one-smooth).
6. Restrict each normalized component to the original dense open. Normalization commutes
   with restriction to opens, giving precisely the displayed componentwise normalization
   (lem-weil-pbc-reduced-algebraic-normalization-field-change). Every restriction contains
   its generic point, hence is dense and nonempty.
7. Over the Noetherian field base all displayed schemes are separated finite type and
   hence finitely presented (pqf-lem-lft-fp-locnoeth,
   lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-open-subscheme-noetherian). Nonempty X has a component, proving
   the empty-index equivalence; commutativity follows from the restricted structure maps.
-/
theorem exists_field_curve_completion_insep
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Module.Finite k K ∧ IsPurelyInseparable k K ∧
      ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (hC : ∀ i, IsIntegral (C i))
        (c : ∀ i, C i ⟶ pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Y B : Fin n → Scheme.{u})
        (e : ∀ i, Y i ≅ @Scheme.normalization (C i) (hC i))
        (j : ∀ i, Y i ⟶ B i)
        (L : Fin n → Type u) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
        (q : ∀ i, B i ⟶ Spec (.of (L i)))
        (p : ∀ i, Y i ⟶ Spec (.of K))
        (ν : (∐ Y) ⟶ pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        (∀ i, IsClosedImmersion (c i) ∧
          Set.range (c i) ∈ irreducibleComponents
            (pullback (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) ∧
        Function.Injective (fun i ↦ Set.range (c i)) ∧
        (∀ Z ∈ irreducibleComponents
          (pullback (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
          ∃ i, Set.range (c i) = Z) ∧
        ν = Sigma.desc (fun i ↦ (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ∧
        (∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) ∧
          IsOpenImmersion (j i) ∧ DenseRange (j i) ∧ Nonempty (Y i) ∧
          Smooth (q i) ∧ IsHProjective (q i) ∧ GeometricallyIrreducible (q i) ∧
          topologicalKrullDim (B i) ≤ 1 ∧
          (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i ≫
            pullback.snd (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) = p i ∧
          j i ≫ q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))) = p i ∧
          LocallyOfFinitePresentation (p i) ∧ QuasiCompact (p i) ∧ QuasiSeparated (p i) ∧
          LocallyOfFinitePresentation
            (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap K (L i))))) ∧
        LocallyOfFinitePresentation (Sigma.desc p) ∧
        QuasiCompact (Sigma.desc p) ∧ QuasiSeparated (Sigma.desc p) ∧
        LocallyOfFinitePresentation (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        QuasiCompact (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        QuasiSeparated (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (n = 0 ↔ IsEmpty X) := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Restrict
public import Sheaf.RingTheory.CompleteIntersectionLocalAlgebra
import Sheaf.TraceFormula.LciPointwiseCriterion
import Sheaf.TraceFormula.LciFieldChangeLocal
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import Mathlib.RingTheory.Extension.Presentation.Basic
import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Sheaf.TraceFormula.SyntomicPointwiseLocalModel

/-!
# The fibrewise complete-intersection locus

Source: Stacks Project, Morphisms, Tag 02V3 (lemma-set-points-where-fibres-lci),
with the local-ring convention of Algebra, Tag 00SD
(blueprint: lem-trf-syntomic-locus-base-change).

## Main definitions and statements

* `Scheme.Hom.IsCompleteIntersectionAtFiberPoint`: the local-ring condition on a fibre.
* `Scheme.Hom.fiberCompleteIntersectionLocus`: the subset `V_f` of the source.
* `Scheme.Hom.HasCompleteIntersectionFibres`: the condition on all local rings of all fibres.
* `syntomic_locus_base_change`: arbitrary base change and the largest syntomic source open.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The local ring at `y` of the scheme-theoretic fibre over `s` is a complete-intersection
local algebra over `κ(s)`. Scalars are induced by the fibre's canonical structure map,
the global sections of `Spec κ(s)`, and the germ at `y`.
Source: Stacks Project, Morphisms, Tag 02V3, and Algebra, Tag 00SD
(blueprint: lem-trf-syntomic-locus-base-change). -/
def Scheme.Hom.IsCompleteIntersectionAtFiberPoint {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (y : f.fiber s) : Prop :=
  @Algebra.IsCompleteIntersectionLocalAlgebra (S.residueField s)
    ((f.fiber s).presheaf.stalk y) _ _
    (((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      (f.fiberToSpecResidueField s).appLE ⊤ ⊤ le_top ≫
      (f.fiber s).presheaf.germ ⊤ y trivial).hom.toAlgebra)

/-- The points `x` whose local ring in the fibre over `f x` is a complete intersection
over `κ(f x)`. The canonical point `f.asFiber x` is provided by the fibre homeomorphism.
Source: Stacks Project, Morphisms, Tag 02V3 (lemma-set-points-where-fibres-lci)
(blueprint: lem-trf-syntomic-locus-base-change). -/
def Scheme.Hom.fiberCompleteIntersectionLocus {X S : Scheme.{u}} (f : X ⟶ S) : Set X :=
  {x | f.IsCompleteIntersectionAtFiberPoint (f x) (f.asFiber x)}

/-- Every local ring of every fibre is a complete-intersection local algebra over the
residue field of the base point. Empty fibres impose no condition.
Source: Stacks Project, Morphisms, Tag 02V3 and Tag 01UE
(blueprint: lem-trf-syntomic-locus-base-change). -/
def Scheme.Hom.HasCompleteIntersectionFibres {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (s : S) (y : f.fiber s), f.IsCompleteIntersectionAtFiberPoint s y

/-- Formation of the fibrewise complete-intersection locus commutes with arbitrary base
change for locally finite type morphisms. If the morphism is also flat and locally of
finite presentation, this subset is an open, and is the largest source open on which the
restriction is flat, locally of finite presentation, and has complete-intersection fibres.

Source: Stacks Project, Morphisms, Tag 02V3 (lemma-set-points-where-fibres-lci),
including its last assertion, using Algebra Tag 00SI and Morphisms Tag 01UE
(blueprint: lem-trf-syntomic-locus-base-change).

Proof:
1. Around a point over `s`, choose finite-type affine charts `Spec B → Spec A` by
   def-weil-finite-type-morphism. The fibre chart is `Spec (B ⊗[A] κ(s))` by
   lem-weil-pbc-open-preimage-fibre-product and lem-weil-pbc-fibre-product-affine-spectra.
   The images of the finite algebra generators of `B` generate this fibre algebra.
2. For any base change, lem-weil-pbc-fibre-of-base-change identifies the new fibre with
   the old fibre extended from `κ(s)` to `κ(s')`. On the affine charts from step 1,
   lem-weil-pbc-affine-open-stalk-localization identifies the fibre local rings with
   localizations at corresponding primes. Apply lem-trf-lci-field-change-local to obtain
   pointwise equivalence of the local-ring conditions, hence equality of the two loci.
3. Now suppose flatness and local finite presentation. At a point of the locus,
   lem-trf-syntomic-pointwise-local-model gives an affine neighbourhood presented as a
   relative global complete intersection over an affine neighbourhood of the base point.
4. By lem-weil-pbc-presentation-base-change, each fibre of that chart has the same numbers
   of generators and equations. The definition def-weil-pbc-relative-global-complete-intersection
   says it is zero or has dimension the number of variables minus the number of equations.
   Thus it is a global complete intersection by def-weil-pbc-complete-intersection-over-field.
   The single principal open `D(1)` makes it a local complete intersection, and
   lem-trf-lci-pointwise-criterion makes every fibre local ring a complete intersection.
   Open immersion stalks are unchanged, so the whole chart lies in the locus. These charts
   cover the locus, proving openness.
5. For a source open `H`, its fibres are the corresponding opens in the original fibres by
   lem-weil-pbc-open-preimage-fibre-product, with the same local rings. Hence its fibre
   condition holds exactly when `H` lies in the locus. Flatness restricts since the local
   maps are unchanged. Local finite presentation restricts by passing to principal affine
   neighbourhoods: localizing `B = A[t]/(h)` at `b` adds one generator and the relation
   `bu - 1`. Apply these facts to the locus itself, and then to any competing source open,
   obtaining its three properties and largestness. Empty fibres and the empty source have
   no local rings to test, so the same argument includes them.
-/
theorem syntomic_locus_base_change {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    (∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      (pullback.snd f g).fiberCompleteIntersectionLocus =
        (pullback.fst f g) ⁻¹' f.fiberCompleteIntersectionLocus) ∧
    (Flat f → LocallyOfFinitePresentation f →
      ∃ U : X.Opens, (U : Set X) = f.fiberCompleteIntersectionLocus ∧
        IsGreatest {V : X.Opens | Flat (V.ι ≫ f) ∧
          LocallyOfFinitePresentation (V.ι ≫ f) ∧
          (V.ι ≫ f).HasCompleteIntersectionFibres} U) := by
  sorry

end AlgebraicGeometry

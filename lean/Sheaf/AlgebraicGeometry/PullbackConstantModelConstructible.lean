/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CondensedConstantConstructibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Pullback of constructible modules with finite constant scalar models

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-proper-base-change-unbounded-pullback.proof.md`, paragraph
"Constructible complexes"; Stacks Project, Tag 054I; Bhatt--Scholze,
The pro-etale topology for schemes, proof of Lemma 6.3.8
(blueprint: lem-sfb-pullback-constant-model-constructible).

The assertion retains each given scalar module and the whole given covering family.
The pulled-back stratification and covers are the existing canonical constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pull back the given constructible locally closed subschemes, keeping their scheme
structures. The input uses the recorded finite locally closed stratification interface;
constructibility is supplied separately. The output includes constructibility, local
closedness, disjointness and the covering property, and has the same finite index set.
Its domains are `pullback (S.immersion a) g`, its immersions are `pullback.snd`, and its
stratum subsets are `g ⁻¹' S.stratum a`.
Source: blueprint pullback proof, "Constructible complexes", and Stacks 054I
(blueprint: lem-sfb-pullback-constant-model-constructible). -/
def constantModelPullbackStratification {Y Y' : Scheme.{u}}
    (S : Y.FiniteLocallyClosedStratification)
    (hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) (g : Y' ⟶ Y) :
    Y'.Stratification :=
  Scheme.Stratification.pullback
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      isConstructible_stratum := hS
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion } g

/-- The two clauses of preservation: constructibility, and the same finite scalar models
on the base changes of any specified witnessing stratification and covers. The scalar
modules are quantified before pullback and occur unchanged on the right of each output
isomorphism. `pullback₂` retains the cover's index type and has members
`U_i ×_{Y_a} (Y_a ×_Y Y')`, with the second projection as covering map.
Source: blueprint pullback proof, "Constructible complexes", expanded local-model argument
(blueprint: lem-sfb-pullback-constant-model-constructible). -/
def ConstantModelPullbackStatement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : Prop :=
  ∀ {Y Y' : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] (g : Y' ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
    IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((CondensedRing.upperStar Λ g).obj M) ∧
      ∀ (S : Y.FiniteLocallyClosedStratification)
        (hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
        (U : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
        (P : ∀ (a : Fin S.n) (_ : (U a).I₀), Mod Ab.{u + 1} (scalarRingObj Λ)),
        (∀ (a : Fin S.n) (i : (U a).I₀),
          Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i)) →
        (∀ (a : Fin S.n) (i : (U a).I₀),
          Nonempty ((CondensedRing.upperStar Λ ((U a).f i)).obj
              ((CondensedRing.upperStar Λ (S.immersion a)).obj M) ≅
            (finiteConstantScalarExtension Λ ((U a).X i)).obj (P a i))) →
        ∀ (a : Fin S.n) (i : (U a).I₀),
          Nonempty ((CondensedRing.upperStar Λ
              (((U a).pullback₂ (pullback.fst (S.immersion a) g)).f i)).obj
                ((CondensedRing.upperStar Λ
                  ((constantModelPullbackStratification S hS g).immersion a)).obj
                    ((CondensedRing.upperStar Λ g).obj M)) ≅
            (finiteConstantScalarExtension Λ
              (((U a).pullback₂ (pullback.fst (S.immersion a) g)).X i)).obj (P a i))

/-- Inverse image preserves constructible modules and their specified constant models for
all the admissible coefficients of the node. Finite discrete rings are represented by
constant ring sheaves (equivalently continuous maps to the finite discrete ring).
The last alternative is specifically the finite-subextension-valued condensed algebraic
closure, rather than all continuous algebraic-closure-valued functions.

Source: blueprint main-20261015, proper-base-change-unbounded pullback proof,
"Constructible complexes"; Stacks 054I; Bhatt--Scholze, proof of Lemma 6.3.8
(blueprint: lem-sfb-pullback-constant-model-constructible).

Proof plan:
1. Pull back each locally closed immersion using
lemma-constructible-pullback-stratification. Apply lem-pur-scheme-constructible-preimage
separately to its constructible image. This is the canonical stratification above.
2. Apply clause 1 of det-pe-topos-functoriality-inverse-image to each map from a new
stratum to the old one. The whole specified family base changes to a cover; the map
between strata need not itself be weakly etale.
3. Choose a finite scalar presentation of each given P. The exact constant-sheaf
functor and right-exact scalar extension turn this particular presentation into a
cokernel of the same scalar matrix on U, as in det-def-sfb-constructible-local-model.
By sk-prop-sfb-cartesian-coefficients, inverse image is exact along the coefficient
comparison. It preserves the regular coefficient module, finite sums and this cokernel;
finite-sum preservation also follows from the adjunction of
sk-def-sfb-module-pushforward-pullback.
4. Naturality of the point-pullback comparison of sk-def-sfb-coefficient-morphisms on
each scalar section, and sk-def-sfb-pulled-back-coefficients, identify every matrix entry
with that same scalar after pullback. The cokernel on the new cover member is therefore
extension of the original P. The composition isomorphism of
sk-def-sfb-module-pushforward-pullback identifies the two composite restrictions.
5. The pulled-back finite constructible locally closed stratification, its covers and
these models witness sk-def-sfb-constructible on the qcqs target scheme. -/
theorem pullback_constantModelConstructible (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj L)]
    (hL :
      (∃ A : CommRingCat.{u + 1}, Finite A ∧
        (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
        Nonempty (L ≅ (constantSheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}).obj
          ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A))) ∨
      L = Profinite.padicIntCondensedRing ℓ ∨
      L = Profinite.padicCondensedRing ℓ ∨
      (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), FiniteDimensional ℚ_[ℓ] E ∧
        (L = Profinite.padicIntegersCondensedRing ℓ E ∨
          L = Profinite.padicSubfieldCondensedRing ℓ E)) ∨
      L = Profinite.padicAlgClCondensedRing ℓ) :
    ConstantModelPullbackStatement ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj L) := by
  sorry

end AlgebraicGeometry.ProEtale

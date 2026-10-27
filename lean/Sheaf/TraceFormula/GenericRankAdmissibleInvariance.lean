/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.Sober
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Sheaf.TraceFormula.FlatFibreFreeNeighbourhood
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus

/-!
# Generic fibre ranks and admissible invariance

Source: Stacks Project, flat.tex, Tag 0811, `lemma-flatten-module-pre`, first two proof
paragraphs; Tag 080Y, `remark-successive-blowups`
(blueprint: lem-trf-generic-rank-admissible-invariance).

The auxiliary rank is precisely the dimension of the residue-field tensor of a stalk.
The finite-chain relation records each actual centre and each successive quotient.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The dimension of the residue-field tensor of a module stalk at `x`.
Source: Stacks Project, Tag 0811, rank paragraph
(blueprint: lem-trf-generic-rank-admissible-invariance). -/
def moduleResidueRank {X : Scheme.{u}} (F : X.Modules) (x : X) : ℕ :=
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  Module.finrank (X.residueField x)
    (TensorProduct (X.presheaf.stalk x) (X.residueField x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F))

/-- Finite sequences of admissible blowups and their successive module strict transforms.
The indices record the length, final family, final module and maps to the original family.
Each successor retains its centre `B.I`. Its module is the exact cokernel used by
`moduleStrictTransform`, written using `moduleStrictTransformRestriction` so that this
relation does not assume quasi-coherence of intermediate transforms: that is a conclusion
of the theorem. No arbitrary module, comparison morphism or quotient is supplied.
Source: Stacks Project, Tag 080Y; Divisors, Tag 080D (1)
(blueprint: lem-trf-generic-rank-admissible-invariance). -/
inductive AdmissibleModuleTransformChain {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) (F : X.Modules) :
    ℕ → {Y T : Scheme.{u}} → (Y ⟶ T) → Y.Modules → (T ⟶ S) → (Y ⟶ X) → Prop
  | nil : AdmissibleModuleTransformChain f U F 0 f F (𝟙 S) (𝟙 X)
  | snoc {n : ℕ} {Y T : Scheme.{u}} {q : Y ⟶ T} {G : Y.Modules}
      {b : T ⟶ S} {p : Y ⟶ X}
      (chain : AdmissibleModuleTransformChain f U F n q G b p)
      (B : IsAdmissible T (b ⁻¹ᵁ U)) :
      AdmissibleModuleTransformChain f U F (n + 1)
        (pullback.snd q B.I.blowupMap)
        (cokernel (kernel.ι (moduleStrictTransformRestriction q B.I G)))
        (B.I.blowupMap ≫ b) (pullback.fst q B.I.blowupMap ≫ p)

/-- Generic ranks are locally constant with finite quasi-compact clopen strata, and all
flattening hypotheses and these ranks are preserved by finite admissible sequences.
The chosen `ξ s` is the unique generic point of the integral fibre; quantifying over
such a choice avoids imposing a choice of representative on the statement.
The hypothesis `hflat` spells out flatness of the stalk `F_{ξ_u}` over `𝒪_{S,u}` along
the stalk map of `f` (relative flatness at a point, def-pc-scheme-module-flat-over).

Source: Stacks Project, Tag 0811, first two proof paragraphs, and Tag 080Y
(blueprint: lem-trf-generic-rank-admissible-invariance).

Proof:
1. The integral fibre is nonempty and irreducible (def-pc-integral-scheme), and its
   generic point exists uniquely (lem-sc-scheme-sober). Its generic local ring is a
   field by lem-sc-integral-function-field-affine-fraction. Every module over that
   field is flat (lem-weil-pbc-module-over-field-flat). Finite presentation over U
   and relative stalk flatness therefore give a finite free neighbourhood by
   lem-trf-flat-fibre-free-neighbourhood, using qcqs-morphism-permanence for the
   restricted family. Tensoring its stalk with the residue field identifies the
   free rank with moduleResidueRank, also in rank zero.
2. The family is open by lem-weil-pbc-flat-lfp-open. The image of each such free
   neighbourhood is open in U. Every fibre meeting it has its generic point in it,
   since that fibre is integral. The same trivialization computes its generic rank,
   proving local constancy on the base.
3. Each rank level is open and closed in U. Compactness of U gives finitely many
   nonempty levels, and each closed level is compact. The levels are the required
   disjoint partition, including the empty partition when U is empty.
4. Affineness, flatness and finite presentation survive arbitrary base change by
   lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-flat-morphism-base-change
   and lem-weil-pbc-qcqs-morphism-permanence. The fibre identification from
   lem-weil-pbc-fibre-of-base-change and pullback associativity show that every
   field extension of a new fibre is a field extension of an original fibre,
   proving geometric integrality.
5. For one admissible blowup use lem-trf-module-admissible-blowup-calculus, its
   permanence clause: the base is qcqs, the transform is quasi-coherent finite type,
   and its quotient is an isomorphism over the inverse image of U. By
   lemma-nagata-admissible-blowup-over-open the base map there is an isomorphism.
   This identifies finite presentation, generic stalks and residue fields with the
   original ones. Restrict the free neighbourhoods to obtain the same ranks.
6. Induct on the chain. The empty chain gives the original family and module. Apply
   step 5 to each retained centre, and step 4 to the new family. Compose the
   identifications over U. This proves every invariance assertion for every finite
   chain, and hence for every prefix of a finite sequence as well.
-/
theorem generic_rank_admissible_invariance
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsAffineHom f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyIntegral f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hfp : ((restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (ξ : (s : U) → f.fiber s.val)
    (hξ : ∀ s : U, IsGenericPoint (ξ s) Set.univ)
    (hflat : ∀ s : U,
      letI x := f.fiberι s.val (ξ s)
      letI : Module (S.presheaf.stalk (f x))
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :=
        Module.compHom _ (f.stalkMap x).hom
      Module.Flat (S.presheaf.stalk (f x))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) :
    ∃ r : U → ℕ,
      (∀ s : U, r s = moduleResidueRank F (f.fiberι s.val (ξ s))) ∧
      (∀ s : U, ∃ W : X.Opens, W ≤ f ⁻¹ᵁ U ∧ f.fiberι s.val (ξ s) ∈ W ∧
        Nonempty (((restrictFunctor W.ι).obj F) ≅
          (restrictFunctor W.ι).obj
            (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r s)))))) ∧
      IsLocallyConstant r ∧ Set.Finite (Set.range r) ∧
      (∀ i ∈ Set.range r, IsClopen {s : U | r s = i} ∧
        IsCompact {s : U | r s = i}) ∧
      (∀ (n : ℕ) {Y T : Scheme.{u}} (q : Y ⟶ T) (G : Y.Modules)
        (b : T ⟶ S) (p : Y ⟶ X),
        AdmissibleModuleTransformChain f U F n q G b p →
        CompactSpace T ∧ QuasiSeparatedSpace T ∧
        IsAffineHom q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧
        QuasiCompact q ∧ QuasiSeparated q ∧ GeometricallyIntegral q ∧
        G.IsQuasicoherent ∧ G.IsFiniteType ∧
        IsIso (b ∣_ U) ∧
        ((restrictFunctor (q ⁻¹ᵁ (b ⁻¹ᵁ U)).ι).obj G).IsFinitePresentation ∧
        Nonempty (((restrictFunctor (q ⁻¹ᵁ (b ⁻¹ᵁ U)).ι).obj G) ≅
          (restrictFunctor (q ⁻¹ᵁ (b ⁻¹ᵁ U)).ι).obj ((tensorPullback p).obj F)) ∧
        (∀ (t : T) (ht : b t ∈ U) (η : q.fiber t),
          IsGenericPoint η Set.univ →
          moduleResidueRank G (q.fiberι t η) = r ⟨b t, ht⟩ ∧
          ∃ W : Y.Opens, W ≤ q ⁻¹ᵁ (b ⁻¹ᵁ U) ∧ q.fiberι t η ∈ W ∧
            Nonempty (((restrictFunctor W.ι).obj G) ≅
              (restrictFunctor W.ι).obj
                (SheafOfModules.free (R := Y.ringCatSheaf)
                  (ULift.{u} (Fin (r ⟨b t, ht⟩))))))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

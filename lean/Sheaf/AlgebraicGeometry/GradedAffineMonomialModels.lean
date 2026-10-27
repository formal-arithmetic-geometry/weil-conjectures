/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.GradedSheafGeneration
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.TensorProduct.Defs

/-! # Finite affine monomial models for graded sheaf modules

Source: Stacks Project, Algebra, Tag 00K0, lemma-graded-module-fg;
Schemes, Tags 01HV and 01IA (blueprint: lem-sfb-graded-affine-monomial-models).

Finite words enumerate the commutative monomials, with harmless repetitions.
The total section modules are algebraic direct sums, without commuting sheaf sums
with sections. The fibre comparison uses the actual module stalk and transports
scalars along the canonical affine residue-field identification.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped DirectSum

namespace AlgebraicGeometry

/-- The product of a word of degree-one sections; the empty word is the structural unit.
Source: Stacks, Algebra, Tag 00K0 (blueprint: lem-sfb-graded-affine-monomial-models). -/
noncomputable def GradedSheafAlgebra.sectionMonomial {S : Scheme.{u}} {B : ℕ → S.Modules}
    (A : GradedSheafAlgebra B) (U : S.Opens) {r : ℕ}
    (x : Fin r → (B 1).val.obj (op U)) :
    (d : ℕ) → (Fin d → Fin r) → (B d).val.obj (op U)
  | 0, _ => A.unit.val.app (op U) (1 : Γ(S, U))
  | d + 1, w => Eq.mp (congrArg (fun n : ℕ ↦ ↥((B n).val.obj (op U))) (Nat.add_comm 1 d))
      (A.mul 1 d U (x (w 0)) (A.sectionMonomial U x d (fun k ↦ w k.succ)))

/-- The finite index set of degree-d monomials times homogeneous module generators.
Source: Stacks, Algebra, Tag 00K0 (blueprint: lem-sfb-graded-affine-monomial-models). -/
def gradedModuleMonomialIndex (r t : ℕ) (b : Fin t → ℕ) (d : ℕ) :=
  Σ j : Fin t, Σ k : Fin (d + 1), {_w : Fin k.val → Fin r // k.val + b j = d}

/-- Multiply a homogeneous module generator by a word of the required complementary degree.
Source: Stacks, Algebra, Tag 00K0 (blueprint: lem-sfb-graded-affine-monomial-models). -/
noncomputable def GradedSheafModule.sectionMonomial {S : Scheme.{u}} {B L : ℕ → S.Modules}
    {A : GradedSheafAlgebra B} (M : GradedSheafModule A L) (U : S.Opens)
    {r t : ℕ} (x : Fin r → (B 1).val.obj (op U)) (b : Fin t → ℕ)
    (e : (j : Fin t) → (L (b j)).val.obj (op U)) (d : ℕ)
    (q : gradedModuleMonomialIndex r t b d) : (L d).val.obj (op U) :=
  Eq.mp (congrArg (fun n : ℕ ↦ ↥((L n).val.obj (op U))) q.2.2.property)
    (M.act q.2.1.val (b q.1) U (A.sectionMonomial U x q.2.1.val q.2.2.val) (e q.1))

/-- A prescribed family on U generates the restriction to U as a sheaf.
This uses the recorded GeneratingSections notion; evaluation is at the terminal object
of the over-site, so the family is the specified family of sections on U.
Source: Stacks, Modules, Tag 01B4 (blueprint: lem-sfb-graded-affine-monomial-models). -/
def sectionsGenerateOn {S : Scheme.{u}} (F : S.Modules) (U : S.Opens)
    {I : Type u} (s : I → F.val.obj (op U)) : Prop :=
  ∃ g : SheafOfModules.GeneratingSections (F.over U),
    ∃ v : g.I ≃ I, ∀ i : g.I, (g.s i).1 (op (Over.mk (𝟙 U))) = s (v i)

/-- The canonical residue-field isomorphism from a point in an affine open to its prime.
It is the affine open immersion's residue map followed by the Spec residue-field iso.
Source: Stacks, Schemes, Tag 01HV (blueprint: lem-sfb-graded-affine-monomial-models). -/
noncomputable def affineMonomialResidueIso {S : Scheme.{u}} (U : S.Opens)
    (hU : IsAffineOpen U) (s : U) :
    S.residueField s ≅ CommRingCat.of (hU.primeIdealOf s).asIdeal.ResidueField :=
  S.residueFieldCongr (hU.fromSpec_primeIdealOf s).symm ≪≫
    asIso (hU.fromSpec.residueFieldMap (hU.primeIdealOf s)) ≪≫
      Scheme.Spec.residueFieldIso Γ(S, U) (hU.primeIdealOf s)

/-- The algebraic direct sum of homogeneous section modules, with its canonical additive
and base-module structures. This is not the sections of a sheaf direct sum.
Source: Stacks, Algebra, Tag 00K0 (blueprint: lem-sfb-graded-affine-monomial-models). -/
abbrev gradedAffineSectionSum {S : Scheme.{u}} (F : ℕ → S.Modules) (U : S.Opens) :=
  ⨁ d : ℕ, (F d).val.obj (op U)

/-- Finite affine models with the same monomial generators for sheaves and sections,
the induced algebra and module structures on their algebraic direct sums, and the
actual stalk-fibre comparison. All covers and generating lists may be empty.
Source: Stacks, Algebra, Tag 00K0; Schemes, Tags 01HV, 01IA, 01IC and 01IT;
Properties, Tag 01PB (blueprint: lem-sfb-graded-affine-monomial-models).

Proof:
1. At each point choose homogeneous generators using def-sfb-graded-sheaf-generation.
   Refine their neighbourhood to an affine open by lem-weil-pbc-affine-opens-basis.
   Restriction preserves their local spanning condition. Quasi-compactness selects a
   finite cover, allowing the empty cover when S is empty. Its section rings are
   Noetherian by pqf-lem-affine-open-locnoeth.
2. Coherence of B_1 includes finite type. Restriction preserves finite type and
   quasi-coherence by lem-weil-pbc-module-restriction-open-immersion-colimits.
   On each selected affine open, lem-weil-pbc-affine-finite-type-generating-sections
   supplies finitely many degree-one sections x_k on that same open.
3. Induct on d. The unit is the degree-zero monomial. Degree-one generation writes
   each section locally as a finite sum of products from degrees one and d.
   Expand the degree-one factors in the x_k and the degree-d factors by induction;
   intersect the finitely many neighbourhoods at the point in question. Bilinearity,
   associativity and commutativity give degree-(d+1) monomials. For a section of L_d,
   expand its homogeneous coefficients in the same way: x^alpha e_j has degree d
   exactly when |alpha|+b_j=d. No generator of degree greater than d contributes.
4. Words of a fixed length over Fin r form a finite type. For module monomials,
   the complementary degree is at most d, so gradedModuleMonomialIndex is finite.
   The free module sheaf on either finite family is quasi-coherent by
   lem-weil-pbc-spec-tilde-free-module, and its target is quasi-coherent by hypothesis.
   The local spanning from step 3 is precisely surjectivity as sheaves, expressed by
   def-weil-pbc-generating-sections. Apply clause (3) of
   lem-weil-pbc-quasi-coherent-module-cokernel-image to its local image. Its affine
   sections equal the image of the free module of sections. Thus the identical lists
   span the section modules; in particular every L_d(U) is finite over O(U).
5. Extend the given graded products and actions by bilinearity to algebraic direct
   sums. The graded laws supply the ring, algebra and module laws. Their additive
   structures and base scalar action are the canonical ones. Each direct-sum element
   has finitely many homogeneous components. Apply step 4 to those components to
   obtain algebra generation by x_k and module generation by e_j.
6. By lem-sbc-affine-module-germ-localization the actual germ identifies L_{d,s}
   with the localization of L_d(U) at its prime. The ring-germ identification is
   lem-weil-pbc-affine-open-stalk-localization, and the residue identification is
   lem-weil-pbc-spec-residue-field-identification composed with the open immersion.
   The tensor map sends (m/t) tensor c to m tensor (t-bar)^(-1)c. Equality of
   fractions and balancing hold because t-bar is invertible. Its inverse sends
   m tensor c to (m/1) tensor c. The composites are identities on pure tensors,
   which generate by def-weil-pbc-module-tensor-product. This is linear over the
   residue field. Extension-of-scalars puts the scalar tensor factor first, using
   the canonical commutativity isomorphism. Empty lists and zero modules satisfy
   the same formulas; for r=0 only the empty word exists in degree zero. -/
theorem graded_affine_monomial_models
    (S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (B L : ℕ → S.Modules) (A : GradedSheafAlgebra B) (M : GradedSheafModule A L)
    (hB : ∀ d : ℕ, (B d).IsQuasicoherent)
    (hL : ∀ d : ℕ, (L d).IsQuasicoherent)
    (hzero : IsIso A.unit) (hone : RingedSpace.IsCoherent S.toRingedSpace (B 1))
    (hgen : A.IsGeneratedInDegreeOne) (hM : M.IsLocallyFinitelyGenerated) :
    ∃ (n : ℕ) (U : Fin n → S.Opens) (hU : ∀ i : Fin n, IsAffineOpen (U i)),
      (⨆ i : Fin n, U i) = ⊤ ∧
      (∀ i : Fin n, IsNoetherianRing Γ(S, U i)) ∧
      ∃ (r t : Fin n → ℕ)
        (x : (i : Fin n) → Fin (r i) → (B 1).val.obj (op (U i)))
        (b : (i : Fin n) → Fin (t i) → ℕ)
        (e : (i : Fin n) → (j : Fin (t i)) → (L (b i j)).val.obj (op (U i))),
        ∀ i : Fin n,
          (∀ d : ℕ,
            sectionsGenerateOn (B d) (U i)
              (fun w : ULift.{u} (Fin d → Fin (r i)) ↦
                A.sectionMonomial (U i) (x i) d w.down) ∧
            sectionsGenerateOn (L d) (U i)
              (fun q : ULift.{u} (gradedModuleMonomialIndex (r i) (t i) (b i) d) ↦
                M.sectionMonomial (U i) (x i) (b i) (e i) d q.down) ∧
            Submodule.span Γ(S, U i)
              (Set.range (A.sectionMonomial (U i) (x i) d)) = ⊤ ∧
            Submodule.span Γ(S, U i)
              (Set.range (M.sectionMonomial (U i) (x i) (b i) (e i) d)) = ⊤ ∧
            Module.Finite Γ(S, U i) ((L d).val.obj (op (U i)))) ∧
          (∃ (c : CommRing (gradedAffineSectionSum B (U i)))
            (a : @Algebra Γ(S, U i) (gradedAffineSectionSum B (U i))
              inferInstance c.toSemiring)
            (m : @Module (gradedAffineSectionSum B (U i)) (gradedAffineSectionSum L (U i))
              c.toSemiring inferInstance),
            c.toAddCommGroup = inferInstanceAs (AddCommGroup (gradedAffineSectionSum B (U i))) ∧
            a.toSMul = inferInstanceAs (SMul Γ(S, U i) (gradedAffineSectionSum B (U i))) ∧
            (∀ (k l : ℕ) (v : (B k).val.obj (op (U i)))
              (w : (B l).val.obj (op (U i))),
              c.mul (DirectSum.of _ k v) (DirectSum.of _ l w) =
                DirectSum.of _ (k + l) (A.mul k l (U i) v w)) ∧
            (∀ z : Γ(S, U i),
              @algebraMap Γ(S, U i) (gradedAffineSectionSum B (U i))
                inferInstance c.toSemiring a z =
                  DirectSum.of _ 0 (A.unit.val.app (op (U i)) z)) ∧
            (∀ (k l : ℕ) (v : (B k).val.obj (op (U i)))
              (w : (L l).val.obj (op (U i))),
              @SMul.smul _ _ m.toSMul (DirectSum.of _ k v) (DirectSum.of _ l w) =
                DirectSum.of _ (k + l) (M.act k l (U i) v w)) ∧
            @Algebra.adjoin Γ(S, U i) (gradedAffineSectionSum B (U i))
              inferInstance c.toSemiring a
              (Set.range (fun k : Fin (r i) ↦ DirectSum.of _ 1 (x i k))) = ⊤ ∧
            @Submodule.span (gradedAffineSectionSum B (U i)) (gradedAffineSectionSum L (U i))
              c.toSemiring inferInstance m
              (Set.range (fun j : Fin (t i) ↦ DirectSum.of _ (b i j) (e i j))) = ⊤) ∧
          ∀ (d : ℕ) (s : U i),
            Nonempty
              ((ModuleCat.extendScalars (S.residue s).hom).obj
                  ((RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj (L d)) ≅
                (ModuleCat.restrictScalars (affineMonomialResidueIso (U i) (hU i) s).hom.hom).obj
                  ((ModuleCat.extendScalars
                    (algebraMap Γ(S, U i) ((hU i).primeIdealOf s).asIdeal.ResidueField)).obj
                      ((L d).val.obj (op (U i))))) := by
  sorry

end AlgebraicGeometry

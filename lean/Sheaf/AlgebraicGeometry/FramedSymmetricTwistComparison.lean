module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.ModuleSheafificationRestriction
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Framed symmetric algebra comparison for an invertible twist

Source: Stacks Project, Constructions, Tag 02NC, lemma-twisting-and-proj,
local trivialization calculation; Modules, Section 01CF
(blueprint: lem-trf-framed-symmetric-twist-comparison).

The conclusion is bundled as its sectionwise maps and equations. The maps are defined
on every subopen, not only affines. Naturality in both directions makes them isomorphisms
of the restricted sheaves. The symmetric degree on arbitrary opens is tested locally
on the canonical affine-basis grading, including sections which are only locally sums
of degree-k monomials.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The local section e tensor-power n, with zeroth power the structure-sheaf unit.
This is the sectionwise version of the existing module tensor power, formed using the
canonical pure-tensor map, with no choice of a module or a section.
Source: Stacks Project, Constructions, Tag 02NC, trivializing the invertible module
(blueprint: lem-trf-framed-symmetric-twist-comparison). -/
noncomputable def framedTensorPowerSection {S : Scheme.{u}} {L : S.Modules}
    {U : S.Opens} (e : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => Scheme.Modules.unitSectionsEquiv U 1
  | n + 1 => Scheme.Modules.tmulSection e (framedTensorPowerSection e n)

/-- Membership in the symmetric degree-k subsheaf, expressed on the existing affine
basis: near every point, the section is the canonical image of a degree-k symmetric
polynomial. This is the local homogeneous-section condition used in the comparison,
not the generally smaller image of the degree-k presheaf over a nonaffine open.
Source: Stacks Project, Modules, Tag 01CG; Constructions, Tag 02NC
(blueprint: lem-trf-framed-symmetric-twist-comparison). -/
def IsLocallySymmetricHomogeneous {S : Scheme.{u}} (E : S.Modules) (k : ℕ)
    (U : S.Opens) (a : (SymmetricAlgebraSheaf.algebra E).right.obj.obj (op U)) : Prop :=
  ∀ x : S, x ∈ U → ∃ (V : S.affineOpens) (h : V.1 ≤ U),
    x ∈ V.1 ∧ ∃ b : SymmetricAlgebraSheaf.sections E (op V.1),
      b ∈ (SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1)).range ^ k ∧
      (SymmetricAlgebraSheaf.algebra E).right.obj.map (homOfLE h).op a =
        SymmetricAlgebraSheaf.sectionMap E (op V.1) b

/-- The complete sectionwise conclusion of the framed twist comparison. Linear and ring
equivalences are the actual maps on all subopens; the equations specify the canonical
maps, their inverses, grading, uniqueness, restriction, frame changes and unit normalization.
Source: Stacks Project, Constructions, Tag 02NC, local trivialization calculation
(blueprint: lem-trf-framed-symmetric-twist-comparison). -/
structure FramedSymmetricTwistComparison {S : Scheme.{u}} (E L : S.Modules) where
  /-- Tensoring with the nth power of the frame, on every subopen. -/
  tau : ∀ (n : ℕ) (U : S.Opens) (e : Γ(L, U)), Scheme.Modules.IsFreeGenerator e →
    ∀ (V : S.Opens), V ≤ U → Γ(E, V) ≃ₗ[Γ(S, V)] Γ(E ⊗ L.tensorPow n, V)
  /-- The symmetric algebra isomorphism, on every subopen. -/
  beta : ∀ (n : ℕ) (U : S.Opens) (e : Γ(L, U)), Scheme.Modules.IsFreeGenerator e →
    ∀ (V : S.Opens), V ≤ U →
      (SymmetricAlgebraSheaf.algebra E).right.obj.obj (op V) ≃+*
        (SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).right.obj.obj (op V)
  /-- The prescribed pure-tensor formula. -/
  tau_apply : ∀ n U e he V h v,
    tau n U e he V h v = Scheme.Modules.tmulSection v
      (framedTensorPowerSection (L.presheaf.map (homOfLE h).op e) n)
  /-- The coefficient contraction is the inverse, including n = 0. -/
  tau_inverse : ∀ n U e he V h (v : Γ(E, V)) (a : Γ(S, V)),
    (tau n U e he V h).symm
      (Scheme.Modules.tmulSection v
        (a • framedTensorPowerSection (L.presheaf.map (homOfLE h).op e) n)) = a • v
  /-- Both module maps commute with all smaller-open restrictions. -/
  tau_natural : ∀ n U e he V h W (i : W ≤ V) v,
    (E ⊗ L.tensorPow n).presheaf.map (homOfLE i).op (tau n U e he V h v) =
      tau n U e he W (i.trans h) (E.presheaf.map (homOfLE i).op v)
  tau_inverse_natural : ∀ n U e he V h W (i : W ≤ V) v,
    E.presheaf.map (homOfLE i).op ((tau n U e he V h).symm v) =
      (tau n U e he W (i.trans h)).symm
        ((E ⊗ L.tensorPow n).presheaf.map (homOfLE i).op v)
  /-- The algebra maps fix the structural scalars. -/
  beta_scalar : ∀ n U e he V h (r : Γ(S, V)),
    beta n U e he V h ((SymmetricAlgebraSheaf.algebra E).hom.hom.app (op V) r) =
      (SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).hom.hom.app (op V) r
  /-- The forward map extends tau on the degree-one inclusion. -/
  beta_generator : ∀ n U e he V h (v : Γ(E, V)),
    beta n U e he V h ((SymmetricAlgebraSheaf.inclusion E).val.app (op V) v) =
      (SymmetricAlgebraSheaf.inclusion (E ⊗ L.tensorPow n)).val.app (op V)
        (tau n U e he V h v)
  /-- The inverse map extends the inverse coefficient contraction. -/
  beta_inverse_generator : ∀ n U e he V h (v : Γ(E ⊗ L.tensorPow n, V)),
    (beta n U e he V h).symm
      ((SymmetricAlgebraSheaf.inclusion (E ⊗ L.tensorPow n)).val.app (op V) v) =
        (SymmetricAlgebraSheaf.inclusion E).val.app (op V) ((tau n U e he V h).symm v)
  /-- Both algebra maps commute with restriction to arbitrary smaller opens. -/
  beta_natural : ∀ n U e he V h W (i : W ≤ V) a,
    (SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).right.obj.map (homOfLE i).op
      (beta n U e he V h a) = beta n U e he W (i.trans h)
        ((SymmetricAlgebraSheaf.algebra E).right.obj.map (homOfLE i).op a)
  beta_inverse_natural : ∀ n U e he V h W (i : W ≤ V) a,
    (SymmetricAlgebraSheaf.algebra E).right.obj.map (homOfLE i).op
      ((beta n U e he V h).symm a) = (beta n U e he W (i.trans h)).symm
        ((SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).right.obj.map
          (homOfLE i).op a)
  /-- On each affine, the map is the symmetric-algebra lift under the canonical units. -/
  beta_affine : ∀ n U e he (V : S.affineOpens) (h : V.1 ≤ U)
      (a : SymmetricAlgebraSheaf.sections E (op V.1)),
    beta n U e he V.1 h (SymmetricAlgebraSheaf.sectionMap E (op V.1) a) =
      SymmetricAlgebraSheaf.sectionMap (E ⊗ L.tensorPow n) (op V.1)
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι Γ(S, V.1)
          Γ(E ⊗ L.tensorPow n, V.1)).comp (tau n U e he V.1 h).toLinearMap) a)
  beta_inverse_affine : ∀ n U e he (V : S.affineOpens) (h : V.1 ≤ U)
      (a : SymmetricAlgebraSheaf.sections (E ⊗ L.tensorPow n) (op V.1)),
    (beta n U e he V.1 h).symm
      (SymmetricAlgebraSheaf.sectionMap (E ⊗ L.tensorPow n) (op V.1) a) =
        SymmetricAlgebraSheaf.sectionMap E (op V.1)
          (SymmetricAlgebra.lift ((SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1)).comp
            (tau n U e he V.1 h).symm.toLinearMap) a)
  /-- Grading is preserved in both directions, for local homogeneous sections. -/
  beta_graded : ∀ n U e he V h k a,
    IsLocallySymmetricHomogeneous E k V a ↔
      IsLocallySymmetricHomogeneous (E ⊗ L.tensorPow n) k V (beta n U e he V h a)
  /-- Uniqueness among graded algebra-sheaf isomorphisms with the generator formula. -/
  beta_unique : ∀ n U e he
      (g : ∀ (V : S.Opens), V ≤ U →
        (SymmetricAlgebraSheaf.algebra E).right.obj.obj (op V) ≃+*
          (SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).right.obj.obj (op V)),
    (∀ V h (r : Γ(S, V)),
      g V h ((SymmetricAlgebraSheaf.algebra E).hom.hom.app (op V) r) =
        (SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).hom.hom.app (op V) r) →
    (∀ V h (v : Γ(E, V)),
      g V h ((SymmetricAlgebraSheaf.inclusion E).val.app (op V) v) =
        (SymmetricAlgebraSheaf.inclusion (E ⊗ L.tensorPow n)).val.app (op V)
          (tau n U e he V h v)) →
    (∀ V h W (i : W ≤ V) a,
      (SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).right.obj.map (homOfLE i).op
        (g V h a) = g W (i.trans h)
          ((SymmetricAlgebraSheaf.algebra E).right.obj.map (homOfLE i).op a)) →
    (∀ V h k a, IsLocallySymmetricHomogeneous E k V a ↔
      IsLocallySymmetricHomogeneous (E ⊗ L.tensorPow n) k V (g V h a)) →
    ∀ V h a, g V h a = beta n U e he V h a
  /-- Restricting the construction agrees with constructing from the restricted frame. -/
  beta_restrict : ∀ n U e he V (h : V ≤ U) W (i : W ≤ V) a,
    beta n U e he W (i.trans h) a =
      beta n V (L.presheaf.map (homOfLE h).op e) (he.map h) W i a
  /-- Frame changes act on the module map by the nth power of the unit. -/
  tau_change_frame : ∀ n U e (he : Scheme.Modules.IsFreeGenerator e) (c : Γ(S, U)ˣ)
      V h v,
    tau n U ((c : Γ(S, U)) • e) (he.units_smul c) V h v =
      (S.presheaf.map (homOfLE h).op (c : Γ(S, U))) ^ n • tau n U e he V h v
  /-- Frame changes on degree k act by c^(n*k), including k = 0. -/
  beta_change_frame : ∀ n U e (he : Scheme.Modules.IsFreeGenerator e) (c : Γ(S, U)ˣ)
      V h k a,
    IsLocallySymmetricHomogeneous E k V a →
    beta n U ((c : Γ(S, U)) • e) (he.units_smul c) V h a =
      (SymmetricAlgebraSheaf.algebra (E ⊗ L.tensorPow n)).hom.hom.app (op V)
        ((S.presheaf.map (homOfLE h).op (c : Γ(S, U))) ^ (n * k)) *
          beta n U e he V h a
  /-- At n = 0, tau is exactly the inverse right unitor. -/
  tau_zero : ∀ U e he V h v,
    tau 0 U e he V h v = (ρ_ E).inv.app V v
  /-- At n = 0, beta is the canonical symmetric extension of that unit identification. -/
  beta_zero_generator : ∀ U e he V h (v : Γ(E, V)),
    beta 0 U e he V h ((SymmetricAlgebraSheaf.inclusion E).val.app (op V) v) =
      (SymmetricAlgebraSheaf.inclusion (E ⊗ L.tensorPow 0)).val.app (op V)
        ((ρ_ E).inv.app V v)
  /-- Its unit normalization is independent of the frame. -/
  beta_zero_independent : ∀ U e he (e' : Γ(L, U))
      (he' : Scheme.Modules.IsFreeGenerator e') V h a,
    beta 0 U e he V h a = beta 0 U e' he' V h a

/-- Finite type and quasi-coherence of the twist, and the complete framed comparison.
Source: Stacks Project, Constructions, Tag 02NC, lemma-twisting-and-proj;
Modules, Tags 01CG and 01CL (blueprint: lem-trf-framed-symmetric-twist-comparison).

Proof: (1) Restrict the explicit sectionwise symmetric-algebra construction to an open;
module sheafification commutes with restriction (lem-weil-pbc-module-sheafification-restriction).
Identify the explicit construction with the symmetric sheaf by the universal property
(lem-weil-pbc-quasi-coherent-symmetric-algebra-core).
(2) The frame gives a coefficient inverse. Its tensor powers give v ↦ v tensor e^n and
the balanced inverse v tensor a e^n ↦ a v. These descend through module sheafification
(def-pur-sheaf-tensor-product and def-weil-presheaf-modules-sheafification), and both
composites are identities on pure tensors. For n = 0 they are the unitors.
(3) Locally the twist is isomorphic to E. Quasi-coherence survives open restriction
(lem-weil-pbc-module-restriction-open-immersion-colimits); local finite presentations by
finite free surjections remain finite free surjections. Thus the twist is quasi-coherent
and finite type (pqf-def-coherent and def-sc-invertible-module).
(4) Extend tau and its inverse using the symmetric sheaf universal property
(lem-weil-pbc-quasi-coherent-symmetric-algebra). Both composites fix scalars and degree-one
generators, so uniqueness makes them inverse. The affine comparison identifies their
section maps with the symmetric-algebra lifts.
(5) Products of k generators span degree k (lem-weil-pbc-symmetric-algebra-graded).
The generator formula therefore preserves degrees on the canonical affine-basis algebra
(def-trf-canonical-symmetric-graded-algebra), hence locally on all opens.
(6) The pure-tensor formulas commute with restriction. Uniqueness of the symmetric
extension identifies restriction of beta with beta for the restricted frame.
(7) Replacing e by c e multiplies its nth tensor power by c^n, and products of k
such generators by c^(n*k). Extend linearly on affine opens and use the affine basis
(lem-weil-pbc-affine-opens-basis) and separatedness on arbitrary opens. Degree zero
fixes scalars. For n = 0 the tensor unit formula and uniqueness give exactly the canonical
symmetric extension of the right unitor, independent of the frame. -/
theorem exists_framedSymmetricTwistComparison (S : Scheme.{u}) (E L : S.Modules)
    [E.IsQuasicoherent] [E.IsFiniteType] [L.IsInvertible] :
    (∀ n : ℕ, (E ⊗ L.tensorPow n).IsQuasiCoherentFiniteType) ∧
      Nonempty (FramedSymmetricTwistComparison E L) := by
  sorry

end AlgebraicGeometry

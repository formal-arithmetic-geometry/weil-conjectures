/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization
import Sheaf.Paper.CondensedPointCoefficients
import Sheaf.Topology.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Finite constant local models for condensed coefficients

Source: blueprint main-20261015, `sk-def-sfb-constructible-local-model.md`
(blueprint: det-def-sfb-constructible-local-model).

Scalars are encoded as a ring object of abelian groups, and scalar modules as internal
modules in abelian groups. These are precisely ordinary modules over the scalar ring.
The constant sheaf on the profinite point is formed before inverse image to a scheme;
only this constant sheaf, rather than an arbitrary condensed module, is called constant.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Sections at the one-point profinite set. Source: blueprint local-model definition,
first paragraph (blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarSections :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (op (Profinite.of PUnit.{u + 1}))

/-- The sections functor has the lax monoidal structure right adjoint to the monoidal
constant sheaf functor. Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable instance scalarSections_laxMonoidal : scalarSections.{u}.LaxMonoidal :=
  (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit).rightAdjointLaxMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]

/-- The scalar ring Λ(*), encoded as a ring object of abelian groups. Its underlying
abelian group is literally evaluation at *. Source: blueprint local-model definition,
first paragraph (blueprint: det-def-sfb-constructible-local-model). -/
noncomputable abbrev scalarRingObj : Ab.{u + 1} := scalarSections.obj Λ

/-- The scalar ring is commutative. Source: blueprint local-model proof, Step 1.
Proof: evaluation's multiplication is induced from the sheaf tensor comparison; the
symmetry and the commutativity of Λ give commutativity on sections.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarRingObj_comm : IsCommMonObj (scalarRingObj Λ) := by
  sorry

attribute [instance] scalarRingObj_comm

/-- Sheafified constant abelian groups pulled to X. This is the constant-sheaf functor
on X: inverse image preserves colimits and the integer tensor unit, hence preserves
constant abelian sheaves, which are presentations by coproducts of that unit.
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarConstant (X : Scheme.{u}) :
    Ab.{u + 1} ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

/-- The constant-sheaf construction followed by inverse image is monoidal.
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable instance scalarConstant_monoidal (X : Scheme.{u}) :
    (scalarConstant X).Monoidal :=
  inferInstanceAs (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
    upperStarFromPoint X).Monoidal

/-- The composed constant construction agrees monoidally with the sheafification of
constant presheaves on X. This records that P_X here really is a constant sheaf.
Source: blueprint local-model definition, first paragraph, and proof, Step 1.
Proof: both functors are additive left adjoints and preserve the tensor unit ℤ.
Present any abelian group by coproducts of ℤ and transport the presentation through
both functors. The unit comparison gives compatible maps on the free presentations
and hence an isomorphism on their cokernels, independent of the presentation.
The resulting isomorphism is natural; checking its unit and tensor compatibility
on free generators gives the monoidal clauses.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarConstant_iso_constantSheaf (X : Scheme.{u}) :
    ∃ e : scalarConstant X ≅ constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1},
      NatTrans.IsMonoidal e.hom := by
  sorry

/-- The scalar map R_X → Λ_X is the inverse image of the constant-sheaf counit at Λ.
Thus a scalar is pulled back from Λ(*) rather than chosen in Γ(X,Λ_X).
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarCoefficientHom (X : Scheme.{u}) :
    (scalarConstant X).obj (scalarRingObj Λ) ⟶ condensedRingObj Λ X :=
  (upperStarFromPoint X).map
    ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app Λ)

/-- The scalar map preserves multiplication and unit. Source: blueprint local-model
proof, Step 1. Proof: the constant-sheaf adjunction is monoidal, so its counit is a
ring morphism, and the monoidal inverse image preserves ring morphisms.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarCoefficientHom_isMonHom (X : Scheme.{u}) :
    IsMonHom (scalarCoefficientHom Λ X) := by
  sorry

attribute [instance] scalarCoefficientHom_isMonHom

/-- The constant scalar ring on X is commutative. Source: blueprint local-model proof,
Step 1. Proof: the constant presheaf functor, sheafification and inverse image are
symmetric monoidal and transport commutative ring objects to commutative ring objects.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarConstant_comm (X : Scheme.{u}) :
    IsCommMonObj ((scalarConstant X).obj (scalarRingObj Λ)) := by
  sorry

attribute [instance] scalarConstant_comm

/-- E_X(P) = Λ_X ⊗_{R_X} P_X, using actual scalar extension along the canonical map.
This functor starts with ordinary scalar modules and takes values in module sheaves.
Source: blueprint local-model definition and proof, Steps 1–2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def finiteConstantScalarExtension (X : Scheme.{u}) :
    Mod Ab.{u + 1} (scalarRingObj Λ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (scalarConstant X).mapMod (scalarRingObj Λ) ⋙ Mod.extendScalars (scalarCoefficientHom Λ X)

/-- A scalar section on X, with the unit comparison included explicitly.
Source: blueprint local-model proof, Steps 1–2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarSection (X : Scheme.{u}) (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X :=
  Functor.LaxMonoidal.ε (scalarConstant X) ≫
    (scalarConstant X).map a ≫ scalarCoefficientHom Λ X

/-- The finite matrix with scalar entries, acting on finite free Λ_X-modules.
The first index is the source column and the second is the target row.
A map ℤ → Λ(*) encodes its value at 1, so these entries are exactly elements of Λ(*).
Source: blueprint local-model definition, Lemma (2), and proof, Step 2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarMatrix (X : Scheme.{u}) {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    Mod.finiteFree (condensedRingObj Λ X) m ⟶
      Mod.finiteFree (condensedRingObj Λ X) n :=
  biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X (A j k))

/-- Finite constant local models on a specified pro-étale cover: the model on each
member is extension of a finitely presented scalar module, with no uniform rank bound.
Source: blueprint local-model definition, second paragraph and Lemma (1)
(blueprint: det-def-sfb-constructible-local-model). -/
def HasFiniteConstantLocalModelOnCover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) : Prop :=
  ∀ i : 𝒰.I₀, ∃ P : Mod Ab.{u + 1} (scalarRingObj Λ),
    Mod.IsFinitelyPresented (scalarRingObj Λ) P ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
        (finiteConstantScalarExtension Λ (𝒰.X i)).obj P)

/-- Scalar finite-presentation matrices on a specified pro-étale cover.
Source: blueprint local-model definition, Lemma (2)
(blueprint: det-def-sfb-constructible-local-model). -/
def HasScalarMatrixPresentationOnCover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) : Prop :=
  ∀ i : 𝒰.I₀, ∃ (m n : ℕ)
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)),
    Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
      cokernel (scalarMatrix Λ (𝒰.X i) A))

/-- The existing finite constant local model predicate is exactly the scalar-extension
formulation. Source: blueprint local-model definition and proof, Steps 1–3.
Proof: a finite presentation by regular condensed modules is a finite scalar matrix,
since maps from the regular module are maps from the integer unit, hence sections
at the terminal profinite set. Its cokernel is extension of the corresponding
finitely presented scalar module by the adjunction and cokernel calculation of
Steps 1–3. Conversely present a scalar module by a finite matrix and take the
same matrix of regular condensed modules before inverse image. Inverse image and
extension of scalars preserve these cokernels. The same cover and its members
are used in both directions.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem finiteConstantLocalModel_iff_exists_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ X M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
        HasFiniteConstantLocalModelOnCover Λ M 𝒰 := by
  sorry

/-- Constant finite scalar models and finite scalar matrices are equivalent on the
same given cover. Source: blueprint local-model lemma, and proof, Steps 1–3.
Proof: the constant-sheaf adjunction and extension/restriction adjunction identify maps
from E_U(P) to N with scalar-linear maps P → N(U). For P = R^k this identifies E_U(P)
with Λ_U^k, preserving each scalar matrix entry. For a scalar matrix A, maps from
E_U(coker A) to N are exactly maps from Λ_U^n killing A, so E_U(coker A) is its cokernel;
no flatness is used. Apply a finite presentation of each P_i for the forward direction.
Conversely take P_i to be the cokernel of the given scalar matrix over R.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem finiteConstantLocalModelOnCover_iff_scalarMatrix {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    HasFiniteConstantLocalModelOnCover Λ M 𝒰 ↔
      HasScalarMatrixPresentationOnCover Λ M 𝒰 := by
  sorry

/-- Finite constant local models imply local finite presentation.
Source: blueprint local-model final paragraph and proof, Step 4.
Proof: replace each constant scalar model by its scalar matrix presentation using
finiteConstantLocalModelOnCover_iff_scalarMatrix. This is a finite free presentation
over Λ_U. Transport along the canonical coefficient isomorphism α_u to the
u^*Λ_X-module category used by IsLocallyFinitelyPresented. Restriction along α_u and
its inverse preserve regular modules, finite sums and cokernel presentations, so the
same cover witnesses local finite presentation.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem HasFiniteConstantLocalModel.isLocallyFinitelyPresented {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  sorry

/-- Local finite presentation does not imply finite constant local models for all
commutative condensed coefficients.
Source: blueprint local-model final sentence and node proof, Steps 5–7.
Proof: take Λ = continuous ℚ_ℓ, S = ℕ ∪ {∞}, Ω an algebraic closure of ℚ,
B = Spec Ω and X = B[S] = Spec LC(S,Ω). The locally constant prime spectrum
identifies |X| with S. The continuous function t(n) = ℓ^(n+1), t(∞) = 0 gives a
coefficient section by point-coefficient evaluation and coefficient-section localization.
The module coker(t : Λ_X → Λ_X) has a one-by-one presentation on the identity cover.
At every geometric point over n its pullback is zero since t(n) is a unit; over ∞
it is the nonzero regular coefficient module since t(∞) = 0. Here localization identifies
the actual multiplication maps, pullback preserves cokernels, and extension of scalars
sends the regular module to the regular module by the extend/restrict adjunction.
If finite constant local models existed, each finitely presented ℚ_ℓ-module would have
a finite basis, so every nonempty covering member would be free of some rank d.
Geometric-point pullback shows its image lies in ℕ if d = 0 and in {∞} otherwise.
The covering condition supplies finitely many affine opens of covering members whose
images cover X. Each image is compact in the Hausdorff space S and hence closed.
The images with rank zero would have union ℕ, making ℕ closed, a contradiction.
This is precisely the failure of the universal implication below, including the zero
ring and empty-scheme cases in its quantifiers.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem not_locallyFinitelyPresented_implies_finiteConstantLocalModel :
    ¬ ∀ (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj L] [IsCommMonObj L] (X : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj L X)),
      IsLocallyFinitelyPresented (condensedRingObj L X) M → HasFiniteConstantLocalModel L X M := by
  sorry

end AlgebraicGeometry.ProEtale

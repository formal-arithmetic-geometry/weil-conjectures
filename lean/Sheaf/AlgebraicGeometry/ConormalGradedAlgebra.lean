/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.RingTheory.AssociatedGradedRingStructure
import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Topology.InverseImageModule
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import Mathlib.LinearAlgebra.TensorProduct.Map
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Sheaf.Topology.StalkDirectSums
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation

import WeilConjectures.AlgebraicGeometry.Coherent
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
/-!
# The conormal graded algebra of a closed immersion

Source: Stacks Project, Divisors, Tags 0630, 0631, 0632, 0633; coherence, Tag 01XZ
(blueprint: lem-pur-conormal-graded-algebra).

The homogeneous modules are actual tensor pullbacks of the ideal powers. The algebra is
specified by a coproduct universal property and the product of representatives, which
uniquely determine it up to the unique isomorphism preserving its homogeneous inclusions.
Thus the existence theorem below postpones only the construction's universal property;
it cannot supply an arbitrary quasi-coherent algebra unrelated to the closed immersion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.ConormalGradedAlgebra

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The ideal-power module with its actual inclusion, including `I^0 = O_X` and `I^1 = I`.
Source: Stacks Tags 0630, 0633 (blueprint: lem-pur-conormal-graded-algebra). -/
def power (n : ℕ) : X.Modules :=
  (Scheme.idealSheafPower i.ker.toModulesι n).1

/-- The inclusion of the ideal power in the structure sheaf.
Source: Stacks Tag 0633 (blueprint: lem-pur-conormal-graded-algebra). -/
def powerInclusion (n : ℕ) : power i n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.idealSheafPower i.ker.toModulesι n).2

/-- The degree `n` conormal module on `Z`, namely `i^*(I^n) = I^n/I^(n+1)`.
Source: Stacks Tag 0633 (blueprint: lem-pur-conormal-graded-algebra). -/
def piece (n : ℕ) : Z.Modules := (Scheme.Modules.tensorPullback i).obj (power i n)

/-- Pull a representative of an ideal-power section to its quotient class on `Z`.
Source: Stacks Tags 0631, 0633 (blueprint: lem-pur-conormal-graded-algebra). -/
def representative (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    (piece i n).val.obj (op (i ⁻¹ᵁ U)) :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    (power i n)).val.app (op U) a

/-- The homogeneous class in an algebra with specified homogeneous inclusions.
Source: Stacks Tags 0630, 0633 (blueprint: lem-pur-conormal-graded-algebra). -/
def homogeneousClass (A : Z.CommAlgebraSheaf) (j : ∀ n, piece i n ⟶ A.toModule)
    (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    A.right.obj.obj (op (i ⁻¹ᵁ U)) :=
  (j n).val.app (op (i ⁻¹ᵁ U)) (representative i n U a)

/-- The quotient identification of the closed-subscheme local ring, induced by the actual
surjective structure-stalk map. Source: Stacks Tag 0633
(blueprint: lem-pur-conormal-graded-algebra). -/
def quotientStalk (z : Z) :
    X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom ≃+* Z.presheaf.stalk z :=
  RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)

/-- A universal presentation of the actual conormal algebra. Its underlying module is the
sheaf coproduct of `i^*(I^n)`; products and constants have their representative formulas.
The affine and stalk charts preserve those classes, and hence specify graded charts.
Source: Stacks Tags 0630--0633, 01XZ
(blueprint: lem-pur-conormal-graded-algebra). -/
structure Presentation where
  algebra : Z.CommAlgebraSheaf
  inclusion : ∀ n, piece i n ⟶ algebra.toModule
  coproduct : IsColimit (Cofan.mk algebra.toModule inclusion)
  quasicoherent : algebra.toModule.IsQuasicoherent
  pieceQuasicoherent : ∀ n, (piece i n).IsQuasicoherent
  powerIdentification : ∀ n,
    ∃ e : power i n ≅ (i.ker ^ n).toModules,
      e.hom ≫ (i.ker ^ n).toModulesι = powerInclusion i n
  multiplication : ∀ (m n : ℕ) (U : X.Opens)
    (a : (power i m).val.obj (op U)) (b : (power i n).val.obj (op U))
    (d : (power i (m + n)).val.obj (op U)),
    (powerInclusion i (m + n)).val.app (op U) d =
        (@id Γ(X, U) ((powerInclusion i m).val.app (op U) a)) *
          (@id Γ(X, U) ((powerInclusion i n).val.app (op U) b)) →
      homogeneousClass i algebra inclusion m U a * homogeneousClass i algebra inclusion n U b =
        homogeneousClass i algebra inclusion (m + n) U d
  constants : ∀ (U : X.Opens) (a : (power i 0).val.obj (op U)),
    homogeneousClass i algebra inclusion 0 U a =
      algebra.hom.hom.app (op (i ⁻¹ᵁ U)) (i.app U a)
  pushforwardPiece : ∀ n,
    ∃ e : (Scheme.Modules.pushforward i).obj (piece i n) ≅
        formalAssociatedGradedPiece i.ker n,
      ∀ (U : X.Opens) (a : (power i n).val.obj (op U)),
        e.hom.val.app (op U) (representative i n U a) =
          (formalAssociatedGradedπ i.ker n).val.app (op U) a
  degreeZero : Nonempty (piece i 0 ≅ SheafOfModules.unit Z.ringCatSheaf)
  affineChart : ∀ U : X.affineOpens,
    ∃ e : algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≅
        CommRingCat.of (Ideal.associatedGraded (i.ker.ideal U)),
      ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
        ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
          e.hom (homogeneousClass i algebra inclusion n U.1 a) =
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩)
  stalkChart : ∀ z : Z,
    ∃ e : TopCat.Presheaf.stalk algebra.right.obj z ≅
        CommRingCat.of (Ideal.associatedGraded (RingHom.ker (i.stalkMap z).hom)),
      ∀ (n : ℕ) (U : X.Opens) (hz : i z ∈ U) (a : (power i n).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i n).val.app (op U) a) ∈
              RingHom.ker (i.stalkMap z).hom ^ n,
          e.hom (TopCat.Presheaf.germ algebra.right.obj (i ⁻¹ᵁ U) z hz
            (homogeneousClass i algebra inclusion n U a)) =
              DirectSum.of (Ideal.associatedGradedPiece (RingHom.ker (i.stalkMap z).hom)) n
                (Submodule.Quotient.mk
                  ⟨X.presheaf.germ U (i z) hz ((powerInclusion i n).val.app (op U) a), h⟩)
  conormalStalk : ∀ z : Z,
    ∃ e : ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)) ≃+
        (RingHom.ker (i.stalkMap z).hom).Cotangent,
      (∀ (r : X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom)
        (x : (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)),
        e (quotientStalk i z r • x) = r • e x) ∧
      ∀ (U : X.Opens) (hz : i z ∈ U) (a : (power i 1).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i 1).val.app (op U) a) ∈ RingHom.ker (i.stalkMap z).hom,
          e (TopCat.Presheaf.germ (piece i 1).presheaf (i ⁻¹ᵁ U) z hz
            (representative i 1 U a)) =
              (RingHom.ker (i.stalkMap z).hom).toCotangent
                ⟨X.presheaf.germ U (i z) hz ((powerInclusion i 1).val.app (op U) a), h⟩
  symmetricStalk : ∀ z : Z,
    ∃ e : TopCat.Presheaf.stalk (SymmetricAlgebraSheaf.algebra (piece i 1)).right.obj z ≅
        CommRingCat.of (SymmetricAlgebra (Z.presheaf.stalk z)
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1))),
      (∀ (U : Z.Opens) (hz : z ∈ U) (r : Γ(Z, U)),
        e.hom (TopCat.Presheaf.germ (SymmetricAlgebraSheaf.algebra (piece i 1)).right.obj
          U z hz ((SymmetricAlgebraSheaf.algebra (piece i 1)).hom.hom.app (op U) r)) =
            algebraMap (Z.presheaf.stalk z)
              (SymmetricAlgebra (Z.presheaf.stalk z)
                ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)))
              (Z.presheaf.germ U z hz r)) ∧
      ∀ (U : Z.Opens) (hz : z ∈ U) (a : (piece i 1).val.obj (op U)),
        e.hom (TopCat.Presheaf.germ (SymmetricAlgebraSheaf.algebra (piece i 1)).right.obj
          U z hz ((SymmetricAlgebraSheaf.inclusion (piece i 1)).val.app (op U) a)) =
            SymmetricAlgebra.ι (Z.presheaf.stalk z)
              ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1))
              (TopCat.Presheaf.germ (piece i 1).presheaf U z hz a)
  coherent : IsLocallyNoetherian X → ∀ n,
    RingedSpace.IsCoherent Z.toRingedSpace (piece i n)
  symmetricComparison : ∃! ψ : SymmetricAlgebraSheaf.algebra (piece i 1) ⟶ algebra,
    ∀ (U : Z.Opens) (a : (piece i 1).val.obj (op U)),
      ψ.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion (piece i 1)).val.app (op U) a) =
        (inclusion 1).val.app (op U) a
  augmentation : ∃! ε : algebra ⟶ Under.mk (𝟙 Z.sheaf),
    ∀ (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)),
      ε.right.hom.app (op (i ⁻¹ᵁ U)) (homogeneousClass i algebra inclusion n U a) =
        if n = 0 then i.app U ((powerInclusion i n).val.app (op U) a) else 0

/-- The conormal algebra exists, with its unique homogeneous-inclusion-preserving comparison
to any other presentation. This is a universal property, not a mere existence of an
unconstrained algebra or normal-cone datum.
Source: Stacks Divisors Tags 0630--0633; coherent sheaves Tag 01XZ
(blueprint: lem-pur-conormal-graded-algebra).

Proof (the ten steps of `lem-pur-conormal-graded-algebra`):
1. Form the sheaf cokernels B_n = I^n/I^(n+1) on X. Quasi-coherent cokernels and the
   affine tilde adjunction identify B_n on Spec R with the module J^n/J^(n+1), carrying
   quotient representatives to their classes. The shared image-power construction
   identifies with `(i.ker ^ n).toModules` by its inclusion into O_X on affine opens;
   both inclusions have image J^n, so these identifications glue uniquely.
2. Multiply local lifts a and b and take the class of ab. Changing the lifts changes
   this product by an element of J^(m+n+1). These products glue, commute with restriction,
   and satisfy the ring laws on an affine refinement by the associated-graded ring laws.
   Degree-zero constants give the unit. No sectionwise cokernel on arbitrary opens is used.
3. The ideal I annihilates B_n, since a product of an element of J with one of J^n lies
   in J^(n+1). This includes n=0.
4. The closed-immersion annihilation theorem descends B_n to Z, with its pushforward
   identified by the canonical unit; fully faithful pushforward determines this descent.
   On Spec(R/J), the maps a tensor r-bar to ra modulo J^(n+1) and [a] to a tensor 1
   identify the fixed piece i^*(I^n) with that descent. Tensor balancing proves both
   composites are identities. The affine tilde adjunction glues these identifications.
5. The tensor formula transports products to the pieces. Their sheaf coproduct is
   quasi-coherent. On affine opens its sections are the direct sum J^n/J^(n+1), with
   the representative products and constants above. Affine tilde preserves this coproduct;
   no commutation of arbitrary non-affine sections with infinite sums is assumed.
6. Degree one is literally i^*I. On an affine chart, a tensor r-bar maps to ra modulo
   J^2, and the inverse sends [a] to a tensor 1. The tensor relations kill J^2 and prove
   that these are inverse. Degree zero similarly identifies with O_Z.
7. Structure and tilde stalks are localizations. Localization exactness gives
   (J^n/J^(n+1))_p = J_p^n/J_p^(n+1); localization commutes with powers by the fraction
   product formula, also for n=0. Stalks commute with the sheaf coproduct. Thus the stalk
   algebra is gr_(J_p)(R_p), and degree one is its cotangent module. The quotient-stalk
   equivalence is the first-isomorphism equivalence of the actual surjective stalk map.
8. Extend the degree-one inclusion by the symmetric-algebra universal property. On affine
   charts the map sends every generator to its degree-one class. Products of generators
   have the same total degree, so this is the canonical graded comparison.
9. Symmetric-algebra base change along localization identifies the symmetric sheaf stalk
   with the symmetric algebra of the module stalk. The identification fixes scalar germs
   and carries each generator germ to the corresponding generator. In particular it is
   canonical even for a zero module stalk. Naturality and Step 7 give the comparison's
   specified degree-one stalk formula.
10. If X is locally Noetherian, so is Z. Each J^n is finite by the Noetherian submodule
    theorem, and its quotient is finite over R/J. The affine finite-type criterion and
    the coherent/quasi-coherent finite-type equivalence give coherence of each piece.
    No coherence assertion is made about the infinite coproduct.
Finally the coproduct property and representative products determine the algebra up to
its unique homogeneous-inclusion-preserving isomorphism: the unique module comparison
preserves products and constants locally, and the opposite comparison is its inverse.
Projection to degree zero fixes constants and kills positive degrees, hence is the unique
augmentation; nonnegative degrees make it multiplicative. This includes empty schemes,
the zero and unit ideals and n=0. -/
theorem exists_conormalGradedAlgebra :
    ∃ A : Presentation i, ∀ B : Presentation i,
      ∃! e : A.algebra ≅ B.algebra,
        ∀ (n : ℕ) (U : Z.Opens) (a : (piece i n).val.obj (op U)),
          e.hom.right.hom.app (op U) ((A.inclusion n).val.app (op U) a) =
            (B.inclusion n).val.app (op U) a := by
  sorry

/-- The conormal algebra chosen from its universal property. Any two such choices have the
unique isomorphism fixing every homogeneous inclusion, the equality used downstream.
Source: Stacks Tags 0630--0633 (blueprint: lem-pur-conormal-graded-algebra). -/
def presentation : Presentation i := (exists_conormalGradedAlgebra i).choose

/-- The canonical graded algebra map from the symmetric algebra of the conormal module.
Source: Stacks Tag 0632 (blueprint: lem-pur-conormal-graded-algebra). -/
def symmetricComparison : SymmetricAlgebraSheaf.algebra (piece i 1) ⟶
    (presentation i).algebra := (presentation i).symmetricComparison.exists.choose

/-- Projection to degree zero, with its uniquely specified homogeneous representative formula.
Source: Stacks Tags 0630, 0636 (blueprint: lem-pur-conormal-graded-algebra). -/
def augmentation : (presentation i).algebra ⟶ Under.mk (𝟙 Z.sheaf) :=
  (presentation i).augmentation.exists.choose

end AlgebraicGeometry.ConormalGradedAlgebra

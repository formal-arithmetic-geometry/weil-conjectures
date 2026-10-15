/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Coset.Defs
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Sheaf.NumberTheory.Padics.LatticeStabilizerOpen
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# The sheaf of integral lattices

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.8.4(6),
pp. 59--60 (blueprint: lem-weil-pbc-lattice-sheaf-locally-constant).

The presentation by a surjection from pairs with its exact kernel relation avoids choosing
representatives of isomorphism classes. Restriction is characterized by the embedded images
on every object of the slice. This also specifies the normalization of the constant-coset
isomorphism without making arbitrary choices of bases for integral modules.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- The commutative-ring version of the continuous coefficient presheaf, with exactly the
same sections and precomposition maps as `continuousMapRingPresheaf`.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientPresheaf (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj V := CommRingCat.of (ULift.{u + 1} C(V.unop.left, T))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.left.base.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction of the scalar-extension ring map to the localized site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), slice restrictions
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def latticeScalarMap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (U : X.ProEt) : R.over U ⟶ S.over U :=
  ⟨Functor.whiskerLeft (Over.forget U).op a.hom⟩

/-- A lattice pair, including the rationalization isomorphism, over a slice object.
Finite local freeness allows varying ranks and the zero module.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
structure IntegralLatticePair {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) (U : X.ProEt) where
  module : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U))
  locallyFree : module.IsFiniteLocallyFree
  rationalization :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) module ≅ L.over U

/-- The exact equivalence relation on pairs: an integral isomorphism intertwines their
rationalizations. Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def IntegralLatticePair.Equivalent {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} {a : R ⟶ S}
    {L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)} {U : X.ProEt}
    (P Q : IntegralLatticePair a L U) : Prop :=
  ∃ e : P.module ≅ Q.module,
    SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (latticeScalarMap a U) P.module e.hom ≫
      Q.rationalization.hom = P.rationalization.hom

set_option backward.isDefEq.respectTransparency false in
/-- The embedded image of a pair on a test object of its slice: apply the rationalization
map to the image of `1 ⊗ m` under the change-of-rings sheafification unit.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, first local calculation
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def IntegralLatticePair.image {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} {a : R ⟶ S}
    {L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)} {U : X.ProEt}
    (P : IntegralLatticePair a L U) (T : (Over U)ᵒᵖ) : Set ((L.over U).val.obj T) :=
  Set.range fun m : P.module.val.obj T ↦
    P.rationalization.hom.val.app T
      ((((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (S.over U)).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module)).app T)
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m))

/-- Continuous coefficients satisfy the sheaf axiom.
Source: Bhatt--Scholze, Lemma 4.2.12 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant).
Proof: forget to sets and identify the presheaf with the lifted restriction of
`continuousMapPresheaf T`. Mathlib's fpqc continuous-function descent theorem makes this
a sheaf. The pro-etale topology is contained in the fpqc topology. Restriction and the
universe lift preserve the sheaf condition, and the forgetful functor from commutative
rings reflects it. Thus the same functions form a sheaf of commutative rings. -/
theorem isSheaf_latticeCoefficientPresheaf (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (latticeCoefficientPresheaf X T) := by
  sorry

/-- The continuous coefficient sheaf, with its commutative-ring structure retained.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientSheaf (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨latticeCoefficientPresheaf X T, isSheaf_latticeCoefficientPresheaf X T⟩

/-- The coefficient map is postcomposition with the specified continuous ring map.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientSheafMap (X : Scheme.{u}) {T T' : Type u}
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
    (f : T →+* T') (hf : Continuous f) :
    latticeCoefficientSheaf X T ⟶ latticeCoefficientSheaf X T' :=
  ⟨{ app := fun _ ↦ CommRingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         ((f.compLeftContinuous _ hf).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The given valuation subring in the field equipped with its canonical absolute value.
`WithAbs.equiv` only changes the topology-bearing type synonym.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeCoefficientIntegers (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Subring (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) :=
  (Padic.coefficientExtensionIntegers l E).comap
    (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)).toRingHom

/-- The integral matrix subgroup in the rational general linear group. Its cosets `gH`
are the orbits of right multiplication, hence use Mathlib's `leftRel` quotient.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def integralMatrixSubgroup {K : Type u} [Field K] (A : Subring K) (n : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) K) :=
  (Matrix.GeneralLinearGroup.map A.subtype).range

/-- The discrete set of lattices in a trivial rank `n` rational module, including `n = 0`.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
abbrev integralMatrixCosets {K : Type u} [Field K] (A : Subring K) (n : ℕ) :=
  Matrix.GeneralLinearGroup (Fin n) K ⧸ integralMatrixSubgroup A n

/-- The underlying ring sheaf of continuous coefficients, retaining the universe lift.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable abbrev latticeModuleRing (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (latticeCoefficientSheaf X T)

/-- The canonical inclusion of continuous integral coefficients in rational coefficients.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def integralLatticeCoefficientMap (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ⟶
      latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) :=
  latticeCoefficientSheafMap X (latticeCoefficientIntegers l E).subtype continuous_subtype_val

/-- A sheaf presentation of isomorphism classes of lattice pairs. The first two clauses
say exactly that its sections are the quotient by intertwining integral isomorphisms.
The last clause specifies restriction by equality of embedded images on every slice object.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, descent of embedded lattices
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
def IsLatticeClassPresentation {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt, IntegralLatticePair a L U → F.obj.obj (op U)) : Prop :=
  (∀ U : X.ProEt, Function.Surjective (c U)) ∧
  (∀ (U : X.ProEt) (P Q : IntegralLatticePair a L U), c U P = c U Q ↔ P.Equivalent Q) ∧
  (∀ (U V : X.ProEt) (f : V ⟶ U)
    (P : IntegralLatticePair a L U) (Q : IntegralLatticePair a L V),
    F.obj.map f.op (c U P) = c V Q ↔
      ∀ T : Over V, P.image (op ((Over.map f).obj T)) = Q.image (op T))

/-- The free rank `n` coefficient sheaf on the localized site, with a lifted finite index.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable abbrev latticeFreeSheaf (X : Scheme.{u}) (K : Type u)
    [TopologicalSpace K] [CommRing K] [IsTopologicalRing K] (U : X.ProEt) (n : ℕ) :=
  SheafOfModules.free (R := (latticeModuleRing X K).over U) (ULift.{u + 1} (Fin n))

/-- A constant rational coefficient as an actual section of the coefficient sheaf.
Source: Bhatt--Scholze, Proposition 6.8.4(6), constant matrix entries
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def latticeConstantCoefficient (X : Scheme.{u}) (K : Type u)
    [TopologicalSpace K] [CommRing K] [IsTopologicalRing K] (V : X.ProEt) (x : K) :
    (latticeCoefficientSheaf X K).obj.obj (op V) :=
  ULift.up (ContinuousMap.const V.left x)

set_option backward.isDefEq.respectTransparency false in
/-- The embedded module `g A^n`: its sections are the integral linear combinations of the
columns of `g`, in the standard coordinate basis of the rational free sheaf.
Source: Bhatt--Scholze, Proposition 6.8.4(6), the map `g ↦ g A^n`
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant). -/
noncomputable def matrixLatticeImage (X : Scheme.{u}) (K : Type u) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K) (U : X.ProEt) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ) :
    Set ((latticeFreeSheaf X K U n).val.obj T) :=
  Set.range fun b : Fin n → (latticeCoefficientSheaf X A).obj.obj (op T.unop.left) ↦
    ∑ i : Fin n,
      (∑ j : Fin n,
        latticeConstantCoefficient X K T.unop.left (g.val i j) *
        (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
          (op T.unop.left) (b j)) •
      (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
        (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
          (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))

/-- The presheaf of integral lattice classes is a sheaf, locally the constant sheaf of
cosets `g GL_n(A)`, with the specified map `g ↦ (g A^n, α_g)`.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, pp. 59--60
(blueprint: lem-weil-pbc-lattice-sheaf-locally-constant).

Proof: (1) The map `m ↦ α(1 ⊗ m)` is injective by a local integral basis and coordinatewise
inclusion of continuous functions. Intertwining isomorphisms are unique, and two pairs are
equivalent exactly when their embedded submodules agree. (2) Matching pairs therefore have
unique transition maps satisfying the cocycle condition. Apply site-module-sheaf gluing
(lem-weil-pbc-site-module-sheaf-gluing). (3) Glue their embeddings in `L`, extend scalars,
and glue the inverse rationalizations. This gives unique amalgamation of classes.
(4) For a trivialization of rank `n`, the constant matrix `g` gives `g A^n`; multiplication
on the right by an integral invertible matrix preserves it. On a nonempty test object,
evaluation at a point shows equality implies equality of cosets. The empty covering handles
empty objects. (5) A local integral basis rationalizes to mutually inverse continuous matrices;
evaluation shows its rank is `n`. (6) The stabilizer of `A^n` is open by
lem-pod-lattice-stabilizer-open. Consequently every continuous matrix lattice agrees locally
with its value at a point. These open covers are pro-etale covers, giving local surjectivity.
(7) Extend the coset map by constant sheafification. Local representatives of sheafification
(lem-weil-pbc-site-sheafification-sections-local) give local injectivity; the local-bijection
criterion for set sheaves gives the asserted isomorphism. Rank zero gives the unique zero
pair, and the empty-cover axiom gives the unique section over an empty scheme. The original
trivializing cover of `L` then gives local constancy with varying ranks. -/
theorem integralLatticeSheaf_locallyConstant (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    [L.IsFiniteLocallyFree] :
    ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
      (c : ∀ U : X.ProEt,
        IntegralLatticePair (integralLatticeCoefficientMap X l E) L U → F.obj.obj (op U)),
      IsLatticeClassPresentation (integralLatticeCoefficientMap X l E) L F c ∧
      ∀ (U : X.ProEt) (n : ℕ)
        (e : L.over U ≅ latticeFreeSheaf X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) U n),
        ∃ k : (constantSheaf ((Scheme.ProEt.topology X).over U) (Type (u + 2))).obj
          (ULift.{u + 2} (integralMatrixCosets (latticeCoefficientIntegers l E) n)) ≅ F.over U,
          ∀ (g : Matrix.GeneralLinearGroup (Fin n)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
            (P : IntegralLatticePair (integralLatticeCoefficientMap X l E) L U),
            k.hom.hom.app (op (Over.mk (𝟙 U)))
              (((toSheafify ((Scheme.ProEt.topology X).over U)
                ((Functor.const (Over U)ᵒᵖ).obj
                  (ULift.{u + 2} (integralMatrixCosets
                    (latticeCoefficientIntegers l E) n)))).app (op (Over.mk (𝟙 U))))
                (ULift.up (Quotient.mk _ g))) = c U P ↔
              ∀ T : (Over U)ᵒᵖ, Set.image (e.hom.val.app T) (P.image T) =
                matrixLatticeImage X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
                  (latticeCoefficientIntegers l E) U n g T := by
  sorry

end AlgebraicGeometry.ProEtale

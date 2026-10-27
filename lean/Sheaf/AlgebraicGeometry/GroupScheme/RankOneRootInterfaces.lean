module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Topology.KrullDimension

/-! # Normalizer quotients and rank-one root terminology

Source: Milne, Algebraic Groups (2017), Sections 6.44--6.46, 21.1--21.2 and 21.11,
pp.424--430 (blueprint: def-sfb-rank-one-root-interfaces).

Normalizers are tested on every algebra, including nonreduced algebras. An SL2
homomorphism is written as its natural family on the actual determinant-one matrices;
this is the functor-of-points description of a morphism of affine group schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.RankOneRoots

/-- Characters, with their pointwise group law. Source: Milne, 21.1--21.2
(blueprint: def-sfb-rank-one-root-interfaces). -/
abbrev Character {F : Type u} [Field F] (T : Grp (Over (Spec (.of F)))) :=
  T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)

/-- Cocharacters are actual morphisms from the multiplicative group. Source: Milne, 21.2
(blueprint: def-sfb-rank-one-root-interfaces). -/
abbrev Cocharacter {F : Type u} [Field F] (T : Grp (Over (Spec (.of F)))) :=
  Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T

/-- The already recorded character weight space for an explicitly specified action.
Source: Milne, 21.2 (blueprint: def-sfb-rank-one-root-interfaces). -/
abbrev weight {F : Type u} [Field F] (T G : Grp (Over (Spec (.of F))))
    (a : ModObj T.X G.X) (χ : Character T) : Submodule F (GrpObj.Lie G.X) :=
  @TorusCharacterTangent.weightSpace F _ T G a χ

/-- Roots are exactly the nontrivial characters with nonzero character weight space.
Source: Milne, 21.2 (blueprint: def-sfb-rank-one-root-interfaces). -/
def roots {F : Type u} [Field F] (T G : Grp (Over (Spec (.of F))))
    (a : ModObj T.X G.X) : Set (Character T) :=
  {χ | χ.hom.hom ≠ 1 ∧ weight T G a χ ≠ ⊥}

/-- The conjugation morphism restricted to T × G. Source: Milne, 21.2
(blueprint: def-sfb-rank-one-root-interfaces). -/
def adjointMap {F : Type u} [Field F] {T G : Grp (Over (Spec (.of F)))}
    (i : T ⟶ G) : T.X ⊗ G.X ⟶ G.X :=
  (fst _ _ ≫ i.hom.hom) * snd _ _ * (fst _ _ ≫ i.hom.hom)⁻¹

/-- The image subgroup on points of any test scheme. Source: Milne, 21.1
(blueprint: def-sfb-rank-one-root-interfaces). -/
def pointImage {F : Type u} [Field F] {T G : Grp (Over (Spec (.of F)))}
    (i : T ⟶ G) (A : Over (Spec (.of F))) : Subgroup (A ⟶ G.X) :=
  (IsMonHom.monoidHom i.hom.hom A).range

/-- Rational points normalizing T after every scalar extension. The first factor
records the same condition on the base's terminal test scheme. Source: Milne, 21.1
(blueprint: def-sfb-rank-one-root-interfaces). -/
def normalizer {F : Type u} [Field F] {T G : Grp (Over (Spec (.of F)))}
    (i : T ⟶ G) : Subgroup (𝟙_ (Over (Spec (.of F))) ⟶ G.X) :=
  Subgroup.normalizer (pointImage i (𝟙_ _) : Set _) ⊓
    ⨅ A : CommAlgCat.{u} F,
      (Subgroup.normalizer
        (pointImage i (StandardGroupSchemes.affine F A) : Set _)).comap
        (pointsPrecomp G.X (toUnit (StandardGroupSchemes.affine F A)))

/-- The denominator T(F) inside its scalar-extension normalizer. Source: Milne, 21.1
(blueprint: def-sfb-rank-one-root-interfaces). -/
def torusInNormalizer {F : Type u} [Field F] {T G : Grp (Over (Spec (.of F)))}
    (i : T ⟶ G) : Subgroup (normalizer i) :=
  (pointImage i (𝟙_ _)).subgroupOf (normalizer i)

/-- The denominator is normal by the normalizer condition on base points.
Source: Milne, 21.1 (blueprint: def-sfb-rank-one-root-interfaces). -/
instance torusInNormalizer_normal {F : Type u} [Field F]
    {T G : Grp (Over (Spec (.of F)))} (i : T ⟶ G) :
    (torusInNormalizer i).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer inf_le_left

/-- The actual rational normalizer quotient, rather than an abstract reflection group.
Source: Milne, 21.1 (blueprint: def-sfb-rank-one-root-interfaces). -/
abbrev Weyl {F : Type u} [Field F] {T G : Grp (Over (Spec (.of F)))} (i : T ⟶ G) :=
  normalizer i ⧸ torusInNormalizer i

/-- Evaluation of the Laurent coordinate of a multiplicative-group point.
Source: Milne, 21.11(e) (blueprint: def-sfb-rank-one-root-interfaces). -/
def multiplicativeValue {F : Type u} [Field F] (A : CommAlgCat.{u} F)
    (z : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F) : A :=
  (Scheme.ΓSpecIso (.of A)).hom
    (z.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
      (LaurentPolynomial.T 1)))

/-- Semisimple rank one means rank one after quotient by the smooth connected radical.
The radical is specified by its largest-subgroup universal property, without a choice.
Source: Milne, 6.44--6.46 and 21.11(a)
(blueprint: def-sfb-rank-one-root-interfaces). -/
def HasSemisimpleRankOne {F : Type u} [Field F]
    (H : Grp (Over (Spec (.of F)))) : Prop :=
  ∃ (R Q : Grp (Over (Spec (.of F)))) (r : R ⟶ H) (q : H ⟶ Q),
    SolvableGroupStructure.IsAlgebraic R ∧ SolvableGroupStructure.IsAlgebraic Q ∧
    IsClosedSubgroupScheme r.hom.hom ∧ IsNormalSubgroupScheme r.hom.hom ∧
    Smooth R.X.hom ∧ ConnectedSpace R.X.left ∧ IsSolvableGroupScheme R.X ∧
    (∀ (S : Grp (Over (Spec (.of F)))) (s : S ⟶ H),
      IsClosedSubgroupScheme s.hom.hom → IsNormalSubgroupScheme s.hom.hom →
      Smooth S.X.hom → ConnectedSpace S.X.left → IsSolvableGroupScheme S.X →
        ∃ f : S ⟶ R, f ≫ r = s) ∧
    SolvableGroupStructure.IsFppfQuotient r.hom.hom q ∧
    (∃ (S : Grp (Over (Spec (.of F)))) (s : S ⟶ Q),
      ReductiveTorusCentralizer.IsMaximalTorus s) ∧
    ∀ (S : Grp (Over (Spec (.of F)))) (s : S ⟶ Q),
      ReductiveTorusCentralizer.IsMaximalTorus s → topologicalKrullDim S.X.left = 1

/-- A group-scheme map SL2 → H, expressed on actual matrix points over every algebra.
Naturality is with respect to every algebra map, not just field extensions.
Source: Milne, 20.32 and 21.11(b)
(blueprint: def-sfb-rank-one-root-interfaces). -/
structure SL2Hom {F : Type u} [Field F] (H : Grp (Over (Spec (.of F)))) where
  /-- The homomorphism on determinant-one matrices. -/
  app (A : CommAlgCat.{u} F) : Matrix.SpecialLinearGroup (Fin 2) A →*
    (StandardGroupSchemes.affine F A ⟶ H.X)
  /-- Compatibility with extension of scalars. -/
  naturality {A B : CommAlgCat.{u} F} (f : A ⟶ B)
    (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    StandardGroupSchemes.map F f.hom ≫ app A g =
      app B (Matrix.SpecialLinearGroup.map f.hom.toRingHom g)

/-- The scheme-theoretic image of an SL2 map is the smallest closed subgroup containing
its image on all algebra points. This retains infinitesimal kernels and images.
Source: Milne, 20.32 and 21.11(b)
(blueprint: def-sfb-rank-one-root-interfaces). -/
def SL2Hom.IsImage {F : Type u} [Field F] {H D : Grp (Over (Spec (.of F)))}
    (v : SL2Hom H) (d : D ⟶ H) : Prop :=
  IsClosedSubgroupScheme d.hom.hom ∧
    (∀ A : CommAlgCat.{u} F, Set.range (v.app A) ⊆
      pointImage d (StandardGroupSchemes.affine F A)) ∧
    ∀ (K : Grp (Over (Spec (.of F)))) (j : K ⟶ H),
      IsClosedSubgroupScheme j.hom.hom →
      (∀ A : CommAlgCat.{u} F, Set.range (v.app A) ⊆
        pointImage j (StandardGroupSchemes.affine F A)) → ∃ f : D ⟶ K, f ≫ j = d

end AlgebraicGeometry.RankOneRoots

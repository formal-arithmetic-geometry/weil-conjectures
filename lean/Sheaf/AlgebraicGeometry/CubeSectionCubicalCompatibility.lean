/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.Combinatorics.DisjointCubicCocycleIntegration

/-! # The cube section preserves the induced cubical structure

Source: Moret-Bailly, Pinceaux de varietes abeliennes, I §2, especially I 2.4.5;
the explicit nine-variable interchange argument in the DAG
(blueprint: lem-sfb-cube-section-cubical-compatibility).

The induced section is specified on simultaneous local frames, fixing all scalar
normalizations. The final two equations are exactly the rigidification and cube-section
conditions of `CubicalRigidifiedLine.Iso`, with underlying isomorphism the given section.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.CubicalLine

/-- Generalized points of the triple product, with their componentwise group structure.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable def cubePoints {S : Scheme.{u}} (G : Over S) [CommGrpObj G] :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (Fin 3 → (T.unop ⟶ G))
  map f := CommGrpCat.ofHom
    { toFun := fun x i ↦ f.unop ≫ x i
      map_one' := by funext i; exact ((yonedaMonObj G).map f).hom.map_one
      map_mul' := fun x y ↦ by
        funext i
        exact ((yonedaMonObj G).map f).hom.map_mul (x i) (y i) }

/-- The actual product projections represent componentwise generalized points.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable def cubePointsRepresentable {S : Scheme.{u}} (G : Over S) [CommGrpObj G] :
    (cubePoints G ⋙ forget _).RepresentableBy (cube G) where
  homEquiv :=
    { toFun := fun a i ↦ a ≫ Pi.π (fun _ : Fin 3 ↦ G) i
      invFun := Pi.lift
      left_inv := fun a ↦ by apply Pi.hom_ext; intro i; simp
      right_inv := fun x ↦ by funext i; simp }
  homEquiv_comp f g := by
    funext i
    exact Category.assoc f g (Pi.π (fun _ : Fin 3 ↦ G) i)

/-- The product group law on the existing triple fibre product, constructed by Yoneda
from coordinatewise multiplication, identity and inverse. No group structure is assumed.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable instance cube_commGrpObj {S : Scheme.{u}} (G : Over S) [CommGrpObj G] :
    CommGrpObj (cube G) :=
  CommGrpObj.ofRepresentableBy (cube G) (cubePoints G) (cubePointsRepresentable G)

/-- Complete a forward frame by its inverse when invertible, and zero otherwise.
The latter branch is used only at irrelevant entries of a partial frame.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable def frameInverse {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) : N ⟶ M :=
  by
    classical
    exact if h : IsIso f then @CategoryTheory.inv _ _ _ _ f h else 0

/-- Tensor the signed frames using the actual evaluation map of the existing word.
Only entries where the finitely many factors are framed will be tested.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable def Word.tensorFrame {X Y T : Scheme.{u}} (A : Word X Y)
    (L : Y.Modules) (b : Frame T L) : Frame T (A.module L) :=
  fun a ↦ ⟨A.frameMap a L b, frameInverse (A.frameMap a L b)⟩

/-- The supplied rigidification at the identity, extended by zero at all other entries.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable def identityFrame {S : Scheme.{u}} {G : Over S} [CommGrpObj G]
    (L : CubicalRigidifiedLine G) : Frame S L.line := by
  classical
  exact fun a ↦ if h : a = (η[G]).left then
    ⟨(eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj L.line) h) ≪≫
      L.rigidification).hom,
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj L.line) h) ≪≫
        L.rigidification).inv⟩ else ⟨0, 0⟩

/-- The canonical unit frame at every map, with the standard pullback/unit comparison.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable def unitFrame {X : Scheme.{u}} (T : Scheme.{u}) :
    Frame T (𝟙_ X.Modules) :=
  fun a ↦ ⟨(pullbackUnit a).hom, (pullbackUnit a).inv⟩

/-- The signed product of the eight pulled-back original cube values. Positive factors
are the triple and singletons; negative factors are the pairs and the empty set.
The inverse is evaluated only on invertible frame values in `InducedCubeSection`.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
noncomputable def inducedCubeValue {S : Scheme.{u}} {G : Over S} [CommGrpObj G]
    (L : CubicalRigidifiedLine G) (T : Over S) (x : Fin 3 → (T ⟶ cube G))
    (b : Frame T.left L.line) : 𝟙_ T.left.Modules ⟶ 𝟙_ T.left.Modules :=
  value L.sectionIso T (fun i ↦ x i ≫ sumMap G {0, 1, 2}) b ≫
  value L.sectionIso T (fun i ↦ x i ≫ sumMap G {0}) b ≫
  value L.sectionIso T (fun i ↦ x i ≫ sumMap G {1}) b ≫
  value L.sectionIso T (fun i ↦ x i ≫ sumMap G {2}) b ≫
  frameInverse (value L.sectionIso T (fun i ↦ x i ≫ sumMap G {0, 1}) b) ≫
  frameInverse (value L.sectionIso T (fun i ↦ x i ≫ sumMap G {0, 2}) b) ≫
  frameInverse (value L.sectionIso T (fun i ↦ x i ≫ sumMap G {1, 2}) b) ≫
  frameInverse (value L.sectionIso T (fun i ↦ x i ≫ sumMap G ∅) b)

/-- The induced tensor-product cube section: in every simultaneous local frame its
value is the product of the sections of the signed homomorphism pullbacks. These are
finite local tests, not an assumption that all pullbacks of L are globally trivial.
They determine the section uniquely, including on nonreduced schemes.
Source: Moret-Bailly I §2 (blueprint: lem-sfb-cube-section-cubical-compatibility). -/
def InducedCubeSection {S : Scheme.{u}} {G : Over S} [CommGrpObj G]
    (L : CubicalRigidifiedLine G)
    (σ : 𝟙_ (cube (cube G)).left.Modules ≅ theta (cube G) (theta G L.line)) : Prop :=
  ∀ (T : Over S) (x : Fin 3 → (T ⟶ cube G)) (b : Frame T.left L.line),
    (∀ I : Finset (Fin 3), Framed T (fun i ↦ x i ≫ sumMap G I) b) →
    Framed T x ((thetaWord G).tensorFrame L.line b) →
    value σ T x ((thetaWord G).tensorFrame L.line b) = inducedCubeValue L T x b

/-- The given cube section is a cubical rigidification-preserving isomorphism from
the unit line to the signed tensor product of its eight homomorphism pullbacks.
The conclusion exposes the induced rigidification r, induced cube section σ, and
unit cube section ε with their canonical frame formulas, then states both conditions
of `CubicalRigidifiedLine.Iso` for the specified underlying isomorphism L.sectionIso.
Source: Moret-Bailly I §2, especially I 2.4.5; agent-written nine-variable interchange
argument in the DAG (blueprint: lem-sfb-cube-section-cubical-compatibility).

Proof, following all five node steps:
1. Commutativity makes every sumMap a homomorphism, including the empty sum.
Pull back the cubical identities, multiply them for tensors and invert them for
negative factors. The normalized tensor/composition comparisons from
lem-weil-pbc-invertible-pullback-tensor identify the underlying line with theta.
Its local frames give r and σ with the displayed formulas. The structure line has
the unit frame, giving ε and its cubical identities.
2. Over H^3, H=G^3, write s(R,C) for the sum of the entries in the indicated
rectangle of the universal three-by-three matrix. Both iterated cube constructions
have signed factors s(R,C)^*L with exponent (-1)^(3-|R|) (-1)^(3-|C|).
3. Trivialize simultaneously the finitely many lines indexed by subsets of the nine
entries, choosing the empty frame from r. The original section gives symmetric
normalized unit coefficients t(U,V,W) for disjoint subsets. Its four-point cocycle
is the disjoint-subset cocycle. Apply lem-sfb-disjoint-cubic-cocycle-integration to
the group of local units; rescaling by its c(B) makes every such coefficient one.
4. In these new frames, both the column-then-row and row-then-column sections are
exactly the product of the rectangle frames with those same signs. Empty subsets
also have coefficient one. Commutativity reorders the factors, and sheaf equality
glues the equality on all of H^3. This proves the last, nine-variable equation.
5. At the identity all eight factors are e^*L; applying the supplied rigidification
to each signed factor gives r. Identity-face normalization sends tau(e,e,e) to one,
proving the penultimate equation. No properness, smoothness, reducedness,
connectedness, or characteristic hypothesis is used. -/
theorem cube_section_cubical_compatibility {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    (L : CubicalRigidifiedLine G) :
    (theta G L.line).IsInvertible ∧
    ∃ (r : (Scheme.Modules.tensorPullback (η[cube G]).left).obj (theta G L.line) ≅
          𝟙_ S.Modules)
      (σ : 𝟙_ (cube (cube G)).left.Modules ≅ theta (cube G) (theta G L.line))
      (ε : 𝟙_ (cube (cube G)).left.Modules ≅ theta (cube G) (𝟙_ (cube G).left.Modules)),
      r.hom = (thetaWord G).frameMap (η[cube G]).left L.line (identityFrame L) ∧
      InducedCubeSection L σ ∧ Compatible σ ∧
      ε.inv = ((Scheme.Modules.tensorPullbackSectionId (cube (cube G)).left).app
        (theta (cube G) (𝟙_ (cube G).left.Modules))).inv ≫
        (thetaWord (cube G)).frameMap (𝟙 _) (𝟙_ (cube G).left.Modules)
          (unitFrame (cube (cube G)).left) ∧
      Compatible ε ∧
      (Scheme.Modules.tensorPullback (η[cube G]).left).map L.sectionIso.hom ≫ r.hom =
        (pullbackUnit (η[cube G]).left).hom ∧
      ε ≪≫ (thetaWord (cube G)).mapIso L.sectionIso = σ := by
  sorry

end AlgebraicGeometry.CubicalLine

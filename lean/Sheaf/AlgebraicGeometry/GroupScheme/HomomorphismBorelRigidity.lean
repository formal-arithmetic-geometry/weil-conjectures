module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Homomorphisms determined by restriction to a Borel subgroup

Source: Milne, Algebraic Groups (2017), Proposition 17.21, printed p.358, case R = k.
(blueprint: lem-sfb-homomorphism-borel-rigidity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Two homomorphisms of smooth connected affine finite-type group schemes over an
algebraically closed field agree if their restrictions to a Borel subgroup agree.
Both the hypothesis and the conclusion are equalities of scheme morphisms, retaining
all algebra-valued points, including points over nonreduced algebras. The Borel predicate
uses the scheme-theoretic commutator subgroup and termination of its derived series.

Source: Milne, Algebraic Groups (2017), Proposition 17.21, printed p.358, case R = k.
(blueprint: lem-sfb-homomorphism-borel-rigidity)

Proof:
1. Apply lem-sfb-general-borel-flag-variety to obtain the nonempty smooth connected proper
   separated finite-type flag scheme X and the point with stabilizer B. Its reduced orbit
   from lem-sfb-smooth-group-orbit-geometry contains every closed point: these are rational
   by lem-weil-pbc-closed-point-residue-field-base and the action is transitive on rational
   points. By lem-sc-lft-over-field-jacobson-space it is dense and hence open, and its closed
   complement is empty. Smoothness makes X reduced by sbc-lem-smooth-geometrically-reduced,
   so the reduced orbit is X as a scheme.
2. By lem-sfb-homogeneous-orbit-quotient-geometry, q : A → X is faithfully flat, with kernel
   pair A × B → A ×_X A given by (a,b) ↦ (a,ab). It is quasi-compact by clause (b) of
   lemma-nagata-finite-type-to-separated-target. Thus it is an fpqc covering in the sense
   of def-weil-pbc-fpqc-covering: inverse images of affine opens have finite affine covers.
3. Set δ(a) = u(a)v(a)⁻¹ using def-sc-group-scheme. Agreement on B gives
   δ(ab) = u(a)u(b)v(b)⁻¹v(a)⁻¹ = δ(a) on every test algebra. This is an identity of
   morphisms on A × B. By lem-weil-pbc-fpqc-representable-descent it descends uniquely to
   δ̄ : X → D. The same uniqueness after composition with the structure maps proves that
   δ̄ is an F-morphism.
4. By lem-weil-pbc-proper-reduced-algclosed-global-sections-product the structural map
   F → Γ(X,O_X) is an isomorphism. Since D is affine, the natural bijection of
   lem-a1-locally-ringed-space-affine-adjunction identifies δ̄ with a constant F-morphism:
   invert that structural map and compose with the ring map induced by δ̄. This gives
   equality of scheme morphisms, including all nonreduced test algebras.
5. Evaluate at the identity of A. Homomorphisms preserve identity, so the constant value
   of δ̄ is the identity of D. Therefore u(a)v(a)⁻¹ = 1 on all test algebras; cancellation,
   equivalently the group-object diagrams of def-sc-group-scheme, gives u = v. -/
theorem hom_ext_of_borel {F : Type u} [Field F] [IsAlgClosed F]
    (A D B : Over (Spec (.of F))) [GrpObj A] [GrpObj D] [GrpObj B]
    [Smooth A.hom] [ConnectedSpace A.left] [IsAffine A.left]
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    [Smooth D.hom] [ConnectedSpace D.left] [IsAffine D.left]
    [LocallyOfFiniteType D.hom] [QuasiCompact D.hom]
    (i : B ⟶ A) (hB : IsBorelGroupScheme i)
    (u v : A ⟶ D) [IsMonHom u] [IsMonHom v]
    (h : (i ≫ u).left = (i ≫ v).left) : u.left = v.left := by
  sorry

end AlgebraicGeometry

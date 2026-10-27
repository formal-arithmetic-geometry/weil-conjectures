/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomRationalPoints
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Smooth multiplicative covers lifting projective representations

Source: Milne, Algebraic Groups (2017), Proposition 18.22, proof p.393, Example 5.49,
p.111, and Proposition 18.6(a), p.388
(blueprint: lem-sfb-projective-representation-smooth-lift).

The quotient is specified by its fppf sheaf universal property, uniformly also in rank one.
A basis identifies GL(V) and SL(V) with the recorded matrix schemes of rank dim(V).
The fibre product is specified by its universal property. Its reduced neutral component
is the actual nilradical reduction of the open neutral component, not an unspecified cover.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ProjectiveRepresentationSmoothLift

variable {F : Type u} [Field F]

/-- The positive dimension of a nonzero finite-dimensional vector space, supplied by
Mathlib's `Module.finrank_pos` for the existing roots-of-unity group interface.
Source: Milne Example 5.49, p.111
(blueprint: lem-sfb-projective-representation-smooth-lift). -/
instance spaceRank_neZero (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] : NeZero (Module.finrank F V) :=
  NeZero.of_pos (Module.finrank_pos (R := F) (M := V))

/-- Reduction of an open subscheme, with its inherited structure morphism to Spec F.
Source: Milne Proposition 18.6(a), p.388; Proposition 1.26, p.13
(blueprint: lem-sfb-projective-representation-smooth-lift). -/
def reducedOpen (E : Over (Spec (.of F))) (U : E.left.Opens) : Over (Spec (.of F)) :=
  Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ E.hom)

/-- The canonical inclusion of that reduced open into E.
Source: Milne Proposition 18.6(a), p.388; Proposition 1.26, p.13
(blueprint: lem-sfb-projective-representation-smooth-lift). -/
def reducedOpenι (E : Over (Spec (.of F))) (U : E.left.Opens) : reducedOpen E U ⟶ E :=
  Over.homMk (U.toScheme.nilradical.subschemeι ≫ U.ι)

/-- Every projective representation has the specified smooth connected multiplicative cover.
The matrix schemes have rank dim(V); choosing any basis of V gives this coordinate form.
The two quotient hypotheses are precisely scalar invariance and the universal property of
fppf sheafification of scalar orbits, not a pointwise quotient on field-valued points.
Source: Milne Proposition 18.22, proof p.393; Example 5.49, p.111; Propositions 1.26 and 1.38,
Corollary 1.39, pp.13,17; Proposition 18.6(a), p.388; Proposition 5.47, pp.110--111
(blueprint: lem-sfb-projective-representation-smooth-lift).

Proof:
1. If dim(V)=1, the scalar quotient is trivial and SL(V)=1. The pullback is G, and its
reduced neutral component is G because G is smooth connected. The identity is faithfully
flat with kernel D(0)=mu_1. This is the fibre-product definition and
sbc-lem-smooth-geometrically-reduced.
2. For higher rank, lem-sfb-projective-matrix-central-cover and
lem-sfb-projective-frames-pgl identify the same scalar quotient. SL -> PGL is finite
surjective with scalar kernel mu_n. Form the group-scheme pullback E with componentwise
operations (def-pc-fibre-product). The affine-spectrum fibre-product formula makes E affine;
finite and surjective base change make E -> G finite surjective, hence E is finite type.
3. Apply lem-sfb-locally-algebraic-group-identity-component to E. Its neutral component U
is clopen and its reduction is smooth connected. Reduction commutes with open restriction,
so this is also (E_red)^0. Its inclusion in E is closed, hence affine and finite;
composition with E -> G makes q finite.
4. By lem-sfb-group-neutral-component-translates, finitely many translates of U cover E.
Their images are closed translates of the image of U (finite maps are closed, by
lem-weil-pbc-finite-closed-map-finite-fibres). Connected G is irreducible by
lem-sfb-locally-algebraic-group-identity-component. One of these finitely many closed
translates must be G; translating back shows U -> G is surjective. Reduction does not
change the underlying space, so q is surjective.
5. Lem-weil-pbc-finite-geometric-point-lift lifts every F-point of G through q.
Lem-sfb-affine-group-homomorphism-image, since G is smooth, now gives faithful flatness
of the coordinate algebra map F[G] -> F[H].
6. Kernels as fibre products give ker(E -> G)=mu_n, with its scalar inclusion. Thus
ker(q) -> mu_n is the base change of the closed immersion H -> E, hence is closed
(lem-weil-pbc-closed-immersion-base-change). Its coordinate algebra is a quotient of
F[z,z^-1]/(z^n-1), spanned by 1,z,...,z^(n-1). Applying
lem-sfb-split-torus-subgroups-diagonalizable to this closed subgroup of Gm gives D(M)
for a finite abelian M, with its canonical group-algebra Hopf operations.
7. Restrict the second projection to H to get rho. The pullback square gives
rho followed by SL -> PGL = q followed by a. All kernel identifications are on schemes,
including nonreduced tests; there is no assumption that n is prime to the characteristic. -/
theorem smooth_lift
    [IsAlgClosed F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V]
    (P : Grp (Over (Spec (.of F))))
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [QuasiCompact P.X.hom]
    (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} (Module.finrank F V)) F ⟶ P.X)
    [IsMonHom π]
    (hscalar : ∀ (T : Over (Spec (.of F)))
      (g : T ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} (Module.finrank F V)) F)
      (z : T ⟶ StandardGroupSchemes.multiplicative F),
      (g * (z ≫ ProjectiveMatrixCentralCover.scalar F (Module.finrank F V))) ≫ π = g ≫ π)
    (hquotient : ∀ (S : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u))
      (b : yoneda.obj
        (GeneralLinearGroup (LinearGroupSchemes.Index.{u} (Module.finrank F V)) F) ⟶ S.obj),
      (∀ (T : Over (Spec (.of F)))
        (g : T ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} (Module.finrank F V)) F)
        (z : T ⟶ StandardGroupSchemes.multiplicative F),
        b.app (op T) (g * (z ≫ ProjectiveMatrixCentralCover.scalar F (Module.finrank F V))) =
          b.app (op T) g) →
      ∃! c : yoneda.obj P.X ⟶ S.obj, yoneda.map π ≫ c = b)
    (G : Over (Spec (.of F))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left] (a : G ⟶ P.X) [IsMonHom a] :
    ∃ (E : Grp (Over (Spec (.of F)))) (p : E.X ⟶ G)
      (r : E.X ⟶ LinearGroupSchemes.specialLinear F (Module.finrank F V)),
      IsMonHom p ∧ IsMonHom r ∧
      IsAffine E.X.left ∧ LocallyOfFiniteType E.X.hom ∧ QuasiCompact E.X.hom ∧
      IsPullback p r a (LinearGroupSchemes.inclusion F (Module.finrank F V) ≫ π) ∧
      ∃ U : E.X.left.Opens,
        (U : Set E.X.left) = connectedComponent (GrpObj.onePoint E.X) ∧
        ∃ gH : GrpObj (reducedOpen E.X U),
          IsMonHom (reducedOpenι E.X U) ∧
          IsClosedImmersion (reducedOpenι E.X U).left ∧
          IsAffine (reducedOpen E.X U).left ∧
          LocallyOfFiniteType (reducedOpen E.X U).hom ∧
          QuasiCompact (reducedOpen E.X U).hom ∧
          Smooth (reducedOpen E.X U).hom ∧ ConnectedSpace (reducedOpen E.X U).left ∧
          ∃ hq : IsMonHom (reducedOpenι E.X U ≫ p),
            IsMonHom (reducedOpenι E.X U ≫ r) ∧
            (reducedOpenι E.X U ≫ p).left.appTop.hom.FaithfullyFlat ∧
            (∃ (M : Type u) (_ : AddCommGroup M) (_ : Finite M)
              (e : GrpObj.ker (reducedOpenι E.X U ≫ p) ≅ (diagonalizableGroup F M).X),
              IsMonHom e.hom) ∧
            ∃ j : GrpObj.ker (reducedOpenι E.X U ≫ p) ⟶
                StandardGroupSchemes.roots F (Module.finrank F V),
              IsClosedSubgroupScheme j ∧
              j ≫ StandardGroupSchemes.rootsInclusion F (Module.finrank F V) ≫
                  ProjectiveMatrixCentralCover.scalar F (Module.finrank F V) =
                GrpObj.kerι (reducedOpenι E.X U ≫ p) ≫ reducedOpenι E.X U ≫ r ≫
                  LinearGroupSchemes.inclusion F (Module.finrank F V) ∧
              (reducedOpenι E.X U ≫ r) ≫
                  (LinearGroupSchemes.inclusion F (Module.finrank F V) ≫ π) =
                (reducedOpenι E.X U ≫ p) ≫ a := by
  sorry

end AlgebraicGeometry.ProjectiveRepresentationSmoothLift

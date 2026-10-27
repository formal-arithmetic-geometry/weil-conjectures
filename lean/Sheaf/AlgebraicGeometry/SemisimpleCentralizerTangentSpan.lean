/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus
import WeilConjectures.AlgebraicGeometry.GroupScheme.LieLocalDimension
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Tangent spanning by proper semisimple centralizers

Source: Milne, Algebraic Groups (2017), Propositions 17.76--17.79, pp.377--378,
and Theorem 17.91, p.381 (blueprint: lem-sfb-semisimple-centralizer-tangent-span).

## Main definitions

- `scalarExtension`: the existing pullback functor on bundled group objects.
- `geometricTangentMatrix`: the actual epsilon coefficient of the base-changed representation.
- `IsIndex`: the rational noncentral semisimple tangent vectors.
- `Centralizer`: a representative of the specified stabilizer functor, without choosing one.

## Main statement

- `tangent_span`: geometric properties, tangent images, spanning and rational nonemptiness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SemisimpleCentralizerTangentSpan

/-- Scalar extension of the given group, with its transported group structure.
Source: Milne 17.79, p.378 (blueprint: lem-sfb-semisimple-centralizer-tangent-span). -/
noncomputable abbrev scalarExtension {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) (K : Type u) [Field K] [Algebra k K] :
    Grp (Over (Spec (.of K))) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp).obj G

/-- The differential of the base-changed representation, read as its epsilon coefficient.
The tangent point in G_K is projected to G, then mapped by the given representation.
Thus this uses the actual Lie algebra of the scalar-extended group, not an arbitrary map.
Source: Milne 17.79, p.378 and 10.14, p.190
(blueprint: lem-sfb-semisimple-centralizer-tangent-span). -/
noncomputable def geometricTangentMatrix {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i : G.X ⟶ GeneralLinearGroup ι k) (K : Type u) [Field K] [Algebra k K]
    (S : GrpObj.Lie (scalarExtension G K).X) : Matrix ι ι K :=
  ((GeneralLinearGroup.homMulEquiv ι k (DualNumber K)
    (Over.homMk ((GrpObj.tangentPoint S).left ≫
      pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ i.left)
      (by
        change ((GrpObj.tangentPoint S).left ≫
          pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
            i.left) ≫ (GeneralLinearGroup ι k).hom =
              Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber K)))
        simp only [Category.assoc, Over.w i, pullback.condition]
        rw [← Category.assoc]
        have h := Over.w (GrpObj.tangentPoint S)
        simp only [scalarExtension, Functor.mapGrp, Over.pullback_obj_hom] at h
        rw [h]
        change Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k K)) =
            Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber K)))
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2)) :
      GL ι (DualNumber K)) : Matrix ι ι (DualNumber K)).map TrivSqZeroExt.snd

/-- The rational indices in Milne 17.79: geometrically diagonalizable tangent matrices
which are not central in the actual tangent Lie algebra. Over the algebraic closure,
Mathlib's semisimple endomorphisms of a finite-dimensional space are diagonalizable.
Source: Milne 17.76--17.79, pp.377--378
(blueprint: lem-sfb-semisimple-centralizer-tangent-span). -/
def IsIndex {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    {G : Grp (Over (Spec (.of k)))} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i : G.X ⟶ GeneralLinearGroup ι k) [IsMonHom i] (X : GrpObj.Lie G.X) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin'
    ((GeneralLinearGroup.RationalHom.differential i X).map (algebraMap k K))) ∧
      ∃ Y : GrpObj.Lie G.X, ⁅X, Y⁆ ≠ 0

/-- A representative of the adjoint stabilizer functor. Its points are specified over
all commutative k-algebras by the faithful matrix action. The equality is equivalent to
Ad(g)(X tensor 1) = X tensor 1 by naturality and injectivity of the faithful differential.
No choice of a centralizer from a mere existence theorem is made here.
Source: Milne 17.76, p.377 (blueprint: lem-sfb-semisimple-centralizer-tangent-span). -/
structure Centralizer {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i : G.X ⟶ GeneralLinearGroup ι k) [IsMonHom i] (X : GrpObj.Lie G.X) where
  /-- The representing group scheme. -/
  group : Grp (Over (Spec (.of k)))
  /-- The structure map is locally of finite type. -/
  [finiteType : LocallyOfFiniteType group.X.hom]
  /-- The structure map is quasi-compact. -/
  [quasiCompact : QuasiCompact group.X.hom]
  /-- Its map to the ambient group. -/
  inclusion : group.X ⟶ G.X
  /-- The inclusion respects group multiplication. -/
  [hom : IsMonHom inclusion]
  /-- The inclusion is a closed subgroup scheme. -/
  closed : IsClosedSubgroupScheme inclusion
  /-- The defining adjoint stabilizer condition, on every test algebra. -/
  represents (R : Type u) [CommRing R] [Algebra k R] :
    Set.range (fun c : points group.X R ↦ c ≫ inclusion) =
      {g : points G.X R | Commute
        (GeneralLinearGroup.RationalHom.points i R g : Matrix ι ι R)
        ((GeneralLinearGroup.RationalHom.differential i X).map (algebraMap k R))}

attribute [instance] Centralizer.finiteType Centralizer.quasiCompact Centralizer.hom

/-- Proper semisimple centralizers have identity-component tangent images spanning Lie(G).

Source: Milne, Algebraic Groups (2017), Propositions 17.76--17.79, pp.377--378,
and Theorem 17.91, p.381 (blueprint: lem-sfb-semisimple-centralizer-tangent-span).

Proof for stage 3:
1. For each rational index apply lem-sfb-semisimple-tangent-stabilizer to the faithful
representation. Its centralizer C is smooth and closed, and its tangent image is the
bracket centralizer. Noncentrality makes that subspace proper, hence C is not G.
The representation has positive dimension since the geometric noncentral vector
excludes GL(0), although the statement permits the empty index type.
2. By lem-sfb-finite-type-group-identity-subgroup, K = C^0 is the open identity component
and a closed subgroup. It is affine and finite type as a closed subscheme of affine C.
lem-pc-open-immersion-smooth-composition makes K smooth; its rational identity gives
geometric connectedness by lem-sbc-connected-rational-point-geometrically-connected.
3. Dual-number tangent maps have one underlying point, the identity. By
lem-weil-pbc-morphism-factors-through-open-subscheme they factor uniquely through K.
Naturality in lem-sfb-affine-group-dual-number-calculus identifies its tangent image
with that of C, hence with the bracket centralizer.
4. lem-ag-smooth-lie-local-dimension and lem-ag-group-identity-local-dimension identify
tangent dimensions with global dimensions. The proper tangent subspace gives dim K < dim G.
5. Use lem-sfb-affine-group-lie-tangent-calculus and the dual-number calculus to identify
scalar extension, matrix brackets and dAd = ad. The characteristic polynomial of ad(Y)
has polynomial coefficients f_j(Y). The geometric noncentral semisimple element makes
some nonconstant coefficient nonzero, so fix a nonzero such polynomial f over k.
6. If char k = 0, k is perfect. For each rational Y with f(Y) nonzero, take its rational
semisimple Jordan part X by lem-sfb-algebraic-lie-additive-jordan. The nonzero eigenvalue
of ad(Y) persists in ad(X), so X is noncentral, semisimple, and commutes with Y.
7. If char k = p > 0, lem-sfb-restricted-rational-differentiation makes a high restricted
power X = Y^[p^N] rational and takes its faithful and adjoint matrices to p^N-th powers.
Over the algebraic closure, choose N large enough to kill the nilpotent Jordan part.
Then X is semisimple, noncentral (a nonzero adjoint eigenvalue stays nonzero), and
commutes with Y by faithfulness and the matrix power formula. No perfectness is needed.
8. Thus every rational Y in D(f) lies in one of these centralizers. A nonzero polynomial
over an infinite field has a rational nonzero value, by induction on the variables.
This proves nonemptiness of the indices. If their span W were proper, choose a nonzero
linear form l vanishing on W and a rational nonzero value of f*l. This contradicts
D(f) being contained in W. Therefore the tangent images span all of Lie(G). -/
theorem tangent_span
    {k K : Type u} [Field k] [Infinite k] [Field K] [Algebra k K] [IsAlgClosure k K]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i : G.X ⟶ GeneralLinearGroup ι k) [IsMonHom i] [IsClosedImmersion i.left]
    (hgeom : ∃ S : GrpObj.Lie (scalarExtension G K).X,
      Module.End.IsSemisimple (Matrix.toLin' (geometricTangentMatrix G i K S)) ∧
        ∃ T : GrpObj.Lie (scalarExtension G K).X, ⁅S, T⁆ ≠ 0) :
    ∃ C : ∀ X : {X : GrpObj.Lie G.X // IsIndex (K := K) i X}, Centralizer G i X.val,
      (∀ X, Smooth (GrpObj.identityComponent (C X).group.X).hom ∧
        GeometricallyConnected (GrpObj.identityComponent (C X).group.X).hom ∧
        IsAffine (GrpObj.identityComponent (C X).group.X).left ∧
        LocallyOfFiniteType (GrpObj.identityComponent (C X).group.X).hom ∧
        QuasiCompact (GrpObj.identityComponent (C X).group.X).hom ∧
        IsClosedSubgroupScheme
          (GrpObj.identityComponentι (C X).group.X ≫ (C X).inclusion) ∧
        topologicalKrullDim (GrpObj.identityComponent (C X).group.X).left <
          topologicalKrullDim G.X.left ∧
        Set.range (GrpObj.differential
          (GrpObj.identityComponentι (C X).group.X ≫ (C X).inclusion)) =
          {Y : GrpObj.Lie G.X | ⁅Y, X.val⁆ = 0}) ∧
      (⨆ X, (GrpObj.differential
        (GrpObj.identityComponentι (C X).group.X ≫ (C X).inclusion)).toLinearMap.range) = ⊤ ∧
      Nonempty {X : GrpObj.Lie G.X // IsIndex (K := K) i X} := by
  sorry

end AlgebraicGeometry.SemisimpleCentralizerTangentSpan

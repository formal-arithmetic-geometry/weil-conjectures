/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.TrivialTorusCoherentData
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Primitive line of an induced Borel character module

Source: Milne, Algebraic Groups (2017), Definition 22.21 and Proposition 22.22,
pp.468--469; Definition 21.72, Theorem 21.73(b) and Remark 21.74, p.448.
(blueprint: lem-sfb-induced-module-primitive-line)

The induced subspace is the existing sectionModule for the inverse character.
Fixedness and weight are tested on every algebra, including the universal points
and nonreduced test algebras. These are the coaction equalizer and character identity
for left translation, without finite-dimensionality of the induced module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RhoSection

/-- The module E_B(lambda), with the inverse in the right-equivariance convention.
This is a specialization of the recorded actual section subspace, not a new induction
construction. Source: Milne, Definition 22.21, p.468
(blueprint: lem-sfb-induced-module-primitive-line). -/
abbrev inducedCharacterModule {F : Type u} [Field F]
    (G B : Grp (Over (Spec (.of F)))) (iB : B ⟶ G)
    (lam : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :=
  sectionModule G B iB lam⁻¹ 1

/-- The U-fixed subspace of E_B(lambda). These equations hold over every algebra,
so they are equivalent to the coaction identity f mapping to f tensor 1, including
at universal and nonreduced points. Source: Milne, Proposition 22.22, pp.468--469
(blueprint: lem-sfb-induced-module-primitive-line). -/
def inducedFixedSpace {F : Type u} [Field F]
    (G B U : Grp (Over (Spec (.of F)))) (iB : B ⟶ G) (iU : U ⟶ B)
    (lam : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    Submodule F (Coordinate G.X) :=
  inducedCharacterModule G B iB lam ⊓
    ⨅ (A : Type u) (_ : CommRing A) (_ : Algebra F A)
      (g : StandardGroupSchemes.affine F A ⟶ G.X)
      (x : StandardGroupSchemes.affine F A ⟶ U.X),
      LinearMap.ker ((evaluate ((x ≫ iU.hom.hom ≫ iB.hom.hom)⁻¹ * g)).toLinearMap -
        (evaluate g).toLinearMap)

end AlgebraicGeometry.RhoSection

namespace AlgebraicGeometry

/-- A nonzero induced module has exactly one U-fixed line, of character w0(lambda).
The representative n0 and torus automorphism e encode conjugation by n0 inverse,
so e.hom followed by the restricted character is precisely w0(lambda).
The radical is specified by its largest smooth connected normal unipotent subgroup
property; no finite-dimensionality assumption is imposed on the induced module.

Source: Milne, Definition 22.21 and Proposition 22.22, pp.468--469;
Definition 21.72, Theorem 21.73(b) and Remark 21.74, p.448.
(blueprint: lem-sfb-induced-module-primitive-line)

Proof plan:
1. By lem-sfb-reductive-borel-pair-structure, S is reductive and B=U semidirect T.
   Rewrite ut as t(t inverse u t) to obtain the stated T times U isomorphism.
   By lem-sfb-longest-weyl-open-cell choose w0 and n0, and the dense open cell
   j(u,b)=u n0 b. The defining right semi-invariance kernel is preserved by left
   translation. Tensoring kernels over F preserves kernels, so the
   left regular coaction restricts to E; its counit and coassociativity restrict too.
2. Smoothness and sbc-lem-smooth-geometrically-reduced make S and U reduced.
   The affine open-cell map is quasi-compact and quasi-separated. By
   lemma-nagata-reduced-dense-image-schematic and def-nagata-scheme-theoretic-image,
   pullback of functions to this cell is injective. Restricting f to x n0 gives
   an injective map r:E to F[U], since j*f(x,b)=lambda(b) inverse r(f)(x).
   Direct substitution gives r(uf)(x)=r(f)(u inverse x) over every algebra.
3. By lem-sfb-comodule-finite-subrepresentation, a nonzero element of E lies in a
   nonzero finite-dimensional rational U-submodule M. Apply
   lem-sfb-unipotent-rational-representation-fixed-vector to obtain a nonzero
   vector fixed by U(F). In a basis, the coefficients of its coaction minus
   v tensor 1 vanish on all U(F). By lem-wf-affine-nullstellensatz-vanishing,
   these coefficients vanish, because F[U] is reduced and finitely generated.
   Thus E has a nonzero vector fixed in the coaction sense in all characteristics.
4. If f is U-fixed then r(f)(u inverse x)=r(f)(x) on every algebra. Set u=x
   and use the universal point over F[U] to conclude r(f) is constant. Hence
   evaluation f at n0 injects the invariant subspace into F. Its nonzero vector
   from step 3 makes that subspace one-dimensional.
5. For t in T(A), normality of U and right equivariance give
   r(tf)(x)=lambda(n0 inverse t n0) r(f)(t inverse x t).
   The latter function is constant for invariant f. Tensoring the injective r
   with A remains injective over the field F (choose a linear left inverse).
   Therefore tf=w0(lambda)(t)f for every A. This is exactly the character
   coaction identity on the entire invariant line. Conversely the equalizer
   equations defining inducedFixedSpace are precisely coaction fixedness, by
   evaluation on the universal pair of points over F[U] tensor F[S]. -/
theorem induced_module_primitive_line {F : Type u} [Field F] [IsAlgClosed F]
    (S T B U : Grp (Over (Spec (.of F))))
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (k : T ⟶ B)
    (hpair : IsRhoBorelPair iT iB k)
    (iU : U ⟶ B)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hUnormal : IsNormalSubgroupScheme iU.hom.hom)
    (hUsmooth : Smooth U.X.hom) (hUconnected : ConnectedSpace U.X.left)
    (hUunipotent : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left →
      SolvableGroupStructure.IsUnipotent N → ∃ f : N ⟶ U, f ≫ iU = iN)
    (a : ModObj T.X B.X)
    (ha : a.smul = (fst T.X B.X ≫ k.hom.hom) * snd T.X B.X *
      (fst T.X B.X ≫ k.hom.hom)⁻¹)
    (lam : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hlam : iU.hom.hom ≫ lam.hom.hom = 1) :
    IsIso ((fst T.X U.X ≫ k.hom.hom) * (snd T.X U.X ≫ iU.hom.hom)) ∧
    ∃ (w0 : RankOneRoots.Weyl iT) (n0 : RankOneRoots.normalizer iT) (e : T ≅ T),
      QuotientGroup.mk n0 = w0 ∧
      e.hom.hom.hom ≫ iT.hom.hom =
        (toUnit T.X ≫ n0.val⁻¹) * iT.hom.hom * (toUnit T.X ≫ n0.val) ∧
      (fun chi ↦ e.hom ≫ chi) '' RankOneRoots.roots T B a =
        (fun chi ↦ chi⁻¹) '' RankOneRoots.roots T B a ∧
      (RhoSection.inducedCharacterModule S B iB lam ≠ ⊥ →
        Module.finrank F (RhoSection.inducedFixedSpace S B U iB iU lam) = 1 ∧
        ∀ (f : RhoSection.Coordinate S.X),
          f ∈ RhoSection.inducedFixedSpace S B U iB iU lam →
          ∀ (A : Type u) [CommRing A] [Algebra F A]
            (t : StandardGroupSchemes.affine F A ⟶ T.X)
            (g : StandardGroupSchemes.affine F A ⟶ S.X),
            RhoSection.evaluate ((t ≫ iT.hom.hom)⁻¹ * g) f =
              RhoSection.characterValue (t ≫ e.hom.hom.hom ≫ k.hom.hom ≫ lam.hom.hom) *
                RhoSection.evaluate g f) := by
  sorry

end AlgebraicGeometry

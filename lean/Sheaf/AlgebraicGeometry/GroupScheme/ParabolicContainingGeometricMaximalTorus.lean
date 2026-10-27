module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Sheaf.AlgebraicGeometry.GroupScheme.BorelConjugationCover
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy

/-! # A torus in a parabolic extends to a geometrically maximal torus

Source: Milne, Algebraic Groups (2017), Theorem 17.82 and Corollary 17.83, p.379;
Theorem 17.10 and the paragraph after Definition 17.12, pp.354--355; Theorem 17.16,
p.356; Theorem 25.1, p.544
(blueprint: lem-sfb-parabolic-containing-geometric-maximal-torus).

The parabolic hypothesis spells out representability of the fppf coset sheaf.
The presheaf coequalizer is the presheaf of right cosets, and the bijection on
maps into every sheaf is precisely its sheafification universal property.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A prescribed closed torus in a parabolic lies in a torus of that parabolic
which is maximal in the ambient reductive group after every algebraic closure.
In `hquot`, the first parallel arrow projects `(g,p)` to `g`, and the second sends
it to `g * iP(p)`. Their presheaf coequalizer is therefore `A ↦ G(A)/P(A)`;
the represented sheaf and the universal arrow specify exactly its sheafification.

Source: Milne, Theorem 17.82, Corollary 17.83, p.379; Theorems 17.10 and 17.16,
pp.354--356; Theorem 25.1, p.544
(blueprint: lem-sfb-parabolic-containing-geometric-maximal-torus).

Proof, following the four steps of the node:
1. Among tori of P containing D, choose T of greatest dimension; the collection
   contains D. By lem-sfb-multiplicative-type-largest-subtorus these tori are smooth
   connected. The dimension bounds and strict increase for a proper smooth connected
   subgroup in lem-sfb-solvable-normal-subgroup-products make T maximal in P.
2. Fix any algebraic closure F/k. By lem-sfb-maximal-torus-field-extension, T_F is
   maximal in P_F. Closedness in the affine finite-type G gives affine finite-type
   P; smoothness and geometric connectedness give smooth connected P_F and G_F.
   By lem-pc-proper-base-change, (G/P)_F is proper. Its fppf local coset descriptions
   identify it with G_F/P_F, carrying the identity coset to the identity coset.
3. Choose a Borel B of G_F by lem-sfb-borel-conjugation-cover. Its action on the
   nonempty proper finite-type G_F/P_F has a rational fixed point by
   lem-sfb-solvable-proper-fixed-point. Lift it to g in G_F(F) using
   lem-sfb-homogeneous-orbit-quotient-geometry. The coset-fibre criterion on every
   algebra puts g⁻¹Bg inside P_F. By lem-sfb-borel-maximal-torus-conjugacy, this
   Borel contains a torus S maximal in G_F, hence also maximal in P_F.
4. Apply the conjugacy clause of lem-sfb-borel-maximal-torus-conjugacy to the
   smooth connected affine group P_F: an element p in P_F(F) conjugates S to T_F.
   Any larger torus in G_F containing T_F conjugates back to one containing S,
   so it equals T_F. Since T was chosen over k before F, the same T works for
   every algebraic closure and retains the prescribed inclusion D into P. -/
theorem exists_geometricMaximalTorus_containing_in_parabolic
    {k : Type u} [Field k] (G P D : Grp (Over (Spec (.of k))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iP : P ⟶ G) (hP : IsClosedSubgroupScheme iP.hom.hom)
    (hPsmooth : Smooth P.X.hom)
    (hPconnected : ConnectedSpace
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj P).X.left)
    (hquot : ∃ Q : Over (Spec (.of k)),
      IsProper Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
      Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of k))) (yoneda.obj Q) ∧
      ∃ ηq : coequalizer (yoneda.map (fst G.X P.X))
          (yoneda.map (lift (fst G.X P.X) (snd G.X P.X ≫ iP.hom.hom) ≫ μ[G.X])) ⟶
            yoneda.obj Q,
        ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type u),
          Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f))
    (iD : D ⟶ P) (hD : IsClosedSubgroupScheme iD.hom.hom)
    (hDtorus : MultiplicativeType.IsTorus D) :
    ∃ (T : Grp (Over (Spec (.of k)))) (iT : T ⟶ P),
      IsClosedSubgroupScheme iT.hom.hom ∧ MultiplicativeType.IsTorus T ∧
      (∃ j : D ⟶ T, j ≫ iT = iD) ∧
      ∀ (F : Type u) [Field F] [Algebra k F] [IsAlgClosure k F],
        ReductiveTorusCentralizer.IsMaximalTorus
          ((MultiplicativeType.baseChange (K := F)).map (iT ≫ iP)) := by
  sorry

end AlgebraicGeometry

module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotient
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource
import WeilConjectures.AlgebraicGeometry.Descent

/-! # Parameters for finite diagonalizable subgroup forms

Source: Conrad, Reductive group schemes, Lemma 2.3.4, printed pp.69-70
(blueprint: lem-sfb-finite-diagonalizable-subgroup-parameter).

Closed embedded subgroups are encoded by their ideal sheaves, so different
parametrizations of the same closed subgroup give one element of the parameter set.
The local isomorphisms compare abstract group schemes and do not compare embeddings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The set P_H(W) of closed subgroups of G_W that are fppf forms of D_A(M).
An ideal belongs to this set precisely when it is the ideal of a closed group
embedding whose source becomes isomorphic to D_A(M) on an fppf covering.
The isomorphisms impose no compatibility with the embedding into G.

Source: Conrad, Reductive group schemes, Lemma 2.3.4, printed pp.69-70
(blueprint: lem-sfb-finite-diagonalizable-subgroup-parameter). -/
def finiteDiagonalizableSubgroupParameters
    (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M]
    (G : Grp (Over (Spec (.of A)))) (W : Over (Spec (.of A))) : Type u :=
  { I : (pullback G.X.hom W.hom).IdealSheafData //
    ∃ (K : Grp (Over W.left)) (j : K ⟶ (Over.pullback W.hom).mapGrp.obj G),
      IsClosedImmersion j.hom.hom.left ∧ j.hom.hom.left.ker = I ∧
      ∃ (ι : Type (u + 1)) (U : ι → Scheme.{u}) (f : ∀ i : ι, U i ⟶ W.left),
        Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage W.left ∧
        ∀ i : ι, Nonempty ((Over.pullback (f i)).mapGrp.obj K ≅
          (Over.pullback (f i ≫ W.hom)).mapGrp.obj (ringDiagonalizableGroup A M)) }

/-- The fppf-form subgroup parameter functor has a quasi-affine, finitely
presented representing scheme. Naturality is stated on ideal sheaves: along
W' → W, the parameter is the inverse image of the closed subgroup of G_W.

Source: Conrad, Reductive group schemes, Lemma 2.3.4, printed pp.69-70
(blueprint: lem-sfb-finite-diagonalizable-subgroup-parameter).

Proof:
1. A[M] is free of rank |M|, and its basis multiplication relations give a finite
   algebra presentation. Thus H is finite locally free. Apply
   lem-sfb-finite-flat-group-hom-scheme to construct the affine finitely presented
   group Hom-scheme B, with its universal homomorphism H_B → G_B.
2. By lem-sfb-finite-locally-free-closed-embedding-locus the embedding locus V
   is quasi-compact open in B. Open immersions are etale and hence locally of
   finite presentation (lem-weil-pbc-open-immersion-etale, lem-kun-etale-lfp).
   Composition preserves local finite presentation
   (lem-sbc-locally-finite-presentation-composition). As a quasi-compact open of
   an affine scheme V is quasi-affine and separated, and V → S is of finite
   presentation, in the sense of def-weil-pbc-scheme-conventions.
3. By lem-sfb-relative-diagonalizable-character-duality, the automorphism
   functor of H is the finite constant group Gamma = Aut(M)^op, also on
   disconnected tests. It acts freely on V by precomposition: an embedding
   cancels on the left.
4. Each finite orbit in V lies in a principal affine open of B contained in V:
   use lem-weil-pbc-prime-avoidance and
   lem-weil-pbc-affine-open-section-vanishing-prime on the ideal of B minus V.
   By lem-sfb-admissible-free-finite-quotient obtain a separated scheme Q and a
   finite etale surjection V → Q with the action kernel-pair identity.
   Representable fpqc descent and lem-trf-fppf-covering-is-fpqc descend V → S
   to Q → S (lem-weil-pbc-fpqc-representable-descent).
5. The torsor has constant degree |Gamma|, which is positive. Finite etale
   implies finite locally free, so
   lem-sfb-finite-locally-free-quasi-affine-reflection shows Q → S quasi-affine.
   Local finite presentation descends by lem-trf-lfp-fppf-source-locality.
   Surjectivity from quasi-compact V and separatedness give quasi-compactness
   and quasi-separatedness, hence finite presentation of Q → S.
6. The universal closed subgroup on V has equal ideal sheaves on the action
   kernel pair, since precomposition does not change the image. Descend it
   uniquely using lem-pc-descent-finite-flat-closed-subschemes. The identity,
   multiplication and inverse descend by representable fpqc descent and the
   monomorphism into G_Q. The resulting subgroup is an fppf form of H.
7. Conversely, trivialize any subgroup form on its fppf cover. The embeddings
   give V-points whose images in Q agree on overlaps, by character duality.
   Glue the Q-points by representable descent. Uniqueness of embedded descent
   shows both constructions are inverse. The constructions commute with every
   base change (lem-galois-fpqc-covering-base-change), giving the stated
   naturality of the bijections. Take Y_H = Q.
8. If A is the zero ring all schemes over S are empty. If M is trivial there
   is just the identity subgroup and Q = S. The group algebra stays finite
   free in characteristics dividing |M|; H need not be reduced. No step needs
   reducedness, a Noetherian hypothesis, or invertibility of |M|. -/
theorem exists_finiteDiagonalizableSubgroupParameter
    (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Finite M]
    (G : Grp (Over (Spec (.of A))))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (i : ringDiagonalizableGroup A M ⟶ G) [IsClosedImmersion i.hom.hom.left] :
    ∃ Y : Over (Spec (.of A)),
      IsQuasiAffineHom Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
      QuasiCompact Y.hom ∧ QuasiSeparated Y.hom ∧
      ∃ e : ∀ W : Over (Spec (.of A)),
        (W ⟶ Y) ≃ finiteDiagonalizableSubgroupParameters A M G W,
        ∀ (W' W : Over (Spec (.of A))) (f : W' ⟶ W) (x : W ⟶ Y),
          (e W' (f ≫ x)).val = (e W x).val.comap
            (pullback.map G.X.hom W'.hom G.X.hom W.hom (𝟙 G.X.left) f.left (𝟙 _)
              ((Category.comp_id _).trans (Category.id_comp _).symm)
              ((Category.comp_id _).trans (Over.w f).symm)) := by
  sorry

end AlgebraicGeometry

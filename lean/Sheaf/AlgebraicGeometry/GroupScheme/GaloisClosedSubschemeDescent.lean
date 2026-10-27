module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.Galois.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Galois descent of closed subschemes and closed subgroup schemes

Source: Milne, Algebraic Groups (2017), Appendix A.64--A.66, printed pp.580--581;
Proposition 1.54(b), printed p.22, for the subgroup consequence.
(blueprint: lem-sfb-galois-closed-subscheme-descent)

Closed subschemes are represented by their defining `Scheme.IdealSheafData`. Their
base change is `IdealSheafData.comap`, so equality includes the full scheme structure.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The semilinear map `id_X × Spec σ` on `X_E`.
Source: Milne, Algebraic Groups (2017), A.65, printed p.581.
(blueprint: lem-sfb-galois-closed-subscheme-descent) -/
noncomputable def closedSubschemeGaloisMap {k E : Type u} [Field k] [Field E]
    [Algebra k E] (X : Over (Spec (.of k))) (σ : E ≃ₐ[k] E) :
    pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  baseChangeMap X.hom
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    (T' := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    (Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) =
        Spec.map (CommRingCat.ofHom (algebraMap k E))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact σ.commutes x))

/-- A Galois-invariant closed subscheme of `X_E` descends to exactly one closed subscheme of X.
Source: Milne, Algebraic Groups (2017), A.64--A.65, printed pp.580--581.
(blueprint: lem-sfb-galois-closed-subscheme-descent)

Proof:
1. On each affine U = Spec A, identify U_E with Spec (A ⊗[k] E), using
   lem-weil-pbc-open-fibre-product and lem-weil-pbc-fibre-product-affine-spectra.
   Let J_U be the defining ideal (def-sbc-closed-immersion-ideal-sheaf).
   The comap calculation lem-pc-ideal-sheaf-comap-affine-extension makes J_U stable
   under id ⊗ σ. Apply lem-sfb-galois-stable-subspace-descent: J_U is the extension
   of I_U = {a | a ⊗ 1 ∈ J_U}. This contraction is an ideal; its E-linear span
   equals its extended ideal since (a ⊗ 1)(b ⊗ c) = ab ⊗ c.
2. On principal opens use lem-weil-pbc-localization-tensor-over-base and
   lem-pc-ideal-sheaf-comap-affine-extension. Faithful flatness and ideal contraction
   (lem-weil-pbc-field-extension-base-change-faithfully-flat and
   lem-weil-pbc-faithfully-flat-ideal-contraction) give I_{U_f} = I_U A_f.
3. Glue by lem-weil-pbc-affine-ideals-closed-subscheme. Base change has ideal J_U
   on every U_E, so lem-weil-pbc-closed-immersions-equal-ideal-isomorphic identifies
   its closed immersion with the prescribed one, including nilpotents.
4. Any other descended ideal has the same extension J_U. Faithfully flat contraction
   forces equality on each affine U, hence equality of the ideal sheaves globally. -/
theorem existsUnique_idealSheafData_of_galois_invariant
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (J : (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))).IdealSheafData)
    (hJ : ∀ σ : E ≃ₐ[k] E, J.comap (closedSubschemeGaloisMap X σ) = J) :
    ∃! I : X.left.IdealSheafData,
      I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))) = J := by
  sorry

/-- The unique descended closed subscheme of a Galois-invariant closed subgroup is a
closed subgroup scheme.
Source: Milne, Algebraic Groups (2017), A.65--A.66, printed p.581, and Proposition 1.54(b).
(blueprint: lem-sfb-galois-closed-subscheme-descent)

Proof:
1. Apply existsUnique_idealSheafData_of_galois_invariant to the kernel ideal of i
   to obtain I and its uniqueness (steps 1--4 of the node).
2. Factorization through the closed subscheme of I is reflected after extension:
   on affine charts a pulled-back section of I vanishes after tensoring with E.
   The map B → B ⊗[k] E is injective by faithful flatness and ideal contraction.
   Thus it already vanishes over B, and the sheaf axiom and
   lem-weil-pbc-closed-immersion-lift-ideal-kills-sections give the factorization.
3. For every k-algebra R, extend points to R ⊗[k] E. The identity, product and
   inverse lie in the given subgroup after extension, hence in the descended
   subscheme by step 2. A closed immersion is injective on these points: maps
   from a quotient algebra are determined by their composites with its quotient.
   The pointwise subgroup condition of def-sc-group-scheme-subgroup therefore
   supplies the group scheme structure and the closed subgroup immersion j.
   Its kernel ideal is I, and uniqueness is precisely uniqueness of I above. -/
theorem exists_closedSubgroupScheme_of_galois_invariant
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (G : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (Z : Grp (Over (Spec (.of E))))
    (i : Z.X ⟶ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).mapGrp.obj G).X)
    [IsClosedSubgroupScheme i]
    (hZ : ∀ σ : E ≃ₐ[k] E, i.left.ker.comap (closedSubschemeGaloisMap G.X σ) = i.left.ker) :
    ∃ (H : Grp (Over (Spec (.of k)))) (j : H.X ⟶ G.X),
      IsClosedSubgroupScheme j ∧
      j.left.ker.comap (pullback.fst G.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))) = i.left.ker ∧
      ∀ I : G.X.left.IdealSheafData,
        I.comap (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))) =
          i.left.ker → I = j.left.ker := by
  sorry

end AlgebraicGeometry

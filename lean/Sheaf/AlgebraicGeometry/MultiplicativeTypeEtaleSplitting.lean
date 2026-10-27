module

public import Sheaf.AlgebraicGeometry.RelativeDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.GroupTheory.Finiteness
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Cover.Open
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale

/-! # Etale splitting of groups of multiplicative type

Source: Conrad, Reductive group schemes, Proposition B.3.4, printed pp.291–292
(blueprint: lem-sfb-multiplicative-type-etale-splitting).

The fppf and etale covering families use Mathlib precoverages. Splittings are
isomorphisms in the category of group objects over each member of the cover.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An fppf form of finite-type diagonalizable groups splits on an affine etale cover.
No restriction on the base or on torsion in the character groups is required.
Source: Conrad, Reductive group schemes, Proposition B.3.4, printed pp.291–292
(blueprint: lem-sfb-multiplicative-type-etale-splitting).

Proof:
1. On affine charts B ⊗[A] A[M] ≃ B[M] by b ⊗ a e_m ↦ ba e_m, with inverse
   b e_m ↦ b ⊗ e_m. These preserve all Hopf operations. Use the affine fibre-product
   formula, tensor pushout, affine adjunction and scheme-morphism gluing to obtain
   base change of D_U(M) on arbitrary schemes (def-sfb-ring-diagonalizable-group,
   lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-algebra-tensor-pushout-universal-property,
   lem-a1-locally-ringed-space-affine-adjunction, lem-weil-pbc-scheme-morphism-gluing).
   All families are sets as in def-weil-size-convention.
2. For every original cover index beta, form the isomorphism sheaf
   F_beta(Z) = Isom_Z-gp(D_Z(M_beta), H_Z). Base-changing fppf covers and using
   fpqc representable descent glues maps, inverses and their group identities
   uniquely (lem-trf-fppf-covering-base-change, lem-trf-fppf-covering-is-fpqc,
   lem-weil-pbc-fpqc-representable-descent).
3. Over V_alpha, relative character duality identifies F_beta with the scheme
   L_beta,alpha = coproduct over Isom_Z(M_alpha, M_beta) of V_alpha.
   On affine opens the labels of an isomorphism are uniquely locally constant;
   glue them and their inverses. Empty labels give the empty scheme
   (lem-sfb-relative-diagonalizable-character-duality, lem-pc-fppf-affine-open-cover,
   lem-weil-pbc-scheme-coproduct-family, lem-weil-pbc-scheme-morphism-gluing).
4. The map from the coproduct A_beta of the L_beta,alpha to F_beta has, over
   every scheme test Z with a section of F_beta, fibre product represented by
   the coproduct of Z ×_U V_alpha: the section determines its unique label.
   Its projection to Z is surjective, flat and locally finitely presented by the
   base-changed fppf cover and source locality
   (lem-weil-pbc-scheme-coproduct-family, lem-trf-fppf-covering-base-change,
   lem-weil-pbc-etale-composition-cancellation, lem-sfb-scheme-etale-source-target-properties).
5. Schemes are algebraic spaces by representable descent, scheme fibre products
   and their identity atlases (def-trf-algebraic-space, def-pc-fibre-product,
   lem-weil-pbc-fpqc-representable-descent, lem-trf-fppf-covering-is-fpqc,
   lem-weil-pbc-etale-composition-cancellation). Apply
   lem-sfb-fppf-space-atlas-bootstrap to A_beta → F_beta and choose a representable
   surjective etale scheme atlas W_beta → F_beta.
6. After base change to V_alpha the map W_beta → U factors through L_beta,alpha
   by two etale morphisms. Source locality and composition, followed by fpqc
   descent, show that W_beta → U is etale
   (lem-weil-pbc-scheme-coproduct-family, lem-weil-pbc-etale-composition-cancellation,
   lem-sfb-scheme-etale-source-target-properties, def-trf-algebraic-space,
   lem-trf-fppf-covering-is-fpqc, lem-galois-fpqc-descend-etale).
7. Every point of U lifts to some V_alpha. Its chosen splitting defines a
   field-valued point of F_alpha, which lifts after a field extension to its
   surjective atlas. Thus the W_beta jointly cover U. Evaluating each atlas
   map at its identity gives its splitting (def-trf-algebraic-space).
8. Refine each W_beta by affine opens and compose with its etale map to U
   (lem-pc-fppf-affine-open-cover, lem-weil-pbc-etale-composition-cancellation).
   Restrict the splitting and use step 1, keeping the character group M_beta.
   For the empty base choose the empty family; zero and torsion groups need
   no changes to this argument. -/
theorem multiplicativeType_etale_splitting (U : Scheme.{u}) (H : Grp (Over U))
    (V : U.Cover.{u} Scheme.fppfPrecoverage) (M : V.I₀ → AddCommGrpCat.{u})
    (hM : ∀ i : V.I₀, AddGroup.FG (M i))
    (hsplit : ∀ i : V.I₀,
      Nonempty ((Over.pullback (V.f i)).mapGrp.obj H ≅
        relativeDiagonalizableGroup (V.X i) (M i))) :
    ∃ W : U.Cover.{u} Scheme.etalePrecoverage,
      (∀ j : W.I₀, IsAffine (W.X j)) ∧
      ∃ N : W.I₀ → AddCommGrpCat.{u}, ∀ j : W.I₀,
        AddGroup.FG (N j) ∧
        Nonempty ((Over.pullback (W.f j)).mapGrp.obj H ≅
          relativeDiagonalizableGroup (W.X j) (N j)) := by
  sorry

end AlgebraicGeometry

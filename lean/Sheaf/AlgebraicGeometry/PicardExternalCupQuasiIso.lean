/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.PicardExternalCupAcyclic
import Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft
import Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension

/-! # Geometric invertibility of the normalized external cup comparison

Source: Stacks Project, Varieties, Tag 0BED, proof after equation 33.29.1.1.
(blueprint: lem-sc-picard-external-cup-quasi-iso).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Every cochain realization with the specified cup normalization induces isomorphisms
on natural-degree homology. No cochain map or cohomology model is chosen here.
Source: Stacks Project, Varieties, Tag 0BED, short exact sequence argument,
the two dimension-shifting inductions and the acyclic base case
(blueprint: lem-sc-picard-external-cup-quasi-iso).

Proof: Choose finite affine covers U of X and V of Y. Affine diagonal ensures that
all nonempty finite intersections are affine; the product cover W has the same
property. Affine Cech comparisons identify the factor and product cohomologies
with those of these covers. Refinement along the two projections and signed cup
define the Cech tensor-total comparison, normalized by Tags 01FD, 07MB and 0FKV.
Sections on affine intersections are exact on quasi-coherent modules, and field
tensor is exact. The affine pullback and tensor section formulas identify product
sections with tensors of factor sections. Consequently a short exact coefficient
sequence in either variable gives a map of short exact sequences of complexes.
The long exact sequences and five lemma give the two-out-of-three principle for
this Cech comparison to be a quasi-isomorphism.
Assign each coefficient a nonnegative cohomological bound, using finite
quasi-coherent cohomological dimension. Embed it in an acyclic quasi-coherent
module; the cokernel has bound smaller by one when the original bound is positive.
First induct on the bound for G with F acyclic, then induct on the bound for F
with arbitrary G. The base has both coefficients acyclic, including the zero case.
For affine V in Y, Cech(U times V, external coefficients) is Cech(U,F) tensor G(V).
Exact field tensor gives zero positive cohomology and Gamma(X,F) tensor G(V) in
degree zero. The higher-direct-image presheaf description therefore gives zero
positive higher direct images under pr2 and identifies its ordinary direct image
with Gamma(X,F) tensor G. Expand Gamma(X,F) in a basis. On qcqs Y cohomology
commutes with that direct sum; hence it vanishes in positive degrees and is the
section tensor product in degree zero. Leray degeneration computes the product
cohomology accordingly. Split the two vector-space complexes into their degree-zero
homology representatives and contractible pairs. Contracting either tensor factor
contracts its tensor summand, with the Koszul sign for the second factor. Thus the
tensor total too is concentrated in degree zero. The Cech comparison in degree zero
sends s tensor t to the product of their projection pullbacks, exactly the affine
section tensor isomorphism. This proves the base case and both inductions.
Finally transport the Cech homology comparison to the fixed resolution models via
picardScalarModelEquiv. The field-linear tensor Kunneth cycle formula and
surjectivity of each homology projection show that tensor-cycle classes span the
source homology. IsPicardExternalCupCochain identifies homologyMap c with the
transported Cech comparison on those classes. They are therefore equal as linear
maps. The latter is an isomorphism, so homologyMap c is one too, in every n. -/
theorem picardExternalCupCochain_isIso
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCupCochain f g F G c) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap c (n : ℤ)) := by
  let : X.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  have : IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k))) := by
    change IsAffineHom (pullback.diagonal f)
    infer_instance
  let : Y.Over (Spec (CommRingCat.of k)) := ⟨g⟩
  have : IsAffineHom (pullback.diagonal (Y ↘ Spec (CommRingCat.of k))) := by
    change IsAffineHom (pullback.diagonal g)
    infer_instance
  obtain ⟨dX, hdX⟩ := exists_quasicoherent_cohomology_bound k X
  obtain ⟨dY, hdY⟩ := exists_quasicoherent_cohomology_bound k Y
  have acyclic_left (F' : X.Modules) [F'.IsQuasicoherent]
      (hF' : ∀ p : ℕ, 0 < p →
        IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F')) :
      ∀ (d : ℕ) (G' : Y.Modules) [G'.IsQuasicoherent],
        (∀ p : ℕ, d < p →
          IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G')) →
        ∀ (c' : picardExternalTotal f g F' G' ⟶
          picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F' G')),
          IsPicardExternalCupCochain f g F' G' c' → ∀ n : ℕ,
            IsIso (HomologicalComplex.homologyMap c' (n : ℤ)) := by
    intro d
    induction d with
    | zero =>
      intro G' _ hG' c' hc' n'
      exact picardExternalCupCochain_isIso_of_acyclic k X Y f g F' G' hF' hG' c' hc' n'
    | succ d ih =>
      intro G' _ hG' c' hc' n'
      exact picardExternalCupCochain_isIso_shiftRight k X Y f g F' d ih G' hG' c' hc' n'
  have bounded_left : ∀ (d : ℕ) (F' : X.Modules) [F'.IsQuasicoherent],
      (∀ p : ℕ, d < p →
        IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F')) →
      ∀ (c' : picardExternalTotal f g F' G ⟶
        picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F' G)),
        IsPicardExternalCupCochain f g F' G c' → ∀ n : ℕ,
          IsIso (HomologicalComplex.homologyMap c' (n : ℤ)) := by
    intro d
    induction d with
    | zero =>
      intro F' _ hF' c' hc' n'
      exact acyclic_left F' hF' dY G (hdY G) c' hc' n'
    | succ d ih =>
      intro F' _ hF' c' hc' n'
      exact picardExternalCupCochain_isIso_shiftLeft k X Y f g G d ih F' hF' c' hc' n'
  exact bounded_left dX F (hdX F) c hc n

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.LinearAlgebra.SemilinearFrobenius

/-! # Compatible coherent Frobenius models for Artin--Schreier exact rows -/

@[expose] public section

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- Coherent Frobenius models and compatible Artin--Schreier exact rows under base change.
Source: Stacks Project, Tag 0A3P, proof, and Tag 02KH, flat coherent base change.
(blueprint: lem-pbc-artin-schreier-frobenius-exact-rows)

Proof: Take G and G' to be the universe-lifted additive structure sheaves on C and C'.
Use the Artin--Schreier sequence on each scheme, transporting the constant term on C'
through the inverse-image constant-sheaf isomorphism. The maps i and i' send a locally
constant prime-field section to that section times 1; wp and wp' act by x^p-x.
The structure-ring pullback gives q from the inverse image of G to G', and the formula
for constant sections gives the asserted square. The degree-zero maps are onto:
smoothness implies reducedness, and proper connectedness over an algebraically closed
field identifies the global sections with the field; x^p-x is onto that field. The
base-changed curve is again smooth, proper and connected, so the same argument applies.
Take V to be coherent H¹(C,O_C), with its actual scalar action. Proper coherent finiteness
makes it finite-dimensional. The etale/Zariski comparison gives b, while flat coherent
base change and the comparison on C' give b'. The sectionwise p-th power endomorphisms
induce semilinear F and F', since (cx)^p=c^p x^p. Naturality of powers under structure-ring
pullback gives the identity on pure tensors. Additivity of cohomology gives the formulas
for wp and wp'. The canonical flat base-change map sends a cohomology class v to 1 tensor v;
use the same affine-cover Cech comparisons on both schemes to obtain the last identity.
These comparisons commute with sectionwise powers even though Frobenius is not O-linear.
If C has dimension zero, smooth proper connected C is Spec k and coherent H¹ vanishes;
use the zero vector space, with the same degree-zero and exact-row arguments. This
statement supplies no degree-one kernel equivalence and uses no fixed-point invariance. -/
theorem exists_artinSchreier_frobenius_exact_rows
    {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    ∃ (V : ModuleCat.{u + 1} k) (_ : FiniteDimensional k V)
      (F : V →ₛₗ[frobenius k p] V)
      (F' : (k' ⊗[k] V) →ₛₗ[frobenius k' p] (k' ⊗[k] V)),
      (∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v) ∧
      ∃ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
        (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
        (i : C.constantZMod p ⟶ G)
        (i' : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj (C.constantZMod p) ⟶ G')
        (wp : G ⟶ G) (wp' : G' ⟶ G')
        (z : i ≫ wp = 0) (z' : i' ≫ wp' = 0)
        (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
        (b : Sheaf.H G 1 ≃+ V) (b' : Sheaf.H G' 1 ≃+ (k' ⊗[k] V)),
        (ShortComplex.mk i wp z).ShortExact ∧
        (ShortComplex.mk i' wp' z').ShortExact ∧
        Function.Surjective (Sheaf.H.map wp 0) ∧
        Function.Surjective (Sheaf.H.map wp' 0) ∧
        (Etale.upperStar AddCommGrpCat.{u + 1} ι').map i ≫ q = i' ∧
        (∀ x, b (Sheaf.H.map wp 1 x) = F (b x) - b x) ∧
        (∀ x, b' (Sheaf.H.map wp' 1 x) = F' (b' x) - b' x) ∧
        ∀ x, b' (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) =
          1 ⊗ₜ[k] b x := by sorry

end AlgebraicGeometry.IsCurve

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.RealBoundaryDecompositionLanding
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
public import Mathlib.Algebra.Algebra.Tower
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.HenselianLocalRootLifting

/-!
# Residue Galois surjectivity and arithmetic constants at a boundary point

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-boundary,
d-real-boundary.md, lines 15–36, and d-real-boundary.proof.md, first paragraph;
Stacks Project, Tags 0BSW and 0BUB (blueprint: lem-real-boundary-local-constants).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale

namespace RealSheaves

/-- Local residue surjectivity and its square with the arithmetic projection.
Source: blueprint main-20261015, d-real-boundary.md, lines 15–36 and the first paragraph
of its proof; Stacks Project, Tags 0BSW and 0BUB.
(blueprint: lem-real-boundary-local-constants)

The henselization and fraction field are the models used by
`exists_boundary_decomposition_landing`. The equivalence `es` identifies the residue of
the henselization with the stalk residue, and `hes` specifies the canonical identification.
The algebra structure `hks` is the scheme's structural residue-field map. The tower from
that residue field to `D.k` is the chosen embedding of constants. The equivalence `e` and
`he` identify reduction in the integral closure with this embedding, and `ha`, `hr` specify
restriction and reduction on every element, exactly as in the decomposition-landing node.

The point `u₀` is the image of the geometric point `b`, and `i` is its map of constants,
as specified by `hu₀` and `hi`. The map `p` is the arithmetic projection: `hp` characterizes
its action on every finite constant cover, using the recorded `fiberConstantCoverEquiv`.
Every embedding into the base-point field factors through `i`, since `D.k` is algebraically
closed. Thus `hp` specifies the full arithmetic projection, with no extra choice of action.
The formula `hθ` is precisely the path-transport formula of the recorded landing theorem;
it is imposed for an arbitrary path and every finite etale cover. The inclusion of residue
Galois groups is Mathlib's `AlgEquiv.restrictScalarsHom`; its range is `Gal(k/k_s)` inside
`Gal(k/k₀)`.

Proof, following the node's eight steps:
1. The field-extension projection from the geometric curve is surjective, hence the curve
is connected. Finite type over a field gives Noetherianity. Smoothness is preserved by base
change, and smooth algebras over a field have regular local rings. The regular, Noetherian,
nonempty connected curve and its geometric base change are therefore integral, by
`regular_normal_and_normal_decomposition`.
2. The open contains the generic point. A boundary point is nongeneric and closed, since
a further strict specialization would contradict dimension one. The closed-point field
theorem gives finite positive residue degree. The stalk is regular local of dimension one,
hence a DVR. The geometric open is irreducible and connected; Noetherianity and restriction
of the diagonal give finite type and separatedness of the open.
3. The henselization has unchanged residue field by its local universal property applied
to the residue field. The henselian residue Galois action supplies the integral closure,
its local structure, reduction homomorphism and equivariant identification of constants.
4. Apply lem-wf-strict-henselian-fraction-inertia to the DVR stalk. Its strict henselization
embeds in a separable closure and gives a surjective residue homomorphism. Restriction from
the algebraic closure to the separable closure is bijective: in positive characteristic,
extend automorphisms uniquely using the unique roots of sufficiently high p-powers.
Finite fields are perfect, so their separable closures are algebraic closures.
5. In the strict henselization, lift all simple roots of T^(q^n)-T by henselian root lifting.
These exhaust the roots in the algebraic closure, so all algebraic constants lie in the
strict henselization, and reduction identifies them with its residue closure. Apply the
same argument to the ordinary henselization to identify the structural finite residue
field. The two residue identifications are consequently compatible over that field.
6. Equivariance on constants identifies this strict-henselian residue action with the
actual action `r` specified by `hr`. The surjection in step 4 proves surjectivity of `r`.
7. On each finite constant cover, local fibre points are embeddings into the algebraic
constants. Equivariant reduction identifies their local action with postcomposition by
`r σ`. Finite-field Galois groups are cyclic, so this is also the deck transformation
given by the restriction of `r σ` to that finite field.
8. Naturality of the arbitrary path for these deck transformations identifies the action
at `u₀`. The constant-cover characterization of the arithmetic projection, as in
lem-wf-arithmetic-lift-fibre-path, proves the square on each finite subextension. Their
union is `D.k`, hence the homomorphisms agree. Surjectivity of `r` gives the stated equality
of subgroups.
-/
theorem boundary_local_constants
    (D : Setup.{u, v}) (C₀ : Scheme.{u}) [C₀.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀) (hS : (U₀ : Set C₀)ᶜ.Finite)
    (s : C₀) (hs : s ∉ U₀)
    [Algebra D.k₀ (C₀.residueField s)]
    (hks : algebraMap D.k₀ (C₀.residueField s) =
      (C₀ ↘ Spec (.of D.k₀)).residueFieldAlgebraMap s)
    (H : Type u) [CommRing H] [HenselianLocalRing H] [IsDomain H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    [Algebra (C₀.presheaf.stalk s) H]
    [IsScalarTower (C₀.presheaf.stalk s)
      (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    (hH : Algebra.IsHenselizationAtPrime' (C₀.presheaf.stalk s)
      (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s)) H)
    (es : IsLocalRing.ResidueField H ≃+* C₀.residueField s)
    (hes : ∀ x : C₀.presheaf.stalk s,
      es (IsLocalRing.residue H (algebraMap (C₀.presheaf.stalk s) H x)) = C₀.residue s x)
    (K : Type u) [Field K] [Algebra H K] [IsFractionRing H K]
    [Algebra (C₀.presheaf.stalk s) K] [IsScalarTower (C₀.presheaf.stalk s) H K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra H Ω] [IsScalarTower H K Ω]
    [IsLocalRing (integralClosure H Ω)]
    [IsLocalHom (algebraMap H (integralClosure H Ω))]
    (a : (Ω ≃ₐ[K] Ω) →* (integralClosure H Ω ≃ₐ[H] integralClosure H Ω))
    (ha : ∀ (σ : Ω ≃ₐ[K] Ω) (x : integralClosure H Ω), (a σ x : Ω) = σ (x : Ω))
    [Algebra (C₀.residueField s) D.k] [IsScalarTower D.k₀ (C₀.residueField s) D.k]
    [IsAlgClosure (C₀.residueField s) D.k]
    (e : IsLocalRing.ResidueField (integralClosure H Ω) ≃+* D.k)
    (he : ∀ x : H,
      e (IsLocalRing.residue (integralClosure H Ω) (algebraMap H (integralClosure H Ω) x)) =
        algebraMap (C₀.residueField s) D.k (es (IsLocalRing.residue H x)))
    (r : (Ω ≃ₐ[K] Ω) →* (D.k ≃ₐ[C₀.residueField s] D.k))
    (hr : ∀ (σ : Ω ≃ₐ[K] Ω) (x : integralClosure H Ω),
      r σ (e (IsLocalRing.residue (integralClosure H Ω) x)) =
        e (IsLocalRing.residue (integralClosure H Ω) (a σ x)))
    (ξ : Spec (.of K) ⟶ U₀.toScheme)
    (hξ : ξ ≫ U₀.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (C₀.presheaf.stalk s) K)) ≫
        C₀.fromSpecStalk s)
    (Ωu : Type u) [Field Ωu] [IsSepClosed Ωu]
    (b : Spec (.of Ωu) ⟶ D.geometricCurve U₀.toScheme)
    (u₀ : Spec (.of Ωu) ⟶ U₀.toScheme)
    (hu₀ : u₀ = b ≫ pullback.fst (U₀.toScheme ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (i : D.k →+* Ωu)
    (hi : Spec.map (CommRingCat.ofHom i) =
      b ≫ pullback.snd (U₀.toScheme ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (G₀ : Type u) [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [CompactSpace G₀]
    (e₀ : G₀ ≃ₜ* Aut (fiber u₀))
    (γ : fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ ξ) ≅ fiber u₀)
    (θ : (Ω ≃ₐ[K] Ω) →* G₀)
    (hθ : ∀ (σ : Ω ≃ₐ[K] Ω) (P : U₀.toScheme.FiniteEtale)
      (z : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ ξ)).obj P),
      (γ.inv.app P ((e₀ (θ σ)).hom.app P (γ.hom.app P z))).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left)
    (p : G₀ →* (D.k ≃ₐ[D.k₀] D.k))
    (hp : ∀ (g : G₀) (A : FiniteEtaleAlgebra D.k₀)
      (z : (fiber u₀).obj (constantCover (U₀.toScheme ↘ Spec (.of D.k₀)) A))
      (μ : A.1 →ₐ[D.k₀] D.k),
      (fiberConstantCoverEquiv (U₀.toScheme ↘ Spec (.of D.k₀)) u₀ A z).1 =
          i.comp μ.toRingHom →
        (fiberConstantCoverEquiv (U₀.toScheme ↘ Spec (.of D.k₀)) u₀ A
          ((e₀ g).hom.app (constantCover (U₀.toScheme ↘ Spec (.of D.k₀)) A) z)).1 =
            i.comp ((p g).toRingHom.comp μ.toRingHom)) :
    Module.Finite D.k₀ (C₀.residueField s) ∧
      0 < Module.finrank D.k₀ (C₀.residueField s) ∧
      Function.Surjective r ∧
      p.comp θ = (AlgEquiv.restrictScalarsHom D.k₀).comp r ∧
      (p.comp θ).range =
        (AlgEquiv.restrictScalarsHom D.k₀ :
          (D.k ≃ₐ[C₀.residueField s] D.k) →* (D.k ≃ₐ[D.k₀] D.k)).range := by
  sorry

end RealSheaves

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.GroupTheory.WeilGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

/-!
# Weil transport on finite étale fibres

Source: Stacks Project, Fundamental Groups, Tags 0BN5, 0BND, 0BTV and 0BTX; the finite-stage
argument in the current blueprint proof of lem-wf-finite-constant-h1-pi1
(blueprint: lem-wf-finite-etale-weil-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Covariant transport postcomposes a finite étale cover with a scheme automorphism and
leaves every underlying cover map unchanged. Source: Stacks Tags 0BN5 and 0BND and the
finite-stage argument for lem-wf-finite-constant-h1-pi1
(blueprint: lem-wf-finite-etale-weil-transport). -/
noncomputable def covariantTransport {U : Scheme.{u}} (a : Aut U) :
    U.FiniteEtale ⥤ U.FiniteEtale :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ MorphismProperty.Over.map (f := a.hom) ⊤
      (inferInstanceAs (Etale a.hom)))
    (fun P ↦ by
      have : IsFinite P.obj.hom := P.property
      exact inferInstanceAs (IsFinite (P.obj.hom ≫ a.hom)))

/-- The canonical map on the full automorphism groups of the geometric fibre functors.
It restricts an automorphism to base-changed covers and conjugates by the canonical fibre
identification; no choice of path is made. Source: Stacks Tag 0BND(3), construction of 0BN5
(blueprint: lem-wf-finite-etale-weil-transport). -/
noncomputable def fiberAutBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (g : Aut (fiber s)) : Aut (fiber (s ≫ f)) :=
  (pullbackFiberIso f s).symm ≪≫ Functor.isoWhiskerLeft (pullback f) g ≪≫ pullbackFiberIso f s

/-- Weil elements give natural transport of finite étale fibres, with conjugation by the
lift for covariant transport and by its inverse for pullback. The unique geometric
automorphism `h` is the specified conjugate inside the arithmetic automorphism group.
Source: Stacks Tags 0BN5, 0BND, 0BTV and 0BTX, finite-stage construction in the current
blueprint proof of lem-wf-finite-constant-h1-pi1
(blueprint: lem-wf-finite-etale-weil-transport).

Proof:
1. For every integer r, projection to P identifies (Phi^(-r))^*P with T_r P. The inverse
is the lift of id_P and Phi^r p. The fibre-product universal property proves the inverse
identities and naturality for every cover map (def-pc-fibre-product). Thus T_r is a functor
on finite étale covers, using base-change stability (def-weil-pbc-finite-etale-category).
2. Put F0 = F_(s over U0), and identify the geometric automorphism group with its normal
image in Aut(F0), using lem-galois-pi1-functoriality and lem-wf-weil-group-exact-sequence.
The degree-n lift acts on constant-cover field embeddings by geometric Frobenius^n
(def-wf-weil-group, def-weil-frobenius-detailed).
3. Descend any finite étale P to P_E at a finite subfield E of the closure, using
lem-wf-finite-etale-field-limit-descent(1). Finite fields are separable and normal by
lem-sfb-finite-field-galois-frobenius. The finite étale E-model Q is an arithmetic cover:
use lem-sc-finite-etale-algebra-criterion, lem-trf-finite-radicial-basechange, and
lem-weil-pbc-etale-composition-cancellation for its structure map.
4. Projection identifies F(T_r P) with the subset S_r of F0(Q) whose scalar embedding
is iota gamma^(-r)|E. The inverse is the unique fibre-product lift using that scalar map
(def-pc-fibre-product). This identification is a bijection j_r.
5. Naturality of the degree-n lift w on the constant E-cover carries S_n bijectively to
S_0. Set tau_P = j_0^(-1) w_Q j_n; its inverse uses w^(-1).
6. Refinement of E commutes with j_r and with w. Two models have a common refinement;
descend their comparison and inverse by lem-wf-finite-etale-field-limit-descent(2), and
the inverse identities by (3). Hence tau is independent of the model.
7. Descend any morphism of covers at a common finite stage. Naturality of w there and
j'_r F(T_r f) = F0(f_E) j_r prove F(f) tau_P = tau_Q F(T_n f). This includes all
morphisms, rather than only isomorphisms (def-galois-fibre-functor).
8. The natural map T_r P to the base change of Q identifies j_r(g x) with i(g) j_r(x)
by lem-galois-pi1-functoriality. Normality gives w i(g) w^(-1) = i(h), with unique h.
Cancel j_0 to obtain tau_P(g x) = h tau_P(x).
9. Apply this construction to w^(-1), whose degree is -n. The comparison in step 1
identifies its covariant transport with pullback along Phi^n. Compose their fibre maps
to get lambda. Naturality of every cover map makes the comparison g-equivariant, so
lambda_P(g x) = (w^(-1) g w) lambda_P(x). Applying the same procedure to the inverse
lift recovers the covariant formulation. No torsor or coefficient action is used. -/
theorem finiteEtaleWeilTransport (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [GeometricallyConnected U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
    (w : weilGroup U₀.hom (s ≫ Limits.pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (Aut (fiber (s ≫ Limits.pullback.fst U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))) :
    (∃ τ : covariantTransport ((D.geometricFrobenius U₀) ^ w.val.2.toAdd) ⋙ fiber s ≅ fiber s,
      ∀ g : Aut (fiber s), ∃! h : Aut (fiber s),
        fiberAutBaseChange (Limits.pullback.fst U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) s h =
          w.val.1 * fiberAutBaseChange (Limits.pullback.fst U₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) s g * w.val.1⁻¹ ∧
        ∀ (P : (D.geometricFiber U₀).left.FiniteEtale)
          (x : (fiber s).obj
            ((covariantTransport ((D.geometricFrobenius U₀) ^ w.val.2.toAdd)).obj P)),
          τ.hom.app P (g.hom.app _ x) = h.hom.app P (τ.hom.app P x)) ∧
    Nonempty (covariantTransport ((D.geometricFrobenius U₀) ^ (-w.val.2.toAdd)) ≅
      pullback ((D.geometricFrobenius U₀) ^ w.val.2.toAdd).hom) ∧
    (∃ lam : pullback ((D.geometricFrobenius U₀) ^ w.val.2.toAdd).hom ⋙ fiber s ≅ fiber s,
      ∀ g : Aut (fiber s), ∃! h : Aut (fiber s),
        fiberAutBaseChange (Limits.pullback.fst U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) s h =
          w.val.1⁻¹ * fiberAutBaseChange (Limits.pullback.fst U₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) s g * w.val.1 ∧
        ∀ (P : (D.geometricFiber U₀).left.FiniteEtale)
          (x : (fiber s).obj
            ((pullback ((D.geometricFrobenius U₀) ^ w.val.2.toAdd).hom).obj P)),
          lam.hom.app P (g.hom.app _ x) = h.hom.app P (lam.hom.app P x)) :=
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale

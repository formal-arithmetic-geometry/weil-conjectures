/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.GroupTheory.WeilGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup

/-!
# The coefficient-free twisted-path description of the Weil group

Source: Stacks Project, Fundamental Groups, Tags 0BND, 0BN5, 0BTV and 0BTX;
Deligne, Weil II (1.1.7), (1.1.10)(ii), (1.1.12)--(1.1.13), pp. 150--153
(blueprint: lem-real-weil-twisted-paths).

The helper predicates spell out componentwise the multiplication, its arithmetic-cover
normalization and the closed-point return path. In particular the pullback comparisons
are the existing `pullbackFiberIso`, and the Weil group is the recorded `weilGroup`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The pairs `(n,p)` with `p : b ⇝ g^n b`, using the recorded finite-étale fibre functor.
Source: Stacks Tags 0BND and 0BN5; Deligne, Weil II (1.1.13)
(blueprint: lem-real-weil-twisted-paths). -/
def TwistedEtaleLoop {X : Scheme.{u}} (g : Aut X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (b : Spec (.of Ω) ⟶ X) : Type (u + 1) :=
  Σ n : ℤ, fiber b ≅ fiber (b ≫ (g ^ n).hom)

/-- Componentwise meaning of `g^n(p)`: apply `p` on the pullback cover and use the canonical
projection comparison on its two fibres. Source: Stacks Tags 0BN5 and 0BND
(blueprint: lem-real-weil-twisted-paths). -/
def IsTwistedEtalePathTranslate {X : Scheme.{u}} (g : Aut X) (n : ℤ)
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    {a : Spec (.of Ω) ⟶ X} {b : Spec (.of Ω') ⟶ X} (p : fiber a ≅ fiber b)
    (pn : fiber (a ≫ (g ^ n).hom) ≅ fiber (b ≫ (g ^ n).hom)) : Prop :=
  ∀ (P : X.FiniteEtale) (z : (fiber a).obj ((pullback (g ^ n).hom).obj P)),
    (pn.hom.app P ((pullbackFiberIso (g ^ n).hom a).hom.app P z)).left =
      (p.hom.app ((pullback (g ^ n).hom).obj P) z).left ≫
        Limits.pullback.fst P.obj.hom (g ^ n).hom

/-- The law `(n,p)(m,q) = (n+m,g^m(p) ∘ q)`, expressed on lifted points without choosing
casts for the equality of the two endpoint schemes. Source: Stacks Tags 0BN5 and 0BTX;
Deligne, Weil II (1.1.13) (blueprint: lem-real-weil-twisted-paths). -/
def IsTwistedEtaleLoopMultiplication {X : Scheme.{u}} (g : Aut X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (b : Spec (.of Ω) ⟶ X)
    (mul : TwistedEtaleLoop g b → TwistedEtaleLoop g b → TwistedEtaleLoop g b) : Prop :=
  ∀ p q, (mul p q).1 = p.1 + q.1 ∧
    ∀ (P : X.FiniteEtale) (z : (fiber b).obj P)
      (y : (fiber b).obj ((pullback (g ^ q.1).hom).obj P)),
      (pullbackFiberIso (g ^ q.1).hom b).hom.app P y = q.2.hom.app P z →
      ((mul p q).2.hom.app P z).left =
        (p.2.hom.app ((pullback (g ^ q.1).hom).obj P) y).left ≫
          Limits.pullback.fst P.obj.hom (g ^ q.1).hom

/-- The canonical restriction of a path to arithmetic covers. This generalizes no group
map: it just composes the recorded fibre comparisons with the whiskered given path.
Source: Stacks Tags 0BND(3) and 0BN5 (blueprint: lem-real-weil-twisted-paths). -/
noncomputable def restrictTwistedEtalePath {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    {a : Spec (.of Ω) ⟶ X} {b : Spec (.of Ω') ⟶ X} (p : fiber a ≅ fiber b) :
    fiber (a ≫ f) ≅ fiber (b ≫ f) :=
  (pullbackFiberIso f a).symm ≪≫ Functor.isoWhiskerLeft (pullback f) p ≪≫
    pullbackFiberIso f b

/-- The coefficient-field geometric Frobenius on its spectrum, for the fixed closure in
`D`. Source: Deligne, Weil II (1.1.7)--(1.1.8)
(blueprint: lem-real-weil-twisted-paths). -/
noncomputable def twistedPathSpecFrobenius (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Aut (Spec (.of D.k)) :=
  letI := Fintype.ofFinite D.k₀
  specMapIso (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv

/-- The degree and action on every arithmetic finite étale cover prescribed in the node.
The right side projects the endpoint lift to the arithmetic cover, implementing the
canonical identification over the same arithmetic geometric point.
Source: Stacks Tags 0BND, 0BN5 and 0BTX; Deligne, Weil II (1.1.13)
(blueprint: lem-real-weil-twisted-paths). -/
def IsWeilTwistedPathIdentification (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [GeometricallyConnected X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (b : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left)
    (E : TwistedEtaleLoop (D.geometricFrobenius X₀) b ≃
      weilGroup X₀.hom
        (b ≫ Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (Aut (fiber
          (b ≫ Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))) :
    Prop :=
  ∀ p, (E p).val.2.toAdd = p.1 ∧
    ∀ (P₀ : X₀.left.FiniteEtale)
      (z : (fiber b).obj ((pullback (Limits.pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).obj P₀)),
      ((E p).val.1.hom.app P₀
        ((pullbackFiberIso (Limits.pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) b).hom.app P₀ z)).left =
        (p.2.hom.app ((pullback (Limits.pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).obj P₀) z).left ≫
          Limits.pullback.fst P₀.obj.hom (Limits.pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))

/-- Closed-point clause: the return path is reparametrization by `γ^e`, and after any path
`τ : a ⇝ b` its twisted loop has the decomposition-group action of geometric Frobenius.
The two projection equations specify exactly the lift of the chosen residue embedding.
The equality `#κ(x) = q^e` specifies its residue degree over the finite base field.
Source: Deligne, Weil II (1.1.8), (1.1.12)--(1.1.13); Stacks Tags 0BN5 and 0BTX
(blueprint: lem-real-weil-twisted-paths). -/
def HasWeilTwistedClosedPointFormula (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [GeometricallyConnected X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (b : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left)
    (E : TwistedEtaleLoop (D.geometricFrobenius X₀) b ≃
      weilGroup X₀.hom
        (b ≫ Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (Aut (fiber
          (b ≫ Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))) :
    Prop :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  ∀ (x : X₀.left), IsClosed ({x} : Set X₀.left) →
    ∀ (e : ℕ), Nat.card (X₀.left.residueField x) = D.q ^ e →
    ∀ (ι : X₀.left.residueField x →+* D.k)
      (a : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left),
      a ≫ Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom ι) ≫ X₀.left.fromSpecResidueField x →
      a ≫ Limits.pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _ →
      a ≫ ((D.geometricFrobenius X₀) ^ (e : ℤ)).hom =
        (twistedPathSpecFrobenius D ^ (e : ℤ)).hom ≫ a ∧
      ∃ c : fiber a ≅ fiber (a ≫ ((D.geometricFrobenius X₀) ^ (e : ℤ)).hom),
        (∀ (P : (D.geometricFiber X₀).left.FiniteEtale) (z : (fiber a).obj P),
          (c.hom.app P z).left = (twistedPathSpecFrobenius D ^ (e : ℤ)).hom ≫ z.left) ∧
        ∀ τ : fiber a ≅ fiber b,
          ∃ τe : fiber (a ≫ ((D.geometricFrobenius X₀) ^ (e : ℤ)).hom) ≅
              fiber (b ≫ ((D.geometricFrobenius X₀) ^ (e : ℤ)).hom),
            IsTwistedEtalePathTranslate (D.geometricFrobenius X₀) (e : ℤ) τ τe ∧
            ∃ hfix : (twistedPathSpecFrobenius D ^ (e : ℤ)).hom ≫
                (a ≫ Limits.pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) =
                a ≫ Limits.pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))),
              (E ⟨(e : ℤ), τ.symm ≪≫ c ≪≫ τe⟩).val.1 =
                (restrictTwistedEtalePath (Limits.pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) τ).symm ≪≫
                  fiberPrecompIso
                    (a ≫ Limits.pullback.fst X₀.hom
                      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
                    (twistedPathSpecFrobenius D ^ (e : ℤ)) hfix ≪≫
                  restrictTwistedEtalePath (Limits.pullback.fst X₀.hom
                    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) τ ∧
              (E ⟨(e : ℤ), τ.symm ≪≫ c ≪≫ τe⟩).val.2.toAdd = (e : ℤ)

/-- The twisted-path group and its canonical degree-preserving Weil-group identification,
including geometric-subgroup normalization and the closed-point Frobenius formula.
Source: Stacks Tags 0BND, 0BN5, 0BTV and 0BTX; Deligne, Weil II (1.1.7), (1.1.10)(ii),
(1.1.12)--(1.1.13), pp. 150--153 (blueprint: lem-real-weil-twisted-paths).

Proof:
1. Use pullback of finite étale covers and `pullbackFiberIso` to translate paths. Projection
of lifted points proves compatibility with composition and successive powers of Frobenius
(def-weil-frobenius-detailed, lem-galois-pi1-functoriality,
def-weil-pbc-finite-etale-category).
2. Both triple products have path g^(m+l)(p) composed with g^l(q) and r. The identity is
(0,id) and the inverse is (-n,g^(-n)(p^(-1))). Hence the displayed law is a group law,
with degree-zero subgroup Aut(F_b) (def-galois-fibre-functor).
3. Restrict a path to descended covers and project its lifts to define its arithmetic
natural automorphism A(n,p); in degree zero this is the canonical fundamental-group map
(lem-galois-pi1-functoriality).
4. Test on finite constant field covers and their geometric sections. Naturality sends
an embedding iota sigma to iota gamma^n sigma, so A(n,p) has degree n
(lem-sfb-finite-field-galois-frobenius, lem-sc-finite-etale-algebra-criterion,
lem-wf-arithmetic-lift-fibre-path, def-wf-weil-group).
5. Naturality for the descent identification of (g^m)^*P gives
A(n+m,g^m(p) composed with q) = A(n,p)A(m,q). On degree zero the map is injective with
image the degree kernel (lem-wf-weil-group-exact-sequence).
6. A degree-n Weil element exists by that exact sequence. Apply only the existence and
all-morphism naturality clause of lem-wf-finite-etale-weil-transport to get a path from b
to g^n b; no arithmetic normalization of that transport is assumed.
7. Fix one such path. The exact sequence identifies each degree fibre as a torsor under
the geometric fundamental group, so A is bijective. Its prescribed components determine
it uniquely (lem-wf-weil-group-exact-sequence, def-galois-fibre-functor).
8. Since gamma^e fixes the embedded residue field, comparison of the two fibre-product
projections gives g^e a = a Spec(gamma^e). Reparametrization of cover lifts is the path c,
with inverse reparametrization by gamma^(-e) (lem-sfb-finite-field-galois-frobenius).
9. Restrict tau to arithmetic covers. Naturality for their descent comparisons identifies
the arithmetic action of g^e(tau) composed with c and tau^(-1) as tau_0 composed with
geometric residue Frobenius and tau_0^(-1). This is precisely the decomposition-group
image, of degree e (lem-galois-pi1-functoriality). -/
theorem weilTwistedPaths (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [GeometricallyConnected X₀.hom]
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (b : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left) :
    ∃ (G : Group (TwistedEtaleLoop (D.geometricFrobenius X₀) b))
      (E : TwistedEtaleLoop (D.geometricFrobenius X₀) b ≃
        weilGroup X₀.hom
          (b ≫ Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
          (Aut (fiber
            (b ≫ Limits.pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))),
      IsTwistedEtaleLoopMultiplication (D.geometricFrobenius X₀) b G.mul ∧
      (∀ p q, E (G.mul p q) = E p * E q) ∧
      IsWeilTwistedPathIdentification D X₀ b E ∧
      (∀ E' : TwistedEtaleLoop (D.geometricFrobenius X₀) b ≃
          weilGroup X₀.hom
            (b ≫ Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
            (Aut (fiber
              (b ≫ Limits.pullback.fst X₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))),
        IsWeilTwistedPathIdentification D X₀ b E' → E' = E) ∧
      (∀ (p : TwistedEtaleLoop (D.geometricFrobenius X₀) b) (h : Aut (fiber b)),
        p.1 = 0 →
        (∀ (P : (D.geometricFiber X₀).left.FiniteEtale) (z : (fiber b).obj P),
          (p.2.hom.app P z).left = (h.hom.app P z).left) →
        (E p).val.1 = fiberAutBaseChange (Limits.pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) b h) ∧
      HasWeilTwistedClosedPointFormula D X₀ b E :=
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Universal property of principal-chart restriction

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-chart-restriction-is-localized)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations.
Source: Stacks, Algebra, Section 00JM.
(blueprint: lem-weil-pbc-proj-chart-restriction-is-localized) -/
local instance localizedModuleHomogeneousScalarsRestrictionLocalization (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false
set_option linter.unusedVariables false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "ModX" => (Proj 𝒜).Modules

/-- The canonical restriction from a homogeneous chart is a localization map,
with scalars restricted along the pulled-back chart constants.

Source: Stacks Project, Constructions, Tags 01M4 (1)(e),(h), 01M7 and 01MB,
last paragraph. (blueprint: lem-weil-pbc-proj-chart-restriction-is-localized)

Proof:
Write r=a/f^n with a homogeneous of degree n*deg(f), and take the positive-degree
homogeneous element g=f*a. Its chart lies inside the f-chart, and the inverse image
of D(r) has image D_+(g). The intersection formula gives U(f,g)=r^deg(f).
The canonicality assumption identifies rhoS(f,g) with restriction of chart
constants: an S-algebra map out of S_f is determined on each a/f^n by its values
on S and the inverse of f. Transport sections along the open immersion and alpha g.
More precisely, let beta:E(V) ≃+ Z g be this transported alpha g. Naturality of
restrictAppIso and hrestriction give beta(l(q))=rho(f,g)(q). The canonical ring
comparison and hscalar give beta(k(x) • s)=rhoS(f,g)(x) • beta(s). Hence
psi=theta(f,g) inverse composed with beta is an R[f]-linear equivalence from E(V)
to the localization of Z f at U(f,g): htheta identifies the R[f] action through
thetaS with rhoS, and gives psi(l(q))=q/1. Multiplication by U is invertible on
this localization. Each psi(s) has the form q/U^j, so U^j • s=l(q). If
l(q1)=l(q2), equality of q1/1 and q2/1 supplies j with U^j • q1=U^j • q2.
Transport these three facts along psi. Put d=deg(f)>0. Since U=r^d, the last two
facts already use powers r^(d*j). For invertibility, if A is multiplication by r
and B is the inverse of A^d, then A commutes with B and A^(d-1)*B is an inverse
of A. Thus every power of r acts invertibly and all three localization conditions
hold for powers of r; equivalently one can use IsLocalizedModule.of_exists_mul_mem.
For r=0 the open is empty, both the transported module and its localization
are zero and the three conditions still hold. For r a unit restriction is the
whole-chart identification. This result asserts only the universal property of
restriction; it constructs neither the final comparison nor its scalar action. -/
theorem gradedModuleChart_restriction_isLocalized
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (U : ∀ (f g : Fidx), R[f])
    (hU : ∀ (f g : Fidx), (U f g).val = Localization.mk (g.val.1 ^ f.val.2)
      (⟨f.val.1 ^ g.val.2, ⟨g.val.2, rfl⟩⟩ : Submonoid.powers f.val.1))
    (theta : ∀ (f g : Fidx), D[g] ≤ D[f] →
      LocalizedModule.Away (U f g) (Z f) ≃+ Z g)
    (thetaS : ∀ (f g : Fidx), D[g] ≤ D[f] → Localization.Away (U f g) ≃+* R[g])
    (htheta : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      (∀ r : R[f], thetaS f g i (algebraMap R[f] (Localization.Away (U f g)) r) =
        rhoS f g i r) ∧
      (∀ q : Z f, theta f g i (mk q 1) = rho f g i q) ∧
      (∀ (r : Localization.Away (U f g)) (q : LocalizedModule.Away (U f g) (Z f)),
        theta f g i (r • q) = thetaS f g i r • theta f g i q))
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val)
    (F : ModX) (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f)
    (hscalar : ∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
      alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s)
    (hrestriction : ∀ (f g : Fidx) (i : D[g] ≤ D[f])
      (s : F.val.obj (op D[f])),
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s))
    (f : Fidx) (r : R[f]) :
    let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
    let E := Scheme.Modules.restrict F D[f].ι
    let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
    let k := (e.hom.appLE ⊤ V (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
    let b := ((F.restrictAppIso D[f].ι ⊤) ≪≫
      F.presheaf.mapIso (eqToIso D[f].ι_image_top.symm).op).addCommGroupIsoToAddEquiv.trans
        (alpha f)
    letI : Module R[f] (E.val.obj (op V)) := Module.compHom (E.val.obj (op V)) k
    ∀ l : Z f →ₗ[R[f]] E.val.obj (op V),
      (∀ q : Z f, l q = E.val.map V.leTop.op (b.symm q)) →
      IsLocalizedModule (Submonoid.powers r) l := by sorry

end AlgebraicGeometry.Proj

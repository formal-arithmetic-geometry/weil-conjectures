/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.EtaleSplitsOffIsolatedPoints

/-!
# Étale local finite restriction of a closed affine relation

Source: Stacks Project, More on Groupoids, Tag 03X5, specialized to an affine
étale equivalence relation with closed relation map (blueprint:
lem-a1-proper-etale-relation-finite-neighbourhood).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed affine étale equivalence relation admits a finite clopen restriction
after an étale residue-field-preserving neighbourhood of any chosen point.

Source: Stacks Project, More on Groupoids, Tag 03X5 (conclusions (a), (d),
(g), and (h)), with the elementary splitting supplied by Tag 02LN.
Proof: write the structure map as `fU`; local quasi-finiteness, affineness,
and the isolated-point criterion give the hypotheses of the Tag 02LN splitting.
Shrink its elementary neighbourhood to an affine open.  Pull back the two
projections and take the inverse image of the chosen clopen piece at both
ends.  The resulting relation is clopen and is the indicated iterated
pullback.  Closed-immersion base change and finiteness of closed immersions
make it finite; étale base change and cancellation make both restricted
projections étale.  Finally an equivalence relation restricts to every subset
of its object set, which gives the last clause pointwise on all test schemes.
Proof steps from the node: (1) local quasi-finiteness gives local finite type,
separatedness follows from the affine source, and the chosen point is isolated
in its fibre. (2) Apply the singleton case of the elementary étale splitting
lemma to obtain a residue-field-preserving étale neighbourhood and a finite
clopen object piece. (3) Shrink the neighbourhood to an affine open; pullback
preserves the clopen decomposition and finiteness. (4) In the relation base
change, take the intersection of the inverse images of the object piece under
the two projections; its induced open subscheme is the iterated pullback in the
statement, with complementary open piece. (5) The restricted map to the
object square is a closed immersion by base change, hence finite; the square is
finite over the base, so the relation is finite. (6) Étale base change and
étale composition/cancellation show that both restricted projections are
étale. (7) On every test scheme, the relation is the restriction of the original
equivalence relation to the selected subset, so reflexivity, symmetry, and
transitivity are inherited.
(blueprint: lem-a1-proper-etale-relation-finite-neighbourhood) -/
theorem exists_finite_etale_restricted_relation_neighbourhood
    {T U R : Scheme.{u}} [IsAffine T] [IsAffine U] [IsAffine R]
    (fU : U ⟶ T) (fR : R ⟶ T) (hquasi : Scheme.Hom.IsLocallyQuasiFinite fU)
    (s t : R ⟶ U) (hs : s ≫ fU = fR) (ht : t ≫ fU = fR)
    (hsEtale : Etale s) (htEtale : Etale t)
    (j : R ⟶ pullback fU fU)
    (hj_s : j ≫ pullback.fst fU fU = s)
    (hj_t : j ≫ pullback.snd fU fU = t)
    (hj_closed : IsClosedImmersion j)
    (hrel : ∀ (H : Scheme.{u}) (hH : H ⟶ T),
      _root_.Equivalence
        (fun (a b : {g : H ⟶ U // g ≫ fU = hH}) =>
          ∃ r : H ⟶ R, r ≫ s = a.1 ∧ r ≫ t = b.1))
    (u : U) :
    let p : T := fU u
    ∃ (T' : Scheme.{u}) (f' : T' ⟶ T) (p' : T'),
      IsAffine T' ∧ Etale f' ∧ f' p' = p ∧ IsIso (f'.residueFieldMap p') ∧
      ∃ (Uo Wo : (pullback fU f').Opens),
        IsCompl Uo Wo ∧
        ∃ (u' : Uo.toScheme),
          pullback.fst fU f' (Uo.ι u') = u ∧
          pullback.snd fU f' (Uo.ι u') = p' ∧
          IsFinite (Uo.ι ≫ pullback.snd fU f') ∧
          ∃ (Ro Wro : (pullback fR f').Opens),
            IsCompl Ro Wro ∧
            IsFinite (Ro.ι ≫ pullback.snd fR f') ∧
            let U0 := pullback fU f'
            let R0 := pullback fR f'
            let s0 : R0 ⟶ U0 :=
              pullback.map fR f' fU f' s (𝟙 T') (𝟙 T)
                (by simpa using hs.symm) (by simp)
            let t0 : R0 ⟶ U0 :=
              pullback.map fR f' fU f' t (𝟙 T') (𝟙 T)
                (by simpa using ht.symm) (by simp)
            let P := pullback Uo.ι s0
            let Q := pullback (pullback.snd Uo.ι s0 ≫ t0) Uo.ι
            let p₁ := pullback.fst Uo.ι s0
            let p₂ := pullback.snd Uo.ι s0
            let q₁ := pullback.fst (pullback.snd Uo.ι s0 ≫ t0) Uo.ι
            let q₂ := pullback.snd (pullback.snd Uo.ι s0 ≫ t0) Uo.ι
            ∃ (q : Ro.toScheme ⟶ Q),
              IsIso q ∧
              q ≫ q₁ ≫ p₂ = Ro.ι ∧
              Ro.ι ≫ s0 = (q ≫ q₁ ≫ p₁) ≫ Uo.ι ∧
              Ro.ι ≫ t0 = (q ≫ q₂) ≫ Uo.ι ∧
              Etale (q ≫ q₁ ≫ p₁) ∧ Etale (q ≫ q₂) ∧
              ∀ (H : Scheme.{u}) (hH : H ⟶ T'),
                _root_.Equivalence
                  (fun (a b :
                    {g : H ⟶ Uo.toScheme //
                      g ≫ (Uo.ι ≫ pullback.snd fU f') = hH}) =>
                    ∃ r : H ⟶ Ro.toScheme,
                      r ≫ (q ≫ q₁ ≫ p₁) = a.1 ∧
                      r ≫ (q ≫ q₂) = b.1) := by
  sorry

end AlgebraicGeometry


module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import Sheaf.RingTheory.SmoothNormalRing
import Sheaf.RingTheory.EtaleNormalRing

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Normality of the localized relative normalization.

Source: Stacks Project, Tags 033C (smooth ascent of normality), 035L
(relative normalization in a normal source), and 0307 (localization of integral closure).
(blueprint: lem-sbc-stalk-normalization-normal-part)

Proof: S is normal because its stalks are domains by integrality and integrally
closed by hS. Smooth ascent gives normality of C, and etale ascent gives normality
of P. Finite presentation over the Noetherian S makes C locally Noetherian; hence
so are C_U and its finite etale cover P. Thus every quasi-compact open of P has
finitely many irreducible components. For an affine V = Spec A in C, f^{-1}(V)
is quasi-compact and is a finite disjoint union of normal integral schemes V_i.
Each B_i = Γ(V_i, O) is a normal domain. The integral closure A_i of A in B_i
is a normal domain: an element of Frac(A_i) integral over A_i is integral over A,
belongs to B_i by normality of B_i, and therefore lies in A_i. Integral closure
commutes with finite products, so the normalization above V is the disjoint union
of Spec A_i. These charts prove that its stalks are normal domains.
Choose an affine neighbourhood T = Spec R of s and restrict to affine charts
V inside c^{-1}(T). Pullback to Spec R_p, where p represents s, localizes each
A_i at the image of R minus p. A surviving component is again a normal domain;
a component whose localization is the zero ring has empty spectrum. Its stalks
are further prime localizations and therefore normal domains. These charts cover
the displayed pullback N and prove the two asserted properties at every point.
For empty P the normalization is empty, so there are no points to check. -/
theorem stalk_normalization_normal_part {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    ∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) := by
  sorry

end AlgebraicGeometry.Scheme

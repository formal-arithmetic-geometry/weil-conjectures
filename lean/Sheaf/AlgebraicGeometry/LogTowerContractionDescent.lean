/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.LogBlowupFullPullback
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Contraction and strict étale descent of log blowup towers

Source: ILO VIII 3.3.8--3.3.11 and proof of 3.3.15, pp.108--110
(blueprint: lem-trf-log-tower-contraction-descent).

The statements quantify over presentations of universal pullbacks and contractions;
no log scheme or canonical map is selected from an arbitrary existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- Contraction deletes exactly the whole centers, commutes canonically with a
surjective strict étale cover, and ordered center-preserving local comparisons descend
uniquely. Equality testing includes the retained embeddings and actual log morphisms.
The first strict étale morphism need not be surjective.

Source: ILO VIII 3.3.8--3.3.11 and proof of 3.3.15, pp.108--110
(blueprint: lem-trf-log-tower-contraction-descent).

Proof:
1. Apply `lem-trf-log-tower-cover-synchronization` to D over Y and the surjective
cover v, not to f. Every induced map is the scheme base change of v, is surjective
strict étale, and reflects precisely the whole centers.
2. Enumerate the proper centers S in their original order and put
r(i) = #{j < i | j ∈ S}. Retain a stage and its actual center for i ∈ S. Otherwise
its universal blowup is the identity: compose the canonical identification and leave
r unchanged. Transport subsequent centers along the inverse identification. This
constructs the contraction, including any run of consecutive deletions. Proper
principal centers belong to S and are retained. The level identifications are log
isomorphisms, including their maps on sections.
3. Run this induction after pullback to W. Synchronization gives the same S. At a
retained stage use the universal property of `def-trf-fs-log-blowup` to identify the
two blowups uniquely; at a deleted stage use the specified identity. This gives the
unique normalized interchange, its count and retained-label equations, and its
commuting log composites.
4. For a contracted A and local isomorphism, compose with the interchange. Both
full pullbacks retain every stage by synchronization. Apply the second paragraph of
`lem-trf-log-tower-cover-rigidity` to get the unique downstairs isomorphism, with
exactly the prescribed local isomorphism and centers.
5. Under consecutive strict étale pullbacks, generating an ideal from the image of
a generated image is generation from the composite image. Whole ideals stay whole;
a surviving ideal that becomes whole at the next pullback is deleted on both routes.
Thus composed counts and retained embeddings enumerate exactly the same surviving
original labels, even for non-surjective maps.
6. Once the base map and labels are fixed, the universal blowup property makes
successive log factorizations unique. Hence comparisons restrict uniquely and their
identities or composites are equal if and only if their restrictions are equal.
Use synchronization at each intermediate level to reflect the labels and rigidity
to reflect the actual log maps. A zero-length tower has just the specified base map,
so this proof also covers length zero and empty sources. -/
theorem log_tower_contraction_descent :
    (∀ (Y : FineSaturatedLogScheme.{u}) (D : LogBlowupTowerOver Y),
      ∃ C : LogBlowupTowerOver Y,
        Nonempty (LogBlowupComparison (EtaleLogHom.id Y) D C)) ∧
    (∀ (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom Y X),
      f.IsStrict → Etale f.base →
      ∀ (B : LogBlowupTowerOver X) (D : LogBlowupTowerOver Y)
        (_r : LogBlowupFullPullback f B D) (C : LogBlowupTowerOver Y)
        (c : LogBlowupComparison (EtaleLogHom.id Y) D C),
      C.IsContracted ∧
      (∀ i, i ∉ Set.range c.retained ↔ D.tower.center i = (fun _ ↦ Set.univ)) ∧
      (∀ i, ∃ b : EtaleLogHom (D.tower.level i) (C.tower.level (c.count i)),
        (c.map i).AreInverses b) ∧
      ∀ (W : FineSaturatedLogScheme.{u}) (v : EtaleLogHom W Y),
        v.IsStrict → Etale v.base → Surjective v.base →
        ∀ (E : LogBlowupTowerOver W) (p : LogBlowupFullPullback v D E)
          (F : LogBlowupTowerOver W)
          (d : LogBlowupComparison (EtaleLogHom.id W) E F)
          (U : LogBlowupTowerOver W) (q : LogBlowupFullPullback v C U),
        p.IsCoverSynchronized ∧ F.IsContracted ∧
        ∃ e : LogBlowupTowerIso U F,
          p.IsContractionInterchange c d q e ∧
          (∀ e' : LogBlowupTowerIso U F, p.IsContractionInterchange c d q e' → e' = e) ∧
          ∀ (A : LogBlowupTowerOver Y), A.IsContracted →
            ∀ (V : LogBlowupTowerOver W) (a : LogBlowupFullPullback v A V)
              (α : LogBlowupTowerIso F V),
            ∃! β : LogBlowupTowerIso C A,
              LogBlowupTowerIso.InducesContractedLocalIso q a e α β) ∧
    (∀ (X Y W : FineSaturatedLogScheme.{u}) (f : EtaleLogHom Y X)
      (v : EtaleLogHom W Y), f.IsStrict → Etale f.base →
      v.IsStrict → Etale v.base → Surjective v.base →
      ∀ (B : LogBlowupTowerOver X) (A : LogBlowupTowerOver Y)
        (U : LogBlowupTowerOver W) (p : LogBlowupFullPullback v A U),
      p.IsCoverSynchronized ∧
      (∀ c : LogBlowupComparison f B A,
        ∃! a : LogBlowupComparison (v.comp f) B U,
          LogBlowupComparison.RestrictsTo p c a) ∧
      ∀ (c d : LogBlowupComparison f B A)
        (a b : LogBlowupComparison (v.comp f) B U),
        LogBlowupComparison.RestrictsTo p c a →
        LogBlowupComparison.RestrictsTo p d b → (c = d ↔ a = b)) ∧
    (∀ (Y W : FineSaturatedLogScheme.{u}) (v : EtaleLogHom W Y),
      v.IsStrict → Etale v.base → Surjective v.base →
      ∀ (A : LogBlowupTowerOver Y) (U : LogBlowupTowerOver W)
        (p : LogBlowupFullPullback v A U)
        (c : LogBlowupComparison (EtaleLogHom.id Y) A A)
        (a : LogBlowupComparison v A U),
      (∀ i, a.count i = p.index (c.count i)) →
      (∀ k, a.retained (p.stage k) = c.retained k) →
      (∀ i, HEq (a.map i) ((p.map (c.count i)).comp (c.map i))) →
      (c.IsIdentityComparison ↔ LogBlowupComparison.AgreesWithFullPullback p a)) ∧
    (∀ (X Y Z W : FineSaturatedLogScheme.{u}) (f : EtaleLogHom Y X)
      (g : EtaleLogHom Z Y) (h : EtaleLogHom Z X) (v : EtaleLogHom W Z),
      f.IsStrict → Etale f.base → g.IsStrict → Etale g.base →
      g.CompEq f h → v.IsStrict → Etale v.base → Surjective v.base →
      ∀ (B : LogBlowupTowerOver X) (A : LogBlowupTowerOver Y)
        (C : LogBlowupTowerOver Z) (U : LogBlowupTowerOver W)
        (p : LogBlowupFullPullback v C U)
        (a : LogBlowupComparison f B A) (b : LogBlowupComparison g A C)
        (c : LogBlowupComparison h B C)
        (b' : LogBlowupComparison (v.comp g) A U)
        (c' : LogBlowupComparison (v.comp h) B U),
      LogBlowupComparison.RestrictsTo p b b' →
      LogBlowupComparison.RestrictsTo p c c' →
      (a.IsCompositeComparison b c ↔ a.IsCompositeComparison b' c')) := by
  sorry

end AlgebraicGeometry

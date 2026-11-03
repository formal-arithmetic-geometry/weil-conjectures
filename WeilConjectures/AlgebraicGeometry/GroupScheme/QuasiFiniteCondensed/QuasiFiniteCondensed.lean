/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.QuasiFiniteCondensed.QuasiFiniteCondensedData
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.GroupScheme.QuasiFiniteCondensed.QuasiFiniteCondensedVanishingMixed
import WeilConjectures.AlgebraicGeometry.GroupScheme.QuasiFiniteCondensed.QuasiFiniteCondensedPurityFinite

/-!
# Quasi-finite condensed direct images

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-general/sec-quasi-finite-maps-and-curves-preserving-irreducibility/
sk-l-dl-general-quasifinite/lem-zl-quasi-finite.md and its proof; separated target
convention as corrected by Wei Yang, Zulip #1441 item 33 (blueprint: lem-zl-quasi-finite).

The ambient pairs `AmbientPair`, their Weil `cohomology` and the compact-support `image`
are defined in `Sheaf.DeligneLaumon.QuasiFiniteCondensedData`, re-exported here.

All objects are actual modules over the pulled-back finite-subextension-valued
condensed algebraic closure. The upper complex-weight condition is written out as
mixedness of each canonical Weil cohomology object, with bound w + degree.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.QuasiFiniteCondensed

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

variable {X₀}
  {Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The five quasi-finite direct-image assertions, including the finite ordinary-image
specialization. The complex-weight clause explicitly expands Wt_{iota,le w}; only
bounded constructibility and the given Weil structure are required of its input.

Source: latest blueprint, lem-zl-quasi-finite.md, clauses (1)--(5), and its proof;
Wei Yang #1441 item 33 supplies the separatedness of Y₀
(blueprint: lem-zl-quasi-finite).

Proof: Zariski's main theorem factors g globally as a quasi-compact open j followed
by a finite p. Since Y₀ is separated finite type, the middle model is too. Base
change and normalized proper/open composition identify Rg! with Rp* D(j!), with
its canonical Weil structure. The finite map is finitely presented over the
Noetherian target. Its direct image and j! are exact and preserve constructibility,
so positive cohomology vanishes and H^b(Rg!K) is p*j!H^b(K).
For the complex bound, extend each finite mixed filtration by the exact j!;
its pure quotients retain their stalks on the open and have zero stalks elsewhere.
The finite pushforward bound then proves the weight bound in each degree b.
The degree-zero instance gives the mixed sheaf assertion. At a closed target point,
the canonical finite-fibre formula is a finite direct sum; Frobenius permutes the
summands in cycles of length e = [kappa(z):kappa(y)]. Its return is the source local
Frobenius, so each target eigenvalue beta satisfies beta^e = alpha for a source
eigenvalue. Since q_z = q_y^e and e is positive, taking e-th roots preserves the
upper bound and the pure-weight equality. Empty fibres contribute no eigenvalues;
nilpotents do not change the sheaf category. For finite g choose j = identity,
so the canonical properness comparison identifies g! with the ordinary g*.
-/
theorem quasiFinite
    (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    [IsSeparated Y₀.hom]
    (g₀ : X₀ ⟶ Y₀) [IsSeparated g₀.left] [LocallyQuasiFinite g₀.left]
    [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (c₀ : Compactification g₀.left)
    (F : AffineLineConventions.WeilSheaf D l X₀) :
    (∀ i : ℕ, 0 < i →
      IsZero (RelativeCurve.higherShriek D l g₀ c₀ F.obj i)) ∧
    (∀ K : AmbientPair D l X₀,
      boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left)
        K.carrier →
      (∀ b : ℤ, NativeL2.Mixed D l X₀ (cohomology D l X₀ K b) iota (w + b)) →
      boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber Y₀).left)
        (image D l g₀ c₀ K).carrier ∧
      ∀ b : ℤ, NativeL2.Mixed D l Y₀
        (cohomology D l Y₀ (image D l g₀ c₀ K) b) iota (w + b)) ∧
    (∃ hF' : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber Y₀).left)
        (RelativeCurve.higherShriek D l g₀ c₀ F.obj 0).carrier,
      let F' : AffineLineConventions.WeilSheaf D l Y₀ :=
        ⟨RelativeCurve.higherShriek D l g₀ c₀ F.obj 0, hF'⟩
      (NativeL2.Mixed D l X₀ F.obj iota w → NativeL2.Mixed D l Y₀ F'.obj iota w) ∧
      (AffineLineConventions.HasPunctualWeightsAtMost F iota w →
        AffineLineConventions.HasPunctualWeightsAtMost F' iota w) ∧
      (NativeL2.Pure D l X₀ F.obj iota w → NativeL2.Pure D l Y₀ F'.obj iota w)) ∧
    (∀ (_hfinite : IsFinite g₀.left),
      NativeL2.Pure D l X₀ F.obj iota w →
        NativeL2.Pure D l Y₀ (NativeL2.middleWeilImage D l g₀ F.obj) iota w) := by
  rcases vanishingAndMixed D l hl iota w g₀ c₀ F with ⟨h₁, h₂⟩
  rcases purityAndFinite D l hl iota w g₀ c₀ F with ⟨h₃, h₄⟩
  exact ⟨h₁, h₂, h₃, h₄⟩

end WeilConjectures.QuasiFiniteCondensed

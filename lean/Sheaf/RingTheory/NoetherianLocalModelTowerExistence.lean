/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.Paper.LimitTowerEssentiallyFinitePresentation

/-!
# Construction of a Noetherian local model tower

Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph and the
transition-localization sentence in its second paragraph.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-existence).
-/

@[expose] public section

universe u v w t p q

namespace Module

/-- An essentially finitely presented local tower and a finitely presented module admit
Noetherian local models, with transition and limit localization comparisons.
Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph and the
transition-localization sentence in the second paragraph.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-existence).

Proof:
1. Lift the three rings to `Type (max u v w)` by `ULift`, transporting their ring,
   algebra and local structures along the canonical ring equivalences. Transport the
   localized presentations over `P` and `Q` by composition with these equivalences.
   The module remains in `Type t`, with the transported top-ring action. A finite
   presentation supplies a finite matrix whose cokernel is the module.
2. Apply `WeilConjectures.limit_tower_essentially_finite_presentation` to the lifted
   tower and this matrix. Its rings are essentially of finite type successively over
   the integers, hence Noetherian: finite type algebras over Noetherian rings are
   Noetherian, as are their localizations. Restrict stage-module actions along the two
   stage ring maps; all stage scalar towers then follow from composition.
3. Use the functors' maps for the transitions, the specified colimit cocones for the
   maps to the limit, and transport the latter through `ULift.down`. The elementwise
   characterization of a filtered colimit supplies the four representation and eventual
   equality clauses. Naturality supplies all commutative squares and semilinearity.
4. Compose the middle- and top-ring transition localizations: tensor associativity,
   localization base change and localization of a localization show that
   `Tᵢ ⊗[Rᵢ] Rⱼ → Tⱼ` is a localization. The other transition clauses come directly
   from the tower theorem.
5. Tensor symmetry converts the limit middle-ring localization to
   `R ⊗[Rᵢ] Sᵢ`. A ring localization is its module localization. For the module put
   `C = S ⊗[Sᵢ] Tᵢ`, acting canonically on `S ⊗[Sᵢ] Nᵢ`. The top-ring limit clause
   identifies `S'` with a localization of `C`; its module clause identifies `M` with
   `S' ⊗[Tᵢ] Nᵢ`. Tensor associativity and localization-tensor compatibility identify
   this with the localization of `S ⊗[Sᵢ] Nᵢ` at the same submonoid, `S`-linearly.
   Transport these comparisons through the lift equivalences. No flatness was used.
-/
theorem exists_noetherian_localModelTower
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    (P : Type p) (Q : Type q) [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra R Q] [Algebra Q S'] [IsScalarTower R Q S']
    [Algebra.FinitePresentation R P] [Algebra.FinitePresentation R Q]
    (W : Submonoid P) (V : Submonoid Q) [IsLocalization W S] [IsLocalization V S']
    [Module.FinitePresentation S' M] :
    Nonempty (NoetherianLocalModelTower R S S' M) := by sorry

end Module

module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentMapTorsionCompletionExtZero
import Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftCompletion

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The underlying morphism-lifting part of Tag 0889(1), with the prescribed
completed comparison retained as an essential hypothesis.

Source: Stacks Project, Tag 0889(1), uniqueness verification, using formal gluing
(Tag 05EK), finite-module completion (Tag 00MA), and sheaf morphism gluing (Tag 04TN).

Proof: Restrict to an affine open Spec A. Coherence gives finite A-modules M, M', N
for F, F', H, and J gives an ideal I. Their coherent formal completions identify
with the reductions of their completed finite modules. Thus theta gives an A-hat-linear
map theta-hat: M-hat -> M'-hat, and htheta gives a'-hat theta-hat = a-hat.
Finite-module completion identifies these completions with tensoring by A-hat.

Choose generators f_i of I. Since powers of I annihilate both kernels and cokernels,
a and a' localize to isomorphisms on every D(f_i). There define g_i = (a'_i)^(-1) a_i.
On double localizations these maps agree, since composing with the invertible a'
identifies both with a. On completed localizations the equation htheta identifies
theta-hat with g_i by the same cancellation. For each x in M, pair theta-hat(x)
with the sections g_i(x/1). This is compatible gluing data for M'. The completion
ring is flat over A and has the same quotient modulo I; formal gluing exactness
therefore gives a unique y in M' with these completed and localized images. Set g(x)=y.
Injectivity of the gluing map proves additivity and A-linearity. Apply the same
injectivity to N: htheta and a'_i g_i = a_i give a'g = a. The construction also
retains the completed image theta-hat(x), so the completion of g is theta.

Transfer g to a morphism of coherent sheaves on this affine open. On overlaps refine
by affine opens. The two restrictions have the same completed image theta and the
same localized comparisons g_i; injectivity for M' identifies them. Sheaf morphism
gluing gives the global g, and a'g = a is checked on the affine cover.

When I = 0, all positive-power quotients are the original module, so completion is
the constant system: theta itself supplies g, and htheta is precisely a'g = a.
When I = A, the torsion hypotheses make a and a' isomorphisms and g = (a')^(-1) a.
The empty scheme has unique morphisms, so no nonempty affine cover is required.
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift-raw) -/
theorem torsionControlled_completion_hom_lift_raw
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F F' : CoherentModules X) (a : F ⟶ H) (a' : F' ⟶ H)
    (ha : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))))
    (ha' : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom))))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a) :
    ∃ g : F ⟶ F', g ≫ a' = a := by
  obtain ⟨_, _, _, _⟩ := ha
  obtain ⟨n, hn⟩ := coherentMap_torsion_completion_ext_zero J F' H a'
    (by obtain ⟨s, hs, hk, hc⟩ := ha'; exact ⟨s, hs, hk⟩)
  let := torsionControlledGraphFst_isIso J a a' ha' θ hθ n hn
  refine ⟨ObjectProperty.homMk
    (inv (torsionControlledGraphFst J a a' θ n) ≫
      torsionControlledGraphSnd J a a' θ n), ?_⟩
  apply ObjectProperty.hom_ext
  change (inv (torsionControlledGraphFst J a a' θ n) ≫
    torsionControlledGraphSnd J a a' θ n) ≫ a'.hom = a.hom
  have hp : torsionControlledGraphSnd J a a' θ n ≫ a'.hom =
      torsionControlledGraphFst J a a' θ n ≫ a.hom := by
    dsimp [torsionControlledGraphSnd, torsionControlledGraphFst]
    simp only [Category.assoc, pullback.condition]
  rw [Category.assoc, hp, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry

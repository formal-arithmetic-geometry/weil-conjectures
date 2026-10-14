module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Pointwise finite pushforward detectors on a Noetherian scheme

This isolates the local detector construction in the proof of Stacks Project Tag 09Z6 (3).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Etale

/-- Every point has a finite pushforward of a finitely generated constant module
with a map from C injective on all geometric stalks above that point.
Source: Stacks Project, Tag 09Z6 (3), proof of (1) transferred to module sheaves.
(blueprint: new-lem-weil-pbc-noetherian-stalk-detector).

Proof: Restrict C to the residue field at x and choose a finite separable extension
trivializing it with a finitely generated module M. Normalize the reduced closure of x
in this extension. The resulting integral morphism nu : Y -> U has normal integral
source. The constant sheaf on Y is the pushforward of its generic restriction (09Z5).
Adjoint the trivialization first along the generic inclusion and then along nu to get
C -> nu_* M. Every algebraically closed geometric point above x lifts to that generic
extension. The triangle identities and the inverse-image stalk comparison identify
the composite of its stalk map with projection to the chosen lifted stalk with the
trivialization; hence the stalk map is injective. Express nu as a cofiltered limit
of finite U-schemes and nu_* M as the corresponding filtered colimit (09Z1).
Constructibility over a Noetherian coefficient ring makes C finitely presentable
(09Z4), so the map factors through one finite stage. Its stalk map stays injective
because its composite with the transition map is injective. Choose this finite
stage and M for each x. On the empty scheme the point-indexed family is empty;
for the zero sheaf the zero module and zero maps suffice. No finite carrier for Λ
or M is required. -/
theorem exists_noetherian_stalk_detector
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    {U : Scheme.{u}} [IsNoetherian U]
    (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (Y : U → Scheme.{u}) (f : ∀ x, Y x ⟶ U), (∀ x, IsFinite (f x)) ∧
      ∃ (M : U → ModuleCat.{u + 1} Λ), (∀ x, Module.Finite Λ (M x)) ∧
        ∃ (ψ : ∀ x, C ⟶ (lowerStar (ModuleCat.{u + 1} Λ) (f x)).obj
          ((constantSheaf (Y x).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M x))),
          ∀ (x : U) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (s : Spec (.of Ω) ⟶ U),
            ((Scheme.SpecToEquivOfField Ω U) s).1 = x →
              Function.Injective
                (((Scheme.pointSmallEtale s).sheafFiber
                  (A := ModuleCat.{u + 1} Λ)).map (ψ x)) := by
  sorry

end AlgebraicGeometry.Etale

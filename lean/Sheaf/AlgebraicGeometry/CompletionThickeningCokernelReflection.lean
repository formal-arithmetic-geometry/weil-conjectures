/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence

/-! # Reflection of cokernel torsion on a closed thickening

Source: Stacks Project, Tags 088A and 0888.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Completion on a fixed closed thickening reflects a uniform cokernel torsion bound.
Source: Stacks Project, Tag 088A, the second use of Remark 0888 and the identification
of coherent modules killed by the thickening ideal (Tag 087T).
https://stacks.math.columbia.edu/tag/088A
https://stacks.math.columbia.edu/tag/0888
(blueprint: lem-weil-pbc-completion-thickening-cokernel-reflection).

Proof: descend F, G and a to Z = V(K^q) using the closed-immersion equivalence.
Closed pushforward identifies their I-completions and ideal actions. Completion on Z
is an equivalence, hence preserves cokernels and reflects zero. The formal cokernel
of the completed map has nth term coker(a modulo I^(n+1)), since quotient formation
is right exact. Thus every term is killed by K^s. Completion of finite modules on
a Noetherian affine is tensoring with the flat completed ring; it preserves images
and identifies the ideal-action image with the completed ideal product. Consequently
completion of K^s coker(a) is zero. Reflect zero on Z, then push forward to X to get
K^s coker(a) = 0. Finally factor the inclusion K^(2s) into K^s. This proof only uses
the cokernel assumption, unlike the simultaneous kernel/cokernel scalar-map argument.
-/
theorem completion_thickening_cokernel_reflection
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (q : ℕ) (hq : 1 ≤ q)
    (hcomplete : ∀ hZ : IsNoetherian (K ^ q).subscheme,
      Functor.IsEquivalence
        (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι)))
    (F G : CoherentModules X) (a : F ⟶ G)
    (hF : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      F.obj))
    (hG : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      G.obj))
    (s : ℕ) (hs : 1 ≤ s)
    (hred : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))))) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (cokernel a.hom)) := by sorry

end AlgebraicGeometry

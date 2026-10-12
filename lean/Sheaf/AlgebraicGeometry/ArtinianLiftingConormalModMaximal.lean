/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.Paper.ArtinianIdealLengthOneFiltration
import Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal

/-!
# Artinian lifting splits the conormal map modulo the maximal ideal

Source: Stacks Project, Algebra, Lemma 02HT, proof of (4) implies (1),
third through last paragraphs.
-/

@[expose] public section

universe u v

namespace Algebra

/-- Source: Stacks Project, Algebra, Lemma 02HT, proof of (4) implies (1),
third through last paragraphs (https://stacks.math.columbia.edu/tag/02HT).
(blueprint: lem-weil-pbc-artinian-lifting-conormal-mod-maximal).

Proof in words:
Let S = A_q, C = P.Ring, J = ker(C -> S), and m = maximalIdeal C. Surjectivity
between local rings identifies the preimage of the maximal ideal of S with m,
so J is contained in m. For each N >= 1, form C/(J^2 + m^N) -> C/(J + m^N).
These are nonzero Artinian local rings: both defining ideals contain m^N and lie
in m, and C is Noetherian. Their kernel has square zero. The natural map from A
into the second quotient has preimage maximal ideal q. Filter the kernel by
ideals with length-one factors. The intervening quotients are Artinian local.
Use the lifting hypothesis successively from the last quotient to the first;
the preimage maximal ideal remains q since a surjection of local rings pulls
back the maximal ideal. This gives an R-compatible lift from A to the first quotient.

Every element outside q maps to a unit, so the lift extends to S. The maximal
ideal of S maps into the maximal ideal of the first quotient, whose N-th power
vanishes. Hence the lift factors through S/(maximalIdeal S)^N, identified with
the second quotient. The resulting map is a section, by localization and quotient
uniqueness. Square-zero section conormal retraction gives a left inverse to the
conormal map for this pair of Artinian quotients.

Artin-Rees for J inside C gives c >= 1 such that m^N intersect J is contained
in m^(N-c) J for N >= c. Choose N = c+1.
Tensor the preceding left inverse with the residue field S/maximalIdeal S. The modular law
identifies the source with J/(J^2 + m J). Differential reduction modulo the maximal ideal,
first for J with exponent 1 and then for m in C/J^2 with exponent N-1,
identifies the target with the reduction of S tensor_C Omega(C/R). On generators,
the resulting map is the reduction of P.cotangentComplex, since both send x to dx.
Write its left inverse as vk and compose with the quotient projection to obtain
the displayed equation. Transport test rings to Type (max u v) using ULift when
necessary; lengths and both lifting equations are preserved. This argument also
covers J = 0 (the conormal module is zero) and zero-variable presentations.
-/
theorem artinian_lifting_conormal_split_mod_maximal
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime]
    (P : Extension.{u} R (Localization.AtPrime q))
    [IsLocalRing P.Ring] [IsNoetherianRing P.Ring]
    (hlift : ∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp (algebraMap R A) = φ.comp ρ →
          Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ) :
    ∃ vk : (P.CotangentSpace ⧸
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.CotangentSpace))) →ₗ[Localization.AtPrime q]
        (P.Cotangent ⧸
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.Cotangent))),
        vk.comp ((((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.CotangentSpace)).mkQ).comp
              P.cotangentComplex) =
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) •
            (⊤ : Submodule (Localization.AtPrime q) P.Cotangent)).mkQ := by sorry

end Algebra

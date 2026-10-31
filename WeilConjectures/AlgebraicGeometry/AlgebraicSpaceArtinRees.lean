/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Operations

import WeilConjectures.AlgebraicGeometry.NoetherianAffineAtlasRelation
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentArtinRees

/-! # Artin-Rees on a Noetherian algebraic space

Source: Stacks Project, Spaces Cohomology, Tag 07UL, lemma-Artin-Rees;
Tag 07UB, lemma-coherent-Noetherian (blueprint: lem-sfb-space-artin-rees).

Ideal products below are locally generated products, including on nonaffine tests.
Their sections are defined by covering sieves, rather than by assuming that global
sections commute with products. Equality on every test is equality of subsheaves.
Under the locally Noetherian hypothesis, quasi-coherent finite type is equivalent
to coherence, including coherence after pullback to every etale scheme chart (07UB).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The ideal of sections of an ideal subsheaf, presented by its inclusion into the ring.
For a monic inclusion its image is already an ideal, so `Ideal.span` changes nothing.
Source: Stacks, Spaces Cohomology, Tag 07UL, ideal products in lemma-Artin-Rees
(blueprint: lem-sfb-space-artin-rees). -/
def idealSectionImage {S : Scheme.{u}} {X : AlgebraicSpace S} {I : X.Modules}
    (i : I ⟶ SheafOfModules.unit X.structureSheaf) (T : X.EtaleSite) :
    Ideal (X.structureSheaf.obj.obj (op T)) :=
  Ideal.span (Set.range (i.val.app (op T)))

/-- Sections locally in the product of the nth ideal power with a family of sections.
When `A` is the family of sections of a submodule sheaf, this is precisely the family
of sections of its ideal product. The span forms finite linear combinations and the
covering sieve sheafifies their local membership condition. At power zero this recovers
`A` for a submodule sheaf, including on objects covered by the empty sieve.
Source: Stacks, Spaces Cohomology, Tag 07UL, ideal products in lemma-Artin-Rees
(blueprint: lem-sfb-space-artin-rees). -/
def idealPowerSubsheafSections {S : Scheme.{u}} {X : AlgebraicSpace S} {I : X.Modules}
    (i : I ⟶ SheafOfModules.unit X.structureSheaf) (F : X.Modules)
    (A : ∀ T : X.EtaleSite, Set (F.val.obj (op T))) (n : ℕ)
    (T : X.EtaleSite) : Set (F.val.obj (op T)) :=
  {s | ∃ R : Sieve T, R ∈ X.etaleTopology T ∧
    ∀ (V : X.EtaleSite) (f : V ⟶ T), R f →
      F.val.map f.op s ∈
        idealSectionImage i V ^ n • Submodule.span (X.structureSheaf.obj.obj (op V)) (A V)}

/-- Artin-Rees for a coherent module and a quasi-coherent submodule on a Noetherian space.
The three hypotheses on `X` mean locally Noetherian, quasi-compact and absolutely
quasi-separated. Coherence of `F` is rendered in its equivalent quasi-coherent finite-type
form under `hln` (Tag 07UB). The inclusions `g` and `i` specify actual submodule sheaves.
Source: Stacks, Spaces Cohomology, Tag 07UL, lemma-Artin-Rees
(blueprint: lem-sfb-space-artin-rees).

Proof:
1. Choose an affine surjective etale atlas U -> X using
   lem-sfb-qc-space-affine-etale-atlas. The Noetherian affine-atlas theorem
   lem-sfb-noetherian-affine-atlas-relation makes U a Noetherian scheme.
2. Restrict F, N and I to U. Local presentations restrict, so they remain
   quasi-coherent. The scheme Zariski-etale quasi-coherent equivalence identifies
   them with Zariski modules and their inclusions, with F coherent on U.
3. Apply lem-weil-pbc-coherent-artin-rees on U to obtain a single bound c.
   Use lem-sfb-scheme-etale-module-exact-finiteness-comparison and
   lem-sfb-space-qcoh-affine-chart-calculus: intersections are kernels of the
   difference map and products are images of tensor multiplication, so the exact
   tensor comparison carries the equality to the small etale site of U.
4. Restriction from X to U preserves sectionwise intersections. It also preserves
   the local finite sums of products defining idealPowerSubsheafSections, because
   the covering families of a test over U are the same after composition to X.
5. For every test T -> X, use the surjective etale cover T x_X U -> T.
   Membership in either subsheaf is local: preimages of a section agree on
   overlaps by monicity of its inclusion, and glue by the sheaf axiom. Descend
   both inclusions to T. The same c works for every n >= c and every test T. -/
theorem coherent_artin_rees
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (F N I : X.Modules) (hF : F.IsQuasicoherent ∧ F.IsFiniteType)
    (g : N ⟶ F) [Mono g] (hN : N.IsQuasicoherent)
    (i : I ⟶ SheafOfModules.unit X.structureSheaf) [Mono i] (hI : I.IsQuasicoherent) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ T : X.EtaleSite,
      idealPowerSubsheafSections i F (fun _ ↦ Set.univ) n T ∩
          Set.range (g.val.app (op T)) =
        idealPowerSubsheafSections i F
          (fun V ↦ idealPowerSubsheafSections i F (fun _ ↦ Set.univ) c V ∩
            Set.range (g.val.app (op V))) (n - c) T := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

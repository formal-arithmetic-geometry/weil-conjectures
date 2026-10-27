/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.ClosedRestrictionDerivedOperations
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.DerivedSectionsScalarCoherence
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import Sheaf.Paper.QlbarTailModuleColimit
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Supported finite-model rigidity for the norm-topological algebraic closure

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md (2), first paragraph, closed-fibre comparison.
Agent-formulated conditional transfer; exact full-generality reference WANTED.
(blueprint: lem-sfb-supported-norm-algcl-model-rigidity-transfer).

The algebraic closure coefficient is the ring of all continuous maps into `PadicAlgCl`,
with its incomplete norm topology. The support chains are paths in finite qcqs open-closed
trees. A chain is represented by adjoining complementary siblings, and a path may stop
at any vertex; the root path is the identity chain. No complement condition is imposed
on the fixed closed immersion. The notation B in the node is expanded as quantifiers.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite-subextension supported-model rigidity implies rigidity for all continuous
norm-topological algebraic-closure finite scalar models, with unrestricted transitions.
Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph;
agent-formulated conditional transfer, exact full-generality reference WANTED.
(blueprint: lem-sfb-supported-norm-algcl-model-rigidity-transfer).

Proof plan (the reviewed DAG):

1. Fix a support chain $J$ and finite scalar $\Omega$-local model $L$. The derived-generation
theorem applies to this exact all-continuous coefficient ring on the qcqs root $T$: it puts
$JL[0]$ in its explicitly defined class $\mathscr G_T$. We will prove that every object of that
class has invertible actual restriction. Its generators are $J'_B(B_W\otimes_{E_W}N)[0]$, with
arbitrary allowed support chain $J'$, finite intermediate field $E$ and finite locally free
$E_W$-module $N$. Such $N$ is an allowed finite scalar local model. No finite-field model for $L$
or its transition maps is chosen.
Uses: lem-sfb-norm-local-model-finite-field-derived-generation.

2. We may compute all following section comparisons after scalar restriction to a fixed finite
$E$. Internal/sectionwise transport preserves underlying sheaves, sections and the open/closed
functors, including their units and counits. Exact inverse image for any pulled-back condensed
coefficient has the same underlying abelian inverse image; hence it commutes with scalar
restriction. The unit-normalized derived-section isomorphisms for scalar restriction identify the
actual derived restriction maps as well: choose a coefficient-module K-injective resolution $I$
and a resolution of $t^*I$, and compare their scalar restrictions to K-injective resolutions over
$E$. Both routes from the original module to the target resolution lift the identical underived
section unit. The K-injective comparison principle makes the two routes equal after localization.
This uses comparison resolutions over $E$, rather than assuming the forgotten complexes or $t^*I$
are K-injective. Therefore it suffices to test invertibility over $E$ with these canonical section
identifications.
Uses: lem-sfb-internal-module-operations-transport, det-prop-sfb-module-pullback-exact-main, lem-
coef-derived-sections-scalar-coherence, lem-sp-kinjective-comparison-principle.

3. Fix one generating chain $J'$ with source $W$, finite field $E$, and lisse $E_W$-module $N$.
Use $C$ for the finite-subextension-valued ring and $B$ for all norm-continuous functions. For
finite $F\supseteq E$ put $H_F=J'_E\operatorname{Res}_{E_W\to F_W}(F_W\otimes_{E_W}N)$. Each
$F_W$-extension of $N$ is locally finite free, so the hypothesis $\mathsf B_F(t)$ applies to this
same chain. Step 2 identifies its actual restriction with $\rho_{H_F}$. The tail coefficient-
colimit theorem gives $C_W=\varinjlim_{F\supseteq E}F_W$ over the small directed tail. Relative
tensor preserves this colimit by its adjunction. Open extension preserves it as a left adjoint;
closed pushforward preserves it because each target is qcqs and its open complement is quasi-
compact. Inducting through $J'$ gives $H_C=\varinjlim_F H_F$, as $E_T$-module sheaves, with the
actual scalar-inclusion maps. Here $H_C$ is precisely the first term of the topology-defect lemma.
This colimit statement is about $C$, not $B$.
Uses: lem-sfb-qlbar-tail-module-colimit, sk-def-sfb-change-of-scalars, lem-weil-pbc-module-
sheaves-colimits-forgetful, lem-weil-pbc-proetale-ringed-open-closed, def-sfb-module-open-lower-
shriek, lem-sfb-internal-module-operations-transport.

4. Apply the closed-restriction continuity theorem over the coefficient ring $E$ to the strict
diagram $H_F[0]$, which has common termwise lower bound zero. It identifies the restriction of
$H_C[0]$ with the filtered colimit of the restriction arrows for $H_F[0]$. Each is invertible by
step 3 and $\mathsf B_F(t)$; its filtered colimit is invertible, the colimit of the inverse arrows
being its inverse. Thus $\rho_{H_C[0]}$ is invertible. The theorem applies to qcqs $T,T_0$ and
needs no quasi-compactness of the complement of the original $t$.
Uses: lem-sfb-closed-restriction-derived-operations.

5. Let $m:H_C\to H_B$ and $D_{J',E,N}=[H_C\xrightarrow m H_B]$ in degrees $-1,0$ be exactly the
objects of the topology-defect lemma for this generating chain. The pair satisfies that lemma's
torsion hypothesis verbatim. It makes $\rho_D$ invertible without the comparison property $\mathsf
B_E(t)$ as an extra premise. The mapping-cone triangle $H_C[0]\to H_B[0]\to D\to H_C[1]$ is
distinguished. The closed-restriction theorem sends this triangle to a morphism of distinguished
triangles, including its connecting arrow. Its first and third arrows are invertible by step 4 and
the defect lemma, so the triangle isomorphism criterion makes its middle arrow $\rho_{H_B[0]}$
invertible. Step 2 transports this actual map to the $B$-module restriction for
$J'_B(B_W\otimes_{E_W}N)[0]$, as required for this generator.
Uses: lem-sfb-supported-coefficient-topology-defect-rigidity, def-weil-abstract-derived-category,
lem-sfb-closed-restriction-derived-operations, lem-sf-triangle-morphism-iso.

6. Let $\mathscr R$ be the full replete class of $K$ for which the actual $\rho_K$ is invertible.
It contains zero since the two additive section functors send zero to zero, and contains every
generator by step 5. The closed-restriction theorem makes it shift-closed. For a distinguished
triangle, its actual restrictions form a morphism of distinguished triangles; two-out-of-three
makes it extension-closed. For a retract $K\xrightarrow{i}M\xrightarrow{p}K$ with $\rho_M$
invertible, the inverse of $\rho_K$ is $\Phi(p)\rho_M^{-1}\Psi(i)$: naturality and $pi=1$ make
both composites identities. For a small product the theorem identifies its restriction with the
product of the restrictions, whose inverse is the product of their inverses. For a strict small
filtered diagram with a common termwise lower bound, the theorem identifies restriction at the
termwise colimit with the colimit of the restriction arrows; the colimit of their inverses is an
inverse. Thus $\mathscr R$ satisfies every defining condition of $\mathscr G_T$, so the
intersection defining $\mathscr G_T$ lies in $\mathscr R$. Step 1 now gives invertibility for
$JL[0]$. The chain and model were arbitrary, proving $\mathsf B_\Omega(t)$, including zero models,
empty schemes and identity chains.
Uses: lem-sfb-closed-restriction-derived-operations, lem-sf-triangle-morphism-iso.
-/
theorem supported_norm_algcl_model_rigidity_transfer
    (ℓ : ℕ) [Fact ℓ.Prime]
    {T₀ T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (ht : ∀ (F : Sheaf T.smallEtaleTopology Ab.{u + 1}),
      Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ,
        Function.Bijective (Etale.cohomologyMap t F q))
    (hfinite : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (S : Scheme.{u}) (tree : QcqsOpenClosedTree T) (p : tree.Path S)
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) S)),
      HasFiniteConstantLocalModel (Profinite.continuousMapRingObj E) S L →
      IsIso ((closedRestrictionRho (Profinite.continuousMapRingObj E) t).app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((p.extension (Profinite.continuousMapRingObj E)).obj L)))) :
    ∀ (S : Scheme.{u}) (tree : QcqsOpenClosedTree T) (p : tree.Path S)
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) S)),
      HasFiniteConstantLocalModel (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) S L →
      IsIso ((closedRestrictionRho (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) t).app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((p.extension (Profinite.continuousMapRingObj (PadicAlgCl ℓ))).obj L))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

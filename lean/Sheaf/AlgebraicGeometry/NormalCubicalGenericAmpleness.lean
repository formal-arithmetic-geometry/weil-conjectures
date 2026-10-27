/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Generic ampleness of a supplied cubical line

Source: Moret-Bailly, Pinceaux de varietes abeliennes, VI 3.0--3.1;
Raynaud, Faisceaux amples, XI 1.13 (Lan cites XI 1.16).
(blueprint: lem-sfb-normal-cubical-generic-ampleness)

The normal locally Noetherian version is the agent prerequisite recorded in the DAG;
the originals are WANTED there. The line on the whole group is supplied as input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A supplied cubical rigidified line over a normal integral locally Noetherian base
is relatively ample if its proper generic fibre restriction is ample and symmetric.
The conclusion tests every affine open of the base, without global quasi-compactness.

Source: Moret-Bailly VI 3.0--3.1; Raynaud XI 1.13 / XI 1.16; Lan Lemma 4.2.1.6.
The locally Noetherian normal-base formulation is the agent prerequisite of the DAG;
the original references are WANTED.
(blueprint: lem-sfb-normal-cubical-generic-ampleness)

Proof plan, following the eight steps of the node:
1. Restrict to each nonempty affine base open T. Apply
   lem-sfb-raynaud-generic-ample-power-model to the ample symmetric generic line.
   It supplies locally a relatively ample ordinary line N whose generic restriction
   is a positive power B^d of the supplied line.
2. Refine so the identity restriction of N is free of rank one, and rigidify N.
   Relative ampleness survives by lem-trf-scheme-relative-ample-base-change.
   Rescale the generic comparison by its identity value to preserve rigidifications.
3. The semiabelian fibres are geometrically connected: the connected torus cosets
   descend any clopen decomposition to the connected abelian quotient. Apply case (b)
   of lem-sfb-semiabelian-cubical-rigidification to N; tensor the supplied cube to get
   the cube on B^d, using def-sfb-cubical-rigidified-line.
4. Express the generic fibre over affine T as the limit of nonzero principal base
   localizations. The finite-presentation modules N and B^d and their specified generic
   isomorphism descend, with inverse, by lem-trf-fp-module-limit-isomorphism-descent.
   Thus the comparison is defined over a nonempty dense principal open U.
5. Its identity value is a unit in the domain of U and is generically one, hence one.
   It preserves rigidifications and therefore cubes by the final clauses of
   lem-sfb-semiabelian-cubical-rigidification.
6. Full faithfulness in lem-sfb-normal-symmetric-cubical-extension extends this cubical
   comparison from the dense OPEN U to T. Transport ampleness from N to B^d.
7. On any affine base open, an affine nonvanishing neighbourhood supplied by a section
   of (B^d)^m is the same neighbourhood for that section of B^(dm), with dm positive.
   The definition def-weil-pbc-ample-invertible-module therefore makes B ample there.
8. The original morphism is quasi-compact, since it is of finite presentation.
   Apply lem-trf-scheme-relative-ample-affine-cover to the resulting affine covering
   to obtain ampleness over every affine base open, including for non-quasi-compact S.
No existence of an extension of a generic line is asserted. -/
theorem normal_cubical_generic_ampleness
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Grp (Over S)) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    (hproper : IsProper (pullback.snd G.X.hom
      (S.fromSpecResidueField (genericPoint S))))
    (B : CubicalRigidifiedLine G.X)
    (hample : ∃ h : ((Scheme.Modules.tensorPullback
      (pullback.fst G.X.hom (S.fromSpecResidueField (genericPoint S)))).obj
        B.line).IsInvertible,
      @Scheme.Modules.IsAmple
        (pullback G.X.hom (S.fromSpecResidueField (genericPoint S)))
        ((Scheme.Modules.tensorPullback
          (pullback.fst G.X.hom (S.fromSpecResidueField (genericPoint S)))).obj
            B.line) h)
    (hsymmetric : Nonempty
      ((Scheme.Modules.tensorPullback
        ι[((Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj G).X].left).obj
          ((Scheme.Modules.tensorPullback
            (pullback.fst G.X.hom (S.fromSpecResidueField (genericPoint S)))).obj B.line) ≅
              (Scheme.Modules.tensorPullback
                (pullback.fst G.X.hom (S.fromSpecResidueField (genericPoint S)))).obj B.line)) :
    ∀ W : S.Opens, IsAffineOpen W →
      ∃ h : ((Scheme.Modules.tensorPullback (G.X.hom ⁻¹ᵁ W).ι).obj B.line).IsInvertible,
        @Scheme.Modules.IsAmple (G.X.hom ⁻¹ᵁ W).toScheme
          ((Scheme.Modules.tensorPullback (G.X.hom ⁻¹ᵁ W).ι).obj B.line) h := by
  sorry

end AlgebraicGeometry

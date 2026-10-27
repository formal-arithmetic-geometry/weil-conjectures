/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentification
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Local frames from ordinary étale identifications

Source: Stacks Project, Descent, Tag 05VG; Spaces, Tag 060X.
(blueprint: lem-trf-ordinary-etale-identification-local-frames).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- An ordinary invertible module, identified naturally with N on a chart,
provides a covering by frames on every test object over that chart.
No atlas, overlap data, or joint-surjectivity hypothesis is needed.

Source: Stacks Project, Descent, Tag 05VG (lemma-equivalence-quasi-coherent-properties),
rank-one case; Spaces, Tag 060X (lemma-finite-locally-free-descends)
(blueprint: lem-trf-ordinary-etale-identification-local-frames).

Proof: for T → V, the ordinary tensor pullback of L to the underlying scheme of T
is invertible. Choose its Zariski trivializing opens; they are jointly surjective
étale scheme maps and hence form a covering of T in F's small étale site.
On each such open U, and every further étale test W → U, tensor pullback of the
ordinary trivialization identifies the tensor-section module with Γ(W, O_W).
The tensor-unit and unit-normalized composition comparisons make these linear
identifications natural in W. Composing their inverses with e.app gives an
isomorphism between N restricted to U and the localized structure module.
Pass from the open covering family to its generated covering sieve. An arrow
in this sieve factors through one of the trivializing opens; pulling the same
frame back along that factorization supplies the required isomorphism there.
The comparison respects all module morphisms, so the resulting maps and inverses
are module-sheaf maps. Empty test schemes cause no exception: their empty
covering is allowed and their assertion follows from the same sheaf condition. -/
theorem ordinary_etale_identification_local_frames
    {S : Scheme.{u}} (F : AlgebraicSpace S) (V : F.EtaleSite)
    (N : F.Modules) (L : (F.etaleForget.obj V).Modules)
    (hL : Scheme.Modules.IsInvertible L) (e : OrdinaryEtaleIdentification F V N L)
    (T : F.EtaleSite) (a : T ⟶ V) :
    ∃ R : Sieve T, R ∈ F.etaleTopology T ∧
      ∀ (U : F.EtaleSite) (f : U ⟶ T), R f →
        Nonempty ((F.etalePullback U).obj N ≅
          SheafOfModules.unit (F.structureSheaf.over U)) := by sorry

end AlgebraicGeometry.AlgebraicSpace

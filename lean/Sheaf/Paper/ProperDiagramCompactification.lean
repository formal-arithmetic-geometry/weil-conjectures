/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.Compactification.NagataSketchClosure
import WeilConjectures.Compactification.Dense

/-!
# Simultaneous compactification of a proper correspondence diagram

Source: literature/varshavsky-lefschetz-verdier-trace-formula_arXiv-math0505564.pdf,
§4.1.4(a), final paragraph, using the graph-closure construction of Remark 1.1.3
(blueprint: lem-trf-proper-diagram-compactification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Simultaneous compactification of a proper correspondence diagram.

Source: literature/varshavsky-lefschetz-verdier-trace-formula_arXiv-math0505564.pdf,
§4.1.4(a), final paragraph, using the graph-closure construction of Remark 1.1.3
(blueprint: lem-trf-proper-diagram-compactification).

All schemes and maps, given and constructed, are `k`-schemes and `k`-morphisms
(`Scheme.Hom.IsOver`), as in the node and in Varshavsky's category of `k`-schemes; the
compactifications are formed by closures in fibre products over `Spec k`.

Proof plan: choose a proper compactification of `Y` and auxiliary compactifications of
`B`, `X`, and `C`. Take successive scheme-theoretic images of the tuples encoding the
maps to these compactifications. Properness and separatedness of the ambient products
make the resulting compactifications proper and finite type. Restricting the images to
`Y`, respectively `B`, identifies them with `X`, respectively `C`, and hence gives the
two Cartesian pullback squares. The tuple projections give all displayed compatibilities;
the equalities on the dense open `C` extend across the separated target. Density follows
from scheme-theoretic density of the closure opens, and the two canonical pullback maps
are isomorphisms. The proof uses `sk-thm-nagata-compactification`,
`sk-lem-nagata-sketch-closure`, `lemma-nagata-scheme-image-restrict-open`,
and the properness, immersion, and separatedness lemmas listed in the DAG node.
-/
theorem exists_proper_diagram_compactification {k : Type u} [Field k]
    {X Y C B : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [C.Over (Spec (.of k))] [B.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    [IsSeparated (B ↘ Spec (.of k))]
    [LocallyOfFiniteType (B ↘ Spec (.of k))]
    [QuasiCompact (B ↘ Spec (.of k))]
    (c₁ c₂ : C ⟶ X) (b₁ b₂ : B ⟶ Y)
    [c₁.IsOver (Spec (.of k))] [c₂.IsOver (Spec (.of k))]
    [b₁.IsOver (Spec (.of k))] [b₂.IsOver (Spec (.of k))]
    (p : X ⟶ Y) (q : C ⟶ B) [p.IsOver (Spec (.of k))] [q.IsOver (Spec (.of k))]
    [IsProper p] [IsProper q]
    (hp₁ : q ≫ b₁ = c₁ ≫ p) (hp₂ : q ≫ b₂ = c₂ ≫ p) :
    ∃ (Xstar Ystar Cstar Bstar : Scheme.{u})
      (_ : Xstar.Over (Spec (.of k))) (_ : Ystar.Over (Spec (.of k)))
      (_ : Cstar.Over (Spec (.of k))) (_ : Bstar.Over (Spec (.of k))),
      IsProper (Xstar ↘ Spec (.of k)) ∧
        IsProper (Ystar ↘ Spec (.of k)) ∧
        IsProper (Cstar ↘ Spec (.of k)) ∧
        IsProper (Bstar ↘ Spec (.of k)) ∧
        ∃ (uX : X ⟶ Xstar) (uY : Y ⟶ Ystar) (uC : C ⟶ Cstar) (uB : B ⟶ Bstar)
          (_ : IsOpenImmersion uX) (_ : IsOpenImmersion uY)
          (_ : IsOpenImmersion uC) (_ : IsOpenImmersion uB)
          (_ : uX.IsOver (Spec (.of k))) (_ : uY.IsOver (Spec (.of k)))
          (_ : uC.IsOver (Spec (.of k))) (_ : uB.IsOver (Spec (.of k))),
          DenseRange uX ∧ DenseRange uY ∧ DenseRange uC ∧ DenseRange uB ∧
            ∃ (pstar : Xstar ⟶ Ystar) (qstar : Cstar ⟶ Bstar)
              (_ : IsProper pstar) (_ : IsProper qstar)
              (_ : pstar.IsOver (Spec (.of k))) (_ : qstar.IsOver (Spec (.of k))),
              ∃ (c₁star c₂star : Cstar ⟶ Xstar)
                (b₁star b₂star : Bstar ⟶ Ystar)
                (_ : c₁star.IsOver (Spec (.of k))) (_ : c₂star.IsOver (Spec (.of k)))
                (_ : b₁star.IsOver (Spec (.of k))) (_ : b₂star.IsOver (Spec (.of k))),
                ∃ (hX : uX ≫ pstar = p ≫ uY)
                  (hC : uC ≫ qstar = q ≫ uB)
                  (hc₁ : uC ≫ c₁star = c₁ ≫ uX)
                  (hc₂ : uC ≫ c₂star = c₂ ≫ uX)
                  (hb₁ : uB ≫ b₁star = b₁ ≫ uY)
                  (hb₂ : uB ≫ b₂star = b₂ ≫ uY)
                  (hleg₁ : qstar ≫ b₁star = c₁star ≫ pstar)
                  (hleg₂ : qstar ≫ b₂star = c₂star ≫ pstar),
                  IsIso (pullback.lift uX p hX) ∧
                    IsIso (pullback.lift uC q hC) := by
  sorry

end AlgebraicGeometry

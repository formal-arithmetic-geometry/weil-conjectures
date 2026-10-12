module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB

import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Constant-integer Ext in the standard large model computes terminal evaluation,
naturally in the coefficient sheaf.
Source: Stacks Project, Tags 01FT and 06XP, Lemma 13.27.2(1).
(blueprint: new-etale-cohomology-natural-derived-evaluation)

Proof: The constant-sheaf adjunction at the terminal object V identifies Hom from
the constant lifted integer sheaf to F with F(V), by evaluation at 1. This is an
additive identification, natural in F. On a chosen injective resolution of F it
identifies the Hom complex with the terminal-section complex, after lifting the
latter to the universe of the standard Ext model. Ext is the homology of the Hom
complex; the right-derived evaluation is the homology of the section complex.
The exact additive universe-lift functor preserves homology, so its homology may
be unlifted. Compose these three identifications for each F and n. A morphism
F -> G lifts to a chain map between their chosen injective resolutions. The
Hom-to-sections identification commutes degreewise with this chain map; both the
Ext computation and the right-derived computation are natural for the lift.
Consequently the composite equivalences satisfy the displayed equation. Different
lifts are homotopic and have the same homology map. The construction uses a fixed
comparison, rather than asserting naturality of arbitrary additive equivalences.
For the zero sheaf and for the empty scheme in positive degree both groups are
zero; the same argument applies without any nonemptiness assumption. -/
theorem etaleCohomologyNaturalDerivedEvaluation
    (X : Scheme.{u}) (V : X.Etale) (hV : IsTerminal V) :
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op V)
    ∃ e : ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ),
        @Sheaf.H _ _ X.smallEtaleTopology F inferInstance (HasExt.standard _) (n + 1) ≃+
          ((E.rightDerived (n + 1)).obj F),
      ∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (φ : F ⟶ G) (n : ℕ)
        (x : @Sheaf.H _ _ X.smallEtaleTopology F inferInstance
          (HasExt.standard _) (n + 1)),
        e G n (@Sheaf.H.map _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
          _ _ φ (n + 1) x) = (E.rightDerived (n + 1)).map φ (e F n x)  := by sorry

end AlgebraicGeometry.Scheme.Modules

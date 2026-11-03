/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerRationalTraceDefs

/-! # The categorical trace input over Qbar
Source: the reviewed Euler-product proof Step 3.
(blueprint: lem-condensed-weil-euler-qbar-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open NativeCondensedModule

/-- The ungrouped ordinary trace identity over Qbar, for the specified native operators.
Source: thm-trf-l-function-euler-product, reviewed proof Step 8 (blueprint Step 3).
Proof: bounded constructibility equals finite Tor constructibility over Qbar. Independent
geometric finiteness and constructible stability put compact supports and geometric
pullbacks in the bounded constructible point category. Apply the model-Frobenius
operator comparison to linearize theta and its m-fold iterate. Its compact comparison
identifies the global model action with the m-th power of the specified geometric
Frobenius; its stalk comparison identifies the local action with the semilinear return,
including inverse source reparametrization. The fixed points of the model Frobenius
iterate are the finite set of extension-valued points. Apply nt-assume-trace-formula
to that model object, with its right duals supplied by the condensed point-supertrace
lemma. That lemma identifies the categorical trace with the ordinary alternating
cohomology trace on both sides. Transfer the operators through their canonical
comparisons, using invariance of ordinary trace under linear isomorphisms and the
constant-section identification. Boundedness makes the degree sums finite. The return
proofs are propositions, so all their choices give the same operators. Empty point
sets and zero complexes give zero sums; arbitrary shifts retain the integer signs.
(blueprint: lem-condensed-weil-euler-qbar-trace). -/
theorem eulerQbarRationalTrace
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (K : strictWeilComplexCategory D ell hEll X₀ .qbar)
    (c₀ : Compactification (D.geometricFiber X₀).hom) (m : ℕ) (hm : 1 ≤ m) :
    ∃ hv : ∀ y : D.extensionPoints X₀ m hm,
        scalarLocalReturn D X₀ (eulerExtensionPoint D X₀ m hm y) m,
      (∑ᶠ j : ℤ, (j.negOnePow : ℤ) • eulerCompactTrace D X₀ ell hEll .qbar K c₀ m j) =
        ∑ᶠ y : D.extensionPoints X₀ m hm, ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
          eulerPointTrace D X₀ ell hEll .qbar K
            (eulerExtensionPoint D X₀ m hm y) m (hv y) j := by
  sorry

end WeilConjectures.CondensedWeilEuler

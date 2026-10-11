## Worker report

(C1, with reviewer fix R-vph1440.)

The node (statement as on sheaf-dag, the delivered correction reverted) says: A a valuation
ring, f : X -> Spec A proper, flat, of finite presentation, F an O_X-module locally free of
constant finite rank; then H^q(X,F) is a finitely presented A-module for every q >= 0.

Lean: `{A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]` (Mathlib's `ValuationRing`
takes `IsDomain`), `{X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] [Flat f]
[LocallyOfFinitePresentation f]` (finite presentation = LFP + qc + qs; proper supplies qc and
separated), `(d : ℕ) (F : X.Modules) [F.IsFiniteLocallyFreeOfRank d]` (recorded
def-amb-finite-locally-free-module), `(q : ℕ)`. Conclusion:
`Module.FinitePresentation A ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫
f.appTop).hom).obj ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F))`: H^q(X,F) is the
landed `RingedSpace.moduleCohomology` (STATE line COHOMOLOGY OF O_X-MODULES), made an A-module
along A ≅ Γ(Spec A) → Γ(X,O_X), as in landed ZeroSupportFiniteScheme.

## Second reading by C1

As fixed by reviewer R-vph1440: the delivery corrected the node to Γ(Spec A, R^q f_*F) "equivalently H^q(X,F)",
claiming H^q(X,F) was not expressible. It is (moduleCohomology), so the correction was unneeded
and is reverted; the corrected form also put an unproved comparison claim into the node and
moved the citer lem-sc-valuation-proper-coherent-sections (which speaks of H^0(X,F)) onto a
comparison. With the reverted statement the `HasInjectiveResolutions X.Modules` binder needed by
the source's `higherDirectImage` goes away. Docstring now carries the node's proof in words.

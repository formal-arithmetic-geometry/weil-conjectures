## Worker report

The module `Sheaf.CategoryTheory.ExtensionIsoQuotientFormula` states the single theorem
`CategoryTheory.Mod.extensionIso_quotient_formula`, with proof `sorry`. It introduces no definitions,
axioms, auxiliary theorems, or replacement scalar-change constructions. The node changes only in
`lean`; its statement and dependencies are unchanged.

Sources read: the complete item's seven proof steps; the current blueprint's
`sec-six-functors-basics/sk-def-sfb-module-lower-shriek/def-sfb-module-open-lower-shriek-adjunction.proof.md`
(last sentence); and
`sec-proetale-coefficients/sk-def-sfb-change-of-scalars/def-sfb-modobj-extension-along-iso.proof.md`
(the comparison through the two adjunctions). The theorem docstring records all seven steps,
including why the identity-Hom adjunction and the inverse-equivalence adjunction have the same unit.

Hypothesis matching:

- The ambient category is `{C : Type u} [Category.{v} C]`, with independent object and morphism
  universes explicitly bound. `[MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]`
  represents the symmetric monoidal closed category.
- `[HasEqualizers C] [HasCoequalizers C]` represents both specified finite limit/colimit hypotheses.
- `[∀ X : C, PreservesColimits (tensorLeft X)]` and the analogous `tensorRight` binder give
  preservation of small colimits in each variable. Every use of an extension declaration
  explicitly supplies the universe-zero instances via Mathlib
  `preservesSmallestColimits_of_preservesColimits`, applied pointwise to both tensor functors.
  These are consequences of the stated hypotheses, not extra binders. No equality of object
  and morphism universes is imposed.
- `{R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]` gives precisely the two
  commutative monoid objects; in particular commutativity of S is retained even though the
  extension API only needs commutativity of R.
- `(φ : R ⟶ S) [IsMonHom φ] [IsIso φ]` means an invertible monoid morphism. Its inverse is
  `(asIso φ).inv`; the published inverse-monoid-hom instance supplies restriction along it.
- `(N : Mod C R)` is an arbitrary internal R-module. Its underlying object is `N.X` and its
  action is `γ[R,N.X]`. There is no additional property of N.

Construction matching: `T_N` is the target of `(extendScalarsIsoComapInv φ).app N`, namely
`(comap (asIso φ).inv).obj N`. Reading `Mod.scalarRestriction` and `Mod.comap` shows that its
underlying object is definitionally `N.X` and its action is
`(asIso φ).inv ▷ N.X ≫ γ[R,N.X]`. This expression is used explicitly throughout the statement.
`F_N` is `(extendScalarsObj φ N)` or definitionally `(extendScalars φ).obj N`.
`extendπ φ N` is the actual chosen coequalizer projection. `η[S]` and `(λ_ N.X).inv` are the
existing monoid unit and inverse left unitor. `p_N` is exactly
`((extendScalarsIsoComapInv φ).hom.app N).hom`, not an arbitrary isomorphism or factor.
`s_N` is written throughout as `(λ_ N.X).inv ≫ η[S] ▷ N.X ≫ extendπ φ N`.
Lean's diagrammatic composition reverses the displayed source's composition order.

Conclusion matching, in conjunction order:

1. The first equality says that the inverse scalar action coequalizes
   `((S ◁ φ ≫ μ[S]) ▷ N.X)` and `((α_ S R N.X).hom ≫ S ◁ γ[R,N.X])`, precisely the pair
   in `extendScalarsObj_X` and `extendπ`.
2. `extendπ φ N ≫ p_N = (asIso φ).inv ▷ N.X ≫ γ[R,N.X]` is the normalization `p_N ∘ q_N = β_N`.
3. The quantified `f : (extendScalarsObj φ N).X ⟶ N.X` clause asserts uniqueness among all
   underlying factors, not merely S-linear factors.
4. The comparison's inverse component equals the fully expanded unit-insertion composite.
5. The next equality is S-linearity of `p_N`, with the source action on F and the twisted
   target action written explicitly. It also follows from its bundled module-morphism type.
6. The next equality is S-linearity of the explicit unit-insertion composite, with the
   twisted action on its domain.
7. `s_N ≫ p_N = 𝟙 N.X` is `p_N ∘ s_N = id_T`.
8. `p_N ≫ s_N = 𝟙 (extendScalarsObj φ N).X` is `s_N ∘ p_N = id_F`.
9. For every `(N' : Mod C R) (h : N ⟶ N')`, the final two equalities state respectively
   `E(h) ≫ p_N' = p_N ≫ h.hom` and `h.hom ≫ s_N' = s_N ≫ E(h)`.
   Restriction keeps the underlying map `h.hom`, so these are exactly both naturalities.

Dependency declarations read and used:

- `sk-def-sfb-ring-object`: the generic paragraph uses `CategoryTheory.MonObj`, `IsMonHom`,
  and `IsCommMonObj` in `Mathlib.CategoryTheory.Monoidal.Mon`. Its recorded RingPresheaf
  module lists these same declarations and is publicly imported, as is Mathlib Mon.
  The ring/sheaf specializations are unnecessary here.
- `sk-def-sfb-module-objects`: `CategoryTheory.Mod`, `ModObj`, `IsModHom`, `Mod.Hom`, and
  `Mod.comap` in `Mathlib.CategoryTheory.Monoidal.Mod`, including their full structures and
  restriction definitions. The regular module and pro-etale specializations are not used.
- `sk-def-sfb-change-of-scalars`: `CategoryTheory.Mod.extendScalars`, `extendScalarsObj`,
  `extendScalarsObj_X`, `extendπ`, `extendUnitHom`, and `extendRestrictAdjunction`, from
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`. The projection's pair and
  the unit's complete definition were checked against the displayed source formulas.
- `def-sfb-modobj-extension-along-iso`: the closed upstream audit records
  `CategoryTheory.Mod.extendScalarsIsoComapInv` in
  `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`. Its full definition is
  `(extendRestrictAdjunction φ).leftAdjointUniq (comapEquivalenceOfIsIso φ).symm.toAdjunction`.
  This is the exact comparison named in the item. `comapEquivalenceOfIsIso` uses inverse
  restriction and the identity/composition restriction isomorphisms.
- The stated proof dependencies are imported through these same modules and explicit ordinary
  imports of `Mathlib.CategoryTheory.Adjunction.Basic`, `.Mates`, `.Unique`,
  `Mathlib.CategoryTheory.Equivalence`, and `Mathlib.CategoryTheory.Limits.HasLimits`.
  These cover `Adjunction.mkOfHomEquiv`, the conjugate comparison and unit equation,
  `Equivalence.toAdjunction`, and `colimit`/`IsColimit`; the other proof dependencies use
  the monoid/module/scalar-change modules above. No proof-dependency import is omitted.

Edge cases checked before writing: for φ the identity, β is the original action and s is
unit insertion into R tensor_R N; every displayed relation has the expected orientation.
For a nontrivial scalar automorphism (complex conjugation on Z[i]), β(s,n) is conjugate(s)n,
so the inverse scalar action, rather than the original action, is necessary. The balanced
relation is then β(sφ(r),n) = β(s,rn). Zero modules and zero ring objects, when present in C,
are not excluded by any nonzero or nonempty assumption. Neither elements nor generation by
pure tensors is assumed in the arbitrary ambient category; the proof uses the quotient's
universal property and categorical unit laws. Arbitrary h, including identities, is covered.

Searches actually run with `msearch.py Q47 lem-sfb-extension-iso-quotient-formula`:

- LeanFinder: "Extension of scalars along an isomorphism of internal monoid objects has
  quotient map the inverse scalar action and inverse insertion of the unit": eight hits,
  including `ModuleCat.extendScalarsId_inv_app_apply`, representation-theoretic unit
  isomorphisms, and the internal algebra/module equivalence. No arbitrary-category formula.
- Loogle: `CategoryTheory.Mod, "extendScalars"`: zero hits.
- Mathlib grep: `extendScalarsIsoComapInv|extendUnitHom|extendπ`, subdirectory CategoryTheory:
  zero hits.
- LeanSearch: "Extension of scalars along an invertible morphism of internal monoids is
  inverse restriction with inverse unit insertion": eight hits, including ordinary
  `ModuleCat.ExtendRestrictScalarsAdj` unit/Hom formulas, linear equivalence restriction,
  and ordinary module restriction. No match for the internal arbitrary-category formula.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item ID and for the scalar-comparison,
  projection, and unit names found the published definitions, numerous consumers, and
  private unit-normalization/inverse-component lemmas in `Sheaf.Paper.ComapUpperStarIsoMate`.
  These private lemmas give only part of this item's clauses. No existing declaration
  states the full quotient/coequalizing/uniqueness/linearity/inverse/naturality conjunction.
  The proposed full theorem name was also searched in both trees, with no occurrence.

No new nodes, unusable dependency interfaces, statement corrections, or disputed statements.
The saved packet's first dry run now reached Lean after the previous published-artifact
outage was resolved. It exposed an instance-inference defect: the hypotheses use
`PreservesColimits` (at the hom universe), whereas the upstream extension API requests
`PreservesColimitsOfSize.{0, 0}`. The corrected signature supplies the exact existing
Mathlib shrinking lemma explicitly in every call to `extendπ`, `extendScalarsObj`,
`extendScalars`, and `extendScalarsIsoComapInv`. The `@` applications only expose these
proof arguments; all module objects, projections, actions, comparison components,
and functors remain the recorded upstream constructions. No auxiliary declaration,
file-local instance, notation, definition, or statement correction is introduced.

## Second reading by Q47

I reread the node and the complete declaration after writing them. This is a self-check;
the dispatcher's independent maintainer review remains independent. The mapping above
checks each hypothesis and each conjunct against the open node. In particular, both
commutativity hypotheses remain, the inverse action is used on s's domain, uniqueness
quantifies over ambient morphisms, p is the existing adjoint-uniqueness comparison, and
both naturality equations are present with the correct composition order. The explicit
inverse formula uses the actual projection, not an unspecified coequalizer map.
No discrepancy or statement change was found. The source contains exactly one named
theorem and its sole proof is `sorry`; every universe and variable is explicitly bound.
All lines are at most 100 characters. On the repair reading I checked every fully
explicit `@` application against the upstream signature: C, its category and monoidal
structure, coequalizers, the two derived preservation proofs, braiding, R and S, their
monoid structures, commutativity of R, φ and its monoid-hom proof, and for the comparison
its isomorphism proof. These only make existing implicit arguments explicit. The
hypotheses remain the original all-small-colimit assumptions, and object and morphism
universes remain independent. I also checked current upstream sources, current node
records, the source blueprint proof files, and searched both project trees for the item
and proposed declaration; neither has an existing full formula. The only changed node
field is `lean`. The module publicly imports every statement-dependency module,
including RingPresheaf, and imports every recorded proof-dependency module.

Validation: the prescribed `scompile.py Q47 lem-sfb-extension-iso-quotient-formula`
compiled the final file both as a sandbox module and at its library module path, with
no errors or warnings (16.3 s and 13.5 s). The prescribed `deliver2.py ... --no-push`
then printed `OK (dry run)`: the packet passes preflight and compiles. Exactly the
item module, its lean-only node update, and this report are staged for delivery.

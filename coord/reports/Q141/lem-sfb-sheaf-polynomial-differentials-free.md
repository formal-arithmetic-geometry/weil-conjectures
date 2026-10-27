## Worker report

Item: `lem-sfb-sheaf-polynomial-differentials-free`, stage 2, Q141.
Module: `Sheaf.CategoryTheory.SheafPolynomialDifferentialsFree`.
Primary declaration:
`CategoryTheory.SheafPolynomialDifferentials.sheaf_polynomial_differentials_free`.
Its only postponed proof is `by sorry`. The three helper definitions have real data;
there are no auxiliary postponed theorems or newly defined independent notions.

Source read: `literature/stacks-project/defos.tex`,
`lemma-NL-represent-ext-class-ringed-topoi` (Tag 08UJ), lines 4136–4200.
The first paragraph identifies the evaluated polynomial differentials with the sheaf
associated to the sectionwise free B-modules. The subsequent E-prime to E construction
uses its functoriality on generators. Polynomial differential bases and sheafification
comparisons supply the argument independently of evaluation surjectivity.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A site small in the chosen universe | Explicit `universe u`, `{C : Type u} [SmallCategory C]`; theorem binds `J : Precoverage C` and `_hJ : J.IsSiteForCoverings`, with sheaves on `J.toGrothendieck`. Both objects and arrows are in the universe of values. |
| Sheaves of commutative rings A and B and their map | `(A B : Sheaf J.toGrothendieck CommRingCat.{u}) (f : A ⟶ B)`. |
| Arbitrary sheaf of generators and map to B | `E : Sheaf J.toGrothendieck (Type u)` and `α : E ⟶ sets B`, quantified for the entire family of comparisons. `sets` is the existing same-universe underlying-set sheaf. |
| P_E is sheafification of U ↦ A(U)[E(U)] | Existing `SheafPolynomialCotangent.polynomials` has precisely those section rings and coefficient/generator restrictions; `polynomialSheaf` applies `presheafToSheaf`. `variableSection` applies `toSheafify` to `MvPolynomial.X e`. |
| Evaluation [e] ↦ α(e), with the prescribed coefficients | Existing `SheafPolynomialCotangent.evaluation f α`, obtained from sectionwise `MvPolynomial.eval₂Hom (f.hom.app U).hom (α.hom.app U)` by the ring-sheafification adjunction. |
| Sheaf differentials obtained by sheafifying sectionwise differentials | Existing `SheafDifferentials.omega (base A E)` and `derivation (base A E)`. The former sheafifies `relativeDifferentials'`; the latter composes `derivation'` with the module-sheafification unit. |
| Tensor extension to B | `term f E α` is exactly `SheafOfModules.changeOfRingsOfUniverses (evaluation f α) (omega (base A E))`, the existing sheafified scalar extension. |
| The free B-module sheaf B^(E) | `(SheafFreeModule.free B).obj E`, the existing sheafification of `PresheafOfModules.freeObj`. Its generators are `SheafFreeModule.generatorRaw B E`. No polynomial algebra is used in place of this module. |
| A canonical B-linear isomorphism Φ_E | The existential family `Φ`, with each component an isomorphism in `ringedSiteModules (SheafFreeModule.ring B)`. Thus its maps are B-linear. The explicit generator normalization fixes the map uniquely by the recorded free-module universal property. |
| [e] ↦ d[e] ⊗ 1 | The first conjunction evaluates `(Φ E α).hom.val.app U` on `generatorRaw` and equates it to `tensorD f E α U 1 (variableSection A E U e)`. |
| Every v : E-prime → E over B | Second conjunction: arbitrary `E E' α α' v`, with exactly `v ≫ α = α'`. |
| The induced differential map F(v) | The existential `F : term f E' α' ⟶ term f E α` is normalized on every local differential tensor: `F(b ⊗ dp) = b ⊗ d(polynomialMap A v p)` for every section p of the actual polynomial sheaf. This specifies the actual induced differential map, rather than a map without its defining action. Existence and uniqueness are asserted by `∃! F` using this formula ALONE; the square is not part of that uniqueness predicate. |
| F(v) Φ_E-prime = Φ_E B^(v) | `(Φ E' α').hom ≫ F = (SheafFreeModule.free B).map v ≫ (Φ E α).hom`. A separate conjunct universally quantifies F satisfying the pure-tensor formula and asserts this square for it. Lean composition is in diagram order. The already constructed free functor acts by linear extension of `[e'] ↦ [v(e')]`. |
| No surjectivity assumption | No `Presentation`, `IsLocallySurjective`, `Surjective`, epimorphism, or condition on α/evaluation is bound anywhere. The helper `term` accepts arbitrary α. |

Tensor order: the project's canonical change-of-rings construction implements scalar
extension as `B ⊗_P Ω`, with B acting on its first factor. Its symmetric tensor
identification with `Ω ⊗_P B` sends `b ⊗ dp` to `dp ⊗ b`. `tensorD` uses precisely the
existing module-sheafification unit on that pure tensor; it introduces neither a new tensor
product nor an arbitrary comparison. This order convention was explicitly anticipated by
step 1 of the node proof. In particular its `b = 1` is exactly the displayed normalization.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`.
- `def-weil-size-convention` is recorded as a metatheoretic convention, without a
  declaration. Explicit universe u and the small category implement it here.
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`:
  `MvPolynomial`, `MvPolynomial.X`, `MvPolynomial.eval₂Hom`, `MvPolynomial.aeval`,
  `MvPolynomial.algHom_ext`; the existing polynomial helpers use this construction.
- `Mathlib.RingTheory.Kaehler.Basic`:
  `KaehlerDifferential`, `KaehlerDifferential.D`, `linearMapEquivDerivation`;
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf`:
  `relativeDifferentials'`, `derivation'`, `isUniversal'`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, through its public
  tensor imports: `SheafOfModules.changeOfRingsOfUniverses` and
  `changeOfRingsPresheafOfUniverses` from `TensorProductOfUniverses`.
- `Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty`:
  `SheafFreeModule.freeModule_restrict_bijective`, `freeModule_restrict_naturality`,
  with `free` and `generatorRaw` from its public `FreeModuleSheafConstruction` import.
- `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`:
  `SheafPolynomialCotangent.sets`, `polynomials`, `polynomialSheaf`, `base`,
  `evaluationPresheaf`, `evaluation`, `polynomialMapPresheaf`, `polynomialMap`.
  Its surjective-presentation structure and cotangent-comparison theorem are not used.
- `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`:
  `SheafDifferentials.omega` and `derivation`, owned by the already landed definition
  node `def-sfb-sheaf-differentials`; no inverse-image theorem is needed.
- Proof-only imports: `Mathlib.RingTheory.Kaehler.Polynomial`
  (`KaehlerDifferential.mvPolynomialBasis`, `mvPolynomialBasis_apply` and
  `mvPolynomialBasis_repr_apply`); `Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel`
  (`sheafified_differentials_cokernel`); and
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`
  (`exists_sheafificationTensorIso`, `nonempty_sheafTensorSheafificationIso`).
  The module-sheafification interface is the existing
  `PresheafOfModules.sheafification`, `sheafificationCompToSheaf`,
  `sheafificationAdjunction` and `toPresheaf_map_sheafificationAdjunction_unit_app`.
  Ring tensor products use the recorded `TensorProduct`, `lift`, `ext'` and `rTensor`.

The item's stmt_deps gains two already landed DEFINITION nodes, as authorized by
brief-stage2 §5 and the explicit return instruction:
`def-sfb-sheaf-differentials` owns the existing sheaf differential construction;
`def-sfb-sheaf-polynomial-cotangent-presentation` owns the existing polynomial algebra
and evaluation helpers. Its lean-only update in this delivery additionally records the
existing `polynomialMapPresheaf` and `polynomialMap` definitions. The mathematical node
statements, proofs and proof_deps are unchanged; no new node or Lean definition is added.
The theorem node `lem-sfb-sheaf-polynomial-cotangent-comparison` is not in stmt_deps.
The Lean import remains its module because that module contains these actual definitions.

The inherited `lem-trf-free-module-sheaf-universal-property` statement dependency stays
as on the base, as requested in the return. Its theorem supplies the proof's generator
uniqueness, while `free`/`generatorRaw` are owned by the already landed definition node
`def-trf-free-module-sheaf-construction`. No new theorem-only statement dependency is added.

Edge cases checked before stating:

- Initial/empty generator sheaf: sectionwise polynomials with no generators have zero
  relative differentials and the corresponding free module is zero. At objects with an
  empty covering, the initial sheaf may have a forced section; the sheafified construction
  still handles this correctly. No pointwise-empty assumption is made.
- Infinite generator sets: MvPolynomial and sectionwise free modules use finite supports;
  no Fintype/Finite hypothesis or infinite unsupported sum occurs.
- Zero coefficient ring/sheaf and empty category: both constructions and the normalized
  formulas are defined; the statement has no Nontrivial or Nonempty hypothesis.
- Arbitrary characteristic: no characteristic hypothesis or division occurs.
- Non-surjective evaluation (e.g. zero generators with a proper coefficient inclusion):
  the theorem still applies; the constant polynomial algebra has zero relative
  differential module. The comparison module's Presentation is deliberately not used.
- Maps v need not be injective or surjective: polynomial rename and the free-module
  functor merge repeated generators and preserve the displayed formula.
- Identity and arbitrary-lift cases are retained: p quantifies over all local sections
  of the sheafified polynomial ring, not only global or polynomial-presheaf lifts.
- The statement has no let/show binder, file-local notation, private definition, or
  implicit unbound parameter. Every helper uses the existing public constructions.

Searches (the msearch wrapper also saved searches.jsonl in the sandbox):

1. `msearch.py ... leanfinder "Differentials of polynomial algebra sheaves after
   evaluation are the free module sheaf naturally in the generators"`: 8 hits,
   including `instFreeMvPolynomialKaehlerDifferential`, `mvPolynomialBasis_repr_D`,
   `polynomial_D_apply`, `mvPolynomialBasis_apply`, and `toKaehler_tmul_D`.
   These are ring results, without the sheaf comparison or generator naturality.
2. `msearch.py ... loogle "MvPolynomial, KaehlerDifferential"`: 12 hits, including
   `mvPolynomialBasis`, `mvPolynomialEquiv`, `mvPolynomialBasis_apply`, and the pderiv
   coordinate formulas. Read the full Polynomial.lean basis signatures/docstrings.
3. `msearch.py ... leansearch "Sheaf differentials of a polynomial algebra after
   evaluation are the free module sheaf on its generators"`: 8 hits, including
   ring polynomial differentials and `SheafOfModules.free`/`ιFree`. The latter free
   object is indexed by a fixed type, whereas this item has an arbitrary sheaf E;
   use the recorded SheafFreeModule interface instead.
4. `msearch.py ... grep "mvPolynomialEquiv|mvPolynomialBasis|relativeDifferentials"
   Algebra/Category/ModuleCat`: 5 hits in Differentials/Presheaf.lean for the
   presheaf construction. No exact sheaf theorem.
5. Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for polynomial/sheaf/
   differential combinations and `MvPolynomial`: discovered the already landed
   `SheafPolynomialCotangentComparison` constructions, which this module reuses.
   The full signatures and docstrings of those helpers were read.
6. `rg` for `lem-sfb-sheaf-polynomial-differentials-free` under WeilConjectures and
   in `dag/lean_names_upstream.json`: no declaration binding. `rg` for the proposed
   namespace and main declaration over Mathlib, WeilConjectures and Sheaf: no collision.

Validation: prescribed server `scompile.py` is rerun on the repaired module, followed
by `deliver2.py --no-push` and the delivery wrapper. Stage 2 only: the main theorem
intentionally retains sorry. No STATEMENT-DISPUTED issue or mathematical node statement
correction is required.

## Second reading by Q141

I reread the delivered node and Lean module in a separate clause-by-clause pass.
No second agent was started, in accordance with the dispatcher's instruction; the
maintainer's independent review remains the separate human-process check.

The site uses the recorded covering predicate, f has exactly domain A and codomain B,
and α is entirely arbitrary. `term` never requires the existing surjective Presentation.
`variableSection` uses the ring-sheafification unit rather than treating presheaf sections
as all sheaf sections. The free module and universal differential module are the existing
ones. `tensorD` uses their actual scalar-extension sheafification unit. Its tensor order
is accounted for by symmetry. The Φ formula has scalar 1, and the F formula retains
arbitrary scalar b and arbitrary local p, which fixes the induced differential map.
The direction E-prime to E agrees with the direction of both F and free.map v, and the
composition equality is correctly reversed only in notation, since Lean writes diagram
order. Both α and α-prime occur in the hypothesis v ≫ α = α-prime.

Repair reading: the live polynomial-presentation definition node was opened in full,
including its existing:true record; `polynomialMapPresheaf` and `polynomialMap` were
reread in the recorded module. Their values are respectively sectionwise rename with
fixed coefficients and its ring sheafification. Both are now explicitly owned by that
definition node. Only its lean record changes; its statement, sources, dependencies,
proofs, review fields, and all other metadata remain byte-for-byte equivalent as JSON.
The current main item was compared to the retained returned node: outside lean and
stmt_deps all fields agree. The corrected item is regenerated from that current main node.

The repaired F statement is `(∃! F, formula F) ∧ (∀ F, formula F → square F)`. This
asserts existence and uniqueness based solely on the canonical pure-tensor action,
then gives the square for that canonical map. In particular, uniqueness does not require
an already known square, and no classical choice or uncharacterized arrow was introduced.
The formula still quantifies over all U, b and p; the over-B condition and square direction
are unchanged. All previously checked edge cases remain included. No mathematical
clause was dropped, no surjectivity condition was added, and no statement correction
was required.


## Dependency modules

`def-sfb-sheaf-polynomial-cotangent-presentation`: lean-only ownership repair expressly
requested by L on returned immutable head `2091695a211d`. The existing record correctly
owns the polynomial algebra and evaluation, but omitted the existing definition helpers
`CategoryTheory.SheafPolynomialCotangent.polynomialMapPresheaf` and
`CategoryTheory.SheafPolynomialCotangent.polynomialMap`. Append these to
lean.declarations, preserving all previous declarations and the main canonical signature;
lean.note explains the omission, their sectionwise rename/sheafification construction,
and the reuse. No source module is delivered for this existing:true dependency, and no
existing declaration is moved, copied or altered. This is an ownership metadata repair,
not a change to the dependency's mathematical statement.

## Returned delivery repairs

Returned head: `2091695a211d` (delivery `2091695a211`). The maintainer's mathematical
clause-by-clause assessment was positive; this repair addresses both requested changes.

1. H2 definition ownership: replace the newly added theorem-node stmt_dep
   `lem-sfb-sheaf-polynomial-cotangent-comparison` with live definition node
   `def-sfb-sheaf-polynomial-cotangent-presentation`. Give the two polynomial renaming
   helpers the requested definition owner by extending only that node's lean record,
   with an explanatory lean.note and no Lean copies. The base free-module theorem
   dependency is retained and its actual definition owner is noted above.
2. Separate canonical-map uniqueness and naturality: the former
   `∃! F, formula F ∧ square F` is now
   `(∃! F, formula F) ∧ (∀ F, formula F → square F)`, with full binders and formulas
   written out. Thus the formula alone identifies the induced F; the square is a
   separate consequence for it. lean.statement is updated verbatim from the file.

The retained sandbox work was compared against the current main item before applying
these changes. Only lean/stmt_deps differ for the item, and only lean differs for the
polynomial-presentation dependency. Delivery wrappers perform the required current-base
refresh/rebase and immutable-head preflight; no shared source is edited directly.

## Worker report

The module `Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas` states
`CategoryTheory.exists_reflector_restricted_adjunction`, with its sole proof
`sorry`. It uses the existing full-subcategory lift rather than introducing a
second definition of a restriction or reflector. No new nodes, dependency
repairs, or statement corrections are needed.

I read the item's entire statement and seven proof steps, all four statement
dependencies and their Mathlib matches, and the full signatures and docstrings
of the matched Mathlib declarations. I checked Stacks algebraization.tex,
`lemma-pushforward-derived-complete-adjoint` (Tag 099K), especially its final
Hom chain, and the natural-bijection constructor and unit/counit conventions
in Mathlib's Adjunction.Basic (Tag 0037). The abstract scalar and normalization
refinement is expressly agent supplied in the node.

Hypotheses and the corresponding Lean:

- The commutative scalar ring is `(A : Type w) [CommRing A]`.
- The two categories are `C : Type u₁` with `[Category.{v₁} C]` and `E : Type u₂`
  with `[Category.{v₂} E]`. The five universes are explicitly declared and
  independent. Each has `Preadditive`, `HasFiniteBiproducts`, and `Linear A`,
  exactly the additive and A-linear structures of the dependency nodes.
- The full subcategories are `Ac : ObjectProperty C`, `Bc : ObjectProperty E`,
  with their canonical `FullSubcategory` categories. Each has
  `HasFiniteBiproducts`; the preadditive and linear structures are inherited
  on the ambient morphisms. Thus they are full additive subcategories with
  the ambient Hom modules, rather than independently chosen Hom structures.
- `CA : C ⥤ C`, `CB : E ⥤ E`, and their `Additive` and `Linear A` instances
  are exactly the two specified additive linear completion endofunctors.
  `hCA` and `hCB` assert that every output belongs to its full subcategory.
- `κA : 𝟭 C ⟶ CA` and `κB : 𝟭 E ⟶ CB` are natural transformations, so their
  naturality is included in the data, not silently assumed afterwards.
- `hκA`, `hκB` quantify over every ambient X and Y belonging to its indicated
  subcategory, asserting bijectivity of `fun f => κ.app X ≫ f`. This is exactly
  precomposition by the unit, including inputs X outside the subcategory.
- `hlocalA`, `hlocalB` are the two pointwise equivalences between membership
  in the subcategory and `IsIso (κ.app X)`, with both directions present.
- `L : C ⥤ E` and `R : E ⥤ C` each have the stated additive and A-linear
  instances; `adj : L ⊣ R` is the specified ordinary adjunction, with its own
  unit `adj.unit` and counit `adj.counit`.
- `hR : ∀ Y : E, Bc Y → Ac (R.obj Y)` is precisely preservation of complete
  objects by R. No preservation of complete objects by L is imposed.

Conclusions, clause by clause:

- In every conclusion, P is literally
  `Ac.ι ⋙ Bc.lift (L ⋙ CB) (fun X => hCB (L.obj X))`.
  The existing `ObjectProperty.lift` maps X to `CB.obj (L.obj X)` and maps a
  to `CB.map (L.map a.hom)`, wrapped as a full-subcategory arrow. This is
  the node's completed left restriction with its prescribed morphism map.
- D is literally
  `Ac.lift (Bc.ι ⋙ R) (fun Y => hR Y.obj Y.property)`, mapping N to R N
  and each arrow to its actual R-image. This is the stated right restriction.
- The first four conjuncts assert `P.Additive`, `Functor.Linear A P`,
  `D.Additive`, `Functor.Linear A D`, respectively.
- The existential gives `adjc : P ⊣ D`. Its first conjunct provides, for
  every M and N, a linear equivalence e on the two subcategory Hom modules
  with `∀ t, e t = adjc.homEquiv M N t`. Thus the adjunction Hom bijection
  itself is A-linear; an unrelated linear equivalence would not suffice.
- The next conjunct is the required normalization for EVERY t:
  `(adjc.homEquiv M N t).hom =
   adj.homEquiv M.obj N.obj (κB.app (L.obj M.obj) ≫ t.hom)`.
  Fullness is the ambient `.hom` projection. The right hand side first
  precomposes with κ and then takes the ordinary adjunct, exactly the
  displayed Hom chain and the final general-adjunct agreement in the node.
- The unit conjunct is the equality of ambient arrows
  `(adjc.unit.app M).hom = adj.unit.app M.obj ≫ R.map (κB.app (L.obj M.obj))`.
  Lean's diagrammatic composition reverses the node's right-to-left notation.
- The counit conjunct is the equality of ambient arrows
  `κB.app (L.obj (R.obj N.obj)) ≫ (adjc.counit.app N).hom = adj.counit.app N.obj`.
  In particular κ is evaluated at L R N, and no inverse of this κ occurs.
- The unit and counit are natural because `Adjunction.unit` and `.counit`
  are natural transformations. Both triangle identities are fields of
  `Adjunction`: `left_triangle_components`, `right_triangle_components`.
  The associated `homEquiv` is natural in both variables by the adjunction
  API. These conclusions are carried by `adjc`, not omitted or replaced by
  a bare existence of an arbitrary bijection. The normalization fixes its
  Hom bijection pointwise. The linear equivalences equal it pointwise and
  therefore share its naturality.

Dependency declarations used:

- `def-weil-additive-category`: `CategoryTheory.Preadditive` in
  `Mathlib.CategoryTheory.Preadditive.Basic` and
  `CategoryTheory.Limits.HasFiniteBiproducts` in
  `Mathlib.CategoryTheory.Limits.Shapes.Biproducts`. The latter is imported
  publicly; empty finite biproducts include the zero object.
- `def-weil-linear-category`: `CategoryTheory.Linear` in
  `Mathlib.CategoryTheory.Linear.Basic`, publicly available through
  `Mathlib.CategoryTheory.Linear.LinearFunctor`.
- `def-weil-linear-functor`: `CategoryTheory.Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` and
  `CategoryTheory.Functor.Linear` in `Mathlib.CategoryTheory.Linear.LinearFunctor`.
- `lem-weil-pbc-adjunction-of-natural-bijection`:
  `CategoryTheory.Adjunction.mkOfHomEquiv`, `Adjunction.CoreHomEquiv`,
  `Adjunction.homEquiv_unit`, and `Adjunction.homEquiv_counit` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. This proof dependency's module
  is already a public statement import because the type uses Adjunction.
- Existing `CategoryTheory.ObjectProperty.lift`, `.ι`, and `.FullSubcategory`
  in `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory` are available
  through the linear-functor imports and supply the actual restrictions.

Edge cases checked mathematically before writing:

- Identity completions and the whole subcategories give the original adjunction
  with κ equal to the identity; both normalization formulas reduce correctly.
- L need not preserve the subcategory. Even when κ on L M is noninvertible,
  the Hom map is bijective because its TARGET N is complete. The statement
  neither uses an inverse of κ on L M nor assumes it is invertible.
- A zero complete subcategory is allowed whenever the given reflection and
  preservation hypotheses hold. Full-subcategory zero morphisms retain their
  ambient meanings; the formulas become the unique maps when appropriate.
- The zero scalar ring is allowed: the hypotheses force the Hom modules to
  be trivial, and there is no nonzero-ring assumption.
- An additive subcategory cannot be empty because its empty biproduct is a
  zero object; no artificial `Nonempty` assumption is introduced.
- Object, morphism, and ring universes are not identified. There is no
  smallness, finite-dimensionality, or existence-of-limits hypothesis.

Searches made (2026-10-21):

- `msearch.py ... leanfinder`: "Restrict an adjunction through a reflector,
  linear Hom bijection, unit and counit formulas" returned eight hits,
  including `reflectorAdjunction`, `unitCompPartialBijectiveAux`,
  `Adjunction.restrictFullyFaithful`, and its Hom/unit/counit formulas.
- `msearch.py ... leansearch`: "An adjunction restricts to reflective full
  subcategories with left adjoint reflector composed with left adjoint and
  right adjoint preserving local objects" returned eight hits in the same
  reflective/restriction APIs, with no exact linear normalized theorem.
- `msearch.py ... loogle`:
  "CategoryTheory.Adjunction.mkOfHomEquiv, CategoryTheory.ObjectProperty.lift"
  returned zero hits.
- `msearch.py ... grep`:
  `restrictFullyFaithful|reflectorAdjunction|homLinearEquiv` in
  `CategoryTheory/Adjunction` returned ten restriction/reflection hits.
  I opened `Adjunction.Restrict`: its construction requires an isomorphism
  between the ambient left adjoint and the proposed restriction after
  inclusion. Here κ on L M need not be invertible, so it is not this statement.
- Direct `rg` in Mathlib CategoryTheory for linear hom equivalences found the
  induced-category linear equivalence but no theorem giving this node's
  completed adjunction and both normalizations.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for reflector/adjunction
  and completed-adjunct patterns found the derived-completion special case
  `reflectorOfDistinguishedAdjunction` and the site-specific
  `Site.reflectorAdjunction` in `CompletionMateComparison`; I opened both.
  Neither is the abstract two-category linear restriction theorem here.
- `grep -rn 'lem-sbc-reflector-adjunction-unit-formulas' lean/WeilConjectures`
  returned no match. The exact proposed declaration name was also searched
  in Mathlib, both project source trees, and `dag/lean_names_upstream.json`;
  no declaration collision was found.

No mathematical node fault or `STATEMENT-DISPUTED` issue was found. The only
postponed proof is the theorem named above, matched to this node; its docstring
contains all seven natural-language proof steps and their node dependencies.
`set_option autoImplicit false` rules out accidentally auto-bound variables.

Validation: the initial prescribed scompile.py invocation failed before Lean
could elaborate this file: the live server lacks
`Mathlib/CategoryTheory/Adjunction/Basic.olean`. Its automatic confirmation
against current sources reports "Live published library is unavailable".
This is a published-build/tool failure, not a missing source declaration.
Further prescribed compile and delivery checks will be attempted after the
packet is complete; no successful compilation is claimed here.

The second scompile.py invocation on the completed packet and the prescribed
`deliver2.py Q31 lem-sbc-reflector-adjunction-unit-formulas --no-push` both
confirmed the same missing Mathlib Adjunction.Basic object file and
"Live published library is unavailable". The dry run ended with
"COMPILE FAILED on the server, nothing pushed" before preflight. This dependency
exists in the source and is indispensable to the statement; replacing its source
interface cannot restore the absent published Mathlib build. The launcher tools
and published library are not editable by this worker. The sandbox retains the
module, lean-only node record, and report for a retry after infrastructure repair.


## Second reading by Q31

On this retry I opened the current node statement and the retained module. The
commutative ring, ambient additive linear categories, full additive subcategories,
completion endofunctors, natural units, universal bijections, exact local-object
conditions, specified linear adjunction, and preservation hypothesis are rendered
by the binders listed individually in the worker report above. The four functor
structure conjuncts, pointwise linear Hom equivalence, normalized adjunct equality,
and two ambient unit/counit equalities render the conclusions; naturality and
both triangle identities are included in the existential Adjunction structure.
The formulas still use the reflection unit at LM and LRN without assuming either
component invertible. All universes are explicit and autoImplicit is false.
The JSON signature matches the source verbatim and no source line exceeds 100
characters. I refreshed the copied node's non-worker fields from the current
read-only source: its lean_audit had changed to an empty record since the saved
attempt, and now only lean differs. No Lean statement changed.

The required first retry command, deliver2.py with --no-push, again failed before
elaboration because Mathlib/CategoryTheory/Adjunction/Basic.olean is absent.
A subsequent direct scompile.py retry independently returned the identical error;
both automatic server confirmations said "Live published library is unavailable".
This is not a busy-server timeout or a statement diagnostic. The existing public
Mathlib Adjunction import is necessary for the specified adjunction, so no source
repair addresses this missing published build. No delivery was pushed and no
successful compilation or preflight is claimed. The saved packet is retained.


## Successful validation on retry (2026-10-21 UTC)

The required initial `deliver2.py Q31
lem-sbc-reflector-adjunction-unit-formulas --no-push` now succeeds:
`OK (dry run): commit df23422ca01 passes the preflight and compiles; nothing pushed`.
This supersedes the historical missing-build diagnostics above. The saved Lean
module is retained unchanged. The current node and saved node differ only in
`lean`; its recorded signature matches the source verbatim, all source lines
meet the 100-character limit, and every variable and universe is explicitly bound.

I rechecked the four dependency records against their Mathlib interfaces, the
full-subcategory lifts, and the source's final Hom chain. The binders and clauses
match the current node as described in the second reading above: both reflectors
and universal properties, the exact invertibility characterizations, the given
linear adjunction and right-adjoint preservation, the specified lifted P and D,
their additive and linear structures, the normalized linear Hom equivalence,
and the ambient unit and counit equalities. Naturality and the triangle identities
are supplied by the same existential adjunction. There is no new mismatch or
statement change. The historical tooling failure has cleared.

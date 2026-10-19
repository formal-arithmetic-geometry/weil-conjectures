## Worker report

The module `Sheaf.AlgebraicTopology.ModelStructureDeterminedByFibrantObjects` states
`HomotopicalAlgebra.modelStructure_determined_by_cofibrations_fibrantObjects`.
Its only theorem has proof `sorry`; it introduces no definitions, auxiliary
axioms, new nodes, dependency repairs, or statement corrections. The item copy
changes only `lean`, preserving NI's current reviewed proof split.

### Hypothesis and clause correspondence

- The category M is `{M : Type u} [Category.{v} M]`. Object and morphism universes
  are independent. `[m₁ : ModelCategory M] (m₂ : ModelCategory M)` are the two
  model structures on this exact same category. Mathlib's `ModelCategory`
  contains its three morphism classes, two-out-of-three, retract closure, finite
  limits and colimits, the lifting axioms, and both factorizations. Its two
  `IsWeakFactorizationSystem` instances were read in `ModelCategory.Basic`.
- The imported model-category conventions additionally require completeness,
  cocompleteness, and functoriality. These are `[HasLimits M] [HasColimits M]`
  and the four `HasFunctorialFactorization` binders: two for each structure.
  The second structure's classes are always explicitly selected from m₂.
  These are inherited conventions, not extra mathematical hypotheses.
- Equality C₁=C₂ is `hC : cofibrations M =
  m₂.categoryWithCofibrations.cofibrations`.
- Equality of fibrant-object predicates is `hf : ∀ X : M, IsFibrant X ↔
  m₂.categoryWithFibrations.fibrations (terminal.from X)`.
  Mathlib's `IsFibrant X` abbreviates `Fibration (terminal.from X)`, and
  `Fibration` is precisely membership in the fibration morphism property.
  Both sides use the same terminal map. The fact that terminal existence can
  also be inferred from either model structure does not select a different
  object: `HasTerminal` is Prop-valued and its proofs are irrelevant.
- W₁=W₂ is the first conjunct, equality of `weakEquivalences M` and m₂'s
  `categoryWithWeakEquivalences.weakEquivalences`.
- F₁=F₂ is the second conjunct, equality of `fibrations M` and m₂'s
  `categoryWithFibrations.fibrations`.
- Equality of trivial cofibrations is the third conjunct, using exactly
  Mathlib's `trivialCofibrations`, with both instance arguments of m₂ explicit.
- Equality of trivial fibrations is the fourth conjunct, using exactly
  Mathlib's `trivialFibrations`, with both instance arguments of m₂ explicit.
  These definitions were read: they are C ∩ W and F ∩ W, respectively.
- The remaining conjunct quantifies over any fixed other model category N,
  with its own independent universes u',v' and the same complete, cocomplete,
  functorial model conventions. It includes every adjunction L ⊣ R both for
  `L : M ⥤ N` and for `L : N ⥤ M`. In particular, neither orientation is lost.
- In each orientation, the first biconditional is the Quillen-adjunction
  assertion. `P ≤ Q.inverseImage L` means that L sends every P-map to a
  Q-map. The two conjuncts assert preservation of cofibrations and trivial
  cofibrations. These are the source's left Quillen conditions; since adj is
  supplied, cocontinuity is automatic. No additional preservation hypothesis
  is imposed by this biconditional.
- In each orientation, the subsequent implication says that, when the first
  structure gives a Quillen adjunction, the two equivalence criteria agree.
  The preceding biconditional makes it a Quillen adjunction for the second
  structure too. Each criterion says: for every cofibrant A, every fibrant B,
  and every `f : L.obj A ⟶ B`, f is a target weak equivalence iff
  `adj.homEquiv A B f` is a source weak equivalence. For the second structure,
  cofibrancy is written as its cofibration property on `initial.to A`, and
  fibrancy as its fibration property on `terminal.from B`. These are exactly
  the existing Mathlib abbreviations, unfolded inline, with no new notion.
  The Quillen-adjunction biconditional plus this conditional biconditional
  is logically precisely the biconditional between the two conjunctions
  "Quillen adjunction and equivalence criterion". If neither is Quillen,
  neither is a Quillen equivalence, so no case is omitted.

### Dependencies and source

The sole statement dependency is `lem-coef-simplicial-boundary-collapse-test`.
I read its full node and the signature/docstring of the recorded
`CategoryTheory.simplicial_boundary_collapse_test`, module
`Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`, which is publicly
imported. Only the model conventions introduced by that node are used here;
this item does not invoke its simplicial realization test as a new hypothesis.
The other public import is Mathlib's
`Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant`, giving `IsCofibrant` and
`IsFibrant`. The two-structure data and all morphism classes are Mathlib's,
not copies. `Adjunction.homEquiv` is the ordinary adjunction bijection.

The recorded proof dependency `lem-coef-fixed-cylinder-fibrant-target-detection`
has no Lean record and remains unsplit in the current DAG. It is used only in
the natural-language proof, not in this theorem's statement; accordingly there
is no module to import for it. It is not a statement prerequisite and no
replacement interface or auxiliary theorem is invented. The theorem docstring
contains all six current proof steps, explicitly naming this detector in step 4.

I opened the cited Joyal PDF online at
https://mat.uab.cat/~kock/crm/hocat/advanced-course/Quadern45-2.pdf,
Appendix E, Proposition E.1.10 (printed p. 431; PDF page 284, zero-based), and
Definitions E.2.1/E.2.3 (printed pp. 433–434). E.1.10 states exactly the
cofibration/fibrant-object determination used here. Its additional one-sided
inclusion statement is not part of this node and has not been added.
I also read the definition after Proposition E.2.10 (printed p. 437): Joyal
calls a Quillen pair an equivalence when its derived adjunction is an
equivalence. The cofibrant-fibrant adjunct criterion is the form explicitly
spelled out in step 6 of this node's proof. Its equivalence to Joyal's derived
form follows by E.1.8 (maps on cofibrant-fibrant inputs represent localized
maps), E.1.4 (saturation), and E.2.10 (the derived adjunction and unit/counit).
Thus the inline criterion expresses the same property rather than assuming
that the PDF prints that criterion as its definition.

Node metadata fault: `source.place` still says E.2.14, whereas its reviewed
proof and the actual PDF identify E.1.10. The module docstring uses E.1.10.
This is a citation-number fault only; the mathematical statement is unchanged.
No STATEMENT-DISPUTED flag is warranted.

WANTED: Joyal, The theory of quasi-categories and its applications (2008),
Appendix E, pp. 431 and 433–438, is not archived locally according to the node;
it was read online at the URL above. No literature or coordination file was edited.

### Edge cases

The single-object category and coincident structures m₁=m₂ are covered; all
conclusions specialize to reflexive equalities and identical criteria.
An empty category cannot satisfy `ModelCategory` because it lacks a terminal
object, exactly as for the node's complete-category hypothesis. No nonempty
or nonzero object is required. The terminal object is always fibrant and the
initial object always cofibrant, so the tests include these cases. Arbitrary
maps, including identities and maps with non-cofibrant/non-fibrant endpoints,
are covered by equality of morphism properties. Neither simplicial enrichment,
properness, local presentability nor a cofibrant/fibrant restriction on every
object is assumed. N is allowed to have different object and morphism
universes from M, and either side of the adjunction can be M. The same-fibrant
condition is not automatic: Kan and Joyal structures on simplicial sets have
the same cofibrations but different fibrant objects. Equality of fibrant
objects alone is likewise insufficient, so hC is retained separately.

### Searches

- `msearch.py ... leanfinder "A model structure is determined by its
  cofibrations and fibrant objects"`: 8 hits, including `ModelCategory`, its
  three data projections, `ModelCategory.mk'`, `bifibrantObjects`,
  `fibrantObjects`, and `BifibrantObject`; none states this comparison theorem.
- `msearch.py ... loogle '"HomotopicalAlgebra.ModelCategory"'`: 12 hits,
  `ModelCategory`, its projections and axiom projections; no extensionality
  theorem or comparison by fibrant objects.
- `msearch.py ... grep 'Quillen|fibrant.*cofibration|cofibration.*fibrant'
  AlgebraicTopology/ModelCategory`: 25 hits, references and homotopy lemmas,
  not equality of two model structures. The candidate `Basic.lean` and
  `IsCofibrant.lean` definitions were read in full at the relevant declarations.
- `rg` over Mathlib's `AlgebraicTopology/ModelCategory` for the ModelCategory
  definition and structure-comparison names found Basic/Transport, not this
  theorem; `ModelCategory.transport` assumes all three class identities and
  transports along an equivalence, so it is not a match.
- `rg` over upstream `WeilConjectures` for ModelCategory and comparison names,
  and `grep -rn` for the exact item id: no matching statement.
- `rg` over `lean/Sheaf` for `model_structure_determined`,
  `determined_by_fibrant`, `same.*fibrant`, and ModelCategory: model structures,
  theorems using them, and references to this node in straightening proofs,
  but no declaration of the comparison. In particular,
  `UnmarkedStraighteningQuillen` only cites this result in its proof plan.
- Generic Quillen definitions were also sought in Mathlib, upstream and
  `lean/Sheaf`. The project's specialized `FrameLeftQuillenClause`,
  `SimplicialQuillenEquivalence` and `QuillenClause` concern additional
  frame/simplicial/localization data. They do not define this arbitrary
  adjunction's exact property. The elementary preservation and adjunct
  criteria are therefore written inline, without introducing a competing
  Quillen definition.

### Validation

`scompile.py Q108 lem-coef-model-structure-determined-by-fibrant-objects
<module>` compiled both its sandbox form (1.2 s) and library module form
(1.4 s), with no error or warning. Every variable and universe is explicitly
bound and `autoImplicit` is disabled. The only proof is `sorry`. The declaration
signature is recorded verbatim, stopping before `:=`, in `lean.statement`.

Process note: the initial investigation mistakenly used read-only Git inspection
in the shared clone and two direct type-check probes instead of `scompile.py`.
No project source was edited by those commands. I stopped that workflow;
all delivery files are in this sandbox and all delivered-module compilation
uses the prescribed `scompile.py` and `deliver2.py` wrappers.

The first dry run recompiled cleanly and reached preflight. Preflight found
that the recorded signature mistakenly included its terminating `:=` token;
I removed that token from `lean.statement` to match the required preflight
signature extraction. The Lean module was unchanged. Its only other finding
was the second-reading section, which is reserved for the independent reader.

## Second reading by Q108

I independently read the sandbox node and module, the base node, the statement
and recorded declaration of `lem-coef-simplicial-boundary-collapse-test`, and
Mathlib's `ModelCategory`, its two weak-factorization-system instances,
`IsCofibrant`, `IsFibrant`, `trivialCofibrations`, `trivialFibrations`,
`HasFunctorialFactorization`, and `MorphismProperty.inverseImage`.
There is no repair note for this item. The sandbox node differs from the base
only in `lean`; there is no statement correction, new node, or dependency module.

My object/hypothesis/conclusion list, with its Lean rendering and verdict:

1. One category M, carrying two model structures: `{M : Type u}`,
   `[Category.{v} M]`, `[m₁ : ModelCategory M]`, `(m₂ : ModelCategory M)`.
   Correct: both structures use exactly the same category instance, with
   independent object and morphism universes. An ordinary explicit argument
   `m₂` does not become the instance used by the first structure's predicates.
2. Model conventions inherited from the boundary-collapse node: two-out-of-three,
   retract closure, two weak factorization systems, completeness, cocompleteness,
   and functorial factorizations. `ModelCategory` supplies the first three and
   finite limits/colimits; `[HasLimits M] [HasColimits M]` and the four
   `HasFunctorialFactorization` instances supply precisely the remaining
   conventions, for each structure separately. Correct. `HasLimits` uses the
   hom universe v, as read in Mathlib's `Limits/HasLimits.lean`; it does not
   impose u=v. The dependency's simplex functor and boundary/collapse hypotheses
   are not part of the inherited model conventions and are correctly absent.
3. Same cofibrations C₁=C₂: `hC : cofibrations M =
   m₂.categoryWithCofibrations.cofibrations`. Correct equality of morphism
   properties on all arrows, not just cofibrant objects.
4. Same fibrant objects: `hf : ∀ X : M, IsFibrant X ↔
   m₂.categoryWithFibrations.fibrations (terminal.from X)`. Correct:
   `IsFibrant X` is `Fibration (terminal.from X)` and `Fibration` is membership
   in the first fibration class. The common terminal map is legitimate because
   `HasTerminal` is Prop-valued; changing its existence proof does not change
   the chosen limit. This is not equality of fibration classes as a hypothesis.
5. W₁=W₂: first conclusion conjunct, `weakEquivalences M =
   m₂.categoryWithWeakEquivalences.weakEquivalences`. Correct, on all arrows.
6. F₁=F₂: second conjunct, `fibrations M =
   m₂.categoryWithFibrations.fibrations`. Correct, on all arrows.
7. Same trivial cofibrations: third conjunct uses `trivialCofibrations M` and
   `@trivialCofibrations M _ m₂.categoryWithCofibrations
   m₂.categoryWithWeakEquivalences`. Correct: Mathlib defines this as C ∩ W.
8. Same trivial fibrations: fourth conjunct uses `trivialFibrations M` and
   `@trivialFibrations M _ m₂.categoryWithFibrations
   m₂.categoryWithWeakEquivalences`. Correct: Mathlib defines this as F ∩ W.
9. Any fixed other model category: the final conjunct quantifies over
   `{N : Type u'} [Category.{v'} N] [ModelCategory N]` and exactly the same
   complete/cocomplete/functorial model conventions. Correct; u',v' are not
   constrained by u,v. It then quantifies over L, R and an actual adjunction
   `adj : L ⊣ R` in both directions M→N and N→M. No orientation is omitted.
10. Quillen adjunction iff for either structure: in each orientation, the
    biconditional compares preservation of cofibrations and trivial
    cofibrations by L. `P ≤ Q.inverseImage L` is exactly
    `∀ f, P f → Q (L.map f)`. Correct: a left adjoint is cocontinuous, so no
    separate colimit-preservation premise is missing. Every m₂ class in the
    second half is explicitly selected, including its trivial class.
11. Quillen equivalence iff for either structure: in each orientation the
    implication assumes the first preservation condition, then compares the
    criteria `∀ A B, cofibrant A → fibrant B → ∀ f : L.obj A ⟶ B,
    weakEquivalence f ↔ weakEquivalence (adj.homEquiv A B f)`.
    Correct: the preceding Quillen-adjunction biconditional transfers its
    premise, so this conditional equivalence is equivalent to invariance of
    the full Quillen-equivalence property. When neither adjunction is Quillen,
    neither is a Quillen equivalence. The second criterion uses m₂ cofibrancy
    for M→N, m₂ fibrancy for N→M, and m₂ weak equivalences in the proper category.

Source verification: I opened [Joyal's PDF](https://mat.uab.cat/~kock/crm/hocat/advanced-course/Quadern45-2.pdf),
Appendix E, Definition E.1.2 (printed p. 427), Proposition E.1.10 and its proof
(p. 431), Definitions E.2.1/E.2.3 (pp. 433–434), and Proposition E.2.10 with the
following definition (p. 437). E.1.10 is the determination result; E.2.14 is
instead a criterion for a Quillen pair. Thus the worker's citation-number
observation is confirmed. The node's maintainer-owned `source.place` remains
untouched, and the Lean docstrings already cite E.1.10 correctly. Joyal's
finitely bicomplete convention is weaker than this node's expressly imported
complete/functorial convention; those binders do not silently strengthen the
node. The derived-adjunction equivalence definition agrees with the node's
cofibrant-fibrant adjunct criterion: the derived hom bijection is represented
by this adjunction bijection, and saturation detects its isomorphisms. This is
an equivalence of formulations, not a different equivalence notion.

Edge cases: M=N and m₁=m₂ are included; the singleton and zero categories are
included. An empty category is excluded by existence of a terminal object,
just as by the node's completeness assumption. Initial/cofibrant and
terminal/fibrant tests include the initial and terminal objects themselves.
All equalities cover identities and arbitrary arrows without imposing
cofibrancy or fibrancy on their endpoints. There are no index sets, schemes,
rings, characteristics, or natural-number parameters in this statement, so
the corresponding edge cases introduce no hidden exclusions. There is no
simplicial, properness, combinatorial, nonzero, or nonempty-object assumption.
All four universe variables are declared explicitly and remain independent.

Independent searches (with queries different from the worker's first search):

- LeanFinder through `msearch.py`: “Two model category structures are equal
  when they have identical cofibrations and fibrant objects”; eight hits,
  including Brown-factorization injectivity, `ModelCategory`, `mk'`, the three
  class projections and the bifibrant-object membership theorem. None gives
  determination from these two data.
- Loogle through `msearch.py`: `"HomotopicalAlgebra.ModelCategory"`; twelve
  hits, the structure and its projections/axioms, no comparison theorem.
- LeanSearch through `msearch.py`: “uniqueness of a model category structure
  from its cofibrations and fibrant objects”; eight hits, including generated
  `noConfusion` recursors. Their signatures require equality already; the
  generated prose descriptions do not turn them into uniqueness theorems.
- `rg` on all Mathlib, upstream `WeilConjectures`, `lean/Sheaf` and upstream
  declaration names for `same cofibrations`, `same fibrant`,
  `ext_of_cofibrations`, `modelCategory.ext`, `determined.*fibrant`, and
  `modelStructure_determined`: no exact comparison declaration. The
  straightening module only cites this node in its proof docstring; interval
  and Bousfield-descent statements compare particular structures.
- I also searched declaration headers for Quillen notions. The project's
  `SimplicialQuillenEquivalence` is specific to enriched simplicial categories,
  and `quillenAdjunctionInfinityLocalization` states an infinity-localization
  result. Neither is the ordinary arbitrary-model-category predicate here;
  writing its preservation and adjunct conditions inline duplicates no
  definition.

The module has no definitions, hollow data, extra axioms, proved helpers,
file-local notation, or private instances. Its only theorem ends in `sorry`.
I checked the six docstring proof steps against the six node steps, including
the common trivial-fibration replacement, fixed cylinders and endpoint lift,
the named fibrant-target detector, recovery of F, and the Quillen corollaries.
The detector has no recorded Lean declaration at this reading, so there is
no proof-dependency module to import. The sole statement-dependency module
is imported publicly. Every line is at most 100 characters, `autoImplicit`
is disabled, and the node's `lean.statement` equals the full file signature
verbatim, stopping before `:=`.

No mathematical or Lean mismatch was found; no source code or node field was
rewritten. The second reading adds this independent report and confirms the
existing citation-number notice for the maintainer.

Second-reader validation: the prescribed `scompile.py` compiled the delivered
module in sandbox form (1.6 s) and library form (1.5 s), with no errors or
warnings. `deliver2.py Q108 lem-coef-model-structure-determined-by-fibrant-objects
--no-push` then printed `OK (dry run)`: preflight and compilation passed.

## Maintainer review fix (2026-10-17)

The delivered signature was degenerate. In Lean 4 every local variable of class
type is a local instance, so the explicit binder `(m₂ : ModelCategory M)`
became the most recent instance and every unqualified class on `M` (`cofibrations M`,
`IsFibrant X`, `weakEquivalences M`, `fibrations M`, `trivialCofibrations M`,
`trivialFibrations M`, `IsCofibrant A`, and the first two
`HasFunctorialFactorization` binders) elaborated to **m₂**, never to m₁
(confirmed with `pp.explicit`). `hC` was therefore `m₂.cof = m₂.cof`, provable by
`rfl`; every conclusion compared m₂ with itself; m₁ was unused, and its
functorial-factorization convention was missing. The claims in both sections above
that `m₂` "does not become the instance used by the first structure's predicates" were
wrong.

Fix: `(m₁ m₂ : ModelCategory M)` are both explicit. Every class on `M` is named
through `m₁.categoryWithCofibrations.cofibrations`, `m₁.categoryWithFibrations.fibrations`,
`m₁.categoryWithWeakEquivalences.weakEquivalences` (resp. m₂), and
`@trivialCofibrations M _ m_i.… m_i.…` / `@trivialFibrations M _ m_i.… m_i.…`.
Fibrancy and cofibrancy on `M` are their unfolded Mathlib forms on `terminal.from` and
`initial.to`. Classes on `N` keep their single instance. The clause structure and
mathematics are unchanged. The fixed file compiles cleanly through nt_compile.py.
A probe confirms that `m₁.cof = m₂.cof := rfl` now fails, and `pp.explicit` shows
m₁ and m₂ in the intended positions.

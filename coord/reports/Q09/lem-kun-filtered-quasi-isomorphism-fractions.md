## Worker report

This delivery states `CochainComplex.finiteFilteredModuleQuasiIso_fractions` in
`Sheaf.Algebra.Homology.FilteredQuasiIsoFractions`. Its proof is `sorry`; it introduces
no new definition and proves nothing. The natural-language statement is unchanged.
The existing landed definition node `def-kun-finite-filtered-module-homotopy` is added
to `stmt_deps` to use the category and morphism property that Q35 already constructed.

The previous BLOCKED report concerned an unchanged stage-1 split already reviewed and
merged for Q28. That split supplies this item's seven-step proof plan, not its Lean
statement. The current base has no Lean record for this item. This delivery supplies
that missing stage-2 statement and retains all stage-1 fields.

Hypotheses and clauses, matched individually:

- A commutative ring is `(R : Type u) [CommRing R]`, with explicitly bound universe `u`.
- Objects are `CochainComplex.FiniteFilteredModuleHomotopy R`. Its underlying objects
  are `FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)` satisfying
  `filtration.IsFinite`. This is a filtration of the complex itself by subobjects,
  hence by subcomplexes, rather than unrelated degreewise filtrations.
- The shared `DecreasingFiltration` has `F_succ_le`; its `IsFinite` asserts integers
  with full and zero steps as complexes. It does not fix bounds uniformly across objects.
  Although its witnesses need not initially satisfy `a < b`, decreasing the lower
  witness and increasing the upper witness gives strict bounds, also for the zero
  complex. Thus this predicate is equivalent to the node's finite-interval condition.
- Morphisms are filtered chain maps modulo
  `finiteFilteredModuleHomotopyRel`. This is the quotient category of those maps by
  ordinary `Homotopy`, with every homotopy component factoring through the same target
  filtration step. For integer cochains only components from `n` to `n-1` can be
  nonzero; requiring filtration preservation for all `n,m` adds no condition.
- `finiteFilteredModuleQuasiIso R` is the shared `W`: it has a representative whose
  `FilteredObject.gradedMapSteps` in every integer filtration degree is a `QuasiIso`.
  The graded complex is the cokernel of `F^(i+1) -> F^i`, as recorded by
  `def-sp-filtered-complex-subquotients`. The definition uses existence of a
  representative; homotopy invariance is the first step in the theorem's proof plan.
- Identities and composition are exactly the inherited `IsMultiplicative` field of
  `(finiteFilteredModuleQuasiIso R).HasRightCalculusOfFractions`.
- Two-out-of-three is the second conjunct,
  `(finiteFilteredModuleQuasiIso R).HasTwoOutOfThreeProperty`. Its three fields give
  composition and cancellation of either factor of a composite in W.
- The Ore square (1) is `HasRightCalculusOfFractions.exists_rightFraction`.
  A `LeftFraction X Y` has `f : X -> Z` and `s : Y -> Z` in W. A witnessing
  `RightFraction X Y` has `s : T -> X` in W and `f : T -> Y`; the field equation
  `ψ.s ≫ φ.f = ψ.f ≫ φ.s` is exactly the node's `f ∘ t = s ∘ g`.
- Cancellation (2) is `HasRightCalculusOfFractions.ext`: given `f₁ f₂ : X -> Y`,
  `s : Y -> Z` in W and `f₁ ≫ s = f₂ ≫ s`, it gives `t : T -> X` in W and
  `t ≫ f₁ = t ≫ f₂`.
- Both witnesses T are objects of the same `FiniteFilteredModuleHomotopy R`, so their
  filtrations are globally finite. Integer cochain degrees are unrestricted. No
  boundedness, projectivity, flatness, K-flatness, or common input interval is assumed.

Dependency declarations inspected and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; ordinary integer cochains and quasi-isomorphisms use the
  existing Mathlib interfaces. This original statement-dependency module is imported.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`:
  `CategoryTheory.DecreasingFiltration`, `DecreasingFiltration.gr`; used through the
  existing homotopy-category module and `Sheaf.Algebra.Homology.FilteredComplexSubquotients`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `DecreasingFiltration.complexQuotient`, `complexQuotientπ`, with `gradedPiece` the
  canonical cokernel of consecutive filtration steps. The full module and dependency
  node's recorded declarations were read.
- `Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy`:
  `FiniteFilteredModuleComplex`, `finiteFilteredModuleHomotopyRel`,
  `FiniteFilteredModuleHomotopy`, `finiteFilteredModuleHomotopyQuotient`,
  `finiteFilteredModuleQuasiIso`. Its full local source and current server source
  from `scompile.py --source` agree; the actual definitions and docstrings were read.
- `Sheaf.CategoryTheory.FiniteFiltrationInduction`:
  `FilteredObject.restrictionSteps`, `FilteredObject.gradedMapSteps`; these construct
  the unique restriction and quotient maps and are reused by the shared W definition.
- `Mathlib.CategoryTheory.Localization.CalculusOfFractions`:
  `MorphismProperty.HasRightCalculusOfFractions` and its fields were opened in full;
  `MorphismProperty.IsMultiplicative` and `HasTwoOutOfThreeProperty` were read in
  `Mathlib.CategoryTheory.MorphismProperty.Composition`.
- Proof-only import `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`:
  `CochainComplex.mappingCone.quasiIso_iff_acyclic`, the recorded declaration of
  `lem-pur-quasi-iso-cone-acyclic`. Its full signature and docstring were inspected.
  It applies to arbitrary integer complexes in an abelian category.

Source and edge cases: read the cached Stacks `derived.tex` at
`lemma-construct-multiplicative-system` (05RG), `lemma-acyclic-general` (05RM), and
`lemma-filtered-acyclic` (05S1), including the preceding definition of filtered
quasi-isomorphism. The source works with degreewise finite filtered objects; the
node restricts to globally finite ones. The explicit cone proof in its seven steps
retains common bounds using min/max, and that verification is retained in the Lean
docstring. Checked the zero ring and zero complexes, a one-step filtration, unequal
input intervals, vanishing graded pieces, s equal to the identity, f equal to g,
and complexes unbounded in both cochain directions. None is excluded. In the
cancellation calculation `u=(f-g,-H)` and `k=-c` give the required signs. Only
finite sums are used, so global filtration bounds remain independent of cochain
degree. No statement fault or STATEMENT-DISPUTED issue was found.

Searches actually run for this delivery (full service outputs in `searches.jsonl`):

- `msearch.py ... leanfinder`: "Filtered quasi-isomorphisms of globally finite filtered
  cochain complexes admit a calculus of right fractions modulo filtration preserving
  homotopies". Eight hits, including ordinary derived-category right fractions and
  factorization results; none states the filtered result.
- `msearch.py ... loogle`: `HasRightCalculusOfFractions, HasTwoOutOfThreeProperty`
  returned unknown identifier; retried the valid query `"HasRightCalculusOfFractions"`.
  The retry returned the class, its fields and generic triangulated-subcategory
  instances. These supply the predicate to state, not this filtered theorem.
- `msearch.py ... grep`: `finiteFilteredModuleQuasiIso|filtered.*[Qq]uasi|HasRightCalculusOfFractions`
  in `Algebra/Homology`. The only hit is the ordinary abelian-category fractions
  instance in `Mathlib/Algebra/Homology/DerivedCategory/Fractions.lean`.
- `rg` of `WeilConjectures` and project `lean/Sheaf` for filtered quasi-isomorphisms,
  `finiteFilteredModuleQuasiIso`, and this node id: the existing finite filtered
  homotopy definition and downstream replacement theorem were found. No theorem
  of fractions for this W exists. Other matches concern filtered colimits of schemes
  or sheaves. The existing shared definition is reused, without a private copy.
- Source inspection of Mathlib's right-fraction and two-out-of-three classes confirmed
  the exact Ore/cancellation orientation and the identity/composition clauses.

Validation: the required file-only `scompile.py Q09
lem-kun-filtered-quasi-isomorphism-fractions <module>` completed with exit code 0.
Both the sandbox probe and actual module compiled cleanly (3.1 s and 37.8 s).
The required `deliver2.py ... --no-push` reruns compilation and server preflight.
No delivery is pushed; the independent second reader delivers.

## Second reading by Q09

I opened the item node, its Stacks source place, the delivered module, and the
recorded dependency `def-kun-finite-filtered-module-homotopy`. The item is a
statement node over `(R : Type u) [CommRing R]`; the module binds exactly this
ring and universe in `finiteFilteredModuleQuasiIso_fractions`.

The node's objects and hypotheses match as follows. The category of objects is
rendered by `FiniteFilteredModuleHomotopy R`, the quotient of filtered integer
cochain complexes of `ModuleCat R` by `finiteFilteredModuleHomotopyRel`; the
underlying finite filtration is `FiniteFilteredModuleComplex`, whose
`FilteredObject.filtration.IsFinite` supplies object-dependent integers with
whole and zero steps. Morphisms and filtered homotopies are therefore exactly
the node's filtration-preserving chain maps and homotopies, with no cochain
degree bound. The class `finiteFilteredModuleQuasiIso R` is the node's `W`:
it requires a representative whose canonical `FilteredObject.gradedMapSteps`
is a `QuasiIso` at every `i : ℤ`, using the canonical graded cokernel from
`FilteredComplexSubquotients`.

The conclusion is rendered verbatim by
`(finiteFilteredModuleQuasiIso R).HasRightCalculusOfFractions ∧
(finiteFilteredModuleQuasiIso R).HasTwoOutOfThreeProperty`. The first conjunct
includes `IsMultiplicative` (identities and composition), the exact
`exists_rightFraction` Ore square for a left fraction, and `ext` cancellation;
the second is the generic two-out-of-three property. Thus the two explicit
clauses in the node, including their composition orientation and the existence
of a globally finite witness object, are represented by the right-fraction
class and its proof docstring. No additional boundedness, projectivity,
flatness, or characteristic assumption occurs.

I checked the edge cases named by the brief and source: the zero ring, zero
complexes, empty/vanishing graded pieces, a one-step filtration, unequal
object-dependent filtration intervals, identity denominators, equal maps in
the cancellation clause, and complexes unbounded in both cochain directions.
The finite-filtration predicate and cone constructions include all of these;
no index set or degree range is required and the integer filtration index is
unrestricted.

I reran the existing-definition searches (LeanFinder, Loogle, LeanSearch,
grep over Mathlib, `WeilConjectures`, and project `lean/Sheaf`). They find only
ordinary derived-category fraction classes and the shared finite filtered
homotopy/quasi-isomorphism definitions; no theorem for this filtered `W`
exists. The dependency module was read in full and supplies the exact shared
notions, so no private duplicate was introduced. The only delivery adjustment
is the authorized addition of the already-landed
`def-kun-finite-filtered-module-homotopy` to `stmt_deps`, because the Lean
signature uses its category and `finiteFilteredModuleQuasiIso` declaration.
The item statement and theorem signature themselves required no repair.

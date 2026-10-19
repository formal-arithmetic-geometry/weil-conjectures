## Worker report

The module `Sheaf.RingTheory.PseudoCoherentNilpotentInvariance` states
`DerivedCategory.isPseudoCoherent_iff_of_surjective_nilpotent_kernel`, with `sorry` as
its entire proof. No new definitions, dependency modules, or statement corrections.
The source was read in local `literature/stacks-project/more-algebra.tex`,
lemma-check-pseudo-coherent-modulo-nilpotent (Tag 0H76), lines 19498 onward.
It agrees with the node.

Hypothesis and clause correspondence:

- Commutative rings R', R are `A B : Type u`, `[CommRing A]`, `[CommRing B]`.
  A common universe loses no pair of rings; `ModuleCat.{max u v}` allows any larger
  module universe. The localization universe `w` is explicit.
- The ring map is `φ : A →+* B` and surjectivity is `hφ : Function.Surjective φ`.
- Its nilpotent ideal kernel is `hnil : IsNilpotent (RingHom.ker φ)`, i.e. some power
  of this ideal is zero. This is ideal nilpotence, not elementwise nilpotence.
- D(R') and D(R) are `DerivedCategory (ModuleCat.{max u v} A)` and the corresponding
  category for B, with their explicitly bound `HasDerivedCategory` instances.
- `K'` is an arbitrary object of the first derived category, with no boundedness,
  flatness or finiteness hypothesis.
- The assignment K = K' derived-tensor R is `L.obj K'`. Its meaning is fixed by
  `ε : Qh ⋙ L ⟶ (extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ Qh` and
  `[L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso ...)]`. These specify the
  total left derived functor by Mathlib's universal property. They are a choice of
  the functor already named in the node, unique up to canonical isomorphism, not
  an extra mathematical restriction on φ or K'. General-site change of rings
  supplies it on the one-object site; existing ring-module derived extension
  interfaces use exactly this universal property (e.g. BaseDerivedExtensionResolution).
  No sheaf-module object is substituted for the node's ordinary module object.
  The explicit `@Functor.mapHomotopyCategory` supplies the already proved
  `(ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive` as a term, avoiding
  an extra additive instance hypothesis or a new definition.
- Both pseudo-coherence clauses use precisely the dependency's
  `DerivedCategory.IsPseudoCoherent`: the conclusion is
  `IsPseudoCoherent (L.obj K') ↔ IsPseudoCoherent K'`, in the node's order.

Dependency declarations and source signatures/docstrings read:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`, the localization
  of integer-indexed complexes at quasi-isomorphisms (def-weil-abstract-derived-category).
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`, exactly
  existence of a bounded-above complex of finite free modules with derived image
  isomorphic to the given object (def-pc-ring-pseudo-coherent-complex).
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`: `SheafOfModules.derivedChangeOfRings`.
  Its signature and docstring provide an additive change-of-rings functor and the
  total left derived functor on the homotopy localization, computed on K-flat
  complexes (lem-pur-derived-change-of-rings). This is imported as a proof dependency;
  the statement spells out the ring-level specialization using existing Mathlib
  functors and universal-property predicates, with no private copied notion.
- Mathlib `ModuleCat.extendScalars`, `ModuleCat.extendRestrictScalarsAdj`, and
  `CategoryTheory.Functor.IsLeftDerivedFunctor` give ordinary scalar extension and
  its total derivation. The latter is the right Kan extension along localization.

All recorded and available proof dependencies are imported: RingPseudoCoherent,
BoundedFlatKFlat, DerivedChangeOfRings, NakayamaNilpotent, Mathlib's projectivity
and flatness modules. `lem-weil-pbc-nilpotent-projective-complex-lift` has no recorded
Lean module and therefore no import yet. Its proof role is retained in the docstring.
The docstring reproduces all six steps, including the quotient identification,
K-flat forward direction, projective-complex lifting, nilpotent Nakayama without
finiteness, split-kernel argument, and final unchanged bounded-above model.

Edge cases checked: zero rings and zero complexes require no nontriviality;
the identity quotient has zero nilpotent kernel; a quotient onto the zero ring
with nilpotent kernel forces the source to be zero. Rank-zero degrees are retained
in the reverse-direction argument. Arbitrary unbounded K' is allowed: boundedness
is a consequence of pseudo-coherence, not a hypothesis. No field or characteristic
restriction, no requirement that B be flat or finite over A, no chosen nilpotence
exponent and no positive-rank restriction are introduced.

Searches:

- msearch LeanFinder: "Pseudo coherent derived complexes are invariant under
  surjective ring maps with nilpotent kernel"; eight unrelated hits, including
  DerivedCategory.instEssSurjCochainComplexIntQ and formal unramified/smooth ring maps.
- msearch Loogle: `"pseudo", "coherent"`; zero hits. Earlier query
  `DerivedCategory, ModuleCat.extensionOfScalars` found no declaration (the correct
  existing ordinary functor name was then found in source as `extendScalars`).
- msearch grep of Mathlib: `pseudo.?coherent.*nilpotent|nilpotent.*pseudo.?coherent`;
  zero hits.
- msearch LeanSearch: "Pseudo coherence of a derived complex is invariant under a
  surjective ring map with nilpotent kernel"; service unavailable (Internal Server Error).
- rg of upstream WeilConjectures and project lean/Sheaf with the same pseudo-coherent /
  nilpotent expression and the proposed declaration name: no matching statement.
- grep of the exact item id in upstream WeilConjectures: no hits.
- Source searches for derived scalar-extension declarations found the one-point-site
  RingRHomBaseChangeData and ModuleCat.exists_baseDerivedExtension_resolution;
  neither states this nilpotent invariance result, and the former uses a different
  sheaf-module encoding. Existing definitions are reused rather than duplicated.

Server validation: scompile.py compiled the delivered file cleanly, 1.2 seconds,
nice 19, two threads, 60-second per-file limit. No local compilation performed.
No STATEMENT-DISPUTED or node fault found.


## Second reading by NN

Independent second reader: read the sandbox node and module, the three statement-dependency
nodes and their recorded source declarations, Stacks more-algebra.tex Tag 0H76
(lemma-check-pseudo-coherent-modulo-nilpotent), its proof, the preceding
lemma-lift-complex-projectives, and the introduction to Section Lifting complexes.
The chapter uses commutative rings and unbounded derived categories; the section adds
no standing Noetherian, local, finiteness, or flatness hypothesis.

The node's object/hypothesis/conclusion inventory and its Lean correspondence:

1. Two commutative rings R', R: `{A B : Type u} [CommRing A] [CommRing B]`.
   Verdict: exact, including the zero ring. A shared ambient universe can contain
   both rings, with no cardinality equality required.
2. A ring homomorphism R' → R: `(φ : A →+* B)`. Verdict: exact; no algebra
   structure or field structure is additionally assumed.
3. Surjectivity: `(hφ : Function.Surjective φ)`. Verdict: exactly the source hypothesis.
4. The kernel is a nilpotent ideal: `(hnil : IsNilpotent (RingHom.ker φ))`.
   Verdict: some ideal power is zero, not merely elementwise nilpotence.
5. The derived categories D(R'), D(R): `DerivedCategory (ModuleCat.{max u v} A)`
   and its B analogue, with explicit `HasDerivedCategory.{w}` choices. Opened
   Mathlib.Algebra.Homology.DerivedCategory.Basic: `Q` localizes integer-indexed
   complexes at quasi-isomorphisms; `Qh` localizes their homotopy category at
   `HomotopyCategory.quasiIso`. Verdict: exactly the recorded
   def-weil-abstract-derived-category, with size choices rather than extra ring properties.
6. An arbitrary K' in D(R'): `(K' : DerivedCategory (ModuleCat.{max u v} A))`.
   Verdict: exact; there is no boundedness assumption on this object.
7. Set K = K' derived-tensor R: `L.obj K'`, with `ε` and
   `[L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso ...)]`. Opened Mathlib's
   `ModuleCat.extendScalars`: its object is B tensor_A M; its homotopy functor
   acts termwise. Opened Functor.Derived.LeftDerived: IsLeftDerivedFunctor means
   the right Kan extension along localization, and `leftDerivedUnique` gives
   uniqueness up to natural isomorphism. Thus these binders specify the functor
   in the node, rather than assuming an arbitrary functor or exact ordinary tensor.
   The additive instance is supplied by the existing scalar-extension adjunction,
   not imposed as another assumption. Opened the full signature of the dependency
   `SheafOfModules.derivedChangeOfRings`: its universal property agrees with this
   one after passage to the one-object identity-cover site. No second definition
   of derived tensor or substitution of sheaf modules for ordinary modules occurs.
   Verdict: the specified derived reduction, with no extra mathematical restriction.
8. Conclusion, in order: `IsPseudoCoherent (L.obj K') ↔ IsPseudoCoherent K'`.
   Opened Sheaf.RingTheory.RingPseudoCoherent and its dependency node:
   `DerivedCategory.IsPseudoCoherent` requires a bounded-above complex whose
   terms are both Module.Free and Module.Finite, with image isomorphic under Q.
   Both sides use this exact predicate. Verdict: both implications and all
   quantifiers agree with the node and Stacks 0H76.

Edge cases: zero complex, zero rings, identity quotient (zero kernel), and finite
free rank zero are included. A surjection onto the zero ring with nilpotent kernel
forces the source ring to be zero, so it introduces no counterexample. Arbitrary
unbounded K' is allowed. No nilpotence exponent is fixed or required to be positive;
a witness exponent zero forces the ideal semiring to be trivial and still satisfies
the intended nilpotence condition. No characteristic restriction appears. The module
universe `max u v` admits modules at least as large as either ring and arbitrarily
larger ones; `w` is explicitly bound as the localization morphism universe. No index
set, scheme, or geometric nonemptiness condition is involved. All variables and
universes are explicitly bound (`autoImplicit false`).

Independent searches (different words from the first reader):

- msearch LeanFinder: "A derived tensor product with a nilpotent quotient detects
  existence of a bounded above finite free resolution" returned eight results,
  including Module.free_of_lTensor_residueField_injective and projective Tor
  vanishing. None states nilpotent invariance of pseudo-coherent derived objects.
- msearch Loogle: `"IsPseudoCoherent"` returned zero hits.
- msearch LeanSearch: "Nilpotent quotients reflect pseudo coherent derived objects"
  was unavailable (Internal Server Error), not evidence of absence.
- rg across pinned Mathlib, upstream WeilConjectures, and project lean/Sheaf:
  `nilpotent.{0,100}(coheren|finite.free)|coheren.{0,100}(nilpotent|nilradical)`
  and the proposed declaration name found only unrelated curve ideal-sheaf
  material in the project, with no matching invariance theorem. Broader searches
  in upstream Algebra/Homology and RingTheory found no candidate either.
  The shared pseudo-coherence definition is reused, not duplicated.

No new definition nodes, dependency modules, or statement correction are present or
needed. The missing proof-level projective-complex lifting node remains a stage-3
proof dependency; no missing declaration is needed to type this statement. Reviewed
the available proof-dependency modules BoundedFlatKFlat and NakayamaNilpotent and
Mathlib's projective/free/flat declarations. They are imported; the not-yet-stated
lifting node has no import. The docstring gives all six node-proof steps in order,
including the quotient identification and rank-zero split-kernel argument. There
are no hollow definitions, local notation/instances, or proofs beyond the sole
named theorem's `sorry`. Source and blueprint docstrings and line lengths conform.

Mismatches found: none. Changes: appended this independent second-reading report;
retained the correct Lean statement and node record unchanged. Checked by exact
string comparison that lean.statement is verbatim the theorem signature in the file.
Server scompile.py validation: clean, 1.2 seconds, nice 19, two threads,
60-second per-file limit; no local compiler was used.

## Worker report

The module `Sheaf.AlgebraicGeometry.BundleEndomorphismDerivedAdjunction` states
`AlgebraicGeometry.BundleEndomorphism.tensor_derived_adjunction`, with one `sorry`.
The node's statement, dependencies, proof, and all other original fields are unchanged;
only `lean` is set. The auxiliary declarations are interfaces to existing constructions,
not additional independent notions or postponed theorems. Their data contains no `sorry`.
All universes and variables are explicitly bound; `autoImplicit` is disabled.

Sources read: Stacks `dga.tex`, tensor-with-complex-derived (09LX) and
tensor-with-complex-hom-adjoint (09LY), with its reference to the unbounded derived Hom
construction; `perfect.tex`, tensor-with-QCoh-complex (09M3). The original node's ten-step
proof is reproduced in full in the theorem docstring, with its dependency IDs. The shared
scheme-derived-category and global-derived-Hom declarations and their docstrings were
read, as were the Mathlib derived category, triangulated functor, and ordinary
endomorphism tensor/Hom interfaces.

Clause-by-clause correspondence:

- **A commutative ring:** `(A : Type a) [CommRing A]`. Its universe `a` is independent of
  the scheme universe `u`.
- **An A-scheme X:** `(X : Scheme.{u})` and `(aX : A →+* Scalars X)`, where `Scalars X`
  abbreviates the existing structure ring evaluated at `op ⊤`. This is the equivalent
  global-section description of an affine-base scheme structure (Γ–Spec adjunction).
  No choice of a second ring or structural action is made.
- **Quasi-compact and quasi-separated:** `[CompactSpace X] [QuasiSeparatedSpace X]`.
- **Finite locally free E, allowing locally varying finite rank:**
  `(E : Modules X) [E.IsFiniteLocallyFree]`. `Modules X` abbreviates exactly
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, retaining its shared category
  and abelian instances. The upstream finite-locally-free predicate uses finite local
  generators which freely generate; it does not require constant rank or positive rank.
- **E viewed in degree zero:** `single X E` is
  `(DerivedCategory.singleFunctor (Modules X) 0).obj E`.
- **B = End(E), composition multiplication:** Mathlib `End E`. Right B-modules are
  `ModuleCat.{u} (End E)ᵐᵒᵖ`. The regular module in `F_E(B) ≅ E` is the regular left
  B-opposite module, canonically the right regular B-module under `unop`.
- **Ordinary V_E:** `tensor X E` abbreviates the existing
  `IsGrothendieckAbelian.tensorObj E`, without copying a tensor construction.
  This is the specified balanced sheaf tensor: a map from the sheafification of
  `U ↦ L ⊗_B E(U)` to N is, by sheafification's universal property, the same as a
  restriction-compatible family of balanced maps. Evaluation identifies that family
  with a B-linear map `L → Hom(E,N)`. The inverse sends `l ⊗ e` to `v(l)(e)`.
  Thus it has precisely Mathlib's tensorObj representing property, naturally in L
  and N. Uniqueness of this adjoint identifies the two presentations; this is not an
  arbitrary functor or a replacement by internal Hom. The existing adjunction also
  supplies the additive instance required to apply the functor to complexes.
- **Unbounded derived categories:** the shared `schemeDerivedCategory X` and
  `DerivedCategory (ModuleCat.{u} (End E)ᵐᵒᵖ)`, with independent explicit localization
  hom universes `w`, `wB`, `wA`, `wΓ`. No bounded subcategory occurs.
- **Everywhere defined total left derived tensor with quasi-coherent image:**
  `∃ F : DerivedCategory (...) ⥤ schemeDerivedQCohCategory X`. The first conjunct
  of `adjunctionStatement` supplies `eps` and `IsLeftDerivedFunctor eps` for the
  actual ordinary tensor on homotopy categories and quasi-isomorphisms. Its target
  is the shared full subcategory defined by quasi-coherence of every cohomology sheaf.
- **F_E(B) ≅ E:** the second conjunct is an isomorphism in the ambient derived
  category from the image of the degree-zero regular B-module to `single X E`.
- **Right adjoint and its actual B-action:** `qcHom X E` is inclusion into the
  ambient derived category followed by `(preadditiveCoyonedaObj E).rightDerivedFunctor`.
  The existing `preadditiveCoyonedaObj` has underlying group `E ⟶ N` and B-opposite
  scalar action by precomposition, and acts on morphisms by postcomposition.
  The `∃ adj : F ⊣ qcHom X E` clause is the adjunction on D_QCoh itself.
- **K-injective computation:** the `∀ K I s, QuasiIso s → I.IsKInjective → ...`
  clause gives an isomorphism in D(Mod-B) to Q of termwise coyoneda applied to I.
  Its degree n is `Hom(E,I.X n)` and its differential sends f to `f ≫ I.d`.
  This includes the B-action on the complex, not only its underlying A-complex.
  Mathlib's K-injective predicate says every map from an acyclic complex is null
  homotopic; testing all shifted acyclic sources gives exactly the node's condition
  that each mapping complex is acyclic. This is not termwise injectivity or a
  bounded-below replacement assumption.
- **Exactness for standard triangles:** the two `∃ s : ...CommShift ℤ,
  Functor.IsTriangulated ...` clauses express the standard exactness of the
  ambient left-derived functor and of the existing ambient right-derived Hom.
  By the shared supported-quasi-coherent triangulated-subcategory result (T = X),
  these give exactness into/from D_QCoh with its inherited distinguished triangles.
  The ambient Hom functor is the one used in the node's resolution computation and
  proof step 5; no alternate triangulation is quantified over.
- **A-linearity of functors and adjunction:** the conclusion existentially supplies
  a `Linear A (Modules X)` structure and fixes it on EVERY sheaf morphism through
  `scalarsCompatible`. Its equation is multiplication by the structural image of a,
  using the existing `Scheme.Modules.smulHom`; hence it determines the actual
  central map A → End(E). Standard induced linear structures are used on localization,
  the full subcategory, and the opposite-endomorphism module category.
  `F.Linear A`, `(qcHom X E).Linear A`, and the scalar equation for every
  `adj.homEquiv L K` give all three asserted linearity clauses. This existential
  structure is uniquely specified by its component equation and is never selected
  from a bare non-unique existence theorem to define data.
- **Natural derived global-Hom comparison after restriction to A:** a natural
  isomorphism of functors compares `qcHom` followed by derived restriction along
  `algebraMap A (End E)ᵐᵒᵖ` with `globalHom X A aX E`. The latter is exactly
  the recorded `schemeGlobalDerivedHom X` with E fixed in its first variable,
  followed by scalar restriction from Γ(X,O_X) along `aX`.
  For the possibly noncommutative B, the existing unbounded `rightDerivedFunctor`
  is used for scalar restriction. Restriction of scalars is exact, so this is its
  canonical functor on derived categories. This avoids the available
  `ChangeOfRingsExact` instance whose target ring is assumed commutative; B is NOT
  assumed commutative. Restriction from Γ to A uses the existing exact
  `mapDerivedCategory` construction.
- **All q in Z, including the B-action:** the final `∃ e : ∀ K (q : ℤ), ... ≃+ ...`
  supplies the cohomology/Hom identification, with `single X E ⟶ K.obj⟦q⟧` as target.
  Its first equation sends `b • x` to
  `(DerivedCategory.singleFunctor ... 0).map b.unop ≫ e K q x`, exactly
  precomposition by b. Its second equation is naturality in EVERY morphism K → L,
  with the shifted derived morphism on the target. No degree, object, or action
  is discarded. The preceding global-Hom comparison is an actual natural
  isomorphism in D(A), not only a family of cohomology isomorphisms.

Recorded statement dependencies used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, Q and Qh.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `schemeDerivedCategory`, `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `def-pc-global-derived-rhom`: `WeilConjectures.AlgebraicGeometry.GlobalDerivedHom`,
  `schemeGlobalDerivedHom` (with its genuine derived internal Hom/global sections).
- `def-weil-triangulated-category`: its Mathlib match in
  `Mathlib.CategoryTheory.Triangulated.Triangulated` and its public functor interface,
  `Functor.CommShift` and `Functor.IsTriangulated`.

Additional existing interfaces: Mathlib Gabriel–Popescu `tensorObj` and its
`tensorObjPreadditiveCoyonedaObjAdjunction`; `preadditiveCoyonedaObj`;
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
`SheafOfModules.IsFiniteLocallyFree`;
`WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, `Scheme.Modules.smulHom`;
the shared unbounded `Functor.rightDerivedFunctor`, and exact module scalar restriction.

Plain proof imports include the recorded available resolving-class, adapted-complex,
K-injective, K-flat/internal-Hom, quasi-coherent kernel/cokernel/coproduct and triangulated
subcategory modules, plus the Mathlib proof leaves. The two archived dg proof dependency
modules `Sheaf.CategoryTheory.DGModuleSemiFreeReplacement` and
`Sheaf.CategoryTheory.SemiFreeDGModule` have no local file. Both prescribed
`scompile.py --source` lookups answered `Module source unavailable`. As the stage-1
review already notes, their sources were removed; their stale records are not usable
imports. They are proof prerequisites only, not notions needed to TYPE this statement;
no substitute dg notion or extra hypothesis is introduced. The ten-step proof retains
both node references for stage 3.

Edge cases checked before writing and again against the final type:

- E = 0 and X empty: B can be the zero ring, its module category consists of zero
  objects, and all Hom/cohomology groups in the statement are zero. No `Nontrivial`
  condition or positive rank appears.
- Rank varies across components, including zero components: only finite LOCAL
  freeness is assumed; no global rank integer or chosen trivialization is required.
- E = O_X: Hom is global sections and its derived functor is RΓ; F(B) ≅ O_X has
  the intended meaning even when X is nonaffine and higher cohomology is nonzero.
- X = Spec k, E = k^r, r > 1: B is a matrix ring. The opposite-ring encoding and
  precomposition equation retain its noncommutativity; no commutative-B API is used.
- q = 0, positive and negative q: integer shifts and the existing unbounded
  complexes are used throughout, with no truncation or boundedness hypotheses.
- No compact-generation, generator, self-Ext vanishing, flatness over B, or
  equivalence hypothesis has been added. These belong to downstream tilting results.

Searches for an existing exact statement (2026-10-24):

1. `msearch.py ... leanfinder`, query
   `For a vector bundle derived tensor over its endomorphism ring is adjoint to global derived Hom`:
   eight hits, including ordinary `IsGrothendieckAbelian.tensorObj` and its adjunction,
   and commutative-module tensor/internal-Hom facts. The ordinary adjunction is reused;
   no hit states the complete unbounded bundle assertion and its comparisons.
2. `msearch.py ... loogle`, query `tensorObj, preadditiveCoyonedaObj`:
   zero hits; service reports unknown identifier `tensorObj` without qualification.
3. `msearch.py ... grep`, query `tensorObj|preadditiveCoyonedaObj`, subdirectory
   `CategoryTheory/Abelian/GrothendieckCategory`: ten hits, locating the ordinary
   Gabriel–Popescu construction, its adjunction and related limits facts, which were read.
4. `rg` over the project's `WeilConjectures` and `Sheaf` sources for bundle/endomorphism
   adjunction, `tensorObj`, global derived Hom and right-derived functors: no exact
   existing statement. The already landed `ProjectiveSpaceTiltingEquivalence` was read;
   its helpers use the same ordinary tensor/Hom and scalar convention, but its theorem
   concerns the special tilting bundle with generation and self-Ext vanishing and is
   not this assertion for every vector bundle.
5. The requested node-ID search in upstream `WeilConjectures` returned no declaration.
   Direct Mathlib/source reads located the opposite-End action, finite locally free
   predicate, standard K-injective definition, scalar multiplication and shared derived
   categories. No private copy of those notions was written.

No statement correction, disputed assertion, new node, or dependency-record change.
Validation: the required `scompile.py` compiles the final module in module mode,
with `autoImplicit false`, against the live build. Final compile has no errors or warnings
other than permitted sorry diagnostics. The final theorem is the sole postponed proof.

## Second reading by NW

The dispatcher explicitly prohibits starting another agent and assigns the maintainer
an independent delivery review. This section records a second complete reading by the
same worker; it does not claim an independent reviewer.

Reopened the node's statement, its five dependency records and the final module. Matched
A, its actual structural map, X, the qc/qs conditions, the shared sheaf category,
finite local freeness, B with composition, right B-modules, V_E, the unbounded left-derived
universal property, quasi-coherent codomain, F(B), the adjunction, K-injective computation,
both exactness clauses, A-linearity including the adjunction bijection, the NATURAL D(A)
comparison, and every integer cohomology identification with B-action and naturality.
Checked that the theorem unfolds the non-opaque `adjunctionStatement` containing all
these clauses, and the existential linear structure is constrained by
`scalarsCompatible`, not assumed or chosen arbitrarily. All helper declarations are
listed in the lean record and refer to the existing constructions.

Implementation faults found and repaired before delivery: naive inference of tensor
additivity wrongly requested product preservation; now use the existing additive
adjunction theorem. The scalar compatibility needed the upstream `smulHom` import,
which is now public. Direct `mapDerivedCategory` for restriction from B would use an
exactness instance requiring a commutative target; it has been replaced by the existing
unbounded derived restriction, retaining arbitrary noncommutative End(E). A long formula
in the proof docstring was wrapped and duplicate direct imports removed. Rechecked the
zero/empty and matrix-ring cases, arbitrary q and independent localization universes.
No mathematical statement was weakened or silently corrected. The final module compiled
cleanly after these repairs.

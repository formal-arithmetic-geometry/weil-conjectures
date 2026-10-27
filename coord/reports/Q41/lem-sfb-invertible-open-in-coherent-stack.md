## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleOpenInCoherentStack` states
`AlgebraicGeometry.invertible_open_in_coherent_stack`, with its sole proof `sorry`.
No definition, dependency statement, or node statement is replaced. The source read is
Stacks Project quot.tex, Tag 0D03, `lemma-picard-stack-open-in-coh`, including its complete
proof (lines 2600–2657 in the local source). The node specializes its algebraic-space
statement to schemes, exactly as its accepted DAG split specifies.

Clause-by-clause correspondence:

- The schemes and morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Properness is `[IsProper f]`, flatness is `[Flat f]`, and finite presentation is
  `[LocallyOfFinitePresentation f]`: the additional quasi-compactness and
  quasi-separatedness in finite presentation already follow from properness, so no
  additional size or finiteness hypotheses are introduced.
- The specified category C_f is exactly `FlatCoherentModuli.category f` from the
  recorded `lem-sfb-coherent-stack-algebraic-lfp` module. Its objects retain their
  quasi-coherence, finite presentation, stalkwise flatness over the test scheme and
  closed-pushforward proper-support witness. Its arrows retain the actual normalized
  tensor-pullback isomorphisms. No category of isomorphism classes is substituted.
- Every line bundle on every X_T belongs to C_f: the first conjunct quantifies over
  `(T : Over S)` and `(L : (pullback f T.hom).Modules)` and concludes the existence of
  `A : FlatCoherentModuli f` with `A.base = T` and `HEq A.module L`. Heterogeneous equality
  only records equality of the module in the dependent fibre after this base equality;
  no isomorphism or extra structure on L is assumed. This ensures the selected full
  subcategory contains all line bundles, rather than just asserting openness for a
  potentially smaller class already lying in the ambient category.
- B_f is the full subcategory selected by `B.property`, with the equality
  `B.property = (fun A : FlatCoherentModuli f ↦ A.module.IsInvertible)`. This reuses
  `Scheme.Modules.IsInvertible`, exactly the recorded notion for line bundles.
  `OpenModuliSubstack.category` is definitionally this full subcategory, and
  `fullModuliInclusion ... B.property` is its actual forgetting functor over Sch/S.
- Full faithfulness is stated by the `Full` and `Faithful` conjuncts for that functor.
  Because the construction is full, these retain exactly the ambient pullback-isomorphism
  arrows, including their automorphisms.
- The witness `B : OpenModuliSubstack ...` includes fibredness, stability of the predicate
  under every pullback arrow, and `B.open_pullback`. The latter states an equivalence
  from an actual representing scheme to the actual comma-defined two-fibre product,
  together with a `ModuliTwoIso` identifying its projection with an open immersion.
  Thus representability includes the specified projection, not just abstract equivalence
  of categories.
- The final conjunct gives `U : A.base.left.Opens` for every coherent family A.
  Every test scheme and every scheme morphism to its base is encoded by
  `(T₁ : Over S) (v : T₁ ⟶ A.base)`: an arbitrary scheme morphism to the base acquires
  its S-structure by composition. The pulled-back module is the dependency's actual
  `(Scheme.Modules.moduleBaseChange f v).obj A.module`, not an arbitrary module or map.
  The conclusion is the equivalence between its invertibility and a factorization
  `∃ w : T₁.left ⟶ U.toScheme, w ≫ U.ι = v.left`.
- This explicit U and the open representing the test two-fibre product are the same
  open subscheme: both classify exactly those base arrows for which the pulled-back
  family is invertible. Over such an arrow the comma groupoid has the pulled-back
  family and its identity as terminal object, and otherwise it is empty. Yoneda and
  uniqueness of open factorizations identify the representing schemes over the base.
  The statement therefore retains both the explicit criterion and the two-fibre-product
  assertion without introducing a separately chosen family-classifying map.
- Neither geometric reducedness nor any condition on f_* O_X appears.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`; its recorded components
  `IsSeparated` and `UniversallyClosed` were read in their respective source modules.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` (with its stalkwise characterization).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.CoherentStackAlgebraicLfp`:
  `coherent_stack_algebraic_lfp`, using `FlatCoherentModuli.category` from its public
  dependency `Sheaf.AlgebraicGeometry.FlatCoherentModuli`. Both complete modules were read.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  `Scheme.Modules.moduleBaseChange`, definitionally tensor pullback along `baseChangeMap`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, with the upstream `tensorPullback`
  and the section-normalized identity and composition comparisons, as used by the
  concrete coherent category.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`,
  `fullModuliSubcategory`, `fullModuliInclusion`, and the open test's actual
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `ModuliTwoIso` declarations.

The imports for recorded proof dependencies include finite locally free sheaves
(`SheafOfModules.IsFiniteLocallyFree`), the common-field-extension theorem,
`Module.Flat.trans`, `Module.finrank_baseChange`, finite tensor base change,
scheme base-change/permanence instances, and open immersions. The genuine proof
prerequisite `lem-sfb-relative-finite-free-locus-base-change` has no Lean record or
Mathlib match on the read base, so there is no module to import yet. It is named in the
proof docstring; no surrogate theorem or extra hypothesis is used in this statement.
The recorded CompactObject example is now withdrawn; its node points to the existing
upstream module, which was read for the current module/header conventions.

Edge cases checked before writing:

- Empty X: invertibility is vacuous on X_T and the representing open is all T.
- Empty T or T₁: all quantifiers and the open factorization remain valid, with no
  nonemptiness binders. The unique module on the empty scheme is invertible.
- The zero module on a nonempty fibre is rank zero, so it is excluded; over empty
  fibres it is invertible, and these base points belong to the locus.
- A family of rank other than one on every nonempty fibre gives the empty open;
  ranks varying across disconnected components give the appropriate open components.
- T₁ → T may be nonflat and not finitely presented; no such assumptions occur.
- No Noetherianity, connectedness, geometric reducedness, global rank bound,
  geometric point, auxiliary field, or independent test-scheme universe is imposed.
  The single arbitrary `u` agrees with the recorded category over `Scheme.{u}`.

Searches actually run (the launcher msearch log records the service output):

- LeanFinder: "Invertible modules form an open substack of the stack of flat finitely
  presented coherent modules for a proper flat finitely presented scheme morphism".
  Eight hits, including `UniversallyOpen.of_flat`, `IsOpenImmersion.of_flat_of_mono`,
  `Module.isOpen_freeLocus`, and unrelated smooth/affine loci. No stack theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.IsInvertible,
  CategoryTheory.OpenModuliSubstack`. Zero hits: the remote index reports unknown
  identifier `AlgebraicGeometry.Scheme.Modules.IsInvertible`. This is an index
  limitation; its actual upstream declaration was found and read locally.
- Mathlib grep through msearch: `invertible.*[Oo]pen|[Oo]pen.*[Ii]nvertible` in
  AlgebraicGeometry. Zero hits for the requested theorem.
- LeanSearch: "Invertible sheaves form an open substack of flat finitely presented
  coherent sheaves in a proper flat family". Eight hits on finite-presentation
  sheaves and universally open morphisms; none states this moduli assertion.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` for
  `FlatCoherentModuli|invertible.*[Oo]pen|[Oo]pen.*[Ii]nvertible|InvertibleModuli`:
  coherent-category definitions found as above. The upstream Picard representability
  file concerns the distinct locus where the direct image is invertible for curves
  over a field; it is not this theorem. A focused follow-up on FlatCoherentModuli and
  `invertible_open_in_coherent` found only the coherent-category construction and its
  algebraicity statement. Direct grep for this item's id in upstream found no match.
- Search for this item's id in the current `literature/blueprint/latest` found no
  separate blueprint declaration (the node has `blueprint.is = null`). Its stated
  source Tag 0D03 was read directly from quot.tex.

No statement correction, new nodes, dependency modules, or STATEMENT-DISPUTED issues.
The source's hypotheses suffice, including for the empty-fibre cases above.

Validation: the delivered module compiles cleanly through scompile.py in both the
sandbox and its intended library module, each in 3.3 seconds. An initial timeout was
diagnosed with a module-mode import/type probe; all dependency declarations were
available, and the unchanged full statement then compiled successfully. No timeout
limit, library file, or launcher tool was modified. A final direct name search in both
Lean roots and dag/lean_names_upstream.json found no conflicting declaration.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

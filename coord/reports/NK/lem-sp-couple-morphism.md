## Worker report

Restated `CategoryTheory.BigradedExactCouple.coupleMorphism` in
`lean/Sheaf/CategoryTheory/ExactCoupleMorphism.lean`, with its whole proof `sorry`.
The node changes only in `lean`. No mathematical statement correction, new node,
or dependency-module repair is needed. The proof docstring follows the node's
current three steps, including the canonical comparisons already furnished by
`halfPlaneConvergence`; it does not invoke the obsolete extra graded-canonical lemma.

Hypotheses and clauses, matched to the node:

- The same abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  Both universes are explicitly declared and independent.
- The two exact couples are `(X Y : BigradedExactCouple C 0)`. The compatibility
  wrapper contains only the dependency's upstream `ExactCouple`, with degrees
  `(-1,1)`, `(2,-1)`, `(0,0)`; it adds no new mathematical hypothesis or data.
- Bidegree-preserving maps are `tD` and `tE`, each quantified over every pair
  `p q : ℤ`, with source and target at the same pair.
- The alpha square is `hα`: `X.alpha p q ≫ tD (p-1) (q+1) =
  tD p q ≫ Y.alpha p q`. This is exactly `t_D α = α' t_D`, written with
  Lean's composition convention.
- The f square is `hf`: `X.f p q ≫ tD (p+2) (q-1) = tE p q ≫ Y.f p q`.
- The g square is `hg`: `X.initialG p q ≫ tE p q = tD p q ≫ Y.initialG p q`.
  The dependency's `initialG` transports the type-zero g target to `(p,q)`;
  it is the node's degree-zero g, not a different map.
- Maps on every spectral-sequence page are the existential family `t r p q`.
  `pageCouple r` denotes actual page `r+2`, so `t 0 p q = tE p q` specifies
  the map on E₂. The following square states compatibility with the differential
  of bidegree `(r+2,-r-1)`.
- The kernel map `k`, its inclusion square, and the `derivedEProjection` square
  specify that each next-page map is induced by the preceding one on homology.
  These express a morphism of spectral sequences, rather than unrelated maps
  commuting individually with differentials.
- The conditional half-plane hypotheses occur inside the conclusion, so the
  page-morphism assertion needs no convergence assumption. For the source they
  are `q < a → IsZero (X.D p q)` and
  `(p < 0 ∨ q < a) → IsZero (X.E p q)`; for the target use the same formulas
  with `Y,b`. Different bounds `a,b : ℤ` are allowed.
- `L,M : LimitSubobjects` and `A,B : ∀ n, AlphaColimit ... n` supply the
  canonical limiting pages and diagonal colimits of the recorded convergence
  interface. `hA,hB` identify the colimit objects with `D 0 n`; the index-zero
  cocone equations normalize those identifications.
- The abutment map is `f n : (A n).obj ⟶ (B n).obj`. Its specified equality
  with `eqToHom (hA n) ≫ tD 0 n ≫ eqToHom (hB n).symm` states that it is
  precisely the node's map on the canonical abutments. Its cocone square at
  every integer p states the induced diagonal map, not an arbitrary lift.
- Preservation of every filtration step is the existential `lift` at each n,p,
  with `lift ≫ targetStep.arrow = sourceStep.arrow ≫ f n`. The two steps are
  exactly `(X.imageFiltration n (A n)).step p` and the corresponding Y step,
  from the dependency. This is the factorization definition of
  `f(F^p A^n) ⊆ F^p B^n` in an abelian category.
- `z` is the restriction of `tE` to limiting cycles, by its inclusion square.
  `tInf` is the induced quotient map, by its boundary-cokernel square. These
  characterize the infinite-page map induced by `tE`, with no arbitrary choice
  of that map.
- `gr p q` is the map on the actual associated graded pieces of the same image
  filtrations, characterized by the `toGradedPiece` square with `tD`.
- `e,e'` identify the infinite pages with these graded pieces; their respective
  `toPageInfinity`/`toGradedPiece` squares enforce the canonical identifications
  of `thm-sp-half-plane-convergence`, rather than arbitrary isomorphisms.
- The last square `(e p q).hom ≫ gr p q = tInf p q ≫ (e' p q).hom` is exactly
  the final compatibility claimed in the node, at total degree `n=p+q`.

Dependency declarations read and used:

- `def-sp-exact-couple`: `WeilConjectures.Algebra.Homology.ExactCouple.Basic`,
  `CategoryTheory.ExactCouple`, `derived`, `derivedIter`, `spectralSequence`.
  `Sheaf.CategoryTheory.ExactCoupleShifted.BigradedExactCouple` is the existing
  single-field compatibility view, and `Sheaf.CategoryTheory.ExactCouple`
  supplies its established `pageCouple`, `d`, and `derivedEProjection` API.
- `def-sp-filtration`: `WeilConjectures.CategoryTheory.Abelian.Filtration`,
  `CategoryTheory.DecreasingFiltration` and its `gr` construction. The existing
  `Sheaf.CategoryTheory.Filtration` extension supplies `step` and `gradedPiece`.
- `def-sp-convergence`: `Sheaf.CategoryTheory.ExactCoupleConvergence`,
  `CategoryTheory.BigradedExactCouple.ConvergesTo`, `LimitSubobjects`,
  `limitBoundary_le_cycle`, `pageInfinity`, `initialG`, `AlphaColimit`,
  `imageFiltration`, `toPageInfinity`, and `toGradedPiece`.
- `thm-sp-half-plane-convergence`: `Sheaf.CategoryTheory.HalfPlaneConvergence`,
  `CategoryTheory.BigradedExactCouple.halfPlaneConvergence`, including its
  index-zero normalization and canonical graded comparison squares.
- Proof-only import: `Sheaf.CategoryTheory.DerivedCoupleFunctoriality`,
  `CategoryTheory.BigradedExactCouple.CoupleMorphism` and
  `derivedCoupleFunctoriality`. Its signature supplies the page and limiting
  quotient squares used in proof steps 1 and 3.

Interface fault repaired: the node's `lead_note` records the withdrawal of the
old interface because `FilteredObject.HomPreservingSteps` is unavailable in the
compiled library. The source reader still displays a version containing it.
An initial attempt to use upstream `FilteredObject.Hom` exposed another published
interface discrepancy: the compiler calls the image filtration's type
`PBCDecreasingFiltration`, whereas the source reader displays `DecreasingFiltration`.
The final statement avoids either bundled-morphism interface and uses the actual
recorded image filtration's steps directly. No notion is redefined and no
comparison between distinct filtration types is assumed. The ordinary morphism
and its step-factorization witnesses express exactly the same preservation condition.

Edge cases checked before writing:

- All integer bidegrees and total degrees, including negative n,p,q, are allowed;
  no positivity assumption is added. Bounds a and b can differ or be negative.
- The zero couple and zero morphisms satisfy the stated squares and allow zero
  induced maps. No nonzero object, nonempty support, or nontrivial page is required.
- At r=0 the initial page is E₂ and the next-page projection gives E₃, with the
  correct `(2,-1)` differential. Every r is included by the natural-number index.
- For n below a (or b), the corresponding abutment is zero by the half-plane
  assumption. The normalization and step-factorization statements still apply.
- Steps at negative p and steps beyond the finite support are included. Empty
  graded pieces and zero limiting cycles do not require an exception.
- No countable coproducts, completeness of the category, or arbitrary lattice
  intersections are assumed: `AlphaColimit` and `LimitSubobjects` retain the
  dependency's universal-property formulations, supplied by half-plane convergence.

Searches for an exact existing statement:

- `msearch.py leansearch`: “a morphism of exact couples preserves the filtration
  on the abutment and induces the associated graded morphism of spectral sequences”
  returned eight bicomplex graded-object, homology-functor and homology-sequence
  results; none gives exact-couple abutment naturality.
- `msearch.py leanfinder`: “morphisms of exact couples induce morphisms of spectral
  sequences compatible with abutment filtration” returned eight homology-sequence
  and short-exact-sequence hits, including
  `HomologicalComplex.HomologySequence.mapComposableArrows₅`; none states this result.
- `msearch.py loogle`: `SpectralSequence.Hom` returned zero hits (unknown identifier).
- `msearch.py grep`: `ExactCouple|coupleMorphism` in Mathlib `Algebra/Homology`
  returned zero hits.
- Direct `rg` of the slopmaster2 `WeilConjectures` source for the node id and
  `coupleMorphism` returned no hit. The upstream-name inventory and current
  upstream source (read with `scompile.py --source`) do give
  `CategoryTheory.ExactCouple.Hom` and `Hom.spectralSequenceMap` in
  `WeilConjectures.Algebra.Homology.ExactCouple.Hom`. Their complete signatures
  cover the page-morphism clause, but neither states filtration preservation nor
  the associated-graded compatibility on the canonical half-plane abutments.
- Direct `rg` of `lean/Sheaf/CategoryTheory` found the withdrawn
  `ExactCoupleMorphism.lean` and its old consumers; it supplies the old statement
  but uses the unavailable interface. The node's binding is empty and its
  `lead_note` explicitly requests this restatement. Thus it is not an exact
  usable existing declaration to rebind.

Validation: the final file passed `scompile.py NK lem-sp-couple-morphism` both as
an isolated sandbox file and at its library module path, with no errors or warnings.
The only postponed proof is the named theorem `coupleMorphism`, whose docstring
contains the complete current DAG proof. No additional declarations are introduced.

## Second reading by NK

I independently opened the node, its Stacks source place, the dependency
declarations, and `ExactCoupleMorphism.lean`. The item-by-item rendering is:

- The common abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`,
  with independent universes. `X Y : BigradedExactCouple C 0` are the two exact
  couples, whose upstream structure has the node's bidegrees `(-1,1)`, `(2,-1)`,
  and `(0,0)`.
- `tD` and `tE` quantify over every integer bidegree. `hα`, `hf`, and `hg` are
  respectively the three structure-map squares; `initialG` is the degree-zero
  `g` map transported back to `(p,q)`, so `hg` has exactly the node's types.
- The existential `t` quantifies over every natural page index `r` (where
  `pageCouple r` is page `r+2`) and every integer bidegree. `t 0 = tE`, the
  differential square, and the kernel map `k` with its inclusion and derived
  projection squares are precisely the Stacks definition of a morphism of
  spectral sequences, including the induced next-page map.
- The half-plane part is under `∀ a b : ℤ`; its four implications are exactly
  `q < a` vanishing for each `D` and `(p < 0 ∨ q < a)` vanishing for each `E`,
  with the corresponding `b` conditions for `Y`. Thus no convergence assumption
  is imposed on the page-morphism part, and different bounds are allowed.
- `L,M`, `A,B`, and `hA,hB` render the limiting subobjects, diagonal colimits,
  abutment object identifications, and index-zero normalizations supplied by
  `halfPlaneConvergence`. The map `f` is transported `tD 0 n`; its step witnesses
  are exactly filtration preservation, and its cocone square gives the induced
  diagonal map at every `p`.
- `z` is the restriction of `tE` to limiting cycles, `tInf` is the induced
  boundary-cokernel quotient map, and `gr` is the associated-graded map. The
  `toGradedPiece` square, the two canonical `toPageInfinity` comparison squares,
  and the final square with `tInf` express exactly the node's compatibility under
  `E∞ ≅ gr`; no arbitrary map or identification is introduced.

Edge cases checked: all integer indices and negative bounds are admitted; `r = 0`
is the `E₂` page; zero couples and zero maps satisfy all displayed squares; empty
graded pieces and zero limiting cycle/boundary objects are allowed; `n = 0`,
negative total degrees, and the characteristic are unrestricted; no countability,
nonzero, finiteness, or universe-equality hypothesis is added.

For the one-definition check I searched the DAG, Mathlib, the local `Sheaf` tree,
and the slopmaster2 `WeilConjectures` tree with `msearch.py` LeanSearch,
LeanFinder, Loogle, and `rg`. The upstream `ExactCouple.Hom` and
`Hom.spectralSequenceMap` declarations cover only the page construction; no
declaration includes the half-plane abutment filtration and graded compatibility.
The existing local `ExactCoupleMorphism` file still contains the withdrawn
`FilteredObject.HomPreservingSteps` interface and fails the prescribed compiler,
so it is not a usable existing binding.

The only interface mismatch found was that withdrawn `HomPreservingSteps` record.
The worker's explicit witnesses
`∃ lift, lift ≫ targetStep.arrow = sourceStep.arrow ≫ f n` state the same
filtration-preservation notion and compile against the current dependency API; I
made no further statement or dependency changes. The node's `lean.statement` is
verbatim the theorem signature, the proof remains the named `sorry` only, and no
new definition or private notion was introduced.

## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProEtale/HypercoverExistence.lean` states
`AlgebraicGeometry.exists_proetale_hypercover_single_affine` with `sorry` proof. It
uses the small pro-etale site `Scheme.ProEt` over a scheme `X`.

The hypotheses are rendered by `(X : Scheme)`, `(U : X.ProEt)`,
`hUqc : CompactSpace U.left`, and `hUqs : QuasiSeparatedSpace U.left`, which are
the scheme-level meanings of “quasi-compact, quasi-separated object”.

The three clauses are rendered as follows.

1. The finite product clause is
`∀ (I : Type u) [Finite I] (D : I → Type u) [∀ i, CommRing (D i)]
[∀ i, IsWContractibleRing (D i)], IsWContractibleRing (∀ i, D i)`.  The dependent
Pi ring is the finite product, and `Finite I` includes the empty product.

2. The singleton-cover clause is
`∀ (V : X.ProEt), CompactSpace V.left → ∃ D f hf g, ...`, where
`D : CommRingCat`, `f : Spec D ⟶ X`, `hf : WeaklyEtale f`, and
`g : ProEt.mk f ⟶ V`.  The covering assertion is
`Presieve.singleton g ∈ (Scheme.ProEt.precoverage X) V`, the small-site
pro-etale covering predicate.

3. The hypercover clause existentially gives a simplicial object
`W : SimplicialObject X.ProEt` and an augmentation
`ε : W ⟶ (Functor.const (SimplexCategoryᵒᵖ)).obj U`.  For every degree `r`, it
gives a ring `D : CommRingCat`, a weakly etale map `Spec D ⟶ X`, and the equality
`W _⦋r⦌ = ProEt.mk f`; it also gives the section-lifting condition from
`proetale_weakContractible_equivalences` for every epimorphism onto the
representable sheaf of `W _⦋r⦌`.  The degree-zero augmentation is a singleton
cover.  For every `r`, a cone `c` over
`SimplicialObject.properFaceDiagram W (r + 1)` and a map
`μ : W _⦋r + 1⦌ ⟶ c.pt` are supplied, with `Nonempty (IsLimit c)`, singleton-cover
membership for `μ`, and the projection equations
`μ ≫ c.π.app (op a) = W.map a.obj.hom.op` for every proper face `a`.  This is the
finite proper-face limit presentation of the matching object; the recorded
coskeleton dependency identifies it with the degree matching object of
`cosk_r sk_r W`.

Dependencies used:

- `sk-def-pe-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt`,
  `Scheme.ProEt.precoverage`, and `Scheme.ProEt.mk` from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `det-pe-wlocal-strict-contractible`: existing
  `WeilConjectures.RingTheory.ProEtale.WContractible.IsWContractibleRing`.
- `det-pe-weak-contractible-equivalences`: existing
  `Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences` declaration
  `AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences`; its first
  equivalent condition is written explicitly in the degree clause.
- `def-weil-pbc-scheme-conventions`: convention-only node; no declaration is
  needed.
- `def-weil-affine-spectrum`: Mathlib `AlgebraicGeometry.Spec`.
- `def-weil-pbc-simplicial-object`: Mathlib
  `CategoryTheory.SimplicialObject`.
- `def-weil-pbc-simplicial-coskeleton`: Mathlib truncated simplicial objects,
  truncation, and coskeleton; the proper-face cone is the matching-object form
  used to state the covering map without adding a Kan-extension hypothesis.

Edge cases checked: `Finite I` permits `I = Empty` (the zero-ring product); the
cover clause permits `V` empty; `r = 0` uses the degree-zero augmentation and the
proper-face cone for degree one; and the statement permits every simplicial degree
to be the empty affine spectrum (`Spec 0`).  The source does not require `X` to be
quasi-compact or quasi-separated, so no such hypotheses were added.

Searches made:

- `msearch.py ... leanfinder "hypercovers by single affine w-contractible objects in the
  pro-etale site"`:
  returned only generic `OneHypercover`/`QuasiCompactCover` and affine-cover results,
  with no matching theorem.
- `msearch.py ... loogle "Scheme.ProEt, SimplicialObject, properFaceDiagram, IsWContractibleRing"`:
  rejected the query because `Scheme.ProEt` is not a Loogle identifier; this gives
  no absence conclusion.
- `msearch.py ... grep "Hypercover|hypercover|w.?contractible" Mathlib/CategoryTheory/Sites`:
  no item-specific match.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for pro-etale, w-contractible,
  hypercover, simplicial, and coskeleton names found only the recorded dependency
  declarations and generic hypercover infrastructure; no declaration of this
  theorem exists.
- The node’s recorded Mathlib searches (LeanSearch, LeanFinder, Loogle and grep)
  were read and agree that no exact item statement exists.

No statement correction or new definition node was needed.  The module compiles
cleanly with `scompile.py`; the only expected warning is the postponed theorem
proof.

## Earlier second reading (a previous round; superseded)

Self-check completed by N5: the module imports only Mathlib/WeilConjectures/Sheaf
modules used by the statement, binds all universes and variables explicitly, and
contains exactly one postponed theorem proof. The node `lean` record has the exact
module, file, declaration, branch, date, and signature. `scompile.py` compiled the
file successfully. Edge cases and all dependency declarations were checked above.


## Second reading by N5

Independent second reading of the sandbox node and module, the shared dependency
nodes and their declaration sources, and Stacks `proetale.tex`,
`lemma-w-contractible-hypercovering` (Tag 09A1), especially (2) and its qcqs-subsite
proof. I also read `hypercovering.tex`, `lemma-w-contractible` (094K), and
`remark-take-unions-hypercovering-X` (0DB2). The source assumes only that `X` is a
scheme. This review supersedes the earlier self-check and the inaccurate clause
renderings in the Worker report above.

Object, hypothesis and conclusion inventory, with final Lean and verdict:

1. Base scheme `X`: `(X : Scheme.{u})`. The site is the recorded
   `AlgebraicGeometry.Scheme.ProEt`, read in Mathlib `Sites/Proetale.lean`:
   `MorphismProperty.Over @WeaklyEtale ⊤ X`. All arrows are X-morphisms, and the
   precoverage is the comap of the actual scheme pro-etale precoverage. PASS:
   the small pro-etale site, with its finite affine-refinement covering condition;
   no quasi-compactness, quasi-separatedness, characteristic or Noetherian
   assumption on `X`.
2. Object `U` of that site: `(U : X.ProEt)`. Its underlying scheme is `U.left`.
   Quasi-compactness is `hUqc : CompactSpace U.left`; quasi-separatedness is
   `hUqs : QuasiSeparatedSpace U.left`. These are absolute properties of `U`,
   as in the source, rather than relative properties of `U.hom`. PASS.
3. Clause 1 introduces a finite family of commutative w-contractible rings.
   `∀ (I : Type u) [Finite I] (D : I → Type u) [∀ i, CommRing (D i)]
   [∀ i, IsWContractibleRing (D i)], IsWContractibleRing (∀ i, D i)`.
   The Pi commutative ring is their product. I opened the recorded upstream class
   `IsWContractibleRing`: it extends `IsWStrictlyLocalRing` with
   `ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))`. This is the
   dependency node's geometric definition, including its closed-point/local-ring
   requirements. PASS; no field or nontrivial-ring restriction.
4. Clause 2 is universal in every quasi-compact site object `V`:
   `∀ (V : X.ProEt), CompactSpace V.left → ...`. Its witnesses are a commutative
   ring `D : CommRingCat.{u}`, a weakly etale structure map `f : Spec D ⟶ X`
   with `hf : WeaklyEtale f`, and an arrow
   `g : @Scheme.ProEt.mk X _ f hf ⟶ V`. The final conjunction is
   `IsWContractibleRing D ∧ Presieve.singleton g ∈ (Scheme.ProEt.precoverage X) V`.
   PASS after repair: the submitted statement omitted the first conjunct. There
   is no quasi-separatedness assumption on `V`, as required. The witnesses are
   chosen after `V`; the ring is not fixed in advance.
5. Clause 3 introduces a simplicial object augmented over `U`:
   `∃ W : SimplicialObject (Over U), ...`. Mathlib's recorded `SimplicialObject`
   is a functor from `SimplexCategoryᵒᵖ`; its objects in the slice carry maps to
   `U`, and its arrows commute with those maps. Thus the augmentation in every
   degree is `(W _⦋r⦌).hom`, and all face and degeneracy identities are part of
   the functor data. PASS after repair: using the slice also corrects the base
   of all matching limits.
6. For every degree, the witnesses `D`, `f`, `hf` satisfy
   `IsWContractibleRing D ∧ (W _⦋r⦌).left = @Scheme.ProEt.mk X _ f hf`.
   PASS after restoring the omitted ring condition. This is precisely a spectrum
   of a w-contractible commutative ring, hence affine. `Spec` is the recorded
   Mathlib `AlgebraicGeometry.Spec` from `AlgebraicGeometry/Scheme.lean`; I opened
   its signature, and no private spectrum construction is used. Equality is
   achievable by choosing spectral representatives and conjugating the operators,
   as the node's final proof step explicitly specifies.
7. The additional stated conclusion that every term is weakly contractible is
   `∀ F φ [Epi φ], ∃ s, s ≫ φ = 𝟙 _`, with target the full-site sheaf
   `(Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj (W _⦋r⦌).left`.
   I opened `Scheme.proetale_weakContractible_equivalences`: this is exactly its
   first equivalent condition, with the same sheaf universe, and its final
   assertion applies to the spectral witnesses here. PASS: weak contractibility
   is on the full site over `X`, not on a different slice topos. The explicit
   ring condition is still necessary; sheaf projectivity does not replace it.
8. Degree zero is
   `Presieve.singleton (W _⦋0⦌).hom ∈ (Scheme.ProEt.precoverage X) U`.
   PASS: the actual augmentation is a singleton cover.
9. For every `r : ℕ` there are a cone `c` on
   `SimplicialObject.properFaceDiagram W (r + 1)` and
   `μ : W _⦋r + 1⦌ ⟶ c.pt`, with `Nonempty (IsLimit c)`, the cover assertion
   `Presieve.singleton μ.left ∈ (Scheme.ProEt.precoverage X) c.pt.left`, and
   `∀ a, μ ≫ c.π.app (Opposite.op a) = W.map a.obj.hom.op`.
   PASS after repair: these are limits in `Over U`, not in `X.ProEt`. In
   particular degree one is `W₀ ×_U W₀`, not `W₀ ×_X W₀`. The equations force
   the canonical matching map; it is not an arbitrary covering arrow. I opened
   `ProperFaceMatchingObject.lean`, including the definition selecting injective
   proper faces and the degree-one and higher-degree signatures. The proper-face
   and all-lower-ordinal-map limits agree: factor a lower ordinal map into a
   surjection followed by its injective image; extend a compatible proper-face
   family using the degeneracy for the surjection. Restriction and extension
   are mutually inverse and natural. This is also step 7 of the node and the
   revised docstring. I read the recorded coskeleton/truncation/Kan-extension
   interfaces in Mathlib and `exists_coskeleton_matching_tuples`. No global
   existence assumption for a chosen Kan-extension functor is added.

Edge cases: `Finite I` allows `I` empty, so the product ring is the zero ring;
no `Nontrivial` or `Nonempty` assumption occurs. Empty `V`, empty `U` and empty
`X` are permitted. For empty `V` the zero-ring spectrum supplies the empty
singleton cover. All degrees, including zero, are quantified; the degree-one
proper-face category consists of the two vertices and the slice computes their
product over `U`. There is no degree-minus-one convention hidden in the formula.
All commutative characteristics are allowed. `u` is arbitrary, schemes and
coordinate rings share that size convention, and the recorded representable
sheaf lives in `Type (u + 1)` over the site of object universe `u + 1` and
morphism universe `u`. Finite index types in `Type u` encode every finite cardinal.
The unused declared universe `v` was removed and `set_option autoImplicit false`
added, so the clean compile also verifies that no variable or universe is unbound.

Independent searches (2026-10-17):

- LeanSearch via `msearch.py N5 det-pe-hypercover-existence leansearch
  "existence hypercover affine weakly contractible proetale"`: eight generic
  results, principally `GrothendieckTopology.OneHypercover`, its constructors
  and nonemptiness, and affine open covers. No theorem with the three clauses.
- LeanFinder via the same wrapper: "simplicial resolution of a quasi compact
  quasi separated scheme by projective affine pro etale objects" returned
  `QuasiCompactCover`, etale objects and affine-transition-limit covers;
  "finite products w contractible rings singleton affine hypercovering proetale"
  returned one-hypercover gluing, formally etale finite products, and generic
  covers. No exact statement or missing alternative notion.
- Wrapper grep `exists.*hypercover|hypercover.*affine|wContractible.*[Pp]i`
  over Mathlib returned zero hits. Direct `rg` searches used `hypercover`,
  `contractible`, `affine`, and their combinations over the full upstream
  `WeilConjectures`, Mathlib, shared `lean/Sheaf` and shared `lean/WeilConjectures`.
  I opened the closest shared theorem,
  `Scheme.ProEt.exists_affine_weaklyContractible_hypercover` in
  `ProEtaleAffineAcyclicHypercover.lean`: it supplies affine/projective terms and
  sheaf-epimorphic matching arrows, but neither the finite-product assertion nor
  clause 2 nor w-contractible coordinate-ring witnesses. It is not the node's
  full statement. `FiniteSplitHypercoverExistence.lean` is etale, rather than
  the present pro-etale affine w-contractible result. Generic Mathlib zero/one
  hypercovers and the upstream pro-etale continuity open one-hypercovers do not
  assert existence in every simplicial degree with these ring conditions.

Repairs made: restored `IsWContractibleRing D` in clauses 2 and 3; encoded the
augmentation and all matching cones in `Over U`; retained full-site weak
contractibility and covering predicates on underlying arrows; replaced the
non-stepwise proof summary by all nine proof steps with their DAG citations;
added the recorded, stated proof-dependency imports for WContractibleAffineCover,
ProEtaleQcqsFiniteFamilyGeometry, SiteFiniteBasisHypercoverExistence and
CoskeletonMatchingTuples; bound all names explicitly and removed unused `v`.
Added the already landed `lem-weil-pbc-matching-object-proper-faces` to
`stmt_deps` because its diagram declaration is used directly. Updated the node's
`lean.statement` verbatim from the final theorem signature.

No new definition node or dependency module is needed: the existing proper-face,
slice, spectrum and weak-contractibility interfaces suffice. No natural-language
statement correction was needed; the node already has the right ring and
relative-matching requirements. There is one theorem and its proof is exactly
`sorry`, no definitions, no hollow data and no proved auxiliaries. All delivered
Lean lines are at most 100 characters. The final file compiled cleanly through
`scompile.py N5 det-pe-hypercover-existence
lean/Sheaf/AlgebraicGeometry/ProEtale/HypercoverExistence.lean`; both sandbox and
library-name checks passed, with no errors or warnings.

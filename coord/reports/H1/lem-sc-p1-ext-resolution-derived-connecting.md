## Worker report

The module `Sheaf.CategoryTheory.Abelian.ExtResolutionDerivedConnecting` states
`CategoryTheory.InjectiveResolution.extMk_resolution_connecting_eq_triangle`, with proof
`sorry`. It expresses equality of the two boundary maps on cocycle representatives, using
Mathlib's existing inverse comparison `InjectiveResolution.extMk`. No definition is added.

Hypothesis and clause correspondence:

- The abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`; enough injectives
  is `[EnoughInjectives C]`. The source object is `M : C`.
- The short exact sequence is `{S : ShortComplex C} (hS : S.ShortExact)`, with objects
  `S.X₁`, `S.X₂`, `S.X₃` and arrows `S.f`, `S.g`. The specified distinguished triangle
  is `hS.singleTriangle`, whose third arrow is `hS.singleδ`.
- The resolution description is given by `RA`, `RB`, `RC : InjectiveResolution` of
  the respective objects. The complex maps `i`, `p`, their composite `hip`, augmentation
  compatibility `hιi`, `hιp`, and degreewise short exactness `hexact` describe an arbitrary
  horseshoe resolution. These are universally quantified choices for computing the
  map in the statement, rather than additional restrictions on the original sequence.
  Each degree splits, since `RA.cocomplex.X k` is injective. The original node's proof
  uses precisely this resolution computation (via its generic bridge dependency).
- The degree is `n : ℕ`, covering every integer degree at least zero in `def-pc-ext`.
  The resolution class is represented by `c : M ⟶ RC.cocomplex.X n` and `hc` says
  it is a cocycle. `b` with `hb` is any lift of `c` to the middle complex. `a`, `ha`,
  `hba` express the cocycle obtained by factoring the differential of `b` through `i`.
  Its class is the ordinary positive snake/cohomology connecting class. In particular,
  `ha` records the cocycle condition required by the existing constructor, not an
  additional assumption on `c`: it follows from the complex identities and injectivity
  of the degreewise monomorphism `i`. Lifts `b` and factors `a` exist for every `c`
  by degreewise splitting and exactness. All representatives and all lifts are allowed.
- The canonical comparison is rendered by `RC.extMk c (n+1) rfl hc` and
  `RA.extMk a (n+1+1) rfl ha`. Reading its full definition shows that `extMk` is
  `extEquivCohomologyClass.symm` applied to the cocycle class; the additive version
  is `extAddEquivCohomologyClass.symm`. Thus the displayed equality says exactly
  that the comparison carries the resolution boundary class to the triangle boundary.
  `extMk_surjective` ensures that testing all cocycles tests every Ext class; the
  construction respects coboundaries (`extMk_eq_zero_iff`).
- The derived-category description is `.hom` of these Ext elements, under Mathlib's
  `Ext.homAddEquiv`. The displayed left side is `homologySequenceδ` for
  `preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor C 0).obj M))` and
  `hS.singleTriangle`, evaluated at the compared input class. Its output equals the
  compared resolution connecting class on the right.
- This connecting map is exactly the requested shifted postcomposition: Mathlib's
  `Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply` identifies it
  with `(x.comp hS.extClass rfl).hom`; `hS.extClass_hom = hS.singleδ`, and the
  definition of shifted composition includes the canonical identification of the
  two successive shifts with shift by `n+1`. This handles the required sign convention.
- `letI := HasExt.standard C` and `letI := HasDerivedCategory.standard C` select
  the standard constructions in universe `max u v`. Neither is an extra hypothesis
  or a restriction of the category's object/hom universes.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-sp-injective-resolutions`: `CategoryTheory.InjectiveResolution`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, including its injective,
  quasi-isomorphism, and homology fields. Enough injectives is the Mathlib class
  `CategoryTheory.EnoughInjectives`.
- `def-pc-ext`: `CategoryTheory.Abelian.Ext` and `Ext.homAddEquiv`,
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`.
- `lem-weil-pbc-ext-via-injective-resolution`:
  `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass`,
  `Mathlib.CategoryTheory.Abelian.Injective.Ext`; its underlying equivalence and
  `extMk` definition supply the exact cocycle/roof comparison, without a private copy.
- `lem-sf-derived-ses-triangle`:
  `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`,
  `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`, together with its
  existing `singleTriangle` and `singleδ` constructions.
- `lem-sp-long-exact-of-triangle`: this node has status `mathlib`, so its
  `mathlib_match` is the authoritative declaration record as required by the brief.
  It names `CategoryTheory.Functor.homologySequence_exact₂` and, one per remaining
  clause, `homologySequence_exact₃`, `homologySequence_exact₁`, and
  `homologySequenceδ_naturality`, in
  `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`. These were read in full,
  including the ambient binders. With `Functor.ShiftSequence.tautological`, the
  shift functors are exactly `K ↦ Φ(K[n])`, so there is no additional hypothesis.
  The main module uses their `homologySequenceδ` construction through the Ext
  exact-sequence API. The stale `lean` record points to a sheaf specialization but
  is irrelevant for this Mathlib leaf; no dependency module or record change is needed.


Edge cases: `n=0` uses degree-zero cocycles without any negative-degree denominator;
`M=0` and zero end objects give zero classes and maps; split sequences have zero
boundary in both descriptions. No assumption excludes a nonsplit sequence or positive
characteristic. The category and hom universes are independently quantified. Changes
of resolution, representative, or lift remain universally allowed. There is no
STATEMENT-DISPUTED finding and no correction of the item's mathematical statement.

Searches (all remote service calls are logged in sandbox `searches.jsonl`):

- LeanFinder: `injective resolution Ext connecting map agrees derived category triangle boundary`.
  Eight hits: resolution `extMk` API and the derived-side
  `preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply`, but no comparison
  with the lifted-differential injective-resolution connecting map.
- Loogle: `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass`.
  Five hits supply the canonical additive comparison, not its boundary compatibility.
- LeanSearch: `Ext injective resolution connecting homomorphism cocycle lift differential`.
  Service unavailable (Internal Server Error); used LeanFinder, Loogle, and grep instead.
- Mathlib grep via msearch: `extMk.*(δ|connect)|connecting.*injective|injective.*connecting`
  under CategoryTheory: zero hits. Local reads of `Injective/Ext.lean`,
  `DerivedCategory/Ext/ExactSequences.lean`, `RightDerived.lean`, and
  `HomComplexCohomology.lean` found no resolution/triangle boundary comparison.
- `rg` in `WeilConjectures` and `lean/Sheaf` for Ext/resolution/connecting patterns,
  and for the item id: no matching theorem; unrelated direct-image and tensor modules.
  `rg` for the chosen full theorem name in Mathlib, source, project, and
  `dag/lean_names_upstream.json`: no collision.
- Loogle: `CategoryTheory.Functor.homologySequenceComposableArrows₅_exact`:
  one exact general homological-functor result. Mathlib grep via msearch:
  `homologySequenceδ_naturality|homologySequenceComposableArrows₅_exact`
  in CategoryTheory/Triangulated: the two general declarations were found and read,
  together with all three exactness signatures and the module docstring.

Source inspected online because the local Stacks source is absent:
[Tag 05TE](https://stacks.math.columbia.edu/tag/05TE) and
[Tag 06XR](https://stacks.math.columbia.edu/tag/06XR).
The module docstring retains both of the node's proof steps and all their cited nodes.
The server compiled the module cleanly in 1.5 seconds.


## Second reading by H1

I independently opened the node copy, the entire proposed module, all six statement
 dependency nodes, and the Mathlib declarations below. The node is unchanged mathematically;
there is no stage-2 `statement_change`, new definition node, or dependency module to review.
The following is my object/hypothesis/conclusion inventory, matched to the actual signature.

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| An arbitrary abelian category with enough injectives | `{C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]` | Exact; object and hom universes are independent. |
| An object M | `(M : C)` | Exact; no projectivity or finiteness assumption. |
| A short exact sequence with objects A, B, C and its two arrows | `{S : ShortComplex C} (hS : S.ShortExact)`; `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g` | Exact; the short complex includes the zero composite and ShortExact supplies exactness, mono, epi. |
| Its distinguished triangle with boundary w | `hS.singleTriangle` in the displayed conclusion | Exact; its objects are the degree-zero single objects, arrows the single-functor images, and third map `hS.singleδ`. |
| Ext in every nonnegative degree | `(n : ℕ)` and `extMk` in degree n and n+1 | Exact; the cited Ext definition explicitly uses integers i >= 0, equivalently naturals. |
| The injective-resolution/right-derived description | `RA`, `RB`, `RC : InjectiveResolution` and complex maps `i`, `p` | Exact computational presentation; these are universally quantified resolution choices, not a restriction to particular resolutions. |
| A horseshoe short exact sequence resolving S | `hip`, `hιi`, `hιp`, `hexact` | Exact computational data: zero composite, both augmentation squares, and short exactness in every degree. Such data exist by the injective horseshoe construction under the existing enough-injectives hypothesis. |
| An arbitrary input class and its resolution boundary | `c`, `hc`, `b`, `hb`, `a`, `ha`, `hba` | Exact representative presentation; `hc` is the cocycle equation, `hb` lifts through p, `hba` is d(b)=i(a), and `ha` types the resulting cocycle. |
| The canonical comparison of resolution cohomology with derived Ext | `RC.extMk c (n + 1) rfl hc` and `RA.extMk a (n + 1 + 1) rfl ha`, followed by `.hom` | Exact; `extMk` is the inverse of the dependency's cohomology comparison on a cocycle class, and `.hom` is `Ext.homAddEquiv`. |
| Equality with the derived-triangle homology connecting map | LHS `preadditiveCoyoneda ... .homologySequenceδ hS.singleTriangle ...`, RHS `(RA.extMk a ...).hom` | Exact equality on every input class, rather than merely exactness of a sequence. |
| Explicit formula xi maps to w[n] composed with xi | The same LHS, by `Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply` | Exact; this declaration expands to `x ≫ T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' ...).inv.app _`, the required shifted postcomposition with its canonical shift identification. |

Why the representative binders do not weaken the conclusion: for each k, the mono
`i.f k` has injective source `RA.cocomplex.X k`, so it splits. The degreewise short
exact sequence therefore splits and `p.f k` has a section. Every cocycle c has a lift
b, regardless of whether M is projective. The equation d(c)=0 and the chain-map
identity show that d(b) factors uniquely through `i.f (n+1)`, giving a. Applying the
next differential and cancelling the monomorphism `i.f (n+2)` proves ha. Thus these
hypotheses merely spell out the standard positive lifted-differential connecting
construction. `InjectiveResolution.extMk_surjective` (Ext.lean:207) supplies a cocycle
for every Ext element, including n=0. Equality is asserted for every such choice, and
hence for the entire connecting homomorphism. This also checks the order of quantifiers:
first the category, object and sequence, then arbitrary resolution data, degree, and
representatives, then the equality; no specially favourable choices are selected.

Source reading: the local repository has no `literature/stacks-project/derived.tex`.
I read the Stacks pages [05TE](https://stacks.math.columbia.edu/tag/05TE) and
[06XR](https://stacks.math.columbia.edu/tag/06XR), and independently fetched and read
[derived.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex)
at `lemma-right-derived-delta-functor`, `lemma-compute-ext-resolutions`, and
`lemma-derived-canonical-delta-functor`. Tag 05TE assumes an additive functor between
abelian categories with an everywhere-defined right derived functor; here Hom(M,-)
is additive and left exact and enough injectives supplies that existence. Its extra
acyclic-embedding condition belongs to universality, not an extra hypothesis of this
comparison. Tag 06XR assumes an abelian category and an injective resolution, with no
ring, characteristic, Noetherian or scheme assumption. The source's canonical SES
boundary is `-p q^{-1}` in its cone convention; the positive lifted-differential
boundary is consistent with that convention. The Lean derived boundary is the actual
canonical `singleδ`, not an arbitrary third arrow or a renamed map with a chosen sign.

Dependency audit: I read `Abelian` (Basic.lean:112), the full `InjectiveResolution`
structure (Resolution.lean:43), and its injectivity and quasi-isomorphism fields;
`Ext` (Ext/Basic.lean:118), `HasExt.standard` (92), and `homAddEquiv` (388);
`extEquivCohomologyClass` (Injective/Ext.lean:40),
`extAddEquivCohomologyClass` (78), `extMk` (130), `extMk_hom` (180), and
`extMk_surjective` (207); `singleδ`, `singleTriangle`, and
`singleTriangle_distinguished` (SingleTriangle.lean:45,55,77); and
`homologySequenceδ`, its naturality, and all three exactness signatures
(HomologicalFunctor.lean:174,182,218,227,235), with their ambient binders.
The last dependency has status `mathlib`: its general Mathlib match supplies the
notion, while its old source-repository `lean` record is a sheaf specialization.
The module correctly uses the general Mathlib API and needs no private or dependency
copy. In Ext/ExactSequences.lean:49 I also read
`preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply`, which directly equates
the displayed derived boundary with composition by `hS.extClass`.
The standard Ext and derived-category instances are available for every such category
in universe `max u v`; they are constructed inside the proposition and add no instance
hypothesis. No missing notion or delivery dependency hole was found.

Edge cases: n=0 is included and uses the degree-zero cocycle comparison, with no
negative-degree predecessor assumed. A zero M, zero end object, or entirely zero
sequence remains allowed; split sequences yield the zero boundary. Empty schemes are
covered when instantiated in their module categories, and no scheme or nonempty-index
condition occurs in this categorical statement. There is no index-set binder to restrict.
No restriction to characteristic zero, a field, a finite category, or equal universes
is introduced. Negative degrees are outside the cited nonnegative Ext definition.

Independent searches, using different wording from the first reader:

- LeanFinder via `msearch.py`: `short exact sequence injective resolutions lift cocycle
  differential boundary Ext`. Eight hits, all resolution constructors/comparison lemmas
  and their projective analogue; none states this boundary compatibility.
- Loogle via `msearch.py`: `CategoryTheory.InjectiveResolution.extMk`. Twelve hits,
  including zero/add/sub/neg/scalar and composition APIs, surjectivity and the roof
  formula; no connecting-map comparison.
- LeanSearch via `msearch.py`: `connecting homomorphism Ext computed from a degreewise
  split short exact sequence of injective resolutions`. Unavailable (Internal Server
  Error); no mathematical verdict is inferred from this failed service call.
- Independent `rg` on Mathlib CategoryTheory and Algebra/Homology, the source
  `WeilConjectures`, the project's `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `ext.*(boundary|connecting)`, `(boundary|connecting).*ext`, `extMk`,
  `injective.*connecting`, `resolution.*boundary`, `boundary.*resolution`,
  `connecting.*resolution`, and the proposed declaration name. Mathlib contains the
  separate Ext resolution and derived long-exact-sequence APIs read above; no combined
  theorem was found. Source/project hits for boundary and extension concern other
  geometry. There is no collision for the proposed declaration name.

Mismatches and repairs: none found in the node-to-Lean correspondence, sign, dependencies,
or conventions. I preserved the Lean and node records and appended only this independent
reading. Both docstrings name the source and blueprint id; the theorem docstring carries
both proof steps with all cited dependencies. The sole theorem proof is `sorry`, there
are no new definitions, and the arithmetic proof used as a shift-index argument is only
bookkeeping. All variables and universes are bound. The widest Lean line has 96 characters.
I checked programmatically that `lean.statement` equals the file's signature verbatim.
The prescribed `scompile.py H1 lem-sc-p1-ext-resolution-derived-connecting ...` compiled
the module cleanly on the server in 1.5 seconds with exit code 0 and no warnings.

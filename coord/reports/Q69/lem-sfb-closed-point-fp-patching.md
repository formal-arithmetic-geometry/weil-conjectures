## Worker report

Item: `lem-sfb-closed-point-fp-patching`. The module
`Sheaf.AlgebraicGeometry.ClosedPointFPPatching` states
`AlgebraicGeometry.finitePresentation_closedPoint_patching`, with its proof exactly
`sorry`. Its only other declaration, `AlgebraicGeometry.overPullbackOverlapIso`, is a
fully constructed canonical comparison of iterated restrictions, built from
`Over.pullbackComp`, the equation `pullback.condition`, and `eqToIso`. It contains
no postponed data or new proof obligation. Both declarations carry this item's
blueprint identifier; the theorem docstring includes every proof step and its
DAG citations. No statement or dependency correction is needed. Only `lean` changes
in the copied existing node.

The source read is `literature/stacks-project/limits.tex`,
`lemma-glueing-near-closed-point` (Tag 0BPA), and
`lemma-glueing-near-point-properties` (Tag 0EY3). The latter's descent-and-locality
argument applies to the smooth and immersion properties using the individual tags
specified in the node. There is no assumption that an object is separated.

Hypothesis and clause correspondence (write `j` in this report for the actual term
`Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime m)))`):

- A Noetherian commutative ring is `(D : Type u) [CommRing D]
  [IsNoetherianRing D]`. A maximal ideal is `(m : Ideal D) [m.IsMaximal]`.
  The point is literally the prime-spectrum point `⟨m, inferInstance⟩`.
- `S` is `Spec (CommRingCat.of D)`; the theorem takes an open `U : S.Opens`
  with `hU : (U : Set S) = {⟨m, inferInstance⟩}ᶜ`, specifying exactly the
  complement named in the node. This does not impose another geometric condition:
  maximality makes that singleton closed, by
  `PrimeSpectrum.isClosed_singleton_iff_isMaximal`, so this open always exists.
- `T` is `Spec (.of (Localization.AtPrime m))`, with its canonical map `j`
  displayed explicitly everywhere in the statement. The overlap is the chosen
  Mathlib fibre product `pullback U.ι j`. Its projections to `U` and `T` are
  `pullback.fst U.ι j` and `pullback.snd U.ι j`. This is canonically the node's
  `V`: pullback of an open is its inverse image, and the only prime of `D_m`
  contracting to `m` is its maximal ideal. Indeed any such prime contains the
  image of `m`, which generates the maximal ideal of `D_m`, hence equals it.
  Thus the inverse image of the complement of `m` is precisely the punctured
  local spectrum, including when that open is empty. Using this canonical fibre
  product is the standard equivalent presentation of the same overlap scheme.
- A scheme over a base `Z` is `Over Z`, its structure map is `.hom`, and its
  morphisms are slice morphisms. Finite presentation is always the explicit
  conjunction `LocallyOfFinitePresentation X.hom ∧ QuasiCompact X.hom ∧
  QuasiSeparated X.hom`, never mere local finite presentation or finite type.
  All quantified objects of `FP` have exactly these hypotheses, and every glued
  output satisfies the same conjunction.
- Pullback of objects and arrows is exactly Mathlib's `Over.pullback`, with
  `.obj`, `.map`, and `.mapIso`-compatible slice isomorphisms. These are not
  independently supplied restriction maps. Their preservation of the three
  finite-presentation conditions is Mathlib's base-change permanence, so these
  restrictions take objects of `FP` to objects of `FP`.
- A patching triple is quantified as `XU`, `XT`, the two finite-presentation
  conjunctions, and an isomorphism `α` in `Over (pullback U.ι j)` between their
  respective base changes. Being a slice isomorphism enforces that it is over
  the overlap, rather than merely an isomorphism of the underlying schemes.
- The first conclusion conjunct is essential surjectivity: it produces a global
  finite-presentation object `X` and slice isomorphisms `eU` and `eT` to the two
  given objects. Its equation
  `map eU.hom ≫ α.hom = (overPullbackOverlapIso U.ι j X).hom ≫ map eT.hom`
  uses the respective overlap pullback functors. It says exactly that the
  prescribed `α` is induced by these identifications, including its value, not
  just the existence of some overlap isomorphism.
- The second conjunct is full faithfulness: for arbitrary finite-presentation
  `X,Y` and slice morphisms `aU,aT`, the displayed square with the canonical
  comparisons on `X` and `Y` is their compatibility. It concludes
  `∃! a : X ⟶ Y, (Over.pullback U.ι).map a = aU ∧
  (Over.pullback j).map a = aT`. Existence and uniqueness are both present.
  Essential surjectivity together with this unique-lifting assertion is exactly
  equivalence of the restriction functor to the stated triple category; no
  alternative category or extra choice of equivalence is substituted.
- The third conjunct quantifies each global finite-presentation `X`. Its first
  equivalence is `Smooth X.hom ↔ Smooth ((Over.pullback U.ι).obj X).hom ∧
  Smooth ((Over.pullback j).obj X).hom`. Its second is the same equivalence with
  `IsSeparated`, whose Mathlib definition is that `pullback.diagonal` is a
  closed immersion. Both implications for both properties are present.
- The fourth conjunct quantifies arbitrary finite-presentation `X,Y` and
  `a : X ⟶ Y`. Its two equivalences apply `IsOpenImmersion` and
  `IsClosedImmersion` to `a.left` and to the underlying maps of its two canonical
  base changes. These are morphism properties of the arrow, not properties of
  the structure maps of `X` or `Y`. No separatedness, smoothness, or additional
  finiteness hypothesis on `a` is added.

Recorded statement dependencies used, after reading their declarations and
source docstrings:

| Node | Module | Declaration used |
| --- | --- | --- |
| `def-weil-affine-spectrum` | `Mathlib.AlgebraicGeometry.Scheme` | `AlgebraicGeometry.Spec`, `Spec.map` |
| `def-weil-pbc-localization-at-prime` | `Mathlib.RingTheory.Localization.AtPrime.Basic` | `Localization.AtPrime` |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme` | `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| `def-sbc-locally-finite-presentation` | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` | `AlgebraicGeometry.LocallyOfFinitePresentation` |
| `def-pc-fibre-product` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `pullback`, `pullback.fst`, `pullback.snd` (publicly imported through the pullback APIs) |
| `def-sbc-smooth-morphisms` | `Mathlib.AlgebraicGeometry.Morphisms.Smooth` | `AlgebraicGeometry.Smooth` |
| `def-weil-closed-immersion` | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` | `AlgebraicGeometry.IsClosedImmersion` |
| `def-weil-open-immersion` | `Mathlib.AlgebraicGeometry.OpenImmersion` | `AlgebraicGeometry.IsOpenImmersion` |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` | `AlgebraicGeometry.QuasiCompact` (from its imported `Morphisms.QuasiCompact`) |
| `def-weil-quasi-separated-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` | `AlgebraicGeometry.QuasiSeparated` |

The additional public imports give Mathlib's scheme pullbacks, `IsSeparated`,
and `CategoryTheory.Over.pullback` / `Over.pullbackComp`. All available recorded
proof-dependency modules are imported without `public`; the unstated proof-only
node `lem-a1-map-over-base-finite-presentation` has no module to import. No
statement depends on an unrecorded postponed helper theorem.

Edge cases checked mathematically before and after writing:

- `D` a field and `m = 0`: `U` and the overlap are empty and `T = S` canonically.
  Essential surjectivity and full faithfulness reduce to the unchanged local
  object, and the four detection assertions retain the `T` restriction.
- More generally `D` local: the same identity localization case is included;
  no nonempty punctured spectrum or positive-dimensional hypothesis occurs.
- The zero ring has no maximal ideal; this is already forced by the node's
  premise, not a new excluded case. Empty total schemes and the empty overlap
  are otherwise allowed throughout: there is no `Nonempty`, dimension, or
  cardinality binder on them.
- Nonseparated finite-presentation schemes are included in both gluing and
  arrow-lifting clauses. The diagonal condition appears only in detection.
- The ring, its localization, and schemes use one arbitrary explicit universe
  `u`. Each chosen finite collection of schemes can be placed in such a universe;
  there is no quantification over test objects in a smaller universe.

Searches performed on 2026-10-24 through the prescribed `msearch.py Q69
lem-sfb-closed-point-fp-patching` wrapper and local source searches:

- LeanFinder: `Schemes of finite presentation glue from the complement of a closed
  point and the spectrum of its local ring`. Eight hits, including
  `Scheme.GlueData`, its `glued`/`gluedScheme` and ideal-sheaf gluing; none state
  the closed-point/local-spectrum finite-presentation equivalence.
- Loogle: `CategoryTheory.Over.pullback, AlgebraicGeometry.LocallyOfFinitePresentation`.
  One hit, the faithfully flat finite-presentation pullback faithfulness instance
  in `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`; not this theorem.
- Mathlib grep: `glueingNear|gluingNear|punctured|Patching|patching`, restricted to
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: `The category of finitely presented schemes is equivalent to gluing
  data on the complement of a closed point and the local scheme`. Eight hits,
  comprising ordinary `Scheme.GlueData`, local representability gluing, scheme
  pullback gluing and finitary extensivity; none match this statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `patching|Patching|glueingNear|gluingNear`
  found ring fibre-product patching, coherent-ideal patching, and unrelated stalk
  patching. None gives this scheme equivalence. Broader searches for punctured
  and closed-point interfaces found open/local and inverse-limit constructions,
  but no duplicate of the item. `grep -rn 'lem-sfb-closed-point-fp-patching'
  lean/WeilConjectures` returned no hit. A name search for
  `overPullbackOverlapIso|finitePresentation_closedPoint_patching` in Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf` returned no hit before writing.

Validation: `scompile.py Q69 lem-sfb-closed-point-fp-patching` compiled the complete
module both as a sandbox module and under its actual library name, with no errors
or warnings after removing an empty line inside the theorem command. The only
postponed theorem is the assigned theorem itself; the canonical comparison has
real data. Dry-run and delivery results are recorded below after execution.

## Second reading by Q69

The dispatcher explicitly forbids starting other agents; this is a second pass by
the same worker, with independent maintainer review to follow delivery. I reopened
the node and module and checked every premise and conclusion against the mapping
above. The essential-surjectivity equation has source the global object's `U`
restriction further restricted to the overlap and target the supplied `XT`
restriction; the full-faithfulness equation has source the restricted `XU` and
target the restricted `YT`. Thus their compositions have the intended direction.
The isomorphisms live in slice categories, so all base-map conditions are enforced.
Finite presentation includes all three required conditions on every object. All
four property statements are equivalences, and the immersion assertions quantify
all arrows without separatedness. The overlap fibre product is canonically the
specified punctured local spectrum, not an arbitrary replacement or an extra
assumption. The only discrepancy found was formatting: the compiler's empty-line
warning was removed, and the complete module was recompiled cleanly. No
mathematical mismatch or statement dispute remains.

Delivery validation: `deliver2.py Q69 lem-sfb-closed-point-fp-patching --no-push`
printed `OK (dry run): commit 55e76920e09 passes the preflight and compiles; nothing
pushed`. The staged packet was exactly the report, item JSON, and single Lean
module. A local field comparison confirmed that the existing node changes only
in `lean`; the module has maximum line width 100 and exactly one `sorry`.

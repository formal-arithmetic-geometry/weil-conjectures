## Worker report

The module `lean/Sheaf/AlgebraicTopology/SharpSpecialColimitGluing.lean` states
`SSet.sharp_special_colimit_gluing` with `sorry` proof.  It renders all three
cases of the node statement as a conjunction of universally quantified clauses:

* For the sequential shape, `U V : ℕ ⥤ SSet` and `p : U ⟶ V` are used.  The
  hypotheses `(∀ n, IsSharp (p.app n))` render objectwise sharpness; the
  quantified `(n m f)` clause renders every homotopy-cartesian naturality
  square; and the two `Mono` clauses on
  `U.map (homOfLE (Nat.le_succ n))` and
  `V.map (homOfLE (Nat.le_succ n))` render successive monomorphisms.  The
  conclusions are sharpness of `colimMap p` and the homotopy-cartesian square
  `IsHomotopyCartesian (colimit.ι U n) (p.app n) (colimMap p)
  (colimit.ι V n)` for every component.
* For the span shape, `WalkingSpan` is the category `1 ← 0 → 2`.  The
  objectwise sharpness and all-arrow naturality clauses are quantified over
  `WalkingSpan`; the specified right leg is rendered by
  `Mono (U.map WalkingSpan.Hom.snd)` and
  `Mono (V.map WalkingSpan.Hom.snd)`.  The sharp colimit and all three
  component squares are stated with the corresponding `colimit.ι` maps.
* For the finite proper-subset shape, `S : Finset ι` and
  `U V : Set.Iio S ⥤ SSet` are used.  The two explicit cofibrancy hypotheses
  quantify injectivity of
  `SSet.ProperSubsetDiagram.latchingMap` in every simplicial degree; no
  nonemptiness assumption on `S` is imposed.  Objectwise sharpness and every
  naturality square are quantified over `Set.Iio S`, followed by sharpness of
  `colimMap p` and the component squares.  Thus `S = ∅` gives the empty
  indexing category, and `|S| = 1` gives the single empty-subset object.

For each of the three shapes, the final clause quantifies a sharp map
`e : E ⟶ H`, compatible cocones `u₀ : U ⟶ const E` and
`v₀ : V ⟶ const H` via
`u₀ ≫ (Functor.const _).map e = p ≫ v₀`, and component homotopy-cartesian
squares `IsHomotopyCartesian (u₀.app i) (p.app i) e (v₀.app i)`.  Its
conclusion is the relative colimit square
`IsHomotopyCartesian (colimit.desc U (Cocone.mk E u₀)) (colimMap p) e
(colimit.desc V (Cocone.mk H v₀))`.

The declaration uses the dependency interfaces
`Sheaf.AlgebraicTopology.SharpPullbackCalculus` (`SSet.IsSharp`,
`SSet.IsHomotopyCartesian`, and `SSet.sharp_pullback_calculus`),
`Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`
(`SSet.KanQuillen.right_proper_kan_quillen_core`), and
`Sheaf.AlgebraicTopology.CofibrantSubsetColimitDecomposition`
(`SSet.ProperSubsetDiagram.latchingMap` and its supporting definitions).
The filtered-equivalence module is imported for the proof plan as recorded by
`proof_deps`.

Edge cases checked: the chain starts at `n = 0`; the span's left leg may be
non-monic as in the source, while the right leg is explicitly monic; the
finite-subset clause handles `S = ∅` (empty diagram) and `|S| = 1`; and no
fibrancy, Kan, or Reedy-fibrancy hypothesis is added.  The relative clause also
allows empty indexing categories.

Searches made: `msearch.py ... leanfinder` for sharp-map gluing returned only
Kan-model lifting declarations and no matching theorem; `msearch.py ...
loogle` for `IsSharp, IsHomotopyCartesian, colimMap` returned no hits because
`IsSharp` is project-defined; `msearch.py ... grep` for
`SharpMap|IsSharp|HomotopyCartesian|sharp_special_colimit` in
`AlgebraicTopology` returned zero hits.  `rg` over the source and project
Lean found no existing `sharp_special_colimit_gluing` declaration.  The only
DAG citers are the recorded sharp-diagonal and related nodes; no citer is
changed.

## Earlier second reading (a previous round; superseded)

The statement was reread against the node clause by clause. The three shape
cases use the specified monomorphism conditions, retain all naturality and
sharpness hypotheses, and include the relative cocone conclusion. No extra
fibrancy or nonemptiness assumption appears; the empty finite-subset indexing
category is retained.

## Second reading by Q84

I reread the node statement, its source citation (Rezk, Proposition 8.1(1)--(3),
printed p. 15, with the stated relative-cocone consequence), the dependency
records, and `SharpSpecialColimitGluing.lean` clause by clause.

* Sequential case: the Lean binders `U V : ℕ ⥤ SSet.{u}` and
  `p : U ⟶ V` are the two diagrams and their natural transformation.  The first
  hypothesis is `∀ n, IsSharp (p.app n)` (objectwise sharpness); the second is
  `∀ n m f, IsHomotopyCartesian (U.map f) (p.app n) (p.app m) (V.map f)` (every
  naturality square); the third gives `Mono` for both successive maps via
  `homOfLE (Nat.le_succ n)`.  The conclusion gives sharpness of `colimMap p`,
  the homotopy-cartesian component square for every `n`, and the relative
  cocone clause for arbitrary `E H`, sharp `e`, compatible natural
  transformations `u₀,v₀`, and component homotopy-cartesian squares.
* Span case: `WalkingSpan` is the source category `1 ← 0 → 2`; the Lean
  quantifiers over all objects and arrows give the objectwise and naturality
  hypotheses, and `WalkingSpan.Hom.snd` is exactly the specified right leg
  `0 → 2` required to be monic in both diagrams.  Sharpness of the colimit,
  all three component squares, and the compatible relative cocone conclusion
  are all present.
* Finite proper-subset case: `{ι : Type u}`, `S : Finset ι`, and
  `U V : Set.Iio S ⥤ SSet.{u}` encode the inclusion poset of proper subsets.
  The two hypotheses quantify injectivity in every simplicial degree of the
  canonical `ProperSubsetDiagram.latchingMap` for every proper `T`, exactly the
  explicit cofibrancy condition in the node.  Objectwise sharpness and every
  naturality square are followed by sharpness of `colimMap p`, every component
  square, and the same relative cocone conclusion over `Set.Iio S`.

No hypothesis is stronger or weaker than the node: no Kan, Reedy-fibrancy,
nonemptiness, characteristic, or finiteness assumption beyond finite `S` is
introduced.  The quantifier order in each case is preserved.  The empty finite
set gives the empty indexing category; for a singleton `S`, `Set.Iio S` has the
single empty-subset object; `n = 0` is included in the sequential case; empty
simplicial sets remain permitted. There is no zero object in simplicial sets;
schemes and characteristics do not enter this statement.  The span left leg is not made
monic.

I checked the recorded interfaces for `SSet.IsSharp`,
`SSet.IsHomotopyCartesian`, `SSet.ProperSubsetDiagram.latchingMap`, and the
Kan--Quillen core.  Searches with `msearch.py` (LeanFinder and Loogle), `rg` in
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, Mathlib, and the project's
`lean/Sheaf` found no existing declaration of this theorem or an equivalent
sharp-map colimit-gluing result.  The dependency declarations are therefore the
single canonical notions used by the file.

Further checks found three documentation/dependency defects: a duplicated
`(blueprint: ...)` marker, a proof summary missing the node's ten detailed steps,
and the missing proof-dependency import `SharpSimplexCriterion`. I repaired all
three, transcribing the ten-step node proof into the docstring. I also added the
already-landed `lem-coef-cofibrant-subset-colimit-decomposition` to `stmt_deps`
because its canonical latching map appears in the signature. The signature and
natural-language statement remain unchanged.  `scompile.py` compiles the module cleanly; its only
proof placeholder is the required theorem `sorry`.

Source verification: I opened [Rezk's paper](https://rezk.web.illinois.edu/rezk-sharp-maps.pdf),
Section 2.3, Proposition 2.7, Section 6.3, Proposition 6.4, Corollary 6.6,
and Proposition 8.1(1)--(3). The source has exactly the three shapes and
monomorphism/cofibrancy assumptions used here; Section 6.3 includes all proper
subsets. Its general simplicial-topos setting specializes to sets, with no
additional fibrancy requirement. The relative clause follows from the node's
explicit comparison to the pullback of the sharp target map.

Fresh independent searches: LeanFinder query "Sharp morphisms of simplicial
sets are stable under sequential unions and cofibrant punctured cube colimits"
returned eight results about generating horns/boundaries and stability of
monomorphisms, none this theorem. Loogle query `"colimMap", "SSet"` returned
zero hits. `rg -i "sharp|equifibered|homotopy.?cartesian"` across Mathlib
AlgebraicTopology, upstream WeilConjectures, and project AlgebraicTopology
found the canonical sharp calculus and simplex criterion; marked-simplicial
sharp markings are a different notion, and no duplicate gluing statement exists.
No repair note, statement_change, new node, or dependency module is present.

The fresh wrapper grep `universal.*pullback|equifibered|Rezk` in
Mathlib/AlgebraicTopology returned no hits. Universe `u` is explicitly bound;
the finite subset index is small in the same universe as the simplicial sets,
and every finite set admits such a finite encoding. There is no additional
size equation on independent mathematical objects. The final expanded module
again compiled cleanly through `scompile.py`.

LeanSearch independently queried "A natural transformation of cofibrant diagrams
of simplicial sets with sharp components and homotopy pullback naturality
squares induces a sharp map on colimits". Its eight results were ordinary
`colimMap`, colimit naturality, and cocone API declarations, with no homotopy or
sharpness assertion. Together with LeanFinder/Loogle and grep this completes
all three required search kinds.

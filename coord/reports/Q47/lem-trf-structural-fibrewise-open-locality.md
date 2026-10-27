## Worker report

The module `Sheaf.AlgebraicGeometry.StructuralFibrewiseOpenLocality` states the three
independent locality assertions of lem-trf-structural-fibrewise-open-locality. Its three
named theorems have sorry proofs. The real definition `structuralFibrewiseConditions`
is an indexed list of eight existing predicates, not a second definition of any of them.
No new nodes, dependency repairs, or statement correction are needed.

Sources read: Stacks `morphisms.tex`, definition-finite-presentation (01TP),
definition-flat (01U3), lemma-closed-immersion (01QO), definition-smooth; the current
blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`
`lem-trf-local-term-locality.md` and its proof; the complete item's seven proof steps.
The auxiliary assertion is the returned Step 14 of semistable marked base change,
not the blueprint unit's own statement. The existing, more specialized theorem
`MultipointedPair.isMultipointed_isSemistable_iff_openCover` in
`Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange` was read and does not state
this node's independent subsets or arbitrary geometric diagram predicate.

Hypothesis and clause correspondence:

* S is any `Scheme.{u}`. `I : Type w`, `U : I → S.Opens`, and
  `hU : ∀ s : S, ∃ i : I, s ∈ U i` express an arbitrary set-indexed open cover.
  The index universe w is independent; there is no finite or nonempty-cover assumption.
* Schemes over S are bundled as `C F X : CategoryTheory.Over S`, with structural
  morphisms `C.hom`, `F.hom`, `X.hom`. This is exactly the category of S-schemes in
  def-weil-scheme-over-base. `j : F ⟶ C` and `r : C ⟶ X` are morphisms over S;
  the Over morphism's commutativity is precisely `j.left ≫ C.hom = F.hom`, i.e.
  q = p composed with j. The first two conclusions do not use X or r, so their
  theorem signatures only bind the objects actually involved. The geometric conclusion
  binds the entire diagram. No additional structural condition is assumed anywhere.
* `d e : ℕ` express both arbitrary nonnegative dimensions.
* The indexed list has 0 = `Flat C.hom`, 1 = `Flat F.hom`.
* Indices 2 and 3 are respectively `LocallyOfFinitePresentation`, `QuasiCompact`,
  and `QuasiSeparated`, conjoined for C.hom and F.hom. In particular finite presentation
  includes the diagonal quasi-compactness requirement, not just local presentation.
* Indices 4 and 5 are respectively
  `∀ s : S, Nonempty (C.hom.fiber s) → (C.hom.fiber s).IsPureDimension d`
  and its F/e counterpart. These are ordinary scheme-theoretic fibres. Empty fibres
  impose no condition, exactly as in the node.
* Index 6 is `IsClosedImmersion j.left`; index 7 is `Etale F.hom`.
* `A : Set (Fin 8)` selects any subset. The structural theorem says
  `(∀ k ∈ A, conditions k) ↔ ∀ i, ∀ k ∈ A, restrictedConditions i k`.
  A = Set.univ gives the whole list simultaneously; singletons give each independent
  equivalence; no selected condition is required to invoke another equivalence.
* Actual restrictions are `(Over.pullback (U i).ι).obj C`, its F/X counterparts,
  and `(Over.pullback (U i).ι).map j` (and r via mapComposableArrows). These are
  the canonical fibre products and induced morphisms, not arbitrary substitutes.
* `marking_smoothNeighbourhood_iff_openCover` renders image containment pointwise:
  `∀ f : F.left, ∃ W : C.left.Opens, j.left f ∈ W ∧ Smooth (W.ι ≫ C.hom)`,
  and the identical expression on each restriction. This is the relative smooth locus
  of DAG Step 6 without assuming local finite presentation globally. Mathlib's bundled
  smoothLocus requires that extra assumption, so its use here would strengthen the node.
  No new smoothness predicate is introduced: the neighbourhood condition is written inline.
* `P : (Ω : Type u) → [Field Ω] → [IsAlgClosed Ω] →
  ComposableArrows (Over (Spec (CommRingCat.of Ω))) 2 → Prop` is an arbitrary rule
  on diagrams of schemes over algebraically closed fields.
  `hP` requires equivalence of truth on isomorphic diagrams over each fixed Ω.
  Such a diagram is the two arrows F → C → X with its field structures, and its
  categorical isomorphisms are exactly compatible triples of isomorphisms over Ω.
* `ComposableArrows.mk₂ j r` is the original diagram, transported by
  `(Over.pullback g).mapComposableArrows 2` to its actual geometric fibre diagram.
  The global geometric point is the explicit canonical map from
  Spec(AlgebraicClosure(S.residueField s)) to S specified by def-weil-geometric-fibre.
* The local side quantifies over i, s and the factorization
  `g : Spec(AlgebraicClosure(S.residueField s)) ⟶ (U i).toScheme` with
  `g ≫ (U i).ι =` that SAME global geometric point. It then tests P after the
  successive actual pullbacks along `(U i).ι` and g. These factorizations exist
  uniquely exactly when s lies in U i (open factorization, since a field spectrum
  has one point). Thus this is every local chosen-closure fibre, expressed with the
  canonical identification of the local and global residue fields. It imposes no
  extra condition, and makes no invariance assumption under field extension or even
  a change of the underlying chosen closure. The arrow equality constrains g entirely;
  this is not an unconstrained-map hypothesis or an arbitrary lift of a canonical map.

Dependency declarations read and used:

* def-pc-fibre-product and def-weil-geometric-fibre:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`
  in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  the recorded explicit closure point uses Spec.map and S.fromSpecResidueField.
  `Scheme.Hom.fiber` in `Mathlib.AlgebraicGeometry.Fiber` is the ordinary fibre.
* def-sbc-locally-finite-presentation: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
* def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
* def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
* def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
* def-weil-flat-morphism: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat` (equivalent to its stalkwise version).
* def-weil-pure-dimension: `AlgebraicGeometry.Scheme.IsPureDimension`,
  `Sheaf.AlgebraicGeometry.PureDimension`, dimension of every irreducible component.
* def-weil-scheme-over-base: `Scheme.Over`, `Scheme.Hom.IsOver`, `asOver` in
  `Mathlib.AlgebraicGeometry.Over`, and their bundled category `CategoryTheory.Over`.
* Proof-dependency Mathlib leaves use `IsZariskiLocalAtTarget.iff_of_iSup_eq_top`,
  `iff_of_openCover` and `of_iSup_eq_top` in Morphisms.Basic; `QuasiCompact` and
  `QuasiSeparated` and their base-change instances; `IsOpenImmersion.lift`,
  `lift_fac`, `lift_uniq` in OpenImmersion; and smooth restriction `instSmoothResLE`,
  smooth composition and smoothness of open immersions in Morphisms.Smooth.
  These modules are imported. All other proof dependencies already occur as statement
  dependencies. No independent unstated proof lemma has been added.

Edge cases checked before writing and again against the final signatures: empty base,
empty index set (hU then forces the base empty), empty marking, arbitrary empty fibres,
d = 0, e = 0, any characteristic, A empty and singleton and full, nonproper and
nonseparated curves, bases with no finiteness assumption, constant true/false P, and
P that depends on the actual algebraically closed field and has no extension invariance.
The smooth assertion is independent of all eight structural conditions. In particular
it cannot silently use the locally-finite-presentation instance from another clause.
Schemes and test fields use the same universe u; no smaller test universe is introduced.

Searches actually run through msearch.py (recorded in searches.jsonl):

* LeanFinder: "Structural conditions and isomorphism invariant geometric fibre diagram
  predicates are local on any open cover of the base". Eight results, including generic
  topological and IsLocalAtTarget locality interfaces; none is this complete assertion.
* Loogle: `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`. One exact
  result for the generic ingredient; it does not cover pure dimensions, the image in
  the relative smooth locus without global lfp, or arbitrary fibre diagram predicates.
* Mathlib grep, AlgebraicGeometry:
  `smoothLocus|geometric.*[Ff]ib.*restrict|IsPureDimension`. Ten hits, including
  smoothLocus, which requires [LocallyOfFinitePresentation f]. Not an exact match.
* LeanSearch: "structural conditions and geometric fibre diagram predicates local on
  open cover of base". Eight hits: generic open-cover locality and sheaf predicates;
  no exact combined theorem.
* Direct rg in lean/WeilConjectures and lean/Sheaf:
  `smoothLocus|IsPureDimension|structuralFibrewise|structural_fibrewise`.
  Existing pure dimension and specialized semistable locality were read and reused or
  distinguished as above. grep of the node id in WeilConjectures returned no match.

Validation: scompile.py compiled the module in sandbox and library modes cleanly,
with no errors or non-sorry warnings. Final preflight and delivery compilation results
are recorded by the prescribed deliver2.py wrapper.

## Second reading by Q47

A second pass by this same dispatcher-started worker reopened the node and Lean file;
no second worker was started, as the task explicitly forbids other agents. The
maintainer's independent review remains the independent reading of this delivery.

I checked all eight list positions against the structural clauses, including both
quasi-separatedness conjuncts and both ordinary (not geometric) pure-dimension tests.
The selector is any set, not only the full set. All three theorem hypotheses contain
only the cover and diagram data, and the last adds exactly P and isomorphism invariance.
The smooth assertion uses open smooth neighbourhoods without a global lfp assumption.
The fibre predicate compares diagrams over precisely the same field on both sides;
checking a local g's equality with the global point ensures both correct residue point
and compatibility with the chosen closure. Over arrows retain q = p composed with j
and compatibility of r, rather than dropping these equations. Empty objects and covers
are not excluded. No mathematical mismatch was found. Explicit imports of the finite
presentation module and the proof-only locality modules were added after the first
successful compile. The JSON signature was extracted verbatim from the final file;
all other original node fields were preserved.

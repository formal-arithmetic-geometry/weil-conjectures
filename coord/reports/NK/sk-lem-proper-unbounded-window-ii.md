## Worker report

The module `Sheaf.Paper.ProperUnboundedCoproducts` states the node in two coefficient
cases. The only theorem proofs are `sorry`. Its helper
`AlgebraicGeometry.ProEtale.ProperUnboundedCoproductAssertions` is a fully written
Prop-valued expansion of the node's two conclusions, not a new construction of
constructible sheaves, derived categories, or pushforward.

Hypotheses and objects, clause by clause:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]` in each theorem. The chosen algebraic
  closure is the existing `PadicAlgCl ℓ`. Every finite subextension is represented
  by `E : PadicAlgCl.FiniteIntermediateField ℓ`, with its induced topology.
- Lambda = E is `Profinite.continuousMapRingObj.{u} E`; Lambda = Qlbar is
  `Profinite.padicAlgClRingObj.{u} ℓ`. The latter is the finite-subextension-valued
  sheaf, not all continuous functions into the valuation-topological closure.
- The standing field is `(k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀]`,
  with `(hp₀ : 0 < p₀)` and `(hpℓ : p₀ ≠ ℓ)`. Thus the characteristic is positive
  and different from ell, exactly as in sk-def-sfb-dc-setting.
- Both `(X Y : Scheme.{u})` carry `Over (Spec (.of k))`. Each structure morphism
  has `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` instances; the last
  two together say finite type. The proper map is `(p : X ⟶ Y) [IsProper p]`,
  with `[p.IsOver (Spec (.of k))]`, making it a k-morphism. These are precisely
  the landed window theorem's standing-setting binders in both coefficient cases.
- The nonnegative integer bound is `(d : ℕ)`. This parametrizes exactly integers
  d >= 0. `hd` says `topologicalKrullDim` of each `pullback p` along the algebraic
  closure of `Y.residueField y`, followed by `Y.fromSpecResidueField y`, is at
  most `(d : WithBot ℕ∞)`. These are precisely the recorded geometric fibres.
- Lambda_T is `condensedRingObj Λ T`, the recorded strong monoidal pullback of
  coefficients from the point. Module sheaves are `CategoryTheory.Mod
  (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)`.
- The ambient category is Mathlib's ordinary `DerivedCategory` of those module
  objects. There is no completed or constructible replacement for that category.
- `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ T)` is IndCons:
  small filtered colimits in the ambient module category of exactly the
  dependency's finite constant scalar-model constructibles. The helper applies
  this to `((DerivedCategory.homologyFunctor _ n).obj K)` for every `n : ℤ`,
  which is exactly membership in Dic as defined in the window node.
- `I : Type (u + 1)` and the `.ind.{u + 1}` parameter impose the fixed site and
  coefficient indexing universe. Schemes are in u; coefficient objects and
  diagrams are in u+1; the existing derived-category instance provides its
  larger localization universe. There is no additional equality of universes.
- Rp_* is `(CondensedRing.lowerStar Λ p).rightDerivedFunctor`, the total right
  derived functor of the full module-pushforward composite.

Conclusions, clause by clause:

- The first conjunct of `ProperUnboundedCoproductAssertions` quantifies over every
  ambient K and takes its Dic membership to the Dic membership of Rp_*K. Since
  Dic is full, restricting the existing functor and its maps gives the functor
  Dic(X) -> Dic(Y) asserted by the node.
- The second conjunct quantifies over every small family K_i in Dic, with no
  common cohomological interval. It asserts existence of ambient colimit cofans
  `c : Cofan K` and `c' : Cofan (fun i ↦ Rp_*.obj (K i))`. Thus coproduct existence
  is a conclusion, not an extra assumption. Both coproduct objects have their
  degreewise IndCons condition included explicitly.
- The comparison is literally `hc'.desc (Cofan.mk (Rp_*.obj c.pt)
  (fun i ↦ Rp_*.map (c.inj i)))`. The universal property gives its component
  Rp_*(iota_i) at every summand, and `IsIso` asserts its invertibility.
  The first conjunct puts its target in Dic(Y), and the second puts its source
  there. Fullness makes the ambient map and its ambient inverse maps in Dic(Y).
  Ambient colimit cofans of these objects are coproducts in the full subcategory.
  Existential choices do not weaken the assertion: any other source and target
  coproducts have unique compatible isomorphisms, which conjugate exactly these
  canonical comparisons.

Recorded dependency declarations used (read signatures and docstrings):

- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`; its public import retains the continuous coefficient
  constructors. The actual E coefficient is the recorded
  `Profinite.continuousMapRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`.
- `sk-def-sfb-qlbar-condensed`: `Profinite.padicAlgClRingObj`,
  `Profinite.padicAlgClCondensedRing` in the published side framework's
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
  Finite subextensions use its existing `PadicAlgCl.FiniteIntermediateField`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `def-weil-geometric-fibre`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, specialized exactly as its record directs.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.condensedRingObj` and `coefficientRing`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod` (including its recorded pro-etale specialization).
- `sk-def-sfb-derived-categories`: public import of its recorded
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`. The ordinary
  `DerivedCategory` and the canonical upstream total right-derived construction
  are the aggregate node's convention components, as its lean.note specifies.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`, reexported by the
  window module. The newer constant-model interface is used, not upstream's
  arbitrary local presentation predicate.
- `sk-lem-proper-unbounded-window`: public import
  `Sheaf.Paper.ProperUnboundedWindow`; its
  `AlgebraicGeometry.ProEtale.ProperUnboundedWindowAssertions` uses exactly the
  same degreewise `.ind` predicate and ordinary derived pushforward. Its theorem
  signatures were read in full; their standing-setting binders are now retained here.
- `sk-def-sfb-dc-setting`: its current recorded module is
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  declaration `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
  Its setting is represented by explicit binders, as in the landed window module;
  no compactification is needed or selected for this theorem. The module's setting
  docstring and the declaration's full signature were read. Its existing notions
  `Scheme.Over`, `Scheme.Hom.IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` are already available through the window import. No copy of a
  setting predicate or compactification construction is introduced.
- `def-weil-size-convention`: a metatheoretic convention with no declaration;
  represented by the explicit universes described above.
- `sk-def-sfb-module-derived-pushpull`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar` and
  `CategoryTheory.Functor.rightDerivedFunctor`. The underived full composite
  and generic total right-derived definition were read, not replaced.

Proof imports include the recorded truncation module
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` and the Mathlib
cohomological isomorphism criterion in
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
`det-ambient-ind-derived-sums` and `det-proper-unbounded-window-ii-bounded`
have no recorded Lean modules on the base, so no import can be supplied for them.
Their proof roles remain in both theorem docstrings. No proof prerequisite is
assumed as an extra hypothesis or re-created in this delivery.

Edge cases checked: empty I is permitted and asserts zero coproducts and their
canonical comparison; zero summands and arbitrary unbounded summands are
permitted; d=0 is retained; empty fibres have Krull dimension bottom and satisfy
hd; empty Y makes hd vacuous exactly as it should, without excluding empty
schemes. A disconnected base has one uniform bound d as the node requires.
No boundedness or nonemptiness was added. Characteristic zero and characteristic
ell are excluded explicitly by the restored source setting, not silently. Changing
`d : ℕ` to an integer was not part of this repair: d=0 and every nonnegative bound
remain covered. To invoke the window theorem, coerce d to an integer; `hd` implies
its finite-lower-bound test by transitivity in `WithBot ℕ∞` and order reflection
on finite natural numbers. This works for empty fibres as well (the antecedent
of the window's finite-lower-bound test is then false).

Searches for an existing statement (2026-10-18):

- msearch.py leansearch: `Proper direct image of ind constructible complexes
  preserves arbitrary coproducts`. Eight results: finite-coproduct preservation
  by additive functors, generic coproduct preservation, AB4 and related facts;
  none is this proper unbounded module-derived theorem.
- msearch.py leanfinder: `Proper derived pushforward preserves arbitrary direct
  sums of unbounded complexes with ind constructible pro etale cohomology`.
  Eight results about exact-functor derived constructions and t-structures;
  none is the statement.
- msearch.py loogle: `CategoryTheory.Limits.PreservesColimitsOfShape`.
  Twelve generic preservation definitions and transfer results, no match.
- msearch.py grep: `proper.*(coproduct|direct.sum)|indConstructible|IndCons`.
  Twenty-five results, none states this theorem.
- rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for the item id and
  proper/coproduct/sum and ind-constructible patterns. The side window and
  constructible-compactness files have related but different conclusions.
  Etale projection formulas and scheme-module preservation facts concern other
  coefficients and categories. No declaration of this node was found.
- A final exact-name search for `ProperUnboundedCoproduct` and
  `properUnbounded.*[Cc]oproduct|properUnbounded.*[Ss]um` in both source roots
  returned no collisions. Existing `.ind` and constant-model definitions were
  inspected and reused; no new notion node or dependency repair is needed.

## Statement corrected

Return H3/H7 is repaired under brief-stage2 §1(C). The old statement began
“Let $X,Y$ be schemes and $p:X\to Y$ a proper morphism”, without the standing
field setting; the complete old statement is retained verbatim in
`statement_change.old_statement`. Proof steps 1 and 4 could not invoke the
landed window theorem with those unrestricted binders.

The source is
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`:
`sk-lem-proper-unbounded-window-ii/_section.md` specifies Rp_* by reference to
`sk-lem-proper-unbounded-window`; that unit's opening sentence takes p,d as in
`sk-lem-proper-heart-bound`; the inherited context is `sk-def-sfb-dc-setting`.
All four source sections were opened. Making this context explicit restores the
source unit's intended meaning, as required by the return, without changing
its conclusion or proof route. Both theorems now have the exact window
k/p₀/Over/IsSeparated/LocallyOfFiniteType/QuasiCompact/IsOver binders.
The original `d : ℕ` and `hd` are unchanged. The item gains the existing setting
node in `stmt_deps`, plus a complete `statement_change`; `proof` and
`proof_deps` are unchanged. The old disputed flag is resolved and removed.

Citer audit: I ran the exact-id search over dag/nodes and opened all four nodes
named in the return, checking actual current stmt_deps and proof_deps rather
than counting unit metadata as a dependency. On the current shared base only
`det-proper-image-localizing-proper` actually names this item in those fields;
`statement_change.citers` contains exactly that current consumer, as §5 requires.
The other three requested nodes are audited below as well, but not falsely
inserted as current dependency edges.

- `det-proper-image-localizing-proper`: holds=true. Its rational-coefficient
  assertion and proof step already impose the standing setting, so the
  application to families in Loc(Dbc) still gives the same canonical comparison.
- `det-prop-int-compactness-direct-sums`: holds=true for the context change.
  It already imposes the standing setting; its current proof independently proves
  the integral window and sum claims, and its actual dependency lists no longer
  cite this rational-coefficient item. The exact-id hit is blueprint_uses metadata.
- `det-proper-unbounded-window-ii-bounded`: holds=true; its current proof is the
  bounded-family induction using continuity and never invokes this item. The
  exact-id hit is its unit field. Its unrestricted statement is not weakened by
  this correction to another node; it remains usable in the more restricted
  setting of the current theorem.
- `det-proper-unbounded-window-ii-general`: holds=false if read as the
  unrestricted application that prompted the return: its schemes still lack
  the standing setting needed by its direct window-theorem invocation. Its
  current actual dependency lists do not cite this item (the exact-id hit is its
  unit field). It requires its own inherited-context repair; it is named here
  and left unedited, as required. The same issue was already identified by the
  landed window theorem's statement_change.

No other node is edited. The sandbox node was compared with current main:
only lean, statement, stmt_deps, and statement_change differ, all authorized.

## Second reading by NK

Fresh repair reading of the saved packet, the node, the final Lean module,
the landed window module, its statement_change, and the source sections open
together. This is a substantive rereading during the returned-delivery repair;
no additional agent was started, as the dispatcher brief forbids that.

The saved packet's claimed second reading missed the inherited setting.
I found and repaired that mismatch, rather than accepting its clean compile:
prime ell is Fact ell.Prime; a finite extension is the existing finite
intermediate field E; the algebraic-closure case uses the finite-subextension
condensed ring; the restored field/characteristic/structure-map/k-morphism
binders match the window theorem in both signatures. Finite type is exactly
LocallyOfFiniteType plus QuasiCompact on each structure map. Properness remains
IsProper p. There is still one nonnegative bound d, with the original geometric
pullbacks and their dimension inequalities at every y. Its integer coercion
supplies the window lemma's bound as explained above, including empty fibres.

For each conclusion I traced the final helper: its first conjunct takes
all-degree IndCons cohomology of any K to all-degree IndCons cohomology of
rightDerivedFunctor(lowerStar). Its second conjunct quantifies over every
small family, then supplies source and image colimit cofans and the Dic
condition on both coproduct objects. The arrow is hc'.desc of the cofan whose
legs are exactly Rp_*(c.inj i), and IsIso is asserted of that specific arrow.
Thus neither coproduct existence nor preservation is assumed. Fullness gives
the claimed restriction and comparison in Dic. The module categories,
constructibility predicate, derived category, and coefficients are unchanged.

I checked both theorem binders individually, the complete old-statement
preservation, the verbatim updated lean.statement, and all four requested
consumer nodes. Empty I, zero complexes, unbounded families, d=0, and empty
schemes/fibres are still included. The helper has real data; both proofs remain
only sorry; all three declarations retain source and blueprint docstrings,
and both theorem docstrings retain the full six-step proof. No second notion,
new definition node, dependency replacement, or added proof assumption is used.

Validation of this repair (2026-10-18): the prescribed scompile.py compiled
both the sandbox file (4.4 s) and its library path (17.1 s) without errors or
warnings. The corrected-packet deliver2.py --no-push then compiled both forms
again and printed `OK (dry run): commit c54bf29123 passes the preflight and
compiles; nothing pushed`. The final delivery wrapper reruns preflight and
compilation after this report update. A source-only consistency check verified
the exact current consumer list, verbatim old statement and old dependencies,
verbatim lean.statement, unchanged proof/proof_deps, two sorry proofs, and
100-character Lean line widths.

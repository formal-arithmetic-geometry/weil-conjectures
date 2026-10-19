## Worker report

The module `Sheaf.Paper.ProjectiveCurveBettiCardinalities` states
`AlgebraicGeometry.projective_curve_betti_cardinalities`, with one whole-proof `sorry`
and no new definitions. The source read was the complete blueprint node
`sec-smooth-purity/sk-prop-sf-cbc/lem-fin-projective-curve-betti-cardinalities.md`,
order 1610, together with the DAG's nine expanded proof steps. The module docstring
reproduces those nine steps and their inputs. No node statement was changed.

Hypotheses and clauses:

- `X S : Scheme.{u}` and `f : X ⟶ S` introduce the schemes and morphism.
- `[IsNoetherian S]` means locally Noetherian and quasi-compact, exactly Noetherian.
- `[SmoothOfRelativeDimension 1 f]` combines smoothness with the requirement that
  every nonempty geometric fibre is pure of dimension one. This is precisely the
  relative-dimension convention recorded by def-sbc-smooth-morphisms (Stacks 02G2),
  including the empty-fibre case. It does not assert connectedness or surjectivity.
- `[IsProjective f]` is the dependency's H-projective, quasi-compact convention.
- `ℓ : ℕ` and `hℓ : ℓ.Prime` give the fixed prime.
- `hinv : ∀ s : S, (ℓ : S.residueField s) ≠ 0` expresses invertibility on S:
  an integer is a unit in a local ring exactly when its residue is nonzero.
  Thus this is equivalent to invertibility in every stalk, not a characteristic-zero
  restriction or a condition on just the generic points.
- Every geometric fibre is literally `pullback f` along
  `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
  (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s`.
  This is the exact def-weil-geometric-fibre recorded construction.
- `b : ℕ → S → ℕ` is existentially bound as the cardinality function, not an extra
  input or a separately defined invariant. Its first clause identifies `b r s`
  with `Cardinal.mk` of the actual derived etale cohomology object. In particular,
  this asserts finiteness rather than silently truncating an infinite cardinal.
  `Etale.cohomology AddCommGrpCat.{u+1} C (r : ℤ)` is applied to
  `(DerivedCategory.singleFunctor _ 0).obj (C.constantZMod ℓ)`.
- In degrees zero and two, the cardinality is `ℓ ^ Nat.card (ConnectedComponents C)`.
  The topological connected-component quotient counts all components, without a
  chosen enumeration or an assumption that there is just one component.
- In degree one it is `ℓ ^ (2 * (pullback.snd f ...).genus)`.
  The already existing `Scheme.Hom.genus` definition takes *any* field-valued
  structure morphism and is the dimension of its global differential forms.
  Its full definition and docstring in `WeilConjectures.AlgebraicGeometry.Curve`
  were read. On a finite disjoint union of smooth proper curves, differentials and
  global sections split into the finite direct sum of those on the components.
  Thus its dimension is exactly the sum of their genera. This uses the existing
  genus construction without defining another genus or requiring connectedness.
  It does not use the connected-curve estimate on a disconnected curve.
- For `r > 2`, the two conditionals give cardinality one. The domain `r : ℕ`
  is exactly the nonnegative sheaf-cohomology degrees in the node.
- For each r, `(Set.range (b r)).Finite` and constructibility of every level set
  `{s : S | b r s = n}` mean a finite constructible partition on which the function
  is constant. Conversely such a partition gives exactly these two conditions.
  No uniform partition for all r is demanded.

Dependency declarations used:

- def-pc-projective-morphism: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective`. That synchronized upstream file is absent from
  this older read-only source snapshot; its original definition and full docstrings
  were read in `Sheaf.AlgebraicGeometry.Morphisms.Projective`, lines 35–51.
  A server probe of the recorded upstream import and `#check` succeeded. The module
  uses the recorded upstream module, not the retired spelling.
- def-sc-curves and def-sc-genus: `WeilConjectures.AlgebraicGeometry.Curve`,
  `IsCurve`, `IsConnectedCurve`, and `Scheme.Hom.genus` (lines 68–123, read in full).
- def-weil-pbc-etale-cohomology:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `Etale.cohomology` and `Etale.rightDerivedGlobalSections`, lines 210–236.
- def-sc-constant-sheaves: `WeilConjectures.AlgebraicGeometry.Sites.Kummer`,
  `Scheme.constantZMod`, lines 380–384; the ULift is already part of this construction.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `Smooth` (lines 58–65) and `SmoothOfRelativeDimension` (lines 128–138).
- def-weil-geometric-fibre: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, lines 94–116.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`
  (lines 56–59), with `IsNoetherian` (line 280) supplying quasi-compactness.
- def-weil-pbc-quasi-compact-scheme: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter`, lines 273–285, used via `IsNoetherian`.
- def-kun-topological-krull-dimension: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, lines 34–40, used by the curve and relative
  dimension conventions; purity is rendered by `SmoothOfRelativeDimension`.
- def-weil-constructible-subset: `Topology.IsConstructible`,
  `Mathlib.Topology.Constructible`, lines 169–179.
- def-weil-pbc-scheme-conventions is explicitly a convention node with no declaration.
  No convention-only dummy import was introduced.

All proof dependencies with a recorded module are imported without `public`, unless
already needed publicly by the statement. The coherent-rank lemma has no Lean record
yet and therefore has no import. Mathlib proof-dependency declarations without module
records are already reached by the smooth/projective/Noetherian imports. No proof
import was removed to evade a cycle.

Edge cases checked: an empty base leaves all pointwise hypotheses vacuous and the
functions have empty range; an empty fibre has no connected components and zero
global differential forms, hence both powers are ℓ^0 = 1. Disconnected fibres add
the component genera, even when those genera differ. A geometrically connected
rational curve gives ℓ, 1, ℓ; genus g gives ℓ, ℓ^(2g), ℓ. Degrees 0, 1, 2 and above
2 select the correct branches. Characteristic ℓ is excluded exactly by invertibility;
other positive characteristics are allowed. Universe u is explicit and shared by
schemes, residue fields and their algebraic closures; the etale coefficient category
is the existing AddCommGrpCat.{u+1} encoding. There are no file-local definitions,
notation, instances, or auto-bound universe/term variables.

Searches made (actual results):

- msearch.py leanfinder: "Cardinality of etale cohomology of smooth projective curves
  in a family is constructible": eight hits, concerning FunctionField.classNumber,
  ClassGroup.cardM, standard smooth rings and Chevalley complexity; no matching theorem.
- msearch.py loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsProper": zero hits.
- msearch.py grep: "betti|etale.*cohomology|cohomology.*etale": zero hits.
- rg of the source project for the node id: none. `tools/lean_names_upstream.py show`
  was consulted; it reported the name inventories, no theorem for this node.
- rg of the source and `lean/Sheaf` for Betti, genus, component and constructibility:
  the source has curve genus and connected-curve cohomology, zeta Betti symmetry;
  side modules have derived-fibre Betti ranks, not this etale family theorem.
- rg of Mathlib AlgebraicGeometry and Topology for IsProjective and constructible
  function definitions: no matching family theorem. Read the concrete constructible
  subset predicate instead and expanded the finite-partition condition inline.

Validation: scompile.py compiled the module on the server cleanly (3.0 seconds,
nice 19, two threads, 60-second limit), including its side-only decomposition import.
No local compiler or library build was run. The initial elaboration error at the
component quotient was repaired with an explicit Scheme category parameter and
carrier coercion. No statement correction, new node or dependency module is needed.


## Second reading by NV

I independently read the node's full statement and nine proof steps beside the
Lean signature, all twelve statement-dependency nodes and their recorded interfaces,
and the complete source blueprint lemma (order 1610). I also read the relevant
Stacks text: etale-cohomology.tex, lemma-cohomology-smooth-projective-curve (03RQ),
Situation situation-what-to-prove and lemma-constant-smooth-statements (0A5B);
curves.tex, definition-genus (0BY7) and lemma-duality-dim-1 (0BS2), especially
parts (5) and (6). The surrounding Situation assumes an algebraically closed
field and a separated finite-type scheme of dimension at most one. The geometric
fibres here satisfy those hypotheses. No missing ambient hypothesis was found.

Object/hypothesis/conclusion checklist, in the node's order:

- Schemes S and X, and f : X → S: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  Verdict: exact; no connectedness, nonemptiness or surjectivity is assumed.
- S Noetherian: `[IsNoetherian S]`. I read Noetherian.lean: the class extends
  `IsLocallyNoetherian S` and `CompactSpace S`, exactly the stated hypothesis.
- f smooth and projective with geometric fibres pure of dimension one:
  `[SmoothOfRelativeDimension 1 f] [IsProjective f]`. I read Smooth.lean's
  standard-smooth chart definition and its smoothness consequence, and the
  recorded H-projective/quasi-compact definition in the side Projective module.
  The relative-dimension-one condition is precisely the smooth pure-fibre
  convention of def-sbc-smooth-morphisms (02G1/02G2), including empty fibres.
  Verdict: exact; neither an independent smoothness hypothesis nor a connected
  curve instance is missing. The synchronized canonical upstream Projective
  import resolves in the server compile.
- Prime ell invertible on S: `(ℓ : ℕ) (hℓ : ℓ.Prime)` and
  `hinv : ∀ s : S, (ℓ : S.residueField s) ≠ 0`. A local-ring element is a unit
  exactly when its residue is nonzero. This tests every point, hence means
  invertibility on S. Verdict: exact, allowing all characteristics away from ell.
- Geometric fibre C_s: every repeated term is `pullback f` along the composite
  `Spec.map` of the algebraic-closure inclusion with `S.fromSpecResidueField s`.
  I read the residue-field map and pullback/projection declarations. The second
  projection equips that same fibre with its algebraically closed base field.
  Verdict: the scheme-valued geometric fibre of the dependency, not its set of
  geometric lifts.
- c_s, the number of connected components: `Nat.card (ConnectedComponents C_s)`.
  I read the quotient definition in Topology/Connected/Clopen.lean. Proper
  finite-type fibres have finitely many components, so Nat.card counts them
  without an extra finiteness assumption. Verdict: exact.
- g_s, the sum of component genera: `(pullback.snd f ...).genus`. I read the
  full `Scheme.Hom.genus` definition and docstring in Curve.lean. It has no
  connectedness instance argument: it is the finite rank over the base field
  of global relative differential forms for any such structure map. On a
  finite clopen decomposition those sections form the finite product of the
  component sections, so their dimensions add. On each smooth proper component
  Stacks 0BS2(5)-(6) identifies this dimension with the H¹(O) genus of 0BY7.
  Thus its value here is exactly the node's sum, also for unequal genera.
  Verdict: exact; it is not the alternative 1-chi arithmetic genus, which
  would fail for disconnected curves.
- Actual etale cohomology cardinalities: the first conjunct identifies
  `Cardinal.mk` of `(Etale.cohomology AddCommGrpCat.{u+1} C_s (r : ℤ)).obj`
  of the constantZMod sheaf placed in degree zero with `(b r s : Cardinal)`.
  I read cohomology/rightDerivedGlobalSections in LowerShriek.lean and
  constantZMod in Kummer.lean. These are the recorded derived global sections
  and the sheafification of constant ULift(ZMod ell). Verdict: exact, and
  equality to a natural cardinal asserts finiteness without truncating infinity.
- r = 0 or 2: the first conditional gives `ℓ ^ c_s`; r = 1: the second gives
  `ℓ ^ (2 * g_s)`; all other natural r give 1. Verdict: exactly all three
  cases of the node. The degree is nonnegative and cast to the derived integer
  indexing; no negative-degree assertion is added.
- Each degree's cardinality function is constructible: the final conjunct is
  `∀ r, (Set.range (b r)).Finite ∧ ∀ n, Topology.IsConstructible {s | b r s = n}`.
  I read the Boolean-subalgebra definition of IsConstructible. Finite range
  gives a finite partition by these constructible level sets, and a finite
  constructible partition conversely gives these two conditions. Verdict:
  exact. The existential b is determined by the preceding cardinal equality;
  it is not an extra input. No common partition across all degrees is demanded.

Edge cases: empty S has vacuous pointwise clauses and empty ranges. Empty
fibres have zero connected components and zero differential sections; every
cardinality formula is ell^0 = 1, including degrees zero and two. The zero
cohomology group has cardinality one. Pure dimension excludes point components
of nonempty fibres. Disconnected fibres with differing component genera are
included. A rational connected fibre has cardinalities ell, 1, ell; genus g
has ell, ell^(2g), ell. Degrees 0, 1, 2, 3 select the intended branches.
Primality excludes ell = 0 and 1; characteristic ell is excluded exactly by
hinv. Arbitrary scheme universe u is explicit; the algebraic closure stays in
u and abelian groups use the recorded site universe u+1. There is no quantified
test-object universe that could make a hypothesis vacuous and no unbound binder.

Independent searches: msearch leanfinder query "Finite constant sheaf cohomology
of a disconnected smooth proper curve has cardinality a power of the coefficient
prime" returned class-number, ModN, Hilbert 90, singular homology and Galois
category hits, none this theorem. Loogle query `AlgebraicGeometry.Scheme.Hom.genus`
returned zero hits (unknown project identifier in its index). msearch grep
`cardinality.*cohomology|cohomology.*cardinality|betti_cardinalities` returned none.
My direct rg searches (including --no-ignore) in the upstream project, Mathlib
AlgebraicGeometry and side Sheaf tree for Betti, cohomology/cardinality combinations
and the declaration name found zeta symmetry and derived-fibre Betti modules,
but no family cardinality theorem. I opened Curve/Estimate.lean: its component
calculations require connected curves and do not state this family result.
The upstream name inventory contains no matching name or node id. These searches
supplement, rather than merely repeat, the worker's recorded three search kinds.

No mismatch requiring a repair was found. No new node, dependency module,
statement correction, private definition, local instance or hollow construction
is present. The module has one named theorem with a whole-proof sorry; its
docstring records all nine proof steps with their named dependencies. Recorded
proof-dependency modules are imported; the coherent-rank lemma has no recorded
module yet. The node's lean.statement was checked programmatically for verbatim
equality with the source signature. I left the correct module and node unchanged
and appended only this independent review.

Validation: scompile.py compiled the delivered module cleanly on the server in
3.0 seconds, with its side-only decomposition dependency compiled in 1.7 seconds;
nice 19, two threads, 60 seconds per file. No local compiler or lake build ran.

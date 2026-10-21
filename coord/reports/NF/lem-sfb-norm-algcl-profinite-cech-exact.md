## Worker report

Repair of returned stage-2 immutable head 1704e7647b20. I retained the saved
Lean module and theorem signature unchanged, and compared the saved node with
current main: its only differences were lean and the spurious theorem stmt_dep
identified in the return. The initial prescribed dry run passed mechanically
(commit 478c785e5cc), but that did not resolve the independent review finding.
This repair replaces lem-sfb-normed-scalar-profinite-cech-exact in stmt_deps
with the new definition node def-sfb-profinite-cech-tuples. The new node records
the two existing definitions in the unchanged NormedScalarProfiniteCechExact
module with existing:true; no theorem conclusion from that module is used.
The original statement, source, proof, proof_deps, proof_origin, split_report
and review metadata are unchanged. No stage-1 re-split is delivered.

The module is lean/Sheaf/Topology/NormAlgclProfiniteCechExact.lean. Its one theorem,
Profinite.NormAlgclCech.normAlgclProfiniteCech_counterexample_and_local_contraction,
states the conjunction of the live node's counterexample and the two explicit
contractions. Its proof is sorry. The six helper definitions have real data and
contain no sorry. They specify the coordinate insertions, name the existing
explicit pullback and first projection, and forget the common base coordinate.
There is one new definition node, described below, and no dependency module repair.

I read the source file named by the node, main-20261015 blueprint
sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3).
That paragraph motivates the analytic auxiliary but does not assert the false
universal noncomplete Cech exactness statement. The live NI correction, which the
return explicitly requires, is the statement formalized here. The module and
all seven declaration docstrings identify the source place and blueprint id.
The main theorem docstring carries the complete eight-step proof from the live
node: split Cantor relation, countable closed finite-field exhaustion, small
coefficients escaping each field, continuity by truncation, fibrewise cocycle
identity, Baire contradiction, split-cover contraction, diagonal-base-change
contraction including empty spaces. Proof work remains for stage 3.

Hypothesis and clause correspondence:

* A fixed prime ell is `(l : Nat) [Fact l.Prime]`.
* The coefficient is an arbitrary `(Omega : Type u)` (written `Ω`),
  `[NormedField Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
  The last instance is exactly the def-weil-algebraic-closure predicate for an
  algebraically closed algebraic extension; the coefficient is not replaced by
  a completion. `hΩ : ∀ a : Padic l, ‖algebraMap (Padic l) Ω a‖ = ‖a‖`
  specifies extension of the p-adic absolute value, and NormedField supplies its
  induced norm topology. There is no CompleteSpace hypothesis, finite-extension
  hypothesis on Ω, or finite-subextension-valued restriction on cochains.
* The size convention is explicit `universe u v`: coefficient and profinite
  carrier universes are independent. Spaces are `Profinite.{v}`, Mathlib's
  compact Hausdorff totally disconnected spaces, with empty spaces permitted.
* The equal-image fibre powers are the existing `Profinite.scalarCechTuples q r`,
  namely `{t : Fin r → T // ∀ i j, q (t i) = q (t j)}`, with its subtype topology
  from the finite product. Cochains are Mathlib `C(scalarCechTuples q r, Ω)`:
  all continuous functions with pointwise operations, as in the recorded
  def-sfb-continuous-map-condensed-ring interface.
* Coordinate deletion is the existing `scalarCechDelete q r j x`, using
  `Fin.succAbove`. The displayed differential is rendered pointwise as
  `∑ j : Fin (r+1), (-1 : Ω)^j.val * f (scalarCechDelete q r j x)`.
  All indices start at zero and retain the displayed sign convention.
* Clause (1) is the first conjunction member: existential `T V : Profinite.{v}`,
  `Nonempty T`, `Nonempty V`, `TopologicalSpace.MetrizableSpace T` and the
  corresponding predicate for V; then existential continuous `q : C(T,V)`
  with `Function.Surjective q`; then `f : C(scalarCechTuples q 2, Ω)`.
  The sum over Fin 3 is `d^1 f = 0`. The negated existential continuous
  `g : C(scalarCechTuples q 1, Ω)` with the sum over Fin 2 equal to f is
  exactly nonexistence of a primitive. A one-coordinate tuple is canonically T.
* The split part of clause (2) is the second conjunction member. It quantifies
  over every T,V,q and surjectivity, every `σ : C(V,T)` with
  `hσ : Function.RightInverse σ q` (q composed with σ is the identity), and
  every positive degree. Here the degree is n+1 for `n : Nat`; thus n=0 is
  precisely the node's n=1 and no positive degree is lost. The cocycle f
  has n+2 coordinates, its differential n+3, and its primitive n+1.
  The conclusion supplies a genuine continuous g, the pointwise equality
  `g x = f (sectionInsert q σ hσ n x)`, and `d g = f`. Unfolding sectionInsert
  and prepend gives `(σ(q(t_0)),t_0,...,t_n)` with no unspecified choice.
* The base-change part of clause (2) is the third conjunction member, for
  arbitrary continuous surjective q and every positive-degree cocycle f.
  `baseChange q` is Mathlib's explicit `CompHausLike.pullback` of q with itself,
  the subset `{p : T×T // q p.1 = q p.2}` with its subspace topology, already
  bundled as profinite. `projection q` is its actual first projection to T.
  An r-tuple in its nerve is a family `(s_i,t_i)` with all s_i equal; it is
  therefore exactly the displayed coordinates `(s;t_i)`.
  The continuous F in the conclusion is specified at every point by
  `F x = f (forgetBase q (n+2) x)`, the actual pullback `(s;t_i) ↦ f(t_i)`.
  The continuous h is specified by `h x = f (baseInsert q n x)`;
  baseInsert returns `(s,t_0,...,t_n)` with s the common first coordinate.
  The final alternating-sum equality on the nerve of projection q is
  `d h = F`, exactly the required diagonal-base-change primitive.
* No nonemptiness or metrizability binder occurs in the two universal
  contraction clauses. For the empty surjection all their positive-length
  tuple domains are empty, so the formulas and equations give the unique
  continuous functions. All identities have values in Ω itself and no
  closure of images or completed equality is used.

Dependency declarations read and used:

* def-weil-algebraic-closure is a Mathlib leaf, not a missing lean record.
  I read AlgebraicClosure in Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
  and the full signature/docstring of `IsAlgClosure` in
  Mathlib.FieldTheory.IsAlgClosed.Basic. The theorem uses the latter predicate
  to cover any fixed algebraic closure, as the node requires.
* def-weil-size-convention has the recorded convention-only lean entry.
  It supplies no declaration to import; explicit u,v implement the convention.
* Sheaf.Topology.ContinuousMapCondensedRing:
  `Profinite.continuousMapRingPresheafOfUniverse`,
  `Profinite.continuousMapRingSheafOfUniverse`, and their underlying
  `C(S,T)` sections and precomposition restrictions were read. This module is
  publicly imported; our formulas use those same unlifted continuous maps.
* New definition dependency def-sfb-profinite-cech-tuples records
  Sheaf.Topology.NormedScalarProfiniteCechExact:
  `Profinite.scalarCechTuples`, `Profinite.scalarCechDelete`. I read their
  complete definitions and the finite-complete-field theorem signature.
  Only the helpers are used; its exactness theorem is never applied to Ω.
* Mathlib.Topology.Category.Profinite.Limits and
  Mathlib.Topology.Category.CompHausLike.Limits:
  `CompHausLike.pullback`, `CompHausLike.pullback.fst`,
  `CompHausLike.ofHom`, and the profinite explicit-pullback instance.
  These already implement the canonical base change; no new pullback
  notion or arbitrary substitute map is introduced.
* Mathlib.Topology.Metrizable.Basic:
  `TopologicalSpace.MetrizableSpace`, the existence of a compatible metric,
  rather than a chosen metric being an added structure on the witnesses.
* Plain proof imports of recorded and stated proof dependencies are
  Sheaf.NumberTheory.Padics.CountableClosedFiniteCover,
  Sheaf.NumberTheory.Padics.ExtensionIntegersDvr,
  Sheaf.Topology.FiniteQuotientFiberProduct, and the Mathlib Baire modules.
  I read the corresponding node statements and declarations. The new NI
  countable-split-cover proof dependency has no Lean record yet, and is not
  needed to state this item; its exact statement is included in proof step 1.

Edge checks: degree one gives d g(x,y)=g(y)-g(x), and
`d f(x,y,z)=f(y,z)-f(x,z)+f(x,y)`. The split formula then gives
`g(t)=f(σ(q(t)),t)` with the correct positive sign. For identity covers,
positive cocycles admit the same insertion contraction; the existential
counterexample does not claim the cover is split. For a finite split cover,
the same formulas are continuous without requiring discreteness of Ω.
For base change, the first projection is intentional: pairs are (s,t), and
forgetBase takes their second coordinates, while baseInsert prefixes s.
The equal-image proof uses each pair's q equality and the equality of the
first projections. The empty surjection is included, and coefficient/space
universes remain independent.

Searches actually run on 2026-10-21:

* msearch.py leanfinder: "Continuous Cech cocycles on a profinite surjection
  with a continuous section have a primitive by inserting the section, but
  algebraic closure p-adic coefficients give a degree one counterexample".
  Eight hits, including Profinite.NobelingProof.CC_exact and locally constant
  integer/function and HomComplex facts; none is this statement.
* msearch.py loogle: "Profinite.scalarCechTuples, Profinite.scalarCechDelete".
  Zero hits, with unknown identifier Profinite.scalarCechTuples in the
  Mathlib search service. Local source search does find both in the landed
  Sheaf module, which is the interface reused.
* msearch.py grep: `(cech|Cech).*(section|contract|primitive)|` followed by
  `(section|contract|primitive).*(cech|Cech)`. Two unrelated StoneCech section
  headings, no match.
* msearch.py leansearch: "A continuous Cech one cocycle on a metrizable
  profinite surjection with values in an algebraic closure of the p-adic
  field can have no continuous primitive". Eight hits, including the
  coefficient types PadicAlgCl and PadicComplex and continuous group
  cochains; none supplies this counterexample or the two contractions.
* rg over lean/WeilConjectures and lean/Sheaf for Cech/cech and algebraic
  closure, the item id, scalarCechTuples and scalarCechDelete: no upstream
  statement of the item; one obsolete parent proof-docstring reference to
  the old global input, and the reusable tuple/deletion definitions in
  NormedScalarProfiniteCechExact. The parent's global use was already
  identified as broken by the live NI review; it is not edited here.

The old universal global exactness assertion is already disputed and
corrected in the live reviewed node. No additional statement correction or
new dispute is introduced by this stage-2 repair.

Validation: scompile.py NF lem-sfb-norm-algcl-profinite-cech-exact compiled the
module in sandbox and library modes against the live server build, cleanly,
with no compiler errors or non-sorry warnings. Every theorem proof is sorry;
none of the helpers is hollow. Final dry-run and push results are recorded by
the prescribed delivery wrapper.

## Second reading by NF

Author's second reading for direct delivery; the maintainer supplies the
independent review. I reopened the current NI JSON, the module and the exact
blueprint paragraph, then compared the statement, each binder, tuple arity,
face sign and inserted coordinate rather than the old returned stage-1 text.

H1 repair: a new module exists with one theorem ending `:= by sorry`; the
item's lean record names the module, all six helpers, and the main theorem,
and contains its signature verbatim. No assertion is claimed proved.

H2 repair: the node copy was regenerated from the live reviewed NI node.
A structural JSON comparison finds only lean and the added definition
node def-sfb-profinite-cech-tuples in stmt_deps changed. In particular split_report remains group NI;
none of statement/proof/proof_deps/proof_origin or review fields is rewritten.
There is no inherited stale NF split to overwrite NI's correction.

H11 repair: this report includes the Worker report above and this second
reading. Clause (1)'s witnesses are explicitly nonempty, metrizable and
profinite, q is continuous and surjective, f is an Ω-valued 1-cocycle, and
nonexistence quantifies over continuous 0-cochains. Clause (2) separately
ranges over all covers, the split section with qσ=id, and every degree n+1.
The two Ω-valued primitives are continuous maps with pointwise specified
formulas, and satisfy the alternating boundary equations.

The substantive checks were the distinction between n (the Lean predecessor
index) and the node's positive degree n+1; the first-projection orientation
of q'; and the deletion of t_0 in the split formula. All are correct: common
q-images identify the section value on every face, and the first pair
coordinate is s while the second is t_i. I removed two redundant additional
conclusions from an initial draft (surjectivity of q' and a separate equation
saying the pullback is a cocycle), leaving just the stated pullback and its
specified primitive. A direct public import of the original continuous-map
dependency was also added. The revised file compiled cleanly again.

I checked that the arbitrary algebraic closure, norm-extension equality,
independent u,v universes, all-continuous cochains, all positive degrees,
and empty universal cases survive unchanged. A completed coefficient,
a finite-dimensional condition on Ω, a local-constancy condition, and a
section assumption on the counterexample would each be a mismatch;
none occurs. The eight-step docstring follows the live proof and does
not claim that the blueprint paragraph proved the discarded global input.


## New nodes

`def-sfb-profinite-cech-tuples` (sec-six-functors-basics) records
`Profinite.scalarCechTuples` and `Profinite.scalarCechDelete`, both already
in `Sheaf.Topology.NormedScalarProfiniteCechExact`. Its `lean.existing` is
true, with no new module and no duplicate declaration. This follows the
return's first permitted repair exactly: a definition node owning the
unchanged module's two definitions, rather than a theorem stmt_dep.

The new statement introduces its objects in full: T,V are compact Hausdorff
totally disconnected spaces (`{S T : Profinite.{v}}`); q is any continuous
map (`q : C(T,S)`); r is any natural number (`r : ℕ`). The tuple space is
`{t : Fin r → T // ∀ i j : Fin r, q (t i) = q (t j)}` with Lean's finite
product and subtype topology. Coordinate deletion is exactly precomposition
by `j.succAbove`, which leaves coordinates below j and shifts the others by
one; the equal-image proof is the existing `x.property` restricted to those
coordinates. There is no surjectivity, nonemptiness, or coefficient hypothesis.
For r=0 the empty tuple is unique, including when T is empty; for r=1 the
condition is vacuous; deletion of either endpoint agrees with the stated
ordering. The source is Stacks topology.tex, Tags 08ZY lemma-profinite and
0A2P lemma-describe-limits (proof, induced topology), with the Cech expansion
in simplicial.tex, Tag 016E example-fibre-products-simplicial-object.

Searches run for this repair (actual msearch responses copied into the new
node's mathlib_searches):

* LeanSearch: “Equal-image finite tuples in the Cech nerve of a continuous map
  of profinite spaces with coordinate deletion face maps”: eight abstract
  categorical Cech nerve/face-map hits, no matching concrete topological API.
* Loogle: “Profinite.scalarCechTuples, Profinite.scalarCechDelete”: no hits,
  unknown identifier scalarCechTuples in the Mathlib service.
* Mathlib grep: “scalarCechTuples|scalarCechDelete|cechNerve|CechNerve”: twenty
  abstract categorical Cech-nerve hits, no scalar tuple definitions.
* Local rg of lean/WeilConjectures and lean/Sheaf for scalarCechTuples,
  scalarCechDelete, setCechNerve and setCechFace: the exact definitions are
  the unchanged Sheaf/Topology/NormedScalarProfiniteCechExact.lean lines 33–41.
  Upstream setCechNerve/setCechFace are set-only with n+1 indexing and
  a fixed-zero equality condition; no topological structure is supplied.
* DAG rg for equal-image tuples and coordinate deletion finds
  def-sfb-set-cech-nerve, which records that set-only upstream interface.
  It does not record this topology-equipped subtype or zero-length tuples.
  No DAG definition already owns the two scalarCech definitions.
* blueprint_refs.py search “profinite Cech” and “coordinate deletion” each
  finds zero blueprint nodes. “fibre powers” finds six unrelated blueprint
  nodes, none defining this interface. ancestor on the item returns None,
  matching the inherited broken provenance chain; the new node preserves
  that null ancestor and prepends the item to its via list.

Second reading of the return repair: H2 and the mechanical theorem-stmt_dep
finding are resolved by replacing the theorem dependency with the new
existing-definition binding. I reopened both original definitions and the
new JSON and checked their complete signatures and bodies, including r=0
and endpoint deletion. The existing import remains correct because the new
node's lean.module is that same unchanged module. The Lean module and main
signature are byte-for-byte retained; no statement_change is needed, no
source claim is weakened, and no proof dependency is promoted to stmt_deps.
There is no dependency module and no further postponed theorem. The only
sorry is still the main theorem's proof.

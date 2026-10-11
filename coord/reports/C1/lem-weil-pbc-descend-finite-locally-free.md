## Worker report

The module states `AlgebraicGeometry.descend_finite_locally_free` for a directed inverse
system `D : Iᵒᵖ ⥤ Scheme` with affine transitions and a limit cone.  The objects `X₀` and
`Y₀` are schemes over the stage `D.obj (op i₀)`, and `f₀` is their morphism over that base.
The compact and quasi-separated hypotheses on both source and target render the node's
quasi-compact and quasi-separated assumptions.  `LocallyOfFinitePresentation f₀.left` is the
node's finite-presentation hypothesis.  The morphism `f` is explicitly required by `hf` to be
the pullback base change of `f₀` to the limit.  Its typeclass
`Scheme.Hom.IsFiniteLocallyFree f` renders the finite locally free limit hypothesis.
The first conjunction clause is the existence of `i ≥ i₀` for which the explicitly constructed
pullback map is finite locally free.  The second clause says that for every `d : ℕ`, if the
limit map has degree `d`, then some such stage map has degree `d`.

The dependency declarations used are `AlgebraicGeometry.Scheme` and pullbacks from Mathlib;
`AlgebraicGeometry.exists_limit_affine_transition` from
`Sheaf.AlgebraicGeometry.LimitAffineTransition`; and
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` from
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.

Edge cases checked: `I` is nonempty and permits an arbitrary chosen base index `i₀`; degree is
quantified over all natural numbers including `0`; no nonemptiness of schemes or fibres is
assumed; universes use one `u` for the index and schemes.

Searches: `msearch.py leanfinder` for finite-locally-free descent (no match); `msearch.py loogle`
for `AlgebraicGeometry.Scheme.Hom.finrank` and `CategoryTheory.Limits.IsLimit` (no match);
`msearch.py grep` and `rg` through Mathlib and `WeilConjectures` (no descent theorem found).
The existing source declaration for finite locally free was used rather than redefining it.

## Earlier second reading (a previous round; superseded)

I reread the node and module.  The inverse system, affine transition typeclass, limit cone,
chosen index, base schemes, morphism, qcqs hypotheses, finite-presentation hypothesis, limit
base-change equation, finite-locally-free conclusion, and degree-preservation implication each
have a corresponding binder or clause in the Lean signature.  The Over formulation packages
“schemes over `S₀`” and `f₀` being over `S₀`; `pullback.map` gives the stated base changes.
No statement correction or new node is needed.

## Second reading by C1

Read the node copy, all seven statement-dependency nodes, their recorded Lean declarations,
the delivered module, and Stacks limits.tex at lines 1738–1747 (Situation 081D) and
1901–1928 (Lemma 06AC). The Stacks source is the local copy at
/home/ubuntu/c1-stacks-review/limits.tex; the repository literature directory has no limits.tex.
The source agrees with the node, including qcqs S₀. No node-statement correction is needed.

Object/hypothesis/conclusion checklist, with the final Lean rendering and verdict:

- Directed set I: `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`.
  Correct; the preorder form is the project convention for directed sets. Nonemptiness is
  also witnessed by the explicitly chosen i₀.
- Inverse system of schemes Sᵢ: `D : Iᵒᵖ ⥤ Scheme.{u}`. Correct: opposite order makes
  D.map (homOfLE hi).op go from Sᵢ to Sᵢ₀.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]`.
  Correct; Mathlib Morphisms/Affine.lean defines this by affine inverse images.
- Limit S with projections: `(c : Cone D) (hc : IsLimit c)`, with S = c.pt and
  projections c.π.app. Correct: Mathlib Cone and IsLimit give the actual categorical
  limit, not merely an arbitrary compatible cone. The recorded dependency
  exists_limit_affine_transition was opened and provides existence of this same limit;
  no invocation of that theorem is needed in a stage-2 statement given a limit cone.
- Chosen 0 ∈ I: `(i₀ : I)`. Correct; no least-element assumption.
- S₀ quasi-compact and quasi-separated:
  `[CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]`.
  MISSING in the first worker's Lean, despite occurring in the node and Situation 081D;
  added both binders. No qcqs assumption is added on earlier/incomparable stages.
- X₀ and Y₀ over S₀ and f₀ over S₀:
  `(X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)`.
  Correct: Over packages structure maps and f₀.w asserts that f₀.left commutes with them.
- X₀ and Y₀ qcqs: CompactSpace and QuasiSeparatedSpace binders on X₀.left and Y₀.left.
  Correct: compactness here is quasi-compactness, with no Hausdorff condition; Mathlib's
  quasiSeparatedSpace_iff_forall_affineOpens identifies scheme quasi-separatedness.
- f₀ locally of finite presentation: `[LocallyOfFinitePresentation f₀.left]`.
  Correct, not an extra finite-presentation hypothesis on either structure morphism.
  Opened Morphisms/FinitePresentation.lean: finite presentation on affine ring maps.
- X, Y and f are base changes to S: the type of f is the map between the two chosen
  pullbacks, and hf equates it to pullback.map with f₀.left and identity maps on S and S₀.
  Correct; opened pullback and pullback.map in Mathlib's HasPullback.lean. The equality
  hf selects the canonical base-changed morphism, imposing no extra property.
- f finite locally free: `[Scheme.Hom.IsFiniteLocallyFree f]`. Correct; opened the
  dependency declaration in WeilConjectures/AlgebraicGeometry/Morphisms/FiberDegree.lean:
  it extends IsFinite, Flat, and LocallyOfFinitePresentation, exactly as the node defines.
- First conclusion: `∃ (i : I) (hi : i₀ ≤ i), Scheme.Hom.IsFiniteLocallyFree (...)`.
  Correct: the displayed pullback.map uses the transition Sᵢ → Sᵢ₀, f₀.left, and identities,
  so it is precisely fᵢ, not a freely chosen morphism or another model.
- Degree clause: `∀ d : ℕ, Scheme.Hom.IsFiniteLocallyFreeOfDegree f d → ∃ i hi, ... d`.
  Correct: the existing degree predicate extends finite local freeness and asserts every
  fibre's residue-field dimension equals d. No independently redefined rank. The two
  existential witnesses may differ, as in the node, and the degree witness is itself
  finite locally free. Quantifiers have the intended order.

Dependency audit: Scheme is Mathlib's locally affine locally ringed space; pullback is its
categorical fibre product (scheme pullbacks exist). The scheme-conventions node explicitly
collects other notions and provides no separate definition to import. The finite-locally-free
node records both predicates used here. All recorded notions are usable; no private copy,
new definition node, dependency module, or correction of the node was necessary.

Edge cases: empty I cannot supply i₀ and is outside the source situation; singleton I is
allowed. Empty schemes are allowed, including S₀, X₀, Y₀ and c.pt; there are no Nonempty
scheme or surjectivity hypotheses. Degree d = 0 is covered; on an empty target the degree
condition is correctly vacuous. No characteristic, field, Noetherian, reducedness, or
separatedness condition is imposed. The original single universe tied I to schemes; changed
I to independent Type v while schemes remain Scheme.{u}, and the server compiled this.
All variables and both universes are explicitly bound.

Independent searches (2026-10-11): msearch leanfinder for “inverse limit schemes descent
finite flat constant rank morphism” returned eight affine-transition-limit results about
factorization/equality of morphisms or sections, none this descent statement. Loogle query
`"IsFiniteLocallyFree"` returned zero hits. LeanSearch for “Finite flat morphisms of finite
presentation descend along inverse limits of schemes with affine transition maps” was
unavailable (HTTP Internal Server Error); no verdict is inferred from its failure. msearch
grep `descend_finite_locally_free|descend.*finite.*flat|06AC` found only faithfully-flat
finite-type/presentation descent results, not inverse-limit finite-locally-free descent.
Direct rg of Mathlib/AlgebraicGeometry, the upstream WeilConjectures tree, and lean/Sheaf
for `descend.*(free|flat)|finite.*locally.*free|06AC` found the existing finite-locally-free
predicates and unrelated sheaf/Hilbert statements, no duplicate theorem. Exact-name search
of dag/lean_names_upstream.json, upstream, and lean/Sheaf found no existing declaration.

Repairs: added missing qcqs S₀ binders; separated index and scheme universes; added the
standard copyright/license header; expanded the theorem docstring from a compressed
argument to the node's four proof steps and named dependencies, with Situation 081D in
both source references. Removed the unused LimitAffineTransition import: the statement
uses only Mathlib's Cone/IsLimit, available from FiberDegree, rather than that existence
theorem. Updated lean.statement verbatim from the final signature. The Worker report
above is retained as requested; its incomplete account of the qcqs assumptions and
its assertion that exists_limit_affine_transition was used are superseded by this audit.
There is no definition with sorry; the only theorem proof remains `by sorry`, and the small
proofs in the signature merely witness the pullback square's already-given commutativity.

Validation: the final single module compiled cleanly on the server through scompile.py
(exit code 0), with no errors or warnings.

## Reviewer fix (R-dfl1154)

The second reading's universe change was wrong: `{I : Type v}` with `Scheme.{u}` violates the
INDEX UNIVERSES rule (an independent index universe makes limit statements false); restored
`{I : Type u}`. The statement is rewritten in the landed descend-* family form (K1 eebffc4b0,
J1 bfbc053b5): the limit base change is `((Over.pullback (c.π.app (op i₀))).map f₀).left`
and the stage base change `((Over.pullback (D.map (homOfLE hi).op)).map f₀).left`, replacing
the explicit `f`/`hf : f = pullback.map …` pair (same morphism); the finite-locally-free
limit hypothesis is a named hypothesis `hf`. `[Nonempty I]` dropped (witnessed by `i₀`,
as in the landed siblings). Hypotheses otherwise unchanged; compiled clean.

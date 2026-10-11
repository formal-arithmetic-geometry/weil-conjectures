## Worker report

The module `Sheaf.AlgebraicGeometry.OpenRestrictionSupportTriangle` states
`AlgebraicGeometry.openRestriction_support_triangle`. Its only proof is `sorry`.
It completes the open-restriction adjunction unit to a distinguished triangle, with
quasi-coherent vertices, cohomology supported on the complement, and the conditional
bounded-below assertion. No definition or auxiliary theorem is introduced.

Hypotheses and clauses, matched individually:

- The scheme Y is `Y : Scheme.{u}`. Its quasi-compactness is `[CompactSpace Y]`;
  quasi-separatedness is `[QuasiSeparatedSpace Y]`, as in the scheme conventions.
- The open subscheme is `V : Y.Opens`; its quasi-compactness is
  `hV : IsCompact (V : Set Y)`. The scheme is `V.toScheme`, and its open immersion
  into Y is the canonical `V.ι`. This is the same arbitrary open subscheme as in
  the node, using Mathlib's chosen restriction rather than a separate isomorphic copy.
- The two explicit `HasDerivedCategory.{w}` binders supply the shared localizations
  of the module-sheaf categories on Y and V. They are category infrastructure,
  not geometric or boundedness assumptions. Both scheme and morphism universes
  are bound explicitly; there is no auto-bound variable and no restriction to a
  small set of points or cohomological degrees.
- `K : schemeDerivedCategory Y` with `hK : schemeDerivedQCohProperty Y K`
  renders precisely K in D_QCoh(Y). The predicate requires quasi-coherence in
  every integer degree, without any boundedness assumed initially.
- Exact open restriction `Lj* K` is
  `(schemeOpenRestriction Y V).mapDerivedCategory.obj K`. Direct image `Rj*`
  is `schemeDerivedDirectImage V.ι`. These are the landed shared definitions.
- The existential `adj` supplies the open-restriction/direct-image adjunction.
  It is a conclusion, not an added hypothesis. `adj.unit.app K` specifies the
  first arrow used by the source and the node's proof; it is not an arbitrary map.
  Adjunctions and their unit triangles differ only by the usual adjunction
  comparison on the direct-image vertex; no adjunction is assumed available from
  the caller. This is the same encoding used by the landed Mayer–Vietoris triangle.
- The existential `Q`, `β`, `δ` give the third vertex and the remaining arrows,
  with `δ : Q ⟶ K⟦(1 : ℤ)⟧`. `Triangle.mk (adj.unit.app K) β δ ∈
  distTriang (schemeDerivedCategory Y)` renders the distinguished triangle.
- The two conclusion predicates `schemeDerivedQCohProperty Y` require the
  middle vertex and Q to be in D_QCoh(Y). Together with hK they express a
  triangle in the full quasi-coherent derived subcategory, using the ambient
  distinguished-triangle predicate. No separate triangulated instance or chosen
  abelian structure on that full subcategory is introduced.
- For every `n : ℤ` and `x : Y` in V, the carrier of the stalk at x of the
  nth cohomology sheaf of Q is `Subsingleton`. A zero module has exactly this
  property. Thus its nonzero-stalk locus is contained in Y minus V, precisely
  the support clause, including all degrees. No closedness claim about the
  nonzero-stalk locus itself is imposed.
- `((∃ a : ℤ, K.IsGE a) → ∃ b : ℤ, Q.IsGE b)` is exactly the last clause.
  Mathlib's `DerivedCategory.isGE_iff` identifies IsGE a with vanishing of
  cohomology below a. Combined with the quasi-coherent predicates above, these
  existentials are membership in D_QCoh^+. The conclusion asks for a bound,
  not a particular numerical improvement or the same bound as K.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is a convention record without a declaration.
  Its scheme/quasi-compact/quasi-separated/open-immersion notions are Mathlib's
  `Scheme`, `CompactSpace`, `QuasiSeparatedSpace`, and the canonical open `V.ι`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`.
  The former uses the shared SheafOfModules carrier and abelian instance; the
  latter tests all cohomology sheaves. The module arrives transitively via the
  direct-image module, not via a private definition.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`, specialization of
  `RingedSpace.derivedModuleDirectImage` to the underlying ringed-space morphism.
  Its full definition and the ringed-space right-derived-functor definition were read.
- `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps`:
  `AlgebraicGeometry.schemeOpenRestriction`, its additivity and finite-limit/
  finite-colimit instances. Its definition is exactly overFunctor composed with
  the explicit overEquiv functor, and mapDerivedCategory is exact restriction.
  The already-landed node `def-pc-derived-open-restriction-maps` is added to
  stmt_deps to cite this shared declaration; no new node is needed.
- Mathlib: `DerivedCategory.homologyFunctor`, `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`, `TopCat.Presheaf.stalk`, `Triangle.mk`, `distTriang`.

Edge cases checked mathematically before writing: V empty allows an arbitrary
supported cone, with the support test vacuous; it does not demand Q = 0. V = Y
makes the unit an isomorphism and forces every cohomology stalk of Q to vanish.
Y empty and K zero are included without Nonempty or nonzero hypotheses.
Unbounded K is allowed, and does not trigger a boundedness conclusion. The bound
for bounded-below K may drop by one in the mapping cone, so no unjustified
same-bound conclusion is stated. Negative cohomological degrees are included.
No characteristic, Noetherian, affine, or separated hypothesis is added.

Searches for an existing statement:

- msearch.py leansearch, query "open restriction derived pushforward triangle
  supported closed complement": service unavailable (Internal Server Error).
- msearch.py leanfinder, query "distinguished triangle K to derived pushforward
  of restriction with cone supported on complement open": eight hits including
  DerivedCategory.triangleOfSESIso, mem_distTriang_iff, and mappingCone triangle
  comparisons, but no scheme restriction/support statement.
- msearch.py loogle, query "Triangle.mk, DerivedCategory.homologyFunctor":
  zero hits, unknown identifier Triangle.mk.
- msearch.py grep, query "restriction.*triangle|triangle.*restriction" in
  Mathlib AlgebraicGeometry: zero hits.
- rg of WeilConjectures for the item id and open-restriction/support-triangle
  text: no matching theorem. An adic lower-star proof mentions restriction of
  a triangle but is a different category and statement.
- rg of lean/Sheaf for support-complement, restriction-triangle and support-stalk
  APIs found the citer RightAdjointOpenSupportCriterion and the shared support
  convention in SupportedPerfectGenerator, but no theorem stating this node.
- tools/lean_names_upstream.py show for the item: no attached declaration.
- The proposed declaration name was searched in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no collision.

Source checked: the repository's literature/stacks-project checkout is absent
on this machine, so the source was opened at
https://stacks.math.columbia.edu/tag/0E4G, proof of Lemma 48.4.3. It agrees with
both the support triangle and the conditional bounded-below conclusion. The
node statement requires no correction, and there is no STATEMENT-DISPUTED flag.

Validation: lcompile.py compiled the module cleanly in 3.5 seconds, with no errors
or warnings. The final deliver2.py --no-push result is recorded below after running
its server compile and maintainer preflight. The independent second reading is
left to the second worker, as required.

The required dry run printed OK: the server compile passed and the maintainer
preflight passed except for the intentionally absent independent second reading.
Nothing was pushed. The second reader writes that section and delivers the item.

## Second reading by U1

Independent reading of the node copy and the complete Lean file, with all four
statement-dependency nodes and their recorded modules open. Verdict: PASS; no
mathematical, signature, or convention mismatch found. Only this review report
was added; the Lean and node copy were retained.

Source read independently: Stacks `duality.tex`, section
`section-restriction-to-opens`, through `lemma-when-sheafy` and its proof
(Lemma 48.4.3, https://stacks.math.columbia.edu/tag/0E4G).
The local literature checkout is absent, so I fetched the original Stacks TeX
into the item's scratchpad. I also read `perfect.tex`,
`lemma-quasi-coherence-direct-image` (Lemma 36.4.1) and
`definition-supported-on` (Definition 36.6.1). The surrounding section assumes
qcqs schemes and a quasi-compact open V; it imposes no Noetherian, separated,
characteristic, or coefficient-field condition on this triangle argument.
The proof's bounded and unbounded cases agree with the node. The other scheme X,
morphism f, and right adjoint a are needed only for the surrounding criterion,
not for construction of the triangle on Y.

The node's objects, hypotheses, and conclusions, matched item by item:

- Arbitrary scheme Y: `Y : Scheme.{u}`. Quasi-compact:
  `[CompactSpace Y]`. Quasi-separated: `[QuasiSeparatedSpace Y]`.
  These are precisely the topological qcqs conditions for schemes. PASS.
- Quasi-compact open subscheme V with its inclusion j: `V : Y.Opens`,
  `hV : IsCompact (V : Set Y)`, `V.toScheme`, and `V.ι`.
  A canonical open restriction models any open subscheme by its canonical
  isomorphic copy; no affine or principal-open condition appears. PASS.
- K in D_QCoh(Y): `K : schemeDerivedCategory Y` and
  `hK : schemeDerivedQCohProperty Y K`. Reading DerivedCategory.lean shows
  that the carrier is the derived category of O_Y-module sheaves, and the
  predicate tests quasi-coherence of cohomology in every integer degree.
  It is not the derived category of the abelian category QCoh(Y). PASS.
- Lj* K: `(schemeOpenRestriction Y V).mapDerivedCategory.obj K`.
  DerivedOpenRestrictionMaps.lean defines this restriction by overFunctor
  followed by the explicit overEquiv functor, with additive and exactness
  instances. This is the shared exact restriction required by the contract.
  No module-pullback convention is substituted for it. PASS.
- Rj* Lj* K: `(schemeDerivedDirectImage V.ι).obj` applied to the preceding
  object. SchemeDerivedDirectImage.lean specializes the ringed-space direct
  image; RingedSpaceDerivedDirectImage.lean uses the unbounded right derived
  functor of moduleDirectImage, not underived direct image. PASS.
- Triangle K → Rj* Lj* K → Q → K[1]: the existential `adj` is the
  restriction/direct-image adjunction, `adj.unit.app K` is its first arrow,
  and existential `Q`, `β`, `δ` supply the cone and the other two arrows.
  `δ : Q ⟶ K⟦(1 : ℤ)⟧` gives the required cohomological shift, and
  `Triangle.mk (adj.unit.app K) β δ ∈ distTriang (schemeDerivedCategory Y)`
  gives distinguishedness. The adjunction is supplied in the conclusion,
  not required of the caller. Its existence is the standard derived open
  restriction adjunction; different choices identify the unit triangles by
  the comparison automorphism of the right adjoint. Thus this encoding
  expresses the source's unit triangle. PASS.
- Triangle in D_QCoh(Y): hK and the two conclusion predicates
  `schemeDerivedQCohProperty Y` on the middle object and Q put all vertices
  in the full quasi-coherent subcategory. Its triangles are the ambient
  distinguished triangles on these vertices. No extra closure hypothesis
  is imposed on the caller. PASS.
- All cohomology sheaves of Q supported on Y minus V: for every `n : ℤ`
  and `x : Y`, `x ∈ V` implies `Subsingleton` of the carrier of the stalk
  of `((DerivedCategory.homologyFunctor ... n).obj Q).val.presheaf` at x.
  Reading the shared module-sheaf carrier shows this is the additive
  underlying stalk of H^n(Q). A module stalk vanishes exactly when its
  carrier is subsingleton. This states containment of support in the closed
  complement, without asserting that the support itself is closed. PASS.
- If K is bounded below, Q is bounded below:
  `((∃ a : ℤ, K.IsGE a) → ∃ b : ℤ, Q.IsGE b)`.
  Mathlib's `DerivedCategory.isGE_iff` says exactly that all cohomology
  below the bound vanishes. With hK and the conclusion's quasi-coherence,
  these are the two D_QCoh^+ memberships. The same Q satisfies both the
  support and conditional boundedness clauses; the bound need not equal a.
  PASS.
- Infrastructure and quantifiers: both `HasDerivedCategory.{w}` instances
  are the shared localizations for the categories actually used, not
  additional geometric hypotheses. Universes u and w are explicit and
  arbitrary. Y, V, K are universal inputs; adj, Q, β, δ are existential
  outputs; the degree, point, and boundedness quantifiers have the node's
  scope. No finiteness, nonemptiness, or initial boundedness assumption
  was added. PASS.

Edge cases: V empty makes the stalk condition vacuous and permits the cone
K[1]; V = Y makes the unit invertible, with acyclic cone. The empty scheme
and zero K are allowed. Unbounded K is allowed without a demanded lower
bound; bounded-below K gives a bound for that same cone. Degree zero and
all negative degrees occur because the quantifier is over ℤ. There is no
index set or integer n ≥ 0, nor any characteristic restriction. Arbitrary
scheme universe u and localization universe w are bound explicitly.

One-definition-per-notion searches, repeated independently with different words:

- LeanFinder: `localization triangle derived sheaves open immersion vanishing
  stalks`; eight hits, principally open-immersion stalk comparison and affine
  site localization, none stating this qcqs derived-module support triangle.
- Loogle: `CategoryTheory.Adjunction.unit`; twelve hits concerning the generic
  unit and its transport, none giving the geometric triangle or its clauses.
- LeanSearch: `cone of derived open immersion unit has cohomology zero on the
  open subset`; service unavailable (Internal Server Error), recorded as
  unavailable rather than as a negative search result.
- rg on Mathlib's AlgebraicGeometry and Algebra/Homology, upstream
  WeilConjectures, and project lean/Sheaf for `localization.*triangle`,
  `triangle.*localization`, `support.*triangle`, `triangle.*support`,
  `jStar`, `jShriek`, and the proposed name. I opened upstream
  SixFunctors/OpenClosed/Supports.lean and Etale/Derived/Localization.lean:
  their support triangles concern étale sheaves with an arbitrary coefficient
  category, not quasi-coherent O_Y-module cohomology on the Zariski site.
  They therefore cannot serve this node. The project's
  RightAdjointOpenSupportCriterion cites this triangle but does not state it.
  No existing exact match or declaration-name collision was found.

The added statement dependency def-pc-derived-open-restriction-maps is already
landed and supplies the shared restriction declaration. Adding that recorded
node is allowed by brief-stage2 §5. There are no new definition nodes,
dependency modules, statement_change, or STATEMENT-DISPUTED flag to review.
No hollow definition or local notation is introduced. The single named theorem
has only `sorry` as its proof. The module and theorem docstrings give the source
and blueprint id; the theorem's three proof steps cover the node's K-injective
cone construction, restriction/support argument, and bounded-below resolution
argument, with their dependencies. Imports are used and lines meet the limit.

Validation: lcompile.py compiled the unchanged module cleanly (exit 0, 3.6 s).
The stage2_delivery.py signature extractor matches lean.statement exactly.
No implicit variable or universe is unbound; autoImplicit is explicitly false.

## Worker report

The module `Sheaf.AlgebraicGeometry.ProperNormalizedFibres` states
`AlgebraicGeometry.Scheme.Hom.connectedSpace_fiber_of_isProper_of_globalSections_iso`.
Its only theorem proof is `sorry`; no definitions or proofs were added.

Hypothesis and clause correspondence:
- A ring R: `{R : Type u} [CommRing R]`, including the zero ring.
- A scheme X and a morphism to Spec R: `{X : Scheme.{u}} (f : X ⟶ Spec (.of R))`.
- Properness: `[IsProper f]`, the recorded dependency declaration.
- H^0(X,O_X) = R: `[IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)]`.
  This is the canonical R-algebra identification, as in the source's normalized affine
  reduction, not an unrelated abstract ring isomorphism. `ΓSpecIso.inv` identifies R
  with the global sections of Spec R and `f.appTop` pulls sections back to X.
- Every scheme-theoretic fibre: the arbitrary binder `(s : Spec (.of R))` and `f.fiber s`.
- Nonempty and connected: `ConnectedSpace (f.fiber s)`. Mathlib's class extends
  `PreconnectedSpace` and includes `toNonempty`, so both clauses are present, without
  a redundant extra conjunct.

Dependencies used:
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; read its complete class signature and docstring.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`; read its definition and the projection declarations.
- `def-weil-connected-scheme`: its mathlib_match `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`; read the full class definition and docstring.
  This module is supplied transitively by the algebraic geometry imports.
- Canonical sections infrastructure: `Scheme.Hom.appTop` and `Scheme.ΓSpecIso`
  in `Mathlib.AlgebraicGeometry.Scheme`; read their signatures and docstrings.

Source checked: https://stacks.math.columbia.edu/tag/03H2, proof of Theorem 37.53.5.
The local literature file is absent on this machine, so the primary source webpage was read.
It explicitly reduces to a proper map to Spec R with canonical global sections R and
proves that the fibre at any point is connected, having already established nonemptiness.
No Noetherian, reducedness, domain, or field hypothesis is assumed in this reduction.
The declaration docstring carries all three DAG proof steps and their dependency ids.

Edge cases checked before writing: for the zero ring Spec R has no points, so the statement
has no fibre to check. For an empty X over a nonzero R, the canonical sections map cannot
be an isomorphism (its target is the zero ring). For the identity of Spec R its fibres are
spectra of residue fields and are nonempty connected. Nilpotents and arbitrary
characteristic are allowed. Disconnected bases are allowed: connectedness is asserted
only fibre by fibre. A disconnected fibre cannot pass as merely preconnected, since the
conclusion uses ConnectedSpace. The shared universe u is the usual Scheme/CommRingCat
universe, with arbitrary u explicitly declared and no auto-bound variables.

Searches performed:
- msearch.py leanfinder: "proper morphism to affine scheme whose canonical global sections
  map is an isomorphism has nonempty connected fibres". Eight hits: IsProper, its
  characterizations, proper/finite-affine criterion, proper maps, affine fibres; no match.
- msearch.py loogle: "AlgebraicGeometry.IsProper, ConnectedSpace". Zero hits.
- msearch.py leansearch: "proper scheme morphism global sections isomorphism connected
  fibers". Unavailable: Internal Server Error. No mathematical verdict from this service.
- msearch.py grep in AlgebraicGeometry: "connected.*fiber|fiber.*connected|ConnectedSpace".
  Eight hits, mainly geometrically connected fibre infrastructure; no proper/global
  sections criterion.
- rg in the project source WeilConjectures and in lean/Sheaf:
  "stein|Stein|normalized.fibre|normalizedFibre|lem-weil-pbc-stein-normalized-fibre-idempotent".
  Read HenselianConnectedness's Stein inputs: these impose different hypotheses and state
  different conclusions (Noetherian finiteness, or intersections with a henselian closed
  fibre), so none is this statement.
- rg in both trees: "connectedSpace.*fiber|connectedSpace_fiber_of|IsIso.*appTop|IsIso.*Γ.map".
  Generic connectedness, slicing, and global-sections examples only; no exact statement
  and no declaration with the proposed full name.
- rg over Mathlib AlgebraicGeometry read the proper, fibre, appTop and ΓSpecIso definitions.

No new nodes, dependency replacements, statement corrections, or disputed statements.

## Second reading by R1

Read the base node, its sandbox copy and ProperNormalizedFibres.lean independently.
The node's objects, hypotheses and conclusions match as follows:

- Ring R: `{R : Type u} [CommRing R]`. Verdict: exact; a ring in the
  scheme source is commutative with identity, and no nontriviality is imposed.
- Scheme X: `{X : Scheme.{u}}`. Verdict: exact; X is unrestricted.
- Morphism f to Spec R: `(f : X ⟶ Spec (.of R))`. Verdict: exact.
- Proper f: `[IsProper f]`. Verdict: exact. Opened the declaration and docstring
  in Mathlib.AlgebraicGeometry.Morphisms.Proper: separated, universally closed,
  locally finite type. UniversallyClosed.lean:167 supplies quasi-compactness,
  so this is the dependency node's finite-type properness, not a weaker notion.
- H^0(X,O_X)=R: `[IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)]`.
  Verdict: exact in the source's canonical sense. Opened Scheme.lean:178-185
  and 592-620: appTop is pullback on global sections, and ΓSpecIso identifies
  Γ(Spec R,O) with R. Their composite is precisely the structural ring map
  R → Γ(X,O_X); an unrelated abstract ring isomorphism would not suffice.
- Every point s of Spec R: `(s : Spec (.of R))`, after all hypotheses.
  Verdict: exact universal quantifier, with no chosen point assumed beforehand.
- Scheme-theoretic fibre X_s: `f.fiber s`. Verdict: exact. Opened the recorded
  definition in Mathlib.AlgebraicGeometry.Fiber:38 and its docstring: the
  pullback along the canonical map from Spec of the residue field. Read the
  projection signatures and fiberHomeo; this is not the set of geometric lifts.
- Nonempty fibre: `ConnectedSpace (f.fiber s)`, whose `toNonempty` field is
  `Nonempty (f.fiber s)`. Verdict: present, with no extra hypothesis.
- Connected fibre: the same conclusion extends `PreconnectedSpace`.
  Verdict: exact. Read Topology.Connected.Basic:697-709 and the dependency
  node's definition of connectedness; empty spaces are excluded in both.

Source check: literature/stacks-project is absent here. Obtained the primary
Stacks more-morphisms.tex in scratchpad/more-morphisms.tex and read the complete
`theorem-stein-factorization-general` and proof, lines 15289-15354, together
with https://stacks.math.columbia.edu/tag/03H2. Its normalized affine reduction
explicitly asks for proper X → Spec R with canonical Γ(X,O_X)=R and an arbitrary
point s. Nonemptiness is already supplied by the universally closed Stein
factorization; connectedness follows by lifting a fibre idempotent and factoring
through κ(s). No Noetherian, domain, reducedness, field, or characteristic
assumption is inherited. The node's three proof steps, including every named
input and the local-ring unit/maximal-ideal argument, are carried in the theorem
docstring. The stronger geometrically connected conclusion of the full Stein
theorem is not added to this normalized-fibre node.

Edge cases: zero R is allowed, and Spec R then has no s, so the assertion is
vacuous. Empty X over a nonzero R cannot satisfy the canonical isomorphism,
since its global sections are the zero ring; no empty scheme is excluded by a
binder. Empty X over zero R is allowed. The identity of Spec R satisfies the
hypotheses and has residue-field fibres. Disconnected and nonreduced bases,
arbitrary characteristic, and non-Noetherian rings remain covered. There is
no index set or integer n in this statement. The explicit arbitrary universe u
is the common Scheme/CommRingCat universe; any pair of sizes can be represented
in a common larger universe, with no test-object quantifier restricted below
its base. Every variable and universe is bound.

Independent searches used different phrases from the worker:

- msearch.py leanfinder: "Stein factorization proper scheme with structure sheaf
  pushforward equal to the base has connected point fibers". Eight hits, proper
  and integral morphism infrastructure; no normalized-fibre theorem.
- msearch.py loogle: "ConnectedSpace, Scheme.Hom.fiber" could not resolve the
  short fibre identifier. Repeated with "AlgebraicGeometry.IsProper,
  ConnectedSpace": zero hits.
- msearch.py grep: "IsIso.*appTop|connectedSpace.*fiber|fiber.*ConnectedSpace".
  Four hits; inspected Geometrically/Connected.lean:63-67. Its fibre instance
  assumes GeometricallyConnected f, not our proper/global-sections hypothesis.
- rg on Mathlib AlgebraicGeometry, WeilConjectures and the project's lean/Sheaf:
  "stein|connected.{0,60}fib(er|re)|fib(er|re).{0,60}connected|globalSections_iso|IsIso.*appTop".
  Opened HenselianConnectedness.lean:51-93: its Stein finiteness requires a
  Noetherian ring and its connected intersection theorem requires a henselian
  pair; neither states this result. GenericConnectedness concerns finite-type
  ring fibres over a dense open with domain and Noetherian hypotheses. The
  Γ/Spec Stein factorization definitions only give the factorization map.
- rg of the exact node id and declaration name in dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf returned no existing declaration.

No duplicate notion or statement was found. There are no new definition nodes,
dependency modules, hollow definitions, statement corrections, or disputed
statements in this delivery. Both imports serve the statement; namespaces,
source tags, line widths and sorry-only proof meet the stage conventions.
No mathematical or Lean mismatch was found, so the module and node were left
unchanged. Only this independent second-reading report was added.

Validation: scompile.py R1 lem-weil-pbc-stein-normalized-fibre-idempotent
lean/Sheaf/AlgebraicGeometry/ProperNormalizedFibres.lean compiled cleanly in
1.7 seconds, exit code 0, without warnings. The node's lean.statement is the
verbatim theorem signature, excluding `:= by`.

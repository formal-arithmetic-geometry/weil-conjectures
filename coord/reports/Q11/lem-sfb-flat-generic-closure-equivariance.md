## Worker report

The module `Sheaf.AlgebraicGeometry.FlatGenericClosureEquivariance` states
`AlgebraicGeometry.flat_generic_closure_equivariance`, with its entire proof `sorry`.
It defines no new notion. The node's statement and dependency lists are unchanged.

Hypothesis correspondence:

- The field is `(k : Type u) [Field k]`. The integral finite-type k-schemes
  S₀, S, T and V have `[IsIntegral ...]`, explicit structure maps p₀, pS, pT,
  pV and `[LocallyOfFiniteType ...] [QuasiCompact ...]` for each structure map.
  The equations hu, ht, hv, hr specify that all displayed base morphisms are k-morphisms.
- The morphism u is birational through `bu : S.PartialIso S₀` and hbu, which
  requires the dense-open isomorphism to restrict this actual u. Likewise bv and hbv
  witness birationality of v. This does not substitute a birational correspondence
  unrelated to the displayed morphism. The domination equation is `hvr : r ≫ v = u`.
- `ηS` and `ηV` are the unique maps from Spec K to the two birational models;
  hηS and hηV say their generic-base squares are cartesian, and hηr identifies their
  composite through r. These are explicit representatives of the canonical generic
  identifications implied by birationality, rather than additional restrictions on
  the morphisms. Here K is literally `S₀.functionField`. No independent scalar field
  is introduced and no universe is identified with another.
- `t` has `[IsHProjective t]`. The square hN identifies `(n,q)` with its generic
  fibre N, including both maps to T and Spec K. `[Smooth q]`,
  `[GeometricallyIntegral q]`, and hdim express the smooth geometrically integral
  curve assumption. The redundant `[IsIntegral N]` provides the generic stalk type;
  it follows already from geometric integrality over the field.
- d is the given closed immersion D into N; `[IsFinite (d ≫ q)]` and
  `[Etale (d ≫ q)]` express the finite etale marking. There is no nonemptiness
  assumption on D. The closed immersion iL with hL is its schematic closure in T:
  `iL.ker = (d ≫ n).ker`.
- H has `[Group H] [Finite H]`. σ₀, σS, σT are homomorphisms into scheme
  automorphism groups. σk acts on Spec k; by the anti-equivalence for affine spectra
  this encodes exactly an action on the field (a field action h is sent to Spec of
  its inverse). This includes semilinear actions. heq₀, heqS and heqT give
  compatibility with k; hequ and heqt give compatibility with u and t.
  σK, σN and σD, with heqK, heqn, heqq and heqd, specify the induced generic
  actions and scheme-theoretic preservation of D. Their compatibility uniquely
  determines these induced actions. There is no action on V, r, TV or LV.
- TV has the closed immersion iV into the actual `pullback t v`; hfV identifies
  its structure map fV. The equations hnVT and hnVV specify the unique generic
  inclusion nV over T and V. The kernel equality hTV makes TV precisely the
  schematic closure of N. jV is the closed immersion LV into TV, and hLV makes
  it the closure of D. The representation nV is part of the closure's canonical
  factorization, not an unconstrained map replacing the construction.
- `[IsHProjective fV] [Flat fV] [LocallyOfFinitePresentation fV]`, with
  QuasiCompact and QuasiSeparated, render projectivity, flatness and finite
  presentation. hpureV tests every component of the fibre over the explicit
  algebraic closure of each residue field and requires `topologicalKrullDim Z = 1`.
- The composite `jV ≫ fV` has IsFinite, Flat, LocallyOfFinitePresentation,
  QuasiCompact and QuasiSeparated, exactly finite, flat and finitely presented.
- hP says `(π,p)` is the pullback of fV along r. hM says `(πM,iM)` is the
  pullback of jV along π; pasting identifies M with LV times_V S. iP and hiPT,
  hiPS specify the unique ambient map into W = `pullback t u`. Thus these
  binders represent the actual products and their maps, without assuming the
  integrality, closedness, generic identifications or equivariance to be proved.

Conclusion correspondence:

- `∃ (_ : IsIntegral P)` supplies integrality, and the equivalence e of function
  fields is pinned by equality of its ring homomorphism to the stalk map of nP,
  after the displayed generic-point equality hgeneric. Thus it is specifically
  `k(P) = k(N)` via the generic inclusion, rather than an arbitrary field isomorphism.
- IsClosedImmersion iP and iM give the claimed closed subschemes. The next clauses
  give H-projectivity, flatness, finite presentation and componentwise geometric
  pure dimension one for P over S, and finite flat finite presentation for M over S.
- The existential nP and dM supply the canonical generic inclusions. Their
  IsPullback clauses identify the generic fibres with N and D over Spec K. Their
  equations specify the maps through TV, T and P, so also specify the marking's
  map to T and both maps to Spec K.
- `iP.ker = (nP ≫ iP).ker` and
  `(iM ≫ iP).ker = (d ≫ nP ≫ iP).ker` identify P and M with the intrinsic
  closures in W. They express independence as closed subschemes: hiPT, hiPS and
  the cartesian square for nP determine its composite into W from the fixed n,
  q and ηS, independently of V or r. Hence every allowed domination gives the
  same two ideal sheaves of W, including all scheme structure.
- τP and τM are genuine group actions by automorphisms. The seven equivariance
  equations express equivariance over S, over T, along M into P, and on both
  generic inclusions. In particular, the equations on the two projections from W
  mean the action on W restricts to these actions. No action on V is concluded
  or required, and no faithfulness assumption is made.
- `iM.ker = (d ≫ nP).ker` is closure of D inside P. The final empty-marking
  consequence is `(IsEmpty D → IsEmpty M)`.

Dependency declarations read and reused (module, declaration):

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsIntegral`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective:
  `AlgebraicGeometry.IsHProjective`, with its finite coordinate type convention.
- WeilConjectures.AlgebraicGeometry.FunctionField and
  Mathlib.AlgebraicGeometry.FunctionField: `Scheme.functionFieldOfComponents`
  and `Scheme.functionField`. The integral-scheme clause of def-sc-function-field
  uses the latter, namely the generic stalk; no component product is substituted.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  `pullback`, `pullback.fst`, `pullback.snd`, with `IsPullback` specifying
  arbitrary representatives of these same universal products.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Geometrically.Integral:
  `AlgebraicGeometry.GeometricallyIntegral`.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: `AlgebraicGeometry.Etale`.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: `AlgebraicGeometry.IsFinite`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; finite presentation also includes
  QuasiCompact and QuasiSeparated, as the dependency's comparison clause requires.
- Mathlib.AlgebraicGeometry.Stalk and .ResidueField:
  `Scheme.fromSpecStalk` and `Scheme.fromSpecResidueField`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.

Additional existing APIs: Mathlib's `Scheme.PartialIso`, `Scheme.Hom.ker`,
`CategoryTheory.Aut`, and monoid homomorphisms supply all remaining notions.
The proof-only imports include the recorded reduced-image theorem and projective
space base-change theorem, and the exact localization and flat torsion-free APIs.
The two proof-dependency nodes lem-trf-geometric-pure-fibre-point-dimension and
lem-trf-field-extension-component-local-dimension have no Lean record or Mathlib
match in the read checkout; they are not imported or duplicated. They are not
needed to formulate this statement. The other Mathlib proof dependencies are
available through the imported flatness, closed-immersion, finite morphism,
quasi-separatedness, pullback, function-field and localization modules.

Edge cases checked: D may be empty, with zero degree and no chosen section;
finite flat schemes are not assumed to have positive rank. H may be trivial or
act nonfaithfully and nontrivially on k. S₀ may have dimension zero, when both
birational models specialize to the same generic field. S₀, S, T, V and N are
nonempty by the actual integrality assumptions, not by an added marking condition.
No normality is assumed. The convention sentence defining normality introduces no
hypothesis. Empty special fibres have no components, so the purity quantifier is
vacuous there, as required by the node. All schemes and residue-field algebraic
closures use universe u, and the group may lie in an independent universe v.

Searches (2026-10-24):

- msearch leanfinder, "Flat generic closures of a curve and a finite marking
  inherit equivariance after base change along a birational domination": eight
  hits about Weierstrass base change; no matching result.
- msearch loogle, "AlgebraicGeometry.Flat, AlgebraicGeometry.Scheme.Hom.ker":
  zero hits.
- msearch grep, "schematicClosure|schematicallyDense|[Ff]lat.*[Kk]er|[Kk]er.*[Ff]lat"
  in AlgebraicGeometry: zero hits.
- msearch leansearch, "Flat scheme over integral base is schematic closure of
  generic fibre and inherits finite group action": eight flatness-definition and
  elementary flatness API hits; no matching closure-equivariance theorem.
- rg in Mathlib AlgebraicGeometry for birationality found `Scheme.PartialIso`;
  its full structure and docstring supply exactly dense source and target opens.
- rg in WeilConjectures and Sheaf for Birational, SchemeAction, generic closure,
  pure dimension, schematic closure, and flat/kernel patterns found related
  preparation and strict-transform results, but no theorem with this statement.
  In particular `exists_equivariant_flat_curve_preparation` is a downstream
  existential preparation theorem, not this arbitrary-domination theorem.
- rg for the node id in WeilConjectures and for the chosen declaration name in
  Mathlib, WeilConjectures and Sheaf found no existing declaration.

Source check: read ILO X Theorem 3.4, Step 2, printed p. 160: after flattening,
proper transforms coincide with base changes. Read Stacks divisors.tex
lemma-strict-transform-flat (080F) and morphisms.tex
lemma-characterize-scheme-theoretically-dense (01RE). The invariant-kernel
extension is explicitly agent-written in this node and is preserved here.
No statement fault or dispute was found; no statement correction is made.

Validation: the first server compile exposed under-specified categories in the
geometric-fibre pullbacks; these were repaired by `(C := Scheme.{u})`.
Final server compilation and the delivery preflight are recorded by the delivery tool.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module defines `schemeModuleSupport` stalkwise and states the finite affine support theorem with the field, finite-type, quasi-compact, coherent, zero-dimensional-support, and invertible-module hypotheses. The conclusion supplies a finite-dimensional `k`-algebra, closed immersion from its spectrum, coherent module, pushforward and tensor isomorphisms, and cohomology linear equivalences for every degree.

Dependencies used: Mathlib scheme, closed immersion, finite-dimensionality and topological Krull dimension; `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; `Sheaf.AlgebraicGeometry.Coherent`; `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`.

Edge cases considered: empty support (the zero algebra), one-point support, and degree zero cohomology.

Searches: grep and ripgrep over Mathlib, `WeilConjectures/`, and `lean/Sheaf`; no existing theorem states this result or a stalkwise support for arbitrary scheme modules.

## Earlier second reading (a previous round; superseded)

The theorem binds the field and finite-type scheme hypotheses, a coherent module, the zero-dimensional
stalkwise support hypothesis, and an invertible twist. Its existential conclusion gives a finite-dimensional
algebra, spectrum closed immersion, coherent module, module and tensor comparison isomorphisms, and additive
cohomology comparisons in every degree. The support definition is stalkwise, so empty support is allowed.

## New nodes

Added `def-pc-module-support`, defining support as the set of points with nontrivial stalk. Searches found no existing Mathlib or source declaration for arbitrary scheme-module support.

## Second reading by C1

I read the item node and both delivered modules independently, the dependency nodes and their
recorded declarations, and Stacks `varieties.tex`, `lemma-chi-tensor-finite` (0AYT), lines
6207--6262, and `lemma-algebraic-scheme-dim-0` (06LH), lines 3735--3780, from the local source
copy `/home/ubuntu/c1-stacks-review/varieties.tex`. The repository's literature checkout is
absent on this machine. The source lemma assumes properness; the particular support construction
in its proof uses only finite type, as the item's statement explicitly does. Its scheme-theoretic
support is closed, algebraic and zero-dimensional, so 06LH applies without properness or
separatedness of X. I have kept the node's own statement unchanged.

Clause-by-clause list, in the order of the node:

- Field k: `{k : Type v} [Field k]`. Exact; no characteristic or algebraic-closure condition.
- Finite-type k-scheme X: `(X : Scheme.{v}) [X.Over (Spec (.of k))]`, with
  `[LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]`.
  Exact finite-type convention, with no extra Noetherian, proper or separated hypothesis.
  I read the Mathlib Scheme, finite-type and quasi-compact definitions.
- Coherent O_X-module F: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. Exact. The recorded Coherent module
  defines finite type plus finite-type kernels of all maps from finite free modules on opens,
  not merely finite presentation or quasi-coherence.
- Support dimension at most zero: `(hS : topologicalKrullDim (schemeModuleSupport F) ≤ 0)`.
  Exact: the support coerces to its subtype with the subspace topology; Mathlib uses
  `WithBot ℕ∞`, including dimension minus infinity for empty support.
- Invertible N: `(N : X.Modules) [N.IsInvertible]`. Exact recorded notion from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, locally the structure sheaf.
- Finite-dimensional k-algebra A: existential `A : Type v`, `CommRing A`, `Algebra k A`,
  `FiniteDimensional k A`. Exact; a zero ring is permitted. Mathlib's finite-dimensional
  abbreviation is finite generation as a vector space; no dimension bound is imposed.
- Closed immersion i: existential `i : Spec (CommRingCat.of A) ⟶ X`, `IsClosedImmersion i`.
  Exact. Added `i ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k A))`
  to express that the algebra structure is the one induced by this subscheme over k,
  rather than an unrelated action on the same ring. This makes explicit the source's
  finite-over-k construction, not a new geometric hypothesis.
- Coherent module G on Spec A: existential G and
  `RingedSpace.IsCoherent (Spec (CommRingCat.of A)).toRingedSpace G`. Exact.
- Underlying set equals support: restored `Set.range i.base = schemeModuleSupport F`.
  Missing in the first file; the closed immersion supplies the identification/homeomorphism.
- F is closed pushforward: `Nonempty (F ≅ (Scheme.Modules.pushforward i).obj G)`.
  Exact O_X-module isomorphism, using Mathlib's recorded sectionwise module pushforward.
- Tensor projection comparison: `Nonempty (Scheme.Modules.tensorObj F N ≅
  (Scheme.Modules.pushforward i).obj (Scheme.Modules.tensorObj G
  ((Scheme.Modules.tensorPullback i).obj N)))`. Repaired the wrong pullback notion
  and put the tensor factors in the node's order. The recorded `tensorPullback` is
  O_Z tensor over i^{-1} O_X with i^{-1} N; I read its ring map, object and functor definitions.
- Twisted coherence: restored `RingedSpace.IsCoherent X.toRingedSpace
  (Scheme.Modules.tensorObj F N)`. Missing previously.
- Twisted support: restored `schemeModuleSupport (Scheme.Modules.tensorObj F N) =
  schemeModuleSupport F`. Missing previously.
- Cohomology in every degree: each of the two final clauses quantifies `∀ q : ℕ` and
  states a module isomorphism from `(RingedSpace.moduleCohomology X.toRingedSpace q).obj`
  applied to F or F tensor N to the corresponding cohomology on Spec A, with
  `ModuleCat.restrictScalars i.appTop.hom` on the target. This uses the recorded right
  derived global-sections functor on O-module sheaves, not the source's Ext of underlying
  abelian sheaves. It retains global-function linearity and therefore k-linearity. The
  closed-immersion comparison gives these isomorphisms; the proof docstring now records
  that construction. The existential isomorphism convention is the one used by the
  project's cohomology nodes; neither a choice of bases nor a dimension equality substitutes
  for a cohomology isomorphism. The first file had only arbitrary additive equivalences
  on the abelian-sheaf Ext encoding, so it did not retain the stated scalar structure.

Dependencies: retained the exact Scheme, morphism-convention, IsCoherent,
`topologicalKrullDim`, Scheme.Modules.IsInvertible, FiniteDimensional and closed-immersion
notions already recorded by the node. Read `Scheme.Modules.eulerChar` and its underlying
`Scheme.Modules.H`: H is explicitly abelian-sheaf Ext. Following the standing convention
COHOMOLOGY OF O_X-MODULES, added the already-landed `def-sc-ringed-space-module-cohomology`
and used `Sheaf.Topology.RingedSpaceModuleCohomology` instead. Also added the already-landed
`def-pc-module-pullback` for its tensor pullback. These are dependency citations, not new
or copied definitions; no dependency module was required. Removed the unused source
ProjectionFormula and Cohomology.Defs imports and added only imports used by the signature.

Edge cases: empty support and F = 0 allow the zero k-algebra (there is no `Nontrivial A`
binder); Spec of that algebra is empty and its image is the empty support. The empty X case
also has no excluded object or point binder. Nonempty finite support, including a single
closed point with a residue extension, is covered without requiring rational points or an
algebraically closed field. Degree q = 0 is included; every q > 0 is included. There is no
index set or tensor-power parameter n in this node. All fields and characteristics are
allowed. The arbitrary universe v is shared by the field, scheme and algebra, as in the
recorded scheme-over-field convention; no independent lower test universe or hidden
unbound variable is used. `relaxedAutoImplicit = false` server compilation succeeded.

Independent searches (different terms from the first worker):

- LeanSearch via msearch: `locus of nonzero stalks of a module sheaf` returned HTTP 500,
  recorded as unavailable, not as a successful negative search.
- LeanFinder via msearch: `sheaf nonzero stalk locus finite length coherent module` returned
  finite-type module sheaves and local generators, and ring-module `Module.support`/
  `Module.rankAtStalk_pos_iff_mem_support`; none defines support of an arbitrary scheme module
  or this finite closed-support theorem.
- Loogle via msearch: `SheafOfModules, stalk` returned no hits (`stalk` is not recognized
  as a global search identifier). No claim of a successful negative lookup is made.
- rg over Mathlib module sheaves, Topology/Sheaves, AlgebraicGeometry, the complete project's
  lean/Sheaf, and WeilConjectures for support/stalk, definitions of support, finite support,
  and coherent support; `tools/blueprint_refs.py search support` and rg of DAG definition ids.
  The matches are ideal-sheaf quotient support, ring-module support, Weil-sheaf support on
  finite closed points, and étale/geometric stalk supports. I opened the source's
  `Etale.sheafSupport` (Perverse/Basic): it is a closure locus on another site, not this
  arbitrary O_X-module stalk locus. There is no existing matching declaration/node to reuse.

New-node reading: `def-pc-module-support` is genuinely needed and is in the item's chapter
and unit, with its ancestor and via as required. Its data is exactly
`{x | Nontrivial (F.presheaf.stalk x)}`: a module stalk is nonzero exactly when its additive
carrier is nontrivial. There is no sorry or hidden structure choice. I repaired its prose
statement to self-contained TeX with both scheme and module-sheaf dependency citations,
updated its search records with the actual independent results, and added the missing
module header/docstring. Its empty proof, null mathlib_match, created and lean_audit fields
meet the new-node contract. Source 0AYT identifies the topological support with the
annihilator subscheme; the stalkwise support is the usual support used there.

Other repairs: both modules now have source-bearing module docstrings and the standard
copyright header. The theorem docstring now carries all four node proof steps with their
named dependencies, including the empty-support construction. The only proof remains
`by sorry`; no theorem was proved and no hollow definition was introduced. Both node
lean.statement strings match their source signatures verbatim after whitespace normalization.

Validation: compiled both delivery modules together using scompile.py, in dependency order
ModuleSupport then ZeroSupportFiniteScheme: clean, exit 0, compiled in 2.0 seconds. No errors
or non-sorry warnings. Delivery dry run and final delivery are recorded by deliver2.py.

## Reviewer fix (R-zsf1216)

The new definition node def-pc-module-support (`schemeModuleSupport`, `Nontrivial` stalk) is dropped
(--drop-nodes): Supp(F) is written inline in the landed form `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`
used by the sibling lem-pc-chi-zero-dim-support (EulerCharZeroDimSupport), so there is one form of the
notion. The module ModuleSupport.lean is not landed; the theorem's three support occurrences are inlined.
Cohomology stays `RingedSpace.moduleCohomology` (STATE line COHOMOLOGY OF O_X-MODULES).

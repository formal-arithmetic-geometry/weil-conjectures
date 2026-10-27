## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedPushforwardPseudoCoherence` states
`AlgebraicGeometry.Scheme.isMPseudoCoherent_closed_pushforward_iff`, with one `sorry`
and no definitions. The item node changes only in `lean`.

Source read: `literature/stacks-project/perfect.tex`,
`lemma-closed-push-pseudo-coherent`, lines 2925–3025 (Tag 09VA, confirmed in
`tags/tags`). Its two induction arguments give exactly this scheme specialization.
The module docstring and declaration docstring identify the source and node;
the declaration docstring carries all ten steps of the accepted DAG proof.
No statement correction or disputed statement was needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes Z and P: `{Z P : Scheme.{u}}`.
- A closed immersion i:Z→P: `(i : Z ⟶ P) [IsClosedImmersion i]`.
- The ordinary direct-image structure module is
  `(RingedSpace.moduleDirectImage i.toLRSHom.toShHom).obj
  (SheafOfModules.unit (moduleRings Z.toRingedSpace))`.
  The source of `moduleDirectImage` was read in full: it is Mathlib's
  `SheafOfModules.pushforward` along the inverse-image functor on opens, with
  scalar action through i-sharp. This is ordinary pushforward, not Ri_*.
- Place that module in degree zero by
  `(DerivedCategory.singleFunctor (SheafOfModules.{u}
  (moduleRings P.toRingedSpace)) 0).obj`.
- Its pseudo-coherence is precisely the hypothesis `h : IsPseudoCoherent P (...)`.
- Every integer m: `(m : ℤ)`, allowing negative, zero and positive degrees.
- Every K in the unbounded derived category: `(K : schemeDerivedCategory Z)`.
- The conclusion is exactly `IsMPseudoCoherent Z m K ↔
  IsMPseudoCoherent P m ((schemeDerivedDirectImage i).obj K)`.
  The same m appears on both sides and the equivalence gives both directions.
- The absence of quasi-coherence, boundedness and Noetherian assumptions is respected:
  K is in the entire derived category and there are no such binders on K, Z or P.
- The `HasDerivedCategory` binders supply the chosen localizations required by the
  recorded definitions. `wZ` and `wP` are independent. For both schemes the
  open-subscheme localizations supply `IsMPseudoCoherent`; for P the over-site
  localizations also supply `IsPseudoCoherent`. These are size/construction
  parameters, not additional geometric or cohomological hypotheses.

Statement dependencies used, with their exact recorded declarations and source modules:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`,
  `Mathlib.AlgebraicGeometry.Scheme`; the locally affine locally ringed space
  structure and `Scheme.Hom` were read.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; a closed embedding with
  surjective stalk maps.
- `def-pur-pseudo-coherent-complex`: `AlgebraicGeometry.Scheme.IsPseudoCoherent`,
  `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`; the full definition
  uses local bounded-above finite free models on the over-site.
- `def-pc-derived-category`: `AlgebraicGeometry.schemeDerivedCategory`,
  `WeilConjectures.AlgebraicGeometry.DerivedCategory`; the shared
  `SheafOfModules.{u} (moduleRings ...)` abelian carrier, not the distinct
  category instance on the `Scheme.Modules` abbreviation.
- `def-sfb-m-pseudo-coherent-complex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`,
  `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`; read the full definition,
  including canonical transport of a strictly perfect complex from the over-site
  to the open subscheme, its map to the derived pullback, isomorphisms above m,
  and epimorphism in degree m.
- `def-pc-derived-direct-image`: `AlgebraicGeometry.schemeDerivedDirectImage`,
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`; it is precisely
  `RingedSpace.derivedModuleDirectImage` of the underlying morphism.
  `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage` was also
  read, including `moduleDirectImage`, the right derived functor definition,
  and its K-injective computation theorem.

All six statement dependency modules are public imports. Plain proof imports cover
all currently recorded proof dependencies: closed-pushforward exactness and stalks,
ringed-site modules, ringed-space derived direct image, exact-functor derived
factorization, perfect complexes, finite type/presentation, locally surjective
sheaf epimorphisms, triangulated categories, and the homology long exact sequence.
Mathlib matches are imported from their recorded modules. The two proof-only nodes
`lem-sfb-ringed-site-pseudocoherent-top-finite-type` and
`lem-sfb-ringed-site-m-pseudocoherent-triangle` have no Lean declaration or Mathlib
match yet, so have no module to import; both remain named in the proof docstring.
They are not needed to state this theorem. No existing consumer modules are edited.

Edge cases checked mathematically against the source and expanded DAG proof:
empty Z, empty P, the identity closed immersion, K=0, acyclic K, arbitrary integers
m, and K unbounded below or with no global upper bound. Empty schemes impose no
pointwise approximation conditions. Off i(Z) the pushforward is zero. The identity
reduces to the same local approximation condition on both sides. The induction
base uses an upper bound p=m-1 rather than a highest nonzero cohomology group, so
acyclic objects and rank-zero approximations are included. Any needed upper bound
is obtained locally from the side assumed m-pseudo-coherent; none is a binder.

Searches for an existing statement (all made before writing):

- `msearch.py ... leanfinder`: "For a closed immersion with pseudo coherent
  pushed forward structure sheaf derived direct image preserves and reflects
  m pseudo coherence". Eight hits: ordinary pushforward, full/faithful
  pushforward for open immersions, closed immersion, and module pseudofunctors;
  none is this theorem.
- `msearch.py ... loogle`: `"IsMPseudoCoherent", "pushforward"`: zero hits.
- `msearch.py ... grep`:
  `pseudo.?[Cc]oher.*(push|closed)|(push|closed).*pseudo.?[Cc]oher`: zero Mathlib hits.
- `msearch.py ... leansearch`: "Closed immersion derived pushforward preserves
  and reflects m pseudo coherence assuming the ordinary pushforward of the
  structure sheaf is pseudo coherent". Eight hits: closed immersion properties
  and ordinary module pushforward; none is the theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, the same pseudo-coherence /
  pushforward pattern and the item id: only source comments in consumers such as
  `AffinePolynomialEmbeddingPseudoCoherence`, `AffinePrincipalRelativePseudoCoherenceGluing`
  and `AffinePrincipalRelativePseudoCoherenceLocalization`; no existing assertion.
- `rg` over both source trees and `dag/lean_names_upstream.json` for
  `isMPseudoCoherent.*closed|closed.*isMPseudoCoherent`: no declaration/name clash.
- The example CompactObject node now points to the upstream definition and its
  old Sheaf module is withdrawn; both records and the upstream example were read.

Validation: prescribed `scompile.py NK lem-sfb-closed-pushforward-pseudocoherence`
compiled this file as both sandbox and library module, cleanly in 10.0 s and 7.1 s.
Every line is at most 100 characters; `autoImplicit false` is set and every universe
is explicitly declared. The only proof is the requested `sorry`.

## Second reading by NK

A second pass by the same worker reopened the node, source and completed Lean file.
No separate agent was started, as the dispatch brief forbids that; the maintainer's
independent delivery review remains the independent review.

On this pass the closed-immersion binder, ordinary pushed-forward structure module,
degree-zero embedding, pseudo-coherent hypothesis, arbitrary integer, arbitrary
unbounded derived object, and both directions at the same integer were matched
again. The `IsMPseudoCoherent` signature needs localizations on open subschemes,
whereas `IsPseudoCoherent` needs localizations on the over-site; the statement
explicitly supplies both interfaces rather than replacing either definition.
No mismatch was found and no mathematical statement was changed.
